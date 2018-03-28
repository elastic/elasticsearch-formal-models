-------------------------- MODULE ReplicaEngine --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

(* Actions on the Lucene index *)
CONSTANTS Lucene_addDocuments, Lucene_updateDocuments, Lucene_deleteDocuments

CONSTANTS ADD, RETRY_ADD, UPDATE, DELETE, NULL

CONSTANTS DocContent

CONSTANTS DocAutoIdTimestamp

CONSTANTS DuplicationLimit

(* We model the activity of a single document, since distinct documents
   (according to their IDs) are independent. Also each indexing operation
   occurs under a lock for that document ID, so there is not much concurrency
   to consider. *)


(* The set of individual requests that can occur on the document *)
Request(request_count)
    (* ADD: An optimised append-only write can only occur as the first operation
    on the document ID in seqno order. Any subsequent attempts to ADD the
    document have the retry flag set and modelled as a RETRY_ADD. Other operations
    on the document are also possible. *)
    ==    [type : {ADD}, seqno : {1}, content : DocContent, autoIdTimeStamp : {DocAutoIdTimestamp}]
    (* RETRY_ADD: A retry of a write that does involve an internally-generated
       document ID. *)
    \cup  [type : {RETRY_ADD}, seqno : 1..request_count, content : DocContent, autoIdTimeStamp : {DocAutoIdTimestamp}]
    (* UPDATE: A write that does not involve an internally-generated document ID. *)
    \cup  [type : {UPDATE}, seqno : 1..request_count, content : DocContent]
    (* DELETE *)
    \cup  [type : {DELETE}, seqno : 1..request_count]

(* The set of sets of requests, which have distinct seqnos *)
RequestSet(request_count)
    == { rs \in SUBSET Request(request_count):
                /\ Cardinality(rs)                   = request_count
                /\ Cardinality({r.seqno : r \in rs}) = request_count
                /\ (* Also ADDs and RETRY_ADDs should have the same content *)
                   Cardinality({r.content: r \in { r \in rs: r.type \in {ADD, RETRY_ADD}}}) <= 1
       }

(* Apply a set of operations to a document in seqno order *)
RECURSIVE ApplyOps(_, _, _)
ApplyOps(requests, nextSeqno, currentContent)
    == IF   \A r \in requests: r.seqno < nextSeqno
       THEN currentContent
       ELSE LET r == CHOOSE r \in requests: r.seqno = nextSeqno
            IN IF r \in requests /\ r.seqno = nextSeqno
               THEN ApplyOps(requests, nextSeqno + 1,
                        CASE r.type = DELETE    -> NULL
                          [] r.type = ADD       -> r.content
                          [] r.type = RETRY_ADD -> r.content
                          [] r.type = UPDATE    -> r.content)
               ELSE Assert(FALSE, "Bad sequence")

(* Calculate the final doc by applying all the requests in order *)
FinalDoc(requests) == ApplyOps(requests, 1, NULL)

(* Apply each the operation in the Lucene buffer, rejecting an
   addDocuments when there is already a document present as this
   would lead to duplication. *)
RECURSIVE ApplyBufferedOperations(_, _)
ApplyBufferedOperations(buffer, origDoc)
    == IF buffer = <<>>
       THEN origDoc
       ELSE LET nextOp  == Head(buffer)
         IN ApplyBufferedOperations(Tail(buffer),
            CASE       nextOp.type = Lucene_deleteDocuments -> NULL
              [] \/    nextOp.type = Lucene_updateDocuments
                 \/ /\ nextOp.type = Lucene_addDocuments
                    /\ origDoc = NULL                       -> [content |-> nextOp.content, seqno |-> nextOp.seqno]
              [] OTHER -> Assert(FALSE, "Error: Lucene_addDocuments when origDoc /= NULL"))

Max(a,b) == IF a <= b THEN b ELSE a

(* --algorithm basic

variables
    request_count \in 1..4,
    replication_requests \in RequestSet(request_count),
    expected_doc = FinalDoc(replication_requests),
    versionMap_needsSafeAccess = FALSE,
    versionMap_isUnsafe = FALSE,
    versionMap_entry = NULL,

(* Other concurrent activity can flag that the version map needs to be safely accessed *)
process SafeAccessEnablerProcess = "SafeAccessEnabler"
begin
    SafeAccessEnablerLoop:
    while pc["Consumer"] /= "Done" do
        versionMap_needsSafeAccess := (versionMap_needsSafeAccess = FALSE);
        (* Technically the only way this can go back to FALSE is via a refresh, but
           we should not need this fact, so model both kinds of change. *)
    end while;
end process;

(* Other concurrent activity can make the version map become unsafe, if safe access mode is disabled *)
process UnsafePutterProcess = "UnsafePutter"
begin
    UnsafePutterLoop:
    while pc["Consumer"] /= "Done" do
        await versionMap_needsSafeAccess = FALSE;
        versionMap_isUnsafe := TRUE;
    end while;
end process;

(* Other concurrent activity can increase the maxUnsafeAutoIdTimestamp *)
process MaxUnsafeAutoIdTimestampIncreaserProcess = "MaxUnsafeAutoIdTimestampIncreaser"
begin
    MaxUnsafeAutoIdTimestampIncreaserLoop:
    while pc["Consumer"] /= "Done" do
        with newTimestamp \in {DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1} do
            await maxUnsafeAutoIdTimestamp < newTimestamp;
            maxUnsafeAutoIdTimestamp := newTimestamp;
        end with;
    end while;
end process;

(* Lucene refreshes can happen at any time *)
process LuceneProcess = "ReplicaLucene"
variables
    lucene_document = NULL,
    lucene_buffer   = <<>>,
begin
    LuceneLoop:
    while pc["Consumer"] /= "Done" \/ lucene_buffer /= <<>> do

        lucene_document := ApplyBufferedOperations(lucene_buffer, lucene_document);
        lucene_buffer := <<>>;
            
        (* TODO Model the inner structure of the version map so this refresh can be
        broken into the individual steps that occur concurrently with ongoing indexing. *)
                        
        versionMap_isUnsafe := FALSE;
        versionMap_needsSafeAccess := FALSE;
        
        if versionMap_entry /= NULL
        then
            if versionMap_entry.type = UPDATE
            then
                versionMap_entry := NULL;
            else
                assert versionMap_entry.type = DELETE;
                versionMap_entry := [ versionMap_entry EXCEPT !.flushed = TRUE ];
            end if;
        end if;           
    end while;
end process;

(* Flushed deletes expire after a time and are cleaned up *)
process DeleteCollectorProcess = "DeleteCollector"
begin
    DeleteCollectorLoop:
    while pc["Consumer"] /= "Done" do
        await /\ versionMap_entry /= NULL
              /\ versionMap_entry.type = DELETE
              /\ versionMap_entry.seqno <= localCheckPoint \* PR #28790
              /\ versionMap_entry.flushed = TRUE;
        versionMap_entry := NULL;
    end while;
end process;

(* Local checkpoint advances as each operation is marked as completed *)
process LocalCheckpointTrackerProcess = "LocalCheckpointTracker"
variables
    localCheckPoint = 0,
    completedSeqnos = {}
begin
    LocalCheckpointTrackerLoop:
    while pc["Consumer"] /= "Done" do
        await localCheckPoint + 1 \in completedSeqnos;
        localCheckPoint := localCheckPoint + 1;
    end while;
end process

process UnsafeSeqnoIncreaserProcess = "UnsafeSeqnoIncreaserProcess"
variables
    maxSeqNoOfNonAppendOnlyOperations = 0,
begin
    UnsafeSeqnoIncreaserProcessLoop:
    while pc["Consumer"] /= "Done" /\ maxSeqNoOfNonAppendOnlyOperations < request_count + 1 do
        maxSeqNoOfNonAppendOnlyOperations := maxSeqNoOfNonAppendOnlyOperations + 1;
    end while;
end process


(* The process that consumes replication requests for a particular document ID, which
   are processed in series because of the lock in the version map. *)
process ConsumerProcess = "Consumer"
variables
    duplicationCount = 0,
    maxUnsafeAutoIdTimestamp \in {0, DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1},
    req, plan,
    deleteFromLucene, currentlyDeleted,
    currentNotFoundOrDeleted, useLuceneUpdateDocument, indexIntoLucene,
begin
  ConsumerLoop:
  while replication_requests /= {} do
    with replication_request \in replication_requests do
        if replication_request.type = ADD
        then
            (* Never see two ADDs - if duplicated, one of them is a RETRY_ADD *)
            either
                (* Process ADD without duplication *)
                replication_requests := replication_requests \ {replication_request};
                req := replication_request;
            or
                await duplicationCount < DuplicationLimit;
                duplicationCount := duplicationCount + 1;
                
                (* Process ADD and leave a duplicate RETRY_ADD for later *)
                replication_requests := (replication_requests \ {replication_request})
                    \cup {[replication_request EXCEPT !.type = RETRY_ADD]};
                req := replication_request;
            or
                await duplicationCount < DuplicationLimit;
                duplicationCount := duplicationCount + 1;

                (* Process duplicate RETRY_ADD and leave the original ADD *)
                req := [replication_request EXCEPT !.type = RETRY_ADD];
            end either;
        else
            req := replication_request;
            either
                await duplicationCount < DuplicationLimit;
                duplicationCount := duplicationCount + 1;
            or
                replication_requests := replication_requests \ {replication_request};
            end either;
        end if;
    end with;
    
    if req.type = DELETE
    then

        versionMap_needsSafeAccess := TRUE;    
    
        (* planDeletionAsNonPrimary *)
        
        maxSeqNoOfNonAppendOnlyOperations := Max(maxSeqNoOfNonAppendOnlyOperations, req.seqno);

        if req.seqno <= localCheckPoint
        then
            (* OP_STALE_OR_EQUAL *)
            plan             := "processButSkipLucene";
            deleteFromLucene := FALSE;
            currentlyDeleted := FALSE;
        else
            if versionMap_isUnsafe
            then
                (* Perform a Lucene refresh *)
                AwaitRefreshOnDelete: \* Label here to allow for other concurrent activity
                await lucene_buffer = <<>>;
                versionMap_needsSafeAccess := TRUE;
            end if;
        
            compareDeleteOpToLuceneDocBasedOnSeqNo: \* Label needed because of AwaitRefreshOnDelete label
    
            if versionMap_entry /= NULL
            then
                (* Doc is in version map *)
                if req.seqno > versionMap_entry.seqno
                then
                    (* OP_NEWER *)
                    plan := "processNormally";
                    deleteFromLucene := TRUE;
                    currentlyDeleted := FALSE;
                else
                    (* OP_STALE_OR_EQUAL *)
                    plan := "processButSkipLucene";
                    deleteFromLucene := FALSE;
                    currentlyDeleted := FALSE;
                end if;
            else
                (* Doc is not in version map - check Lucene *)
                if lucene_document = NULL
                then
                    (* LUCENE_DOC_NOT_FOUND *)
                    plan := "processNormallyExceptNotFound";
                    deleteFromLucene := TRUE;
                    currentlyDeleted := TRUE;
                else
                    if req.seqno > lucene_document.seqno
                    then
                        (* OP_NEWER *)
                        plan := "processNormally";                 
                        deleteFromLucene := TRUE;
                        currentlyDeleted := FALSE;
                    else
                        (* OP_STALE_OR_EQUAL *)
                        plan := "processButSkipLucene";                  
                        deleteFromLucene := FALSE;
                        currentlyDeleted := FALSE;
                    end if;
                end if;
            end if;
        end if;
        
        ExecuteDeletePlan:  \* Label needed because of AwaitRefreshOnDelete label
        if deleteFromLucene
        then
            if currentlyDeleted = FALSE
            then
                lucene_buffer := Append(lucene_buffer, [ type |-> Lucene_deleteDocuments ]);
            end if;

            versionMap_entry := [ type |-> DELETE, seqno |-> req.seqno, flushed |-> FALSE ];
        end if;
    
        completedSeqnos := completedSeqnos \cup {req.seqno};
    else

        (* planIndexingAsNonPrimary *)
        
        (* A RETRY_ADD has canOptimiseAddDocument = TRUE and
            mayHaveBeenIndexedBefore = TRUE so is planned normally,
            but also updates maxUnsafeAutoIdTimestamp within
            mayHaveBeenIndexedBefore() *)

        if req.type = RETRY_ADD
        then
            maxUnsafeAutoIdTimestamp := Max(maxUnsafeAutoIdTimestamp, req.autoIdTimeStamp);
        end if;
           
        (* An ADD can be optimized if mayHaveBeenIndexedBefore = FALSE
            which is calculated by comparing timestamps. *)
        
        if /\ req.type = ADD
           /\ maxUnsafeAutoIdTimestamp < req.autoIdTimeStamp
           /\ maxSeqNoOfNonAppendOnlyOperations < req.seqno \* PR #28787
        then
            plan                     := "optimisedAppendOnly";
            currentNotFoundOrDeleted := TRUE;
            useLuceneUpdateDocument  := FALSE;
            indexIntoLucene          := TRUE;
        else
            if req.type \notin {ADD, RETRY_ADD}
            then
                maxSeqNoOfNonAppendOnlyOperations := Max(maxSeqNoOfNonAppendOnlyOperations, req.seqno);
            end if;
        
            (* All other operations are planned normally *)
            versionMap_needsSafeAccess := TRUE;
            
            if req.seqno <= localCheckPoint
            then
                (* OP_STALE_OR_EQUAL *)        
                plan                     := "processButSkipLucene";
                currentNotFoundOrDeleted := FALSE;
                useLuceneUpdateDocument  := FALSE;
                indexIntoLucene          := FALSE;
            else
                if versionMap_isUnsafe
                then
                    (* Perform a Lucene refresh *)
                    AwaitRefreshOnIndex: \* Label here to allow for other concurrent activity
                    await lucene_buffer = <<>>;
                    versionMap_needsSafeAccess := TRUE;                
                end if;
            
                compareIndexOpToLuceneDocBasedOnSeqNo: \* Label needed because of AwaitRefreshOnIndex label
                
                if req.seqno <= localCheckPoint                         \* PR #29276
                then                                                    \* PR #29276
                    (* OP_STALE_OR_EQUAL *)                             \* PR #29276
                    plan                     := "processButSkipLucene"; \* PR #29276
                    currentNotFoundOrDeleted := FALSE;                  \* PR #29276
                    useLuceneUpdateDocument  := FALSE;                  \* PR #29276
                    indexIntoLucene          := FALSE;                  \* PR #29276
                elsif versionMap_entry /= NULL
                then
                    (* Doc is in version map *)
                    if req.seqno > versionMap_entry.seqno
                    then
                        (* OP_NEWER *)
                        plan := "processNormally";
                        currentNotFoundOrDeleted := FALSE;
                        useLuceneUpdateDocument  := TRUE;
                        indexIntoLucene          := TRUE;
                    else
                        (* OP_STALE_OR_EQUAL *)
                        plan := "processButSkipLucene";
                        currentNotFoundOrDeleted := FALSE;
                        useLuceneUpdateDocument  := FALSE;
                        indexIntoLucene          := FALSE;
                    end if;
                else
                    (* Doc is not in version map - check Lucene *)
                    if lucene_document = NULL
                    then
                        (* LUCENE_DOC_NOT_FOUND *)
                        plan := "processNormallyExceptNotFound";
                        currentNotFoundOrDeleted := TRUE;
                        useLuceneUpdateDocument  := FALSE;
                        indexIntoLucene          := TRUE;
                    else
                        if req.seqno > lucene_document.seqno
                        then
                            (* OP_NEWER *)
                            plan := "processNormally";                 
                            currentNotFoundOrDeleted := FALSE;
                            useLuceneUpdateDocument  := TRUE;
                            indexIntoLucene          := TRUE;
                        else
                            (* OP_STALE_OR_EQUAL *)
                            plan := "processButSkipLucene";                  
                            currentNotFoundOrDeleted := FALSE;
                            useLuceneUpdateDocument  := FALSE;
                            indexIntoLucene          := FALSE;
                        end if;
                    end if;
                end if;
            end if;
        end if;
        
        (* planIndexingAsNonPrimary finished - now time to execute the plan *)
        ExecuteIndexPlan: \* Label needed because of AwaitRefreshOnIndex label
        
        if indexIntoLucene
        then
            lucene_buffer := Append(lucene_buffer, 
                [ type    |-> IF useLuceneUpdateDocument THEN Lucene_updateDocuments ELSE Lucene_addDocuments
                , seqno   |-> req.seqno
                , content |-> req.content
                ]);

            if versionMap_needsSafeAccess
            then
                versionMap_entry := [ type |-> UPDATE, seqno |-> req.seqno ];
            else
                versionMap_isUnsafe := TRUE;

                if /\ versionMap_entry /= NULL
                   /\ versionMap_entry.type = DELETE
                   /\ versionMap_entry.seqno < req.seqno
                then
                    versionMap_entry := NULL; \* Desync bug #3 (no PR number yet)
                end if;
            end if;
        end if;
        
        completedSeqnos := completedSeqnos \cup {req.seqno}
    end if;
  end while;
end process

end algorithm

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES request_count, replication_requests, expected_doc, 
          versionMap_needsSafeAccess, versionMap_isUnsafe, versionMap_entry, 
          pc, lucene_document, lucene_buffer, localCheckPoint, 
          completedSeqnos, maxSeqNoOfNonAppendOnlyOperations, 
          duplicationCount, maxUnsafeAutoIdTimestamp, req, plan, 
          deleteFromLucene, currentlyDeleted, currentNotFoundOrDeleted, 
          useLuceneUpdateDocument, indexIntoLucene

vars == << request_count, replication_requests, expected_doc, 
           versionMap_needsSafeAccess, versionMap_isUnsafe, versionMap_entry, 
           pc, lucene_document, lucene_buffer, localCheckPoint, 
           completedSeqnos, maxSeqNoOfNonAppendOnlyOperations, 
           duplicationCount, maxUnsafeAutoIdTimestamp, req, plan, 
           deleteFromLucene, currentlyDeleted, currentNotFoundOrDeleted, 
           useLuceneUpdateDocument, indexIntoLucene >>

ProcSet == {"SafeAccessEnabler"} \cup {"UnsafePutter"} \cup {"MaxUnsafeAutoIdTimestampIncreaser"} \cup {"ReplicaLucene"} \cup {"DeleteCollector"} \cup {"LocalCheckpointTracker"} \cup {"UnsafeSeqnoIncreaserProcess"} \cup {"Consumer"}

Init == (* Global variables *)
        /\ request_count \in 1..4
        /\ replication_requests \in RequestSet(request_count)
        /\ expected_doc = FinalDoc(replication_requests)
        /\ versionMap_needsSafeAccess = FALSE
        /\ versionMap_isUnsafe = FALSE
        /\ versionMap_entry = NULL
        (* Process LuceneProcess *)
        /\ lucene_document = NULL
        /\ lucene_buffer = <<>>
        (* Process LocalCheckpointTrackerProcess *)
        /\ localCheckPoint = 0
        /\ completedSeqnos = {}
        (* Process UnsafeSeqnoIncreaserProcess *)
        /\ maxSeqNoOfNonAppendOnlyOperations = 0
        (* Process ConsumerProcess *)
        /\ duplicationCount = 0
        /\ maxUnsafeAutoIdTimestamp \in {0, DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1}
        /\ req = defaultInitValue
        /\ plan = defaultInitValue
        /\ deleteFromLucene = defaultInitValue
        /\ currentlyDeleted = defaultInitValue
        /\ currentNotFoundOrDeleted = defaultInitValue
        /\ useLuceneUpdateDocument = defaultInitValue
        /\ indexIntoLucene = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "SafeAccessEnabler" -> "SafeAccessEnablerLoop"
                                        [] self = "UnsafePutter" -> "UnsafePutterLoop"
                                        [] self = "MaxUnsafeAutoIdTimestampIncreaser" -> "MaxUnsafeAutoIdTimestampIncreaserLoop"
                                        [] self = "ReplicaLucene" -> "LuceneLoop"
                                        [] self = "DeleteCollector" -> "DeleteCollectorLoop"
                                        [] self = "LocalCheckpointTracker" -> "LocalCheckpointTrackerLoop"
                                        [] self = "UnsafeSeqnoIncreaserProcess" -> "UnsafeSeqnoIncreaserProcessLoop"
                                        [] self = "Consumer" -> "ConsumerLoop"]

SafeAccessEnablerLoop == /\ pc["SafeAccessEnabler"] = "SafeAccessEnablerLoop"
                         /\ IF pc["Consumer"] /= "Done"
                               THEN /\ versionMap_needsSafeAccess' = (versionMap_needsSafeAccess = FALSE)
                                    /\ pc' = [pc EXCEPT !["SafeAccessEnabler"] = "SafeAccessEnablerLoop"]
                               ELSE /\ pc' = [pc EXCEPT !["SafeAccessEnabler"] = "Done"]
                                    /\ UNCHANGED versionMap_needsSafeAccess
                         /\ UNCHANGED << request_count, replication_requests, 
                                         expected_doc, versionMap_isUnsafe, 
                                         versionMap_entry, lucene_document, 
                                         lucene_buffer, localCheckPoint, 
                                         completedSeqnos, 
                                         maxSeqNoOfNonAppendOnlyOperations, 
                                         duplicationCount, 
                                         maxUnsafeAutoIdTimestamp, req, plan, 
                                         deleteFromLucene, currentlyDeleted, 
                                         currentNotFoundOrDeleted, 
                                         useLuceneUpdateDocument, 
                                         indexIntoLucene >>

SafeAccessEnablerProcess == SafeAccessEnablerLoop

UnsafePutterLoop == /\ pc["UnsafePutter"] = "UnsafePutterLoop"
                    /\ IF pc["Consumer"] /= "Done"
                          THEN /\ versionMap_needsSafeAccess = FALSE
                               /\ versionMap_isUnsafe' = TRUE
                               /\ pc' = [pc EXCEPT !["UnsafePutter"] = "UnsafePutterLoop"]
                          ELSE /\ pc' = [pc EXCEPT !["UnsafePutter"] = "Done"]
                               /\ UNCHANGED versionMap_isUnsafe
                    /\ UNCHANGED << request_count, replication_requests, 
                                    expected_doc, versionMap_needsSafeAccess, 
                                    versionMap_entry, lucene_document, 
                                    lucene_buffer, localCheckPoint, 
                                    completedSeqnos, 
                                    maxSeqNoOfNonAppendOnlyOperations, 
                                    duplicationCount, maxUnsafeAutoIdTimestamp, 
                                    req, plan, deleteFromLucene, 
                                    currentlyDeleted, currentNotFoundOrDeleted, 
                                    useLuceneUpdateDocument, indexIntoLucene >>

UnsafePutterProcess == UnsafePutterLoop

MaxUnsafeAutoIdTimestampIncreaserLoop == /\ pc["MaxUnsafeAutoIdTimestampIncreaser"] = "MaxUnsafeAutoIdTimestampIncreaserLoop"
                                         /\ IF pc["Consumer"] /= "Done"
                                               THEN /\ \E newTimestamp \in {DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1}:
                                                         /\ maxUnsafeAutoIdTimestamp < newTimestamp
                                                         /\ maxUnsafeAutoIdTimestamp' = newTimestamp
                                                    /\ pc' = [pc EXCEPT !["MaxUnsafeAutoIdTimestampIncreaser"] = "MaxUnsafeAutoIdTimestampIncreaserLoop"]
                                               ELSE /\ pc' = [pc EXCEPT !["MaxUnsafeAutoIdTimestampIncreaser"] = "Done"]
                                                    /\ UNCHANGED maxUnsafeAutoIdTimestamp
                                         /\ UNCHANGED << request_count, 
                                                         replication_requests, 
                                                         expected_doc, 
                                                         versionMap_needsSafeAccess, 
                                                         versionMap_isUnsafe, 
                                                         versionMap_entry, 
                                                         lucene_document, 
                                                         lucene_buffer, 
                                                         localCheckPoint, 
                                                         completedSeqnos, 
                                                         maxSeqNoOfNonAppendOnlyOperations, 
                                                         duplicationCount, req, 
                                                         plan, 
                                                         deleteFromLucene, 
                                                         currentlyDeleted, 
                                                         currentNotFoundOrDeleted, 
                                                         useLuceneUpdateDocument, 
                                                         indexIntoLucene >>

MaxUnsafeAutoIdTimestampIncreaserProcess == MaxUnsafeAutoIdTimestampIncreaserLoop

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF pc["Consumer"] /= "Done" \/ lucene_buffer /= <<>>
                    THEN /\ lucene_document' = ApplyBufferedOperations(lucene_buffer, lucene_document)
                         /\ lucene_buffer' = <<>>
                         /\ versionMap_isUnsafe' = FALSE
                         /\ versionMap_needsSafeAccess' = FALSE
                         /\ IF versionMap_entry /= NULL
                               THEN /\ IF versionMap_entry.type = UPDATE
                                          THEN /\ versionMap_entry' = NULL
                                          ELSE /\ Assert(versionMap_entry.type = DELETE, 
                                                         "Failure of assertion at line 147, column 17.")
                                               /\ versionMap_entry' = [ versionMap_entry EXCEPT !.flushed = TRUE ]
                               ELSE /\ TRUE
                                    /\ UNCHANGED versionMap_entry
                         /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneLoop"]
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
                         /\ UNCHANGED << versionMap_needsSafeAccess, 
                                         versionMap_isUnsafe, versionMap_entry, 
                                         lucene_document, lucene_buffer >>
              /\ UNCHANGED << request_count, replication_requests, 
                              expected_doc, localCheckPoint, completedSeqnos, 
                              maxSeqNoOfNonAppendOnlyOperations, 
                              duplicationCount, maxUnsafeAutoIdTimestamp, req, 
                              plan, deleteFromLucene, currentlyDeleted, 
                              currentNotFoundOrDeleted, 
                              useLuceneUpdateDocument, indexIntoLucene >>

LuceneProcess == LuceneLoop

DeleteCollectorLoop == /\ pc["DeleteCollector"] = "DeleteCollectorLoop"
                       /\ IF pc["Consumer"] /= "Done"
                             THEN /\ /\ versionMap_entry /= NULL
                                     /\ versionMap_entry.type = DELETE
                                     /\ versionMap_entry.seqno <= localCheckPoint
                                     /\ versionMap_entry.flushed = TRUE
                                  /\ versionMap_entry' = NULL
                                  /\ pc' = [pc EXCEPT !["DeleteCollector"] = "DeleteCollectorLoop"]
                             ELSE /\ pc' = [pc EXCEPT !["DeleteCollector"] = "Done"]
                                  /\ UNCHANGED versionMap_entry
                       /\ UNCHANGED << request_count, replication_requests, 
                                       expected_doc, 
                                       versionMap_needsSafeAccess, 
                                       versionMap_isUnsafe, lucene_document, 
                                       lucene_buffer, localCheckPoint, 
                                       completedSeqnos, 
                                       maxSeqNoOfNonAppendOnlyOperations, 
                                       duplicationCount, 
                                       maxUnsafeAutoIdTimestamp, req, plan, 
                                       deleteFromLucene, currentlyDeleted, 
                                       currentNotFoundOrDeleted, 
                                       useLuceneUpdateDocument, 
                                       indexIntoLucene >>

DeleteCollectorProcess == DeleteCollectorLoop

LocalCheckpointTrackerLoop == /\ pc["LocalCheckpointTracker"] = "LocalCheckpointTrackerLoop"
                              /\ IF pc["Consumer"] /= "Done"
                                    THEN /\ localCheckPoint + 1 \in completedSeqnos
                                         /\ localCheckPoint' = localCheckPoint + 1
                                         /\ pc' = [pc EXCEPT !["LocalCheckpointTracker"] = "LocalCheckpointTrackerLoop"]
                                    ELSE /\ pc' = [pc EXCEPT !["LocalCheckpointTracker"] = "Done"]
                                         /\ UNCHANGED localCheckPoint
                              /\ UNCHANGED << request_count, 
                                              replication_requests, 
                                              expected_doc, 
                                              versionMap_needsSafeAccess, 
                                              versionMap_isUnsafe, 
                                              versionMap_entry, 
                                              lucene_document, lucene_buffer, 
                                              completedSeqnos, 
                                              maxSeqNoOfNonAppendOnlyOperations, 
                                              duplicationCount, 
                                              maxUnsafeAutoIdTimestamp, req, 
                                              plan, deleteFromLucene, 
                                              currentlyDeleted, 
                                              currentNotFoundOrDeleted, 
                                              useLuceneUpdateDocument, 
                                              indexIntoLucene >>

LocalCheckpointTrackerProcess == LocalCheckpointTrackerLoop

UnsafeSeqnoIncreaserProcessLoop == /\ pc["UnsafeSeqnoIncreaserProcess"] = "UnsafeSeqnoIncreaserProcessLoop"
                                   /\ IF pc["Consumer"] /= "Done" /\ maxSeqNoOfNonAppendOnlyOperations < request_count + 1
                                         THEN /\ maxSeqNoOfNonAppendOnlyOperations' = maxSeqNoOfNonAppendOnlyOperations + 1
                                              /\ pc' = [pc EXCEPT !["UnsafeSeqnoIncreaserProcess"] = "UnsafeSeqnoIncreaserProcessLoop"]
                                         ELSE /\ pc' = [pc EXCEPT !["UnsafeSeqnoIncreaserProcess"] = "Done"]
                                              /\ UNCHANGED maxSeqNoOfNonAppendOnlyOperations
                                   /\ UNCHANGED << request_count, 
                                                   replication_requests, 
                                                   expected_doc, 
                                                   versionMap_needsSafeAccess, 
                                                   versionMap_isUnsafe, 
                                                   versionMap_entry, 
                                                   lucene_document, 
                                                   lucene_buffer, 
                                                   localCheckPoint, 
                                                   completedSeqnos, 
                                                   duplicationCount, 
                                                   maxUnsafeAutoIdTimestamp, 
                                                   req, plan, deleteFromLucene, 
                                                   currentlyDeleted, 
                                                   currentNotFoundOrDeleted, 
                                                   useLuceneUpdateDocument, 
                                                   indexIntoLucene >>

UnsafeSeqnoIncreaserProcess == UnsafeSeqnoIncreaserProcessLoop

ConsumerLoop == /\ pc["Consumer"] = "ConsumerLoop"
                /\ IF replication_requests /= {}
                      THEN /\ \E replication_request \in replication_requests:
                                IF replication_request.type = ADD
                                   THEN /\ \/ /\ replication_requests' = replication_requests \ {replication_request}
                                              /\ req' = replication_request
                                              /\ UNCHANGED duplicationCount
                                           \/ /\ duplicationCount < DuplicationLimit
                                              /\ duplicationCount' = duplicationCount + 1
                                              /\ replication_requests' =                     (replication_requests \ {replication_request})
                                                                         \cup {[replication_request EXCEPT !.type = RETRY_ADD]}
                                              /\ req' = replication_request
                                           \/ /\ duplicationCount < DuplicationLimit
                                              /\ duplicationCount' = duplicationCount + 1
                                              /\ req' = [replication_request EXCEPT !.type = RETRY_ADD]
                                              /\ UNCHANGED replication_requests
                                   ELSE /\ req' = replication_request
                                        /\ \/ /\ duplicationCount < DuplicationLimit
                                              /\ duplicationCount' = duplicationCount + 1
                                              /\ UNCHANGED replication_requests
                                           \/ /\ replication_requests' = replication_requests \ {replication_request}
                                              /\ UNCHANGED duplicationCount
                           /\ IF req'.type = DELETE
                                 THEN /\ versionMap_needsSafeAccess' = TRUE
                                      /\ maxSeqNoOfNonAppendOnlyOperations' = Max(maxSeqNoOfNonAppendOnlyOperations, req'.seqno)
                                      /\ IF req'.seqno <= localCheckPoint
                                            THEN /\ plan' = "processButSkipLucene"
                                                 /\ deleteFromLucene' = FALSE
                                                 /\ currentlyDeleted' = FALSE
                                                 /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteDeletePlan"]
                                            ELSE /\ IF versionMap_isUnsafe
                                                       THEN /\ pc' = [pc EXCEPT !["Consumer"] = "AwaitRefreshOnDelete"]
                                                       ELSE /\ pc' = [pc EXCEPT !["Consumer"] = "compareDeleteOpToLuceneDocBasedOnSeqNo"]
                                                 /\ UNCHANGED << plan, 
                                                                 deleteFromLucene, 
                                                                 currentlyDeleted >>
                                      /\ UNCHANGED << maxUnsafeAutoIdTimestamp, 
                                                      currentNotFoundOrDeleted, 
                                                      useLuceneUpdateDocument, 
                                                      indexIntoLucene >>
                                 ELSE /\ IF req'.type = RETRY_ADD
                                            THEN /\ maxUnsafeAutoIdTimestamp' = Max(maxUnsafeAutoIdTimestamp, req'.autoIdTimeStamp)
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED maxUnsafeAutoIdTimestamp
                                      /\ IF /\ req'.type = ADD
                                            /\ maxUnsafeAutoIdTimestamp' < req'.autoIdTimeStamp
                                            /\ maxSeqNoOfNonAppendOnlyOperations < req'.seqno
                                            THEN /\ plan' = "optimisedAppendOnly"
                                                 /\ currentNotFoundOrDeleted' = TRUE
                                                 /\ useLuceneUpdateDocument' = FALSE
                                                 /\ indexIntoLucene' = TRUE
                                                 /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteIndexPlan"]
                                                 /\ UNCHANGED << versionMap_needsSafeAccess, 
                                                                 maxSeqNoOfNonAppendOnlyOperations >>
                                            ELSE /\ IF req'.type \notin {ADD, RETRY_ADD}
                                                       THEN /\ maxSeqNoOfNonAppendOnlyOperations' = Max(maxSeqNoOfNonAppendOnlyOperations, req'.seqno)
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED maxSeqNoOfNonAppendOnlyOperations
                                                 /\ versionMap_needsSafeAccess' = TRUE
                                                 /\ IF req'.seqno <= localCheckPoint
                                                       THEN /\ plan' = "processButSkipLucene"
                                                            /\ currentNotFoundOrDeleted' = FALSE
                                                            /\ useLuceneUpdateDocument' = FALSE
                                                            /\ indexIntoLucene' = FALSE
                                                            /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteIndexPlan"]
                                                       ELSE /\ IF versionMap_isUnsafe
                                                                  THEN /\ pc' = [pc EXCEPT !["Consumer"] = "AwaitRefreshOnIndex"]
                                                                  ELSE /\ pc' = [pc EXCEPT !["Consumer"] = "compareIndexOpToLuceneDocBasedOnSeqNo"]
                                                            /\ UNCHANGED << plan, 
                                                                            currentNotFoundOrDeleted, 
                                                                            useLuceneUpdateDocument, 
                                                                            indexIntoLucene >>
                                      /\ UNCHANGED << deleteFromLucene, 
                                                      currentlyDeleted >>
                      ELSE /\ pc' = [pc EXCEPT !["Consumer"] = "Done"]
                           /\ UNCHANGED << replication_requests, 
                                           versionMap_needsSafeAccess, 
                                           maxSeqNoOfNonAppendOnlyOperations, 
                                           duplicationCount, 
                                           maxUnsafeAutoIdTimestamp, req, plan, 
                                           deleteFromLucene, currentlyDeleted, 
                                           currentNotFoundOrDeleted, 
                                           useLuceneUpdateDocument, 
                                           indexIntoLucene >>
                /\ UNCHANGED << request_count, expected_doc, 
                                versionMap_isUnsafe, versionMap_entry, 
                                lucene_document, lucene_buffer, 
                                localCheckPoint, completedSeqnos >>

ExecuteDeletePlan == /\ pc["Consumer"] = "ExecuteDeletePlan"
                     /\ IF deleteFromLucene
                           THEN /\ IF currentlyDeleted = FALSE
                                      THEN /\ lucene_buffer' = Append(lucene_buffer, [ type |-> Lucene_deleteDocuments ])
                                      ELSE /\ TRUE
                                           /\ UNCHANGED lucene_buffer
                                /\ versionMap_entry' = [ type |-> DELETE, seqno |-> req.seqno, flushed |-> FALSE ]
                           ELSE /\ TRUE
                                /\ UNCHANGED << versionMap_entry, 
                                                lucene_buffer >>
                     /\ completedSeqnos' = (completedSeqnos \cup {req.seqno})
                     /\ pc' = [pc EXCEPT !["Consumer"] = "ConsumerLoop"]
                     /\ UNCHANGED << request_count, replication_requests, 
                                     expected_doc, versionMap_needsSafeAccess, 
                                     versionMap_isUnsafe, lucene_document, 
                                     localCheckPoint, 
                                     maxSeqNoOfNonAppendOnlyOperations, 
                                     duplicationCount, 
                                     maxUnsafeAutoIdTimestamp, req, plan, 
                                     deleteFromLucene, currentlyDeleted, 
                                     currentNotFoundOrDeleted, 
                                     useLuceneUpdateDocument, indexIntoLucene >>

ExecuteIndexPlan == /\ pc["Consumer"] = "ExecuteIndexPlan"
                    /\ IF indexIntoLucene
                          THEN /\ lucene_buffer' =              Append(lucene_buffer,
                                                   [ type    |-> IF useLuceneUpdateDocument THEN Lucene_updateDocuments ELSE Lucene_addDocuments
                                                   , seqno   |-> req.seqno
                                                   , content |-> req.content
                                                   ])
                               /\ IF versionMap_needsSafeAccess
                                     THEN /\ versionMap_entry' = [ type |-> UPDATE, seqno |-> req.seqno ]
                                          /\ UNCHANGED versionMap_isUnsafe
                                     ELSE /\ versionMap_isUnsafe' = TRUE
                                          /\ IF /\ versionMap_entry /= NULL
                                                /\ versionMap_entry.type = DELETE
                                                /\ versionMap_entry.seqno < req.seqno
                                                THEN /\ versionMap_entry' = NULL
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED versionMap_entry
                          ELSE /\ TRUE
                               /\ UNCHANGED << versionMap_isUnsafe, 
                                               versionMap_entry, lucene_buffer >>
                    /\ completedSeqnos' = (completedSeqnos \cup {req.seqno})
                    /\ pc' = [pc EXCEPT !["Consumer"] = "ConsumerLoop"]
                    /\ UNCHANGED << request_count, replication_requests, 
                                    expected_doc, versionMap_needsSafeAccess, 
                                    lucene_document, localCheckPoint, 
                                    maxSeqNoOfNonAppendOnlyOperations, 
                                    duplicationCount, maxUnsafeAutoIdTimestamp, 
                                    req, plan, deleteFromLucene, 
                                    currentlyDeleted, currentNotFoundOrDeleted, 
                                    useLuceneUpdateDocument, indexIntoLucene >>

compareDeleteOpToLuceneDocBasedOnSeqNo == /\ pc["Consumer"] = "compareDeleteOpToLuceneDocBasedOnSeqNo"
                                          /\ IF versionMap_entry /= NULL
                                                THEN /\ IF req.seqno > versionMap_entry.seqno
                                                           THEN /\ plan' = "processNormally"
                                                                /\ deleteFromLucene' = TRUE
                                                                /\ currentlyDeleted' = FALSE
                                                           ELSE /\ plan' = "processButSkipLucene"
                                                                /\ deleteFromLucene' = FALSE
                                                                /\ currentlyDeleted' = FALSE
                                                ELSE /\ IF lucene_document = NULL
                                                           THEN /\ plan' = "processNormallyExceptNotFound"
                                                                /\ deleteFromLucene' = TRUE
                                                                /\ currentlyDeleted' = TRUE
                                                           ELSE /\ IF req.seqno > lucene_document.seqno
                                                                      THEN /\ plan' = "processNormally"
                                                                           /\ deleteFromLucene' = TRUE
                                                                           /\ currentlyDeleted' = FALSE
                                                                      ELSE /\ plan' = "processButSkipLucene"
                                                                           /\ deleteFromLucene' = FALSE
                                                                           /\ currentlyDeleted' = FALSE
                                          /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteDeletePlan"]
                                          /\ UNCHANGED << request_count, 
                                                          replication_requests, 
                                                          expected_doc, 
                                                          versionMap_needsSafeAccess, 
                                                          versionMap_isUnsafe, 
                                                          versionMap_entry, 
                                                          lucene_document, 
                                                          lucene_buffer, 
                                                          localCheckPoint, 
                                                          completedSeqnos, 
                                                          maxSeqNoOfNonAppendOnlyOperations, 
                                                          duplicationCount, 
                                                          maxUnsafeAutoIdTimestamp, 
                                                          req, 
                                                          currentNotFoundOrDeleted, 
                                                          useLuceneUpdateDocument, 
                                                          indexIntoLucene >>

AwaitRefreshOnDelete == /\ pc["Consumer"] = "AwaitRefreshOnDelete"
                        /\ lucene_buffer = <<>>
                        /\ versionMap_needsSafeAccess' = TRUE
                        /\ pc' = [pc EXCEPT !["Consumer"] = "compareDeleteOpToLuceneDocBasedOnSeqNo"]
                        /\ UNCHANGED << request_count, replication_requests, 
                                        expected_doc, versionMap_isUnsafe, 
                                        versionMap_entry, lucene_document, 
                                        lucene_buffer, localCheckPoint, 
                                        completedSeqnos, 
                                        maxSeqNoOfNonAppendOnlyOperations, 
                                        duplicationCount, 
                                        maxUnsafeAutoIdTimestamp, req, plan, 
                                        deleteFromLucene, currentlyDeleted, 
                                        currentNotFoundOrDeleted, 
                                        useLuceneUpdateDocument, 
                                        indexIntoLucene >>

compareIndexOpToLuceneDocBasedOnSeqNo == /\ pc["Consumer"] = "compareIndexOpToLuceneDocBasedOnSeqNo"
                                         /\ IF req.seqno <= localCheckPoint
                                               THEN /\ plan' = "processButSkipLucene"
                                                    /\ currentNotFoundOrDeleted' = FALSE
                                                    /\ useLuceneUpdateDocument' = FALSE
                                                    /\ indexIntoLucene' = FALSE
                                               ELSE /\ IF versionMap_entry /= NULL
                                                          THEN /\ IF req.seqno > versionMap_entry.seqno
                                                                     THEN /\ plan' = "processNormally"
                                                                          /\ currentNotFoundOrDeleted' = FALSE
                                                                          /\ useLuceneUpdateDocument' = TRUE
                                                                          /\ indexIntoLucene' = TRUE
                                                                     ELSE /\ plan' = "processButSkipLucene"
                                                                          /\ currentNotFoundOrDeleted' = FALSE
                                                                          /\ useLuceneUpdateDocument' = FALSE
                                                                          /\ indexIntoLucene' = FALSE
                                                          ELSE /\ IF lucene_document = NULL
                                                                     THEN /\ plan' = "processNormallyExceptNotFound"
                                                                          /\ currentNotFoundOrDeleted' = TRUE
                                                                          /\ useLuceneUpdateDocument' = FALSE
                                                                          /\ indexIntoLucene' = TRUE
                                                                     ELSE /\ IF req.seqno > lucene_document.seqno
                                                                                THEN /\ plan' = "processNormally"
                                                                                     /\ currentNotFoundOrDeleted' = FALSE
                                                                                     /\ useLuceneUpdateDocument' = TRUE
                                                                                     /\ indexIntoLucene' = TRUE
                                                                                ELSE /\ plan' = "processButSkipLucene"
                                                                                     /\ currentNotFoundOrDeleted' = FALSE
                                                                                     /\ useLuceneUpdateDocument' = FALSE
                                                                                     /\ indexIntoLucene' = FALSE
                                         /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteIndexPlan"]
                                         /\ UNCHANGED << request_count, 
                                                         replication_requests, 
                                                         expected_doc, 
                                                         versionMap_needsSafeAccess, 
                                                         versionMap_isUnsafe, 
                                                         versionMap_entry, 
                                                         lucene_document, 
                                                         lucene_buffer, 
                                                         localCheckPoint, 
                                                         completedSeqnos, 
                                                         maxSeqNoOfNonAppendOnlyOperations, 
                                                         duplicationCount, 
                                                         maxUnsafeAutoIdTimestamp, 
                                                         req, deleteFromLucene, 
                                                         currentlyDeleted >>

AwaitRefreshOnIndex == /\ pc["Consumer"] = "AwaitRefreshOnIndex"
                       /\ lucene_buffer = <<>>
                       /\ versionMap_needsSafeAccess' = TRUE
                       /\ pc' = [pc EXCEPT !["Consumer"] = "compareIndexOpToLuceneDocBasedOnSeqNo"]
                       /\ UNCHANGED << request_count, replication_requests, 
                                       expected_doc, versionMap_isUnsafe, 
                                       versionMap_entry, lucene_document, 
                                       lucene_buffer, localCheckPoint, 
                                       completedSeqnos, 
                                       maxSeqNoOfNonAppendOnlyOperations, 
                                       duplicationCount, 
                                       maxUnsafeAutoIdTimestamp, req, plan, 
                                       deleteFromLucene, currentlyDeleted, 
                                       currentNotFoundOrDeleted, 
                                       useLuceneUpdateDocument, 
                                       indexIntoLucene >>

ConsumerProcess == ConsumerLoop \/ ExecuteDeletePlan \/ ExecuteIndexPlan
                      \/ compareDeleteOpToLuceneDocBasedOnSeqNo
                      \/ AwaitRefreshOnDelete
                      \/ compareIndexOpToLuceneDocBasedOnSeqNo
                      \/ AwaitRefreshOnIndex

Next == SafeAccessEnablerProcess \/ UnsafePutterProcess
           \/ MaxUnsafeAutoIdTimestampIncreaserProcess \/ LuceneProcess
           \/ DeleteCollectorProcess \/ LocalCheckpointTrackerProcess
           \/ UnsafeSeqnoIncreaserProcess \/ ConsumerProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

Invariant == Terminated => /\ expected_doc  = NULL => lucene_document = NULL
                           /\ expected_doc /= NULL => lucene_document.content = expected_doc

=============================================================================
