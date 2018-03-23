-------------------------- MODULE ReplicaEngine --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

(* Actions on the Lucene index *)
CONSTANTS Lucene_addDocuments, Lucene_updateDocuments, Lucene_deleteDocuments

CONSTANTS ADD, RETRY_ADD, UPDATE, DELETE, NULL

CONSTANTS DocContent

CONSTANTS DocAutoIdTimestamp

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
    ==    { [type |-> ADD, seqno |-> 1, content |-> content, autoIdTimeStamp |-> DocAutoIdTimestamp]
          : content \in DocContent
          }
    (* RETRY_ADD: A retry of a write that does involve an internally-generated
       document ID. *)
    \cup  { [type |-> RETRY_ADD, seqno |-> seqno, content |-> content, autoIdTimeStamp |-> DocAutoIdTimestamp]
          : seqno   \in 1..request_count
          , content \in DocContent
          }
    (* UPDATE: A write that does not involve an internally-generated document ID. *)
    \cup  { [type |-> UPDATE, seqno |-> seqno, content |-> content]
          : seqno   \in 1..request_count
          , content \in DocContent
          }
    (* DELETE *)
    \cup  { [type |-> DELETE, seqno |-> seqno]
          : seqno \in 1..request_count
          }

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
        versionMap_needsSafeAccess := TRUE;
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
            
        LuceneUpdateVersionMap: (* TODO needs an invariant saying that the VM is >= Lucene and also contains the buffered ops *)
                        
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

(* The process that consumes replication requests for a particular document ID, which
   are processed in series because of the lock in the version map. *)
process ConsumerProcess = "Consumer"
variables
    maxUnsafeAutoIdTimestamp \in {0, DocAutoIdTimestamp - 1, DocAutoIdTimestamp, DocAutoIdTimestamp + 1},
    req, plan,
    deleteFromLucene, currentlyDeleted,
    currentNotFoundOrDeleted, useLuceneUpdateDocument, indexIntoLucene,
begin
  ConsumerLoop:
  while replication_requests /= {} do
    with replication_request \in replication_requests do
        req := replication_request;
        replication_requests := replication_requests \ {replication_request};
    end with;
    
    if req.type = DELETE
    then

        versionMap_needsSafeAccess := TRUE;    
    
        (* planDeletionAsNonPrimary *)
        
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
        then
            plan                     := "optimisedAppendOnly";
            currentNotFoundOrDeleted := TRUE;
            useLuceneUpdateDocument  := FALSE;
            indexIntoLucene          := TRUE;
        else
        
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
                
                if versionMap_entry /= NULL
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
          pc, lucene, localCheckPoint, completedSeqnos, 
          maxUnsafeAutoIdTimestamp, req, plan, deleteFromLucene, 
          currentlyDeleted, currentNotFoundOrDeleted, useLuceneUpdateDocument, 
          indexIntoLucene

vars == << request_count, replication_requests, expected_doc, 
           versionMap_needsSafeAccess, versionMap_isUnsafe, versionMap_entry, 
           pc, lucene, localCheckPoint, completedSeqnos, 
           maxUnsafeAutoIdTimestamp, req, plan, deleteFromLucene, 
           currentlyDeleted, currentNotFoundOrDeleted, 
           useLuceneUpdateDocument, indexIntoLucene >>

ProcSet == {"SafeAccessEnabler"} \cup {"UnsafePutter"} \cup {"MaxUnsafeAutoIdTimestampIncreaser"} \cup {"ReplicaLucene"} \cup {"DeleteCollector"} \cup {"LocalCheckpointTracker"} \cup {"Consumer"}

Init == (* Global variables *)
        /\ request_count \in 1..4
        /\ replication_requests \in RequestSet(request_count)
        /\ expected_doc = FinalDoc(replication_requests)
        /\ versionMap_needsSafeAccess = FALSE
        /\ versionMap_isUnsafe = FALSE
        /\ versionMap_entry = NULL
        (* Process LuceneProcess *)
        /\ lucene = [ document |-> NULL
                    , buffer   |-> <<>>
                    ]
        (* Process LocalCheckpointTrackerProcess *)
        /\ localCheckPoint = 0
        /\ completedSeqnos = {}
        (* Process ConsumerProcess *)
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
                                        [] self = "Consumer" -> "ConsumerLoop"]

SafeAccessEnablerLoop == /\ pc["SafeAccessEnabler"] = "SafeAccessEnablerLoop"
                         /\ IF pc["Consumer"] /= "Done"
                               THEN /\ versionMap_needsSafeAccess' = TRUE
                                    /\ pc' = [pc EXCEPT !["SafeAccessEnabler"] = "SafeAccessEnablerLoop"]
                               ELSE /\ pc' = [pc EXCEPT !["SafeAccessEnabler"] = "Done"]
                                    /\ UNCHANGED versionMap_needsSafeAccess
                         /\ UNCHANGED << request_count, replication_requests, 
                                         expected_doc, versionMap_isUnsafe, 
                                         versionMap_entry, lucene, 
                                         localCheckPoint, completedSeqnos, 
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
                                    versionMap_entry, lucene, localCheckPoint, 
                                    completedSeqnos, maxUnsafeAutoIdTimestamp, 
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
                                                         lucene, 
                                                         localCheckPoint, 
                                                         completedSeqnos, req, 
                                                         plan, 
                                                         deleteFromLucene, 
                                                         currentlyDeleted, 
                                                         currentNotFoundOrDeleted, 
                                                         useLuceneUpdateDocument, 
                                                         indexIntoLucene >>

MaxUnsafeAutoIdTimestampIncreaserProcess == MaxUnsafeAutoIdTimestampIncreaserLoop

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF pc["Consumer"] /= "Done" \/ lucene.buffer /= <<>>
                    THEN /\ lucene.buffer /= <<>>
                         /\ lucene' =       [lucene EXCEPT
                                      !.document = ApplyBufferedOperations(lucene.buffer, @),
                                      !.buffer   = <<>>
                                      ]
                         /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneUpdateVersionMap"]
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
                         /\ UNCHANGED lucene
              /\ UNCHANGED << request_count, replication_requests, 
                              expected_doc, versionMap_needsSafeAccess, 
                              versionMap_isUnsafe, versionMap_entry, 
                              localCheckPoint, completedSeqnos, 
                              maxUnsafeAutoIdTimestamp, req, plan, 
                              deleteFromLucene, currentlyDeleted, 
                              currentNotFoundOrDeleted, 
                              useLuceneUpdateDocument, indexIntoLucene >>

LuceneUpdateVersionMap == /\ pc["ReplicaLucene"] = "LuceneUpdateVersionMap"
                          /\ versionMap_isUnsafe' = FALSE
                          /\ versionMap_needsSafeAccess' = FALSE
                          /\ IF versionMap_entry /= NULL
                                THEN /\ IF versionMap_entry.type = UPDATE
                                           THEN /\ versionMap_entry' = NULL
                                           ELSE /\ Assert(versionMap_entry.type = DELETE, 
                                                          "Failure of assertion at line 158, column 17.")
                                                /\ versionMap_entry' = [ versionMap_entry EXCEPT !.flushed = TRUE ]
                                ELSE /\ TRUE
                                     /\ UNCHANGED versionMap_entry
                          /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneLoop"]
                          /\ UNCHANGED << request_count, replication_requests, 
                                          expected_doc, lucene, 
                                          localCheckPoint, completedSeqnos, 
                                          maxUnsafeAutoIdTimestamp, req, plan, 
                                          deleteFromLucene, currentlyDeleted, 
                                          currentNotFoundOrDeleted, 
                                          useLuceneUpdateDocument, 
                                          indexIntoLucene >>

LuceneProcess == LuceneLoop \/ LuceneUpdateVersionMap

DeleteCollectorLoop == /\ pc["DeleteCollector"] = "DeleteCollectorLoop"
                       /\ IF pc["Consumer"] /= "Done"
                             THEN /\ /\ versionMap_entry /= NULL
                                     /\ versionMap_entry.type = DELETE
                                     /\ versionMap_entry.flushed = TRUE
                                  /\ versionMap_entry' = NULL
                                  /\ pc' = [pc EXCEPT !["DeleteCollector"] = "DeleteCollectorLoop"]
                             ELSE /\ pc' = [pc EXCEPT !["DeleteCollector"] = "Done"]
                                  /\ UNCHANGED versionMap_entry
                       /\ UNCHANGED << request_count, replication_requests, 
                                       expected_doc, 
                                       versionMap_needsSafeAccess, 
                                       versionMap_isUnsafe, lucene, 
                                       localCheckPoint, completedSeqnos, 
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
                                              versionMap_entry, lucene, 
                                              completedSeqnos, 
                                              maxUnsafeAutoIdTimestamp, req, 
                                              plan, deleteFromLucene, 
                                              currentlyDeleted, 
                                              currentNotFoundOrDeleted, 
                                              useLuceneUpdateDocument, 
                                              indexIntoLucene >>

LocalCheckpointTrackerProcess == LocalCheckpointTrackerLoop

ConsumerLoop == /\ pc["Consumer"] = "ConsumerLoop"
                /\ IF replication_requests /= {}
                      THEN /\ \E replication_request \in replication_requests:
                                /\ req' = replication_request
                                /\ replication_requests' = replication_requests \ {replication_request}
                           /\ IF req'.type = DELETE
                                 THEN /\ IF req'.seqno <= localCheckPoint
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
                                      /\ UNCHANGED << versionMap_needsSafeAccess, 
                                                      maxUnsafeAutoIdTimestamp, 
                                                      currentNotFoundOrDeleted, 
                                                      useLuceneUpdateDocument, 
                                                      indexIntoLucene >>
                                 ELSE /\ IF req'.type = RETRY_ADD
                                            THEN /\ maxUnsafeAutoIdTimestamp' = Max(maxUnsafeAutoIdTimestamp, req'.autoIdTimeStamp)
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED maxUnsafeAutoIdTimestamp
                                      /\ IF /\ req'.type = ADD
                                            /\ maxUnsafeAutoIdTimestamp' < req'.autoIdTimeStamp
                                            THEN /\ plan' = "optimisedAppendOnly"
                                                 /\ currentNotFoundOrDeleted' = TRUE
                                                 /\ useLuceneUpdateDocument' = FALSE
                                                 /\ indexIntoLucene' = TRUE
                                                 /\ pc' = [pc EXCEPT !["Consumer"] = "ExecuteIndexPlan"]
                                                 /\ UNCHANGED versionMap_needsSafeAccess
                                            ELSE /\ versionMap_needsSafeAccess' = TRUE
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
                                           maxUnsafeAutoIdTimestamp, req, plan, 
                                           deleteFromLucene, currentlyDeleted, 
                                           currentNotFoundOrDeleted, 
                                           useLuceneUpdateDocument, 
                                           indexIntoLucene >>
                /\ UNCHANGED << request_count, expected_doc, 
                                versionMap_isUnsafe, versionMap_entry, lucene, 
                                localCheckPoint, completedSeqnos >>

ExecuteDeletePlan == /\ pc["Consumer"] = "ExecuteDeletePlan"
                     /\ IF deleteFromLucene
                           THEN /\ IF currentlyDeleted = FALSE
                                      THEN /\ lucene' = [lucene EXCEPT !.buffer = Append(@, [ type |-> Lucene_deleteDocuments ])]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED lucene
                                /\ versionMap_entry' = [ type |-> DELETE, seqno |-> req.seqno, flushed |-> FALSE ]
                           ELSE /\ TRUE
                                /\ UNCHANGED << versionMap_entry, lucene >>
                     /\ completedSeqnos' = (completedSeqnos \cup {req.seqno})
                     /\ pc' = [pc EXCEPT !["Consumer"] = "ConsumerLoop"]
                     /\ UNCHANGED << request_count, replication_requests, 
                                     expected_doc, versionMap_needsSafeAccess, 
                                     versionMap_isUnsafe, localCheckPoint, 
                                     maxUnsafeAutoIdTimestamp, req, plan, 
                                     deleteFromLucene, currentlyDeleted, 
                                     currentNotFoundOrDeleted, 
                                     useLuceneUpdateDocument, indexIntoLucene >>

ExecuteIndexPlan == /\ pc["Consumer"] = "ExecuteIndexPlan"
                    /\ IF indexIntoLucene
                          THEN /\ lucene' =       [lucene EXCEPT !.buffer = Append(@,
                                            [ type    |-> IF useLuceneUpdateDocument THEN Lucene_updateDocuments ELSE Lucene_addDocuments
                                            , seqno   |-> req.seqno
                                            , content |-> req.content
                                            ])]
                               /\ IF versionMap_needsSafeAccess
                                     THEN /\ versionMap_entry' = [ type |-> UPDATE, seqno |-> req.seqno ]
                                          /\ UNCHANGED versionMap_isUnsafe
                                     ELSE /\ versionMap_isUnsafe' = TRUE
                                          /\ UNCHANGED versionMap_entry
                          ELSE /\ TRUE
                               /\ UNCHANGED << versionMap_isUnsafe, 
                                               versionMap_entry, lucene >>
                    /\ completedSeqnos' = (completedSeqnos \cup {req.seqno})
                    /\ pc' = [pc EXCEPT !["Consumer"] = "ConsumerLoop"]
                    /\ UNCHANGED << request_count, replication_requests, 
                                    expected_doc, versionMap_needsSafeAccess, 
                                    localCheckPoint, maxUnsafeAutoIdTimestamp, 
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
                                                ELSE /\ IF lucene.document = NULL
                                                           THEN /\ plan' = "processNormallyExceptNotFound"
                                                                /\ deleteFromLucene' = TRUE
                                                                /\ currentlyDeleted' = TRUE
                                                           ELSE /\ IF req.seqno > lucene.document.seqno
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
                                                          lucene, 
                                                          localCheckPoint, 
                                                          completedSeqnos, 
                                                          maxUnsafeAutoIdTimestamp, 
                                                          req, 
                                                          currentNotFoundOrDeleted, 
                                                          useLuceneUpdateDocument, 
                                                          indexIntoLucene >>

AwaitRefreshOnDelete == /\ pc["Consumer"] = "AwaitRefreshOnDelete"
                        /\ lucene.buffer = <<>>
                        /\ pc' = [pc EXCEPT !["Consumer"] = "compareDeleteOpToLuceneDocBasedOnSeqNo"]
                        /\ UNCHANGED << request_count, replication_requests, 
                                        expected_doc, 
                                        versionMap_needsSafeAccess, 
                                        versionMap_isUnsafe, versionMap_entry, 
                                        lucene, localCheckPoint, 
                                        completedSeqnos, 
                                        maxUnsafeAutoIdTimestamp, req, plan, 
                                        deleteFromLucene, currentlyDeleted, 
                                        currentNotFoundOrDeleted, 
                                        useLuceneUpdateDocument, 
                                        indexIntoLucene >>

compareIndexOpToLuceneDocBasedOnSeqNo == /\ pc["Consumer"] = "compareIndexOpToLuceneDocBasedOnSeqNo"
                                         /\ IF versionMap_entry /= NULL
                                               THEN /\ IF req.seqno > versionMap_entry.seqno
                                                          THEN /\ plan' = "processNormally"
                                                               /\ currentNotFoundOrDeleted' = FALSE
                                                               /\ useLuceneUpdateDocument' = TRUE
                                                               /\ indexIntoLucene' = TRUE
                                                          ELSE /\ plan' = "processButSkipLucene"
                                                               /\ currentNotFoundOrDeleted' = FALSE
                                                               /\ useLuceneUpdateDocument' = FALSE
                                                               /\ indexIntoLucene' = FALSE
                                               ELSE /\ IF lucene.document = NULL
                                                          THEN /\ plan' = "processNormallyExceptNotFound"
                                                               /\ currentNotFoundOrDeleted' = TRUE
                                                               /\ useLuceneUpdateDocument' = FALSE
                                                               /\ indexIntoLucene' = TRUE
                                                          ELSE /\ IF req.seqno > lucene.document.seqno
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
                                                         lucene, 
                                                         localCheckPoint, 
                                                         completedSeqnos, 
                                                         maxUnsafeAutoIdTimestamp, 
                                                         req, deleteFromLucene, 
                                                         currentlyDeleted >>

AwaitRefreshOnIndex == /\ pc["Consumer"] = "AwaitRefreshOnIndex"
                       /\ lucene.buffer = <<>>
                       /\ pc' = [pc EXCEPT !["Consumer"] = "compareIndexOpToLuceneDocBasedOnSeqNo"]
                       /\ UNCHANGED << request_count, replication_requests, 
                                       expected_doc, 
                                       versionMap_needsSafeAccess, 
                                       versionMap_isUnsafe, versionMap_entry, 
                                       lucene, localCheckPoint, 
                                       completedSeqnos, 
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
           \/ ConsumerProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

Invariant == Terminated => /\ expected_doc  = NULL => lucene_document = NULL
                           /\ expected_doc /= NULL => lucene_document.content = expected_doc

=============================================================================
