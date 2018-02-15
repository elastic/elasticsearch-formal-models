----------------------------- MODULE versionmap -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS INDEX, DELETE, NULL
CONSTANTS OPEN, CLOSED

ClientRequestType == {
        [op EXCEPT !.version = v]
        : op \in {[version |-> NULL, type |-> INDEX,  content |-> "A"]
                 ,[version |-> NULL, type |-> INDEX,  content |-> "B"]
                 ,[version |-> NULL, type |-> DELETE]
                 }
        , v \in ({NULL, 1, 2})
        }

(* --algorithm basic

variables
    initial_client_requests \in {x \in SUBSET ClientRequestType: Cardinality(x) <= 5},
    client_requests = initial_client_requests,
    replication_requests = {},
    isGeneratingRequests = TRUE,
    lucene =
        [ document           |-> NULL
        , buffered_operation |-> NULL
        , state              |-> OPEN
        ]

process ReplicationRequestGeneratorProcess = "ReplicationRequestGenerator"
variables
    next_seqno = 1,
    document = NULL,
    highest_document_version = 0,
begin

    GeneratorStart:
    either
        skip;
    or
        highest_document_version := highest_document_version + 1;
        document := [ version |-> highest_document_version
                    , seqno   |-> next_seqno
                    , content |-> "NEW"
                    ];
                    
        with replication_message_duplicates \in {1,2} do
            replication_requests := replication_requests
                \union {[ version     |-> highest_document_version
                        , seqno       |-> next_seqno
                        , content     |-> "NEW"
                        , type        |-> INDEX
                        , count       |-> replication_message_duplicates
                        , append_only |-> TRUE
                        ]};
        end with;
        next_seqno := next_seqno + 1;
    end either;

    GeneratorLoop:
    while client_requests /= {} do
        HandleClientRequest:
        with client_request \in client_requests do
            client_requests := client_requests \ {client_request};
            
            if \/ client_request.version = NULL
               \/ client_request.version > highest_document_version
            then
            
                highest_document_version := IF client_request.version = NULL
                                            THEN highest_document_version + 1
                                            ELSE client_request.version;
            
                with replication_message_duplicates \in {1,2} do
                
                    if client_request.type = INDEX
                    then
                        document := [ version |-> highest_document_version
                                    , seqno   |-> next_seqno
                                    , content |-> client_request.content
                                    ];
                        replication_requests := replication_requests
                            \union {[ version     |-> highest_document_version
                                    , seqno       |-> next_seqno
                                    , content     |-> client_request.content
                                    , type        |-> INDEX
                                    , count       |-> replication_message_duplicates
                                    , append_only |-> FALSE
                                    ]};
                    
                    elsif client_request.type = DELETE
                    then
                        document := NULL;
                        replication_requests := replication_requests
                            \union {[ seqno       |-> next_seqno
                                    , type        |-> DELETE
                                    , count       |-> replication_message_duplicates
                                    , append_only |-> FALSE                                    
                                    ]};
                    end if;
        
                    next_seqno := next_seqno + 1;
                end with;
            end if;
        end with;
    end while;
    isGeneratingRequests := FALSE;
end process

process LuceneProcess = "ReplicaLucene"
begin
    LuceneLoop:
    while lucene.state /= CLOSED \/ lucene.buffered_operation /= NULL do
        await lucene.buffered_operation /= NULL;
        LuceneRefresh:
        lucene := [lucene EXCEPT
            !.document =
                CASE lucene.buffered_operation.type = INDEX
                -> [ version |-> lucene.buffered_operation.version
                   , seqno   |-> lucene.buffered_operation.seqno
                   , content |-> lucene.buffered_operation.content
                   ]
                  [] lucene.buffered_operation.type = DELETE
                -> NULL,
            !.buffered_operation = NULL
            ];
        indexing_seqno := NULL;
    end while;
end process;

process ReplicaEngineProcess = "ReplicaEngine"
variables
    local_check_point = 0, (* have processed _all_ operations <= local_check_point *)
    seqnos_above_local_check_point = {},
    deletion_seqno = NULL,
    indexing_seqno = NULL,
    append_only_unsafe_up_to = 0, (* greatest seqno of non-append-only ops *)
    replication_request = NULL,
begin
    ReplicaStart:
    await ~ isGeneratingRequests;
    
    ReplicaLoop:
    while replication_requests /= {} do
    
        GetReplicationRequest:
        with next_replication_request \in replication_requests do
        
            replication_request := next_replication_request;
         
            (* consume request *)
            replication_requests := (replication_requests \ {replication_request})
                \union IF replication_request.count > 1
                       THEN {[replication_request EXCEPT !.count = replication_request.count - 1]}
                       ELSE {};
                       
        end with;
                
        if  /\ local_check_point < replication_request.seqno
            /\ replication_request.append_only
            /\ replication_request.seqno < append_only_unsafe_up_to
        then
            AwaitingRefresh:
            (* Perform a refresh *)
            await lucene.buffered_operation = NULL;
        end if;
        
        Refreshed:

        if /\ local_check_point < replication_request.seqno
           /\  replication_request.append_only
               =>  \/  append_only_unsafe_up_to < replication_request.seqno
                   \/  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                   
           /\  ~ replication_request.append_only
               =>  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                   /\  indexing_seqno  = NULL \/ indexing_seqno        < replication_request.seqno
                   /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
        then
                   
            if replication_request.seqno > local_check_point + 1
            then
                (* cannot advance local check point *)
                seqnos_above_local_check_point := seqnos_above_local_check_point
                    \union {replication_request.seqno};
                    
            else
                (* advance local check point *)
                local_check_point := CHOOSE n \in (local_check_point .. next_seqno):
                                                /\ n > local_check_point
                                                /\ (n + 1) \notin seqnos_above_local_check_point
                                                /\ ((local_check_point + 2) .. n) \subseteq seqnos_above_local_check_point;
                seqnos_above_local_check_point := { n \in seqnos_above_local_check_point: local_check_point < n };
            end if;
                    
            if ~ replication_request.append_only
            then
              append_only_unsafe_up_to := replication_request.seqno;
            end if;
                    
            if replication_request.type = INDEX
            then
                lucene.buffered_operation := replication_request;
                if replication_request.seqno <= local_check_point
                then 
                    indexing_seqno := NULL;
                else
                    indexing_seqno := replication_request.seqno;
                end if;
                
                if deletion_seqno /= NULL /\ deletion_seqno <= local_check_point
                then
                    deletion_seqno := NULL;
                end if;
                
            elsif replication_request.type = DELETE
            then
                lucene.buffered_operation := [ type |-> DELETE ];
                if replication_request.seqno <= local_check_point
                then 
                    deletion_seqno := NULL;
                else
                    deletion_seqno := replication_request.seqno;
                end if;
                                   
                if indexing_seqno /= NULL /\ indexing_seqno <= local_check_point
                then 
                    indexing_seqno := NULL;
                end if;
                
            end if;
        end if;
    end while;
    lucene.state := CLOSED;
end process

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES initial_client_requests, client_requests, replication_requests, 
          isGeneratingRequests, lucene, pc, next_seqno, document, 
          highest_document_version, local_check_point, 
          seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
          append_only_unsafe_up_to, replication_request

vars == << initial_client_requests, client_requests, replication_requests, 
           isGeneratingRequests, lucene, pc, next_seqno, document, 
           highest_document_version, local_check_point, 
           seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
           append_only_unsafe_up_to, replication_request >>

ProcSet == {"ReplicationRequestGenerator"} \cup {"ReplicaLucene"} \cup {"ReplicaEngine"}

Init == (* Global variables *)
        /\ initial_client_requests \in {x \in SUBSET ClientRequestType: Cardinality(x) <= 5}
        /\ client_requests = initial_client_requests
        /\ replication_requests = {}
        /\ isGeneratingRequests = TRUE
        /\ lucene = [ document           |-> NULL
                    , buffered_operation |-> NULL
                    , state              |-> OPEN
                    ]
        (* Process ReplicationRequestGeneratorProcess *)
        /\ next_seqno = 1
        /\ document = NULL
        /\ highest_document_version = 0
        (* Process ReplicaEngineProcess *)
        /\ local_check_point = 0
        /\ seqnos_above_local_check_point = {}
        /\ deletion_seqno = NULL
        /\ indexing_seqno = NULL
        /\ append_only_unsafe_up_to = 0
        /\ replication_request = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "ReplicationRequestGenerator" -> "GeneratorStart"
                                        [] self = "ReplicaLucene" -> "LuceneLoop"
                                        [] self = "ReplicaEngine" -> "ReplicaStart"]

GeneratorStart == /\ pc["ReplicationRequestGenerator"] = "GeneratorStart"
                  /\ \/ /\ TRUE
                        /\ UNCHANGED <<replication_requests, next_seqno, document, highest_document_version>>
                     \/ /\ highest_document_version' = highest_document_version + 1
                        /\ document' = [ version |-> highest_document_version'
                                       , seqno   |-> next_seqno
                                       , content |-> "NEW"
                                       ]
                        /\ \E replication_message_duplicates \in {1,2}:
                             replication_requests' =                     replication_requests
                                                     \union {[ version     |-> highest_document_version'
                                                             , seqno       |-> next_seqno
                                                             , content     |-> "NEW"
                                                             , type        |-> INDEX
                                                             , count       |-> replication_message_duplicates
                                                             , append_only |-> TRUE
                                                             ]}
                        /\ next_seqno' = next_seqno + 1
                  /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "GeneratorLoop"]
                  /\ UNCHANGED << initial_client_requests, client_requests, 
                                  isGeneratingRequests, lucene, 
                                  local_check_point, 
                                  seqnos_above_local_check_point, 
                                  deletion_seqno, indexing_seqno, 
                                  append_only_unsafe_up_to, 
                                  replication_request >>

GeneratorLoop == /\ pc["ReplicationRequestGenerator"] = "GeneratorLoop"
                 /\ IF client_requests /= {}
                       THEN /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "HandleClientRequest"]
                            /\ UNCHANGED isGeneratingRequests
                       ELSE /\ isGeneratingRequests' = FALSE
                            /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "Done"]
                 /\ UNCHANGED << initial_client_requests, client_requests, 
                                 replication_requests, lucene, next_seqno, 
                                 document, highest_document_version, 
                                 local_check_point, 
                                 seqnos_above_local_check_point, 
                                 deletion_seqno, indexing_seqno, 
                                 append_only_unsafe_up_to, replication_request >>

HandleClientRequest == /\ pc["ReplicationRequestGenerator"] = "HandleClientRequest"
                       /\ \E client_request \in client_requests:
                            /\ client_requests' = client_requests \ {client_request}
                            /\ IF \/ client_request.version = NULL
                                  \/ client_request.version > highest_document_version
                                  THEN /\ highest_document_version' = (IF client_request.version = NULL
                                                                       THEN highest_document_version + 1
                                                                       ELSE client_request.version)
                                       /\ \E replication_message_duplicates \in {1,2}:
                                            /\ IF client_request.type = INDEX
                                                  THEN /\ document' = [ version |-> highest_document_version'
                                                                      , seqno   |-> next_seqno
                                                                      , content |-> client_request.content
                                                                      ]
                                                       /\ replication_requests' =                     replication_requests
                                                                                  \union {[ version     |-> highest_document_version'
                                                                                          , seqno       |-> next_seqno
                                                                                          , content     |-> client_request.content
                                                                                          , type        |-> INDEX
                                                                                          , count       |-> replication_message_duplicates
                                                                                          , append_only |-> FALSE
                                                                                          ]}
                                                  ELSE /\ IF client_request.type = DELETE
                                                             THEN /\ document' = NULL
                                                                  /\ replication_requests' =                     replication_requests
                                                                                             \union {[ seqno       |-> next_seqno
                                                                                                     , type        |-> DELETE
                                                                                                     , count       |-> replication_message_duplicates
                                                                                                     , append_only |-> FALSE
                                                                                                     ]}
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED << replication_requests, 
                                                                                  document >>
                                            /\ next_seqno' = next_seqno + 1
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << replication_requests, 
                                                       next_seqno, document, 
                                                       highest_document_version >>
                       /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "GeneratorLoop"]
                       /\ UNCHANGED << initial_client_requests, 
                                       isGeneratingRequests, lucene, 
                                       local_check_point, 
                                       seqnos_above_local_check_point, 
                                       deletion_seqno, indexing_seqno, 
                                       append_only_unsafe_up_to, 
                                       replication_request >>

ReplicationRequestGeneratorProcess == GeneratorStart \/ GeneratorLoop
                                         \/ HandleClientRequest

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF lucene.state /= CLOSED \/ lucene.buffered_operation /= NULL
                    THEN /\ lucene.buffered_operation /= NULL
                         /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneRefresh"]
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
              /\ UNCHANGED << initial_client_requests, client_requests, 
                              replication_requests, isGeneratingRequests, 
                              lucene, next_seqno, document, 
                              highest_document_version, local_check_point, 
                              seqnos_above_local_check_point, deletion_seqno, 
                              indexing_seqno, append_only_unsafe_up_to, 
                              replication_request >>

LuceneRefresh == /\ pc["ReplicaLucene"] = "LuceneRefresh"
                 /\ lucene' =       [lucene EXCEPT
                              !.document =
                                  CASE lucene.buffered_operation.type = INDEX
                                  -> [ version |-> lucene.buffered_operation.version
                                     , seqno   |-> lucene.buffered_operation.seqno
                                     , content |-> lucene.buffered_operation.content
                                     ]
                                    [] lucene.buffered_operation.type = DELETE
                                  -> NULL,
                              !.buffered_operation = NULL
                              ]
                 /\ indexing_seqno' = NULL
                 /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneLoop"]
                 /\ UNCHANGED << initial_client_requests, client_requests, 
                                 replication_requests, isGeneratingRequests, 
                                 next_seqno, document, 
                                 highest_document_version, local_check_point, 
                                 seqnos_above_local_check_point, 
                                 deletion_seqno, append_only_unsafe_up_to, 
                                 replication_request >>

LuceneProcess == LuceneLoop \/ LuceneRefresh

ReplicaStart == /\ pc["ReplicaEngine"] = "ReplicaStart"
                /\ ~ isGeneratingRequests
                /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                /\ UNCHANGED << initial_client_requests, client_requests, 
                                replication_requests, isGeneratingRequests, 
                                lucene, next_seqno, document, 
                                highest_document_version, local_check_point, 
                                seqnos_above_local_check_point, deletion_seqno, 
                                indexing_seqno, append_only_unsafe_up_to, 
                                replication_request >>

ReplicaLoop == /\ pc["ReplicaEngine"] = "ReplicaLoop"
               /\ IF replication_requests /= {}
                     THEN /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "GetReplicationRequest"]
                          /\ UNCHANGED lucene
                     ELSE /\ lucene' = [lucene EXCEPT !.state = CLOSED]
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Done"]
               /\ UNCHANGED << initial_client_requests, client_requests, 
                               replication_requests, isGeneratingRequests, 
                               next_seqno, document, highest_document_version, 
                               local_check_point, 
                               seqnos_above_local_check_point, deletion_seqno, 
                               indexing_seqno, append_only_unsafe_up_to, 
                               replication_request >>

GetReplicationRequest == /\ pc["ReplicaEngine"] = "GetReplicationRequest"
                         /\ \E next_replication_request \in replication_requests:
                              /\ replication_request' = next_replication_request
                              /\ replication_requests' =                     (replication_requests \ {replication_request'})
                                                         \union IF replication_request'.count > 1
                                                                THEN {[replication_request' EXCEPT !.count = replication_request'.count - 1]}
                                                                ELSE {}
                         /\ IF /\ local_check_point < replication_request'.seqno
                               /\ replication_request'.append_only
                               /\ replication_request'.seqno < append_only_unsafe_up_to
                               THEN /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "AwaitingRefresh"]
                               ELSE /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Refreshed"]
                         /\ UNCHANGED << initial_client_requests, 
                                         client_requests, isGeneratingRequests, 
                                         lucene, next_seqno, document, 
                                         highest_document_version, 
                                         local_check_point, 
                                         seqnos_above_local_check_point, 
                                         deletion_seqno, indexing_seqno, 
                                         append_only_unsafe_up_to >>

AwaitingRefresh == /\ pc["ReplicaEngine"] = "AwaitingRefresh"
                   /\ lucene.buffered_operation = NULL
                   /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Refreshed"]
                   /\ UNCHANGED << initial_client_requests, client_requests, 
                                   replication_requests, isGeneratingRequests, 
                                   lucene, next_seqno, document, 
                                   highest_document_version, local_check_point, 
                                   seqnos_above_local_check_point, 
                                   deletion_seqno, indexing_seqno, 
                                   append_only_unsafe_up_to, 
                                   replication_request >>

Refreshed == /\ pc["ReplicaEngine"] = "Refreshed"
             /\ IF /\ local_check_point < replication_request.seqno
                   /\  replication_request.append_only
                       =>  \/  append_only_unsafe_up_to < replication_request.seqno
                           \/  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                   
                   /\  ~ replication_request.append_only
                       =>  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                           /\  indexing_seqno  = NULL \/ indexing_seqno        < replication_request.seqno
                           /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                   THEN /\ IF replication_request.seqno > local_check_point + 1
                              THEN /\ seqnos_above_local_check_point' =                               seqnos_above_local_check_point
                                                                        \union {replication_request.seqno}
                                   /\ UNCHANGED local_check_point
                              ELSE /\ local_check_point' = (CHOOSE n \in (local_check_point .. next_seqno):
                                                                       /\ n > local_check_point
                                                                       /\ (n + 1) \notin seqnos_above_local_check_point
                                                                       /\ ((local_check_point + 2) .. n) \subseteq seqnos_above_local_check_point)
                                   /\ seqnos_above_local_check_point' = { n \in seqnos_above_local_check_point: local_check_point' < n }
                        /\ IF ~ replication_request.append_only
                              THEN /\ append_only_unsafe_up_to' = replication_request.seqno
                              ELSE /\ TRUE
                                   /\ UNCHANGED append_only_unsafe_up_to
                        /\ IF replication_request.type = INDEX
                              THEN /\ lucene' = [lucene EXCEPT !.buffered_operation = replication_request]
                                   /\ IF replication_request.seqno <= local_check_point'
                                         THEN /\ indexing_seqno' = NULL
                                         ELSE /\ indexing_seqno' = replication_request.seqno
                                   /\ IF deletion_seqno /= NULL /\ deletion_seqno <= local_check_point'
                                         THEN /\ deletion_seqno' = NULL
                                         ELSE /\ TRUE
                                              /\ UNCHANGED deletion_seqno
                              ELSE /\ IF replication_request.type = DELETE
                                         THEN /\ lucene' = [lucene EXCEPT !.buffered_operation = [ type |-> DELETE ]]
                                              /\ IF replication_request.seqno <= local_check_point'
                                                    THEN /\ deletion_seqno' = NULL
                                                    ELSE /\ deletion_seqno' = replication_request.seqno
                                              /\ IF indexing_seqno /= NULL /\ indexing_seqno <= local_check_point'
                                                    THEN /\ indexing_seqno' = NULL
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED indexing_seqno
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << lucene, 
                                                              deletion_seqno, 
                                                              indexing_seqno >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << lucene, local_check_point, 
                                        seqnos_above_local_check_point, 
                                        deletion_seqno, indexing_seqno, 
                                        append_only_unsafe_up_to >>
             /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
             /\ UNCHANGED << initial_client_requests, client_requests, 
                             replication_requests, isGeneratingRequests, 
                             next_seqno, document, highest_document_version, 
                             replication_request >>

ReplicaEngineProcess == ReplicaStart \/ ReplicaLoop
                           \/ GetReplicationRequest \/ AwaitingRefresh
                           \/ Refreshed

Next == ReplicationRequestGeneratorProcess \/ LuceneProcess
           \/ ReplicaEngineProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

NoClientRequestsAtTermination      == /\ isGeneratingRequests \/ client_requests = {}
                                      /\ Terminated => ~ isGeneratingRequests
NoReplicationRequestsAtTermination == Terminated => replication_requests = {}
EmptyBuffersAtTermination          == Terminated => lucene.buffered_operation = NULL
EqualStatesAtTermination           == Terminated => lucene.document = document

CannotAdvanceLocalCheckPoint == (\A n \in seqnos_above_local_check_point: local_check_point + 1 < n)
VersionMapContainsNoEntriesBeforeLocalCheckPoint == /\ \/ deletion_seqno = NULL
                                                       \/ deletion_seqno > local_check_point
                                                    /\ \/ indexing_seqno = NULL
                                                       \/ indexing_seqno > local_check_point

=============================================================================
\* Modification History
\* Last modified Thu Feb 15 13:51:14 GMT 2018 by davidturner
\* Created Tue Feb 13 13:02:51 GMT 2018 by davidturner
