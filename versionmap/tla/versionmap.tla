----------------------------- MODULE versionmap -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS ADD, UPDATE, DELETE, NULL
CONSTANTS OPEN, CLOSED


(* --algorithm basic

variables
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
    request_count = NULL,
begin

    GeneratorStart:
    with tmp_request_count \in 1..4 do
        request_count := tmp_request_count;
    end with;

    GeneratorLoop:
    while Cardinality(replication_requests) < request_count do
        with client_request \in {[type |-> UPDATE,  content |-> "A"]
                                ,[type |-> UPDATE,  content |-> "B"]
                                ,[type |-> DELETE]
                                } \union
                                
                                IF \E req \in replication_requests : req.type = ADD
                                THEN {}
                                ELSE {[type |-> ADD, content |-> "NEW"]}
                                
                                do
        
            with replication_message_duplicates \in IF client_request.type = ADD THEN {1} ELSE {1,2} do
            
                if client_request.type = UPDATE \/ client_request.type = ADD
                then
                    await client_request.type = UPDATE \/ next_seqno = 1;
                    document := [ seqno   |-> next_seqno
                                , content |-> client_request.content
                                ];
                    replication_requests := replication_requests
                        \union {[ seqno       |-> next_seqno
                                , content     |-> client_request.content
                                , type        |-> client_request.type
                                , count       |-> replication_message_duplicates
                                ]};
                
                else
                    assert client_request.type = DELETE;
                    document := NULL;
                    replication_requests := replication_requests
                        \union {[ seqno       |-> next_seqno
                                , type        |-> DELETE
                                , count       |-> replication_message_duplicates
                                ]};
                end if;
    
                next_seqno := next_seqno + 1;
            end with;
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
        assert lucene.buffered_operation.type = ADD => lucene.document = NULL; 
        lucene := [lucene EXCEPT
            !.document =
                CASE lucene.buffered_operation.type = UPDATE
                -> [ seqno   |-> lucene.buffered_operation.seqno
                   , content |-> lucene.buffered_operation.content
                   ]
                  [] lucene.buffered_operation.type = ADD
                -> [ seqno   |-> lucene.buffered_operation.seqno
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
            /\ replication_request.type = ADD
            /\ replication_request.seqno < append_only_unsafe_up_to
        then
            AwaitingRefresh:
            (* Perform a refresh *)
            await lucene.buffered_operation = NULL;
            skip;
        end if;
        
        ReadyToApplyToLucene:

        if /\ local_check_point < replication_request.seqno
           /\  replication_request.type = ADD
               =>  \/  append_only_unsafe_up_to < replication_request.seqno
                   \/  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                       /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                   
           /\  replication_request.type /= ADD
               =>  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                   /\  indexing_seqno  = NULL \/ indexing_seqno        < replication_request.seqno
                   /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
        then
       
            if replication_request.type = ADD
            then
                (* fast path *)
                lucene.buffered_operation := 
                    [ type    |-> ADD
                    , seqno   |-> replication_request.seqno
                    , content |-> replication_request.content
                    ];
            elsif replication_request.type = UPDATE
            then
                append_only_unsafe_up_to := replication_request.seqno;
                lucene.buffered_operation :=
                        [ type    |-> UPDATE
                        , seqno   |-> replication_request.seqno
                        , content |-> replication_request.content
                        ];
                indexing_seqno := replication_request.seqno;   
            else
                assert replication_request.type = DELETE;
                append_only_unsafe_up_to := replication_request.seqno;
                lucene.buffered_operation := [ type |-> DELETE ];
                deletion_seqno := replication_request.seqno;
            end if;
                                
            if replication_request.seqno > local_check_point + 1
            then
                (* cannot advance local check point *)
                seqnos_above_local_check_point := seqnos_above_local_check_point
                    \union {replication_request.seqno};
                    
            else
            
                AdvanceLocalCheckPoint:
                
                (* advance local check point *)
                local_check_point := CHOOSE n \in (local_check_point .. next_seqno):
                                                /\ n > local_check_point
                                                /\ (n + 1) \notin seqnos_above_local_check_point
                                                /\ ((local_check_point + 2) .. n) \subseteq seqnos_above_local_check_point;
                seqnos_above_local_check_point := { n \in seqnos_above_local_check_point: local_check_point < n };
                
                if deletion_seqno /= NULL /\ deletion_seqno <= local_check_point
                then
                    deletion_seqno := NULL;
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
VARIABLES replication_requests, isGeneratingRequests, lucene, pc, next_seqno, 
          document, request_count, local_check_point, 
          seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
          append_only_unsafe_up_to, replication_request

vars == << replication_requests, isGeneratingRequests, lucene, pc, next_seqno, 
           document, request_count, local_check_point, 
           seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
           append_only_unsafe_up_to, replication_request >>

ProcSet == {"ReplicationRequestGenerator"} \cup {"ReplicaLucene"} \cup {"ReplicaEngine"}

Init == (* Global variables *)
        /\ replication_requests = {}
        /\ isGeneratingRequests = TRUE
        /\ lucene = [ document           |-> NULL
                    , buffered_operation |-> NULL
                    , state              |-> OPEN
                    ]
        (* Process ReplicationRequestGeneratorProcess *)
        /\ next_seqno = 1
        /\ document = NULL
        /\ request_count = NULL
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
                  /\ \E tmp_request_count \in 1..4:
                       request_count' = tmp_request_count
                  /\ \/ /\ TRUE
                        /\ UNCHANGED <<replication_requests, next_seqno, document>>
                     \/ /\ document' = [ seqno   |-> next_seqno
                                       , content |-> "NEW"
                                       ]
                        /\ \E replication_message_duplicates \in {1,2}:
                             replication_requests' =                     replication_requests
                                                     \union {[ seqno       |-> next_seqno
                                                             , content     |-> "NEW"
                                                             , type        |-> ADD
                                                             , count       |-> replication_message_duplicates
                                                             ]}
                        /\ next_seqno' = next_seqno + 1
                  /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "GeneratorLoop"]
                  /\ UNCHANGED << isGeneratingRequests, lucene, 
                                  local_check_point, 
                                  seqnos_above_local_check_point, 
                                  deletion_seqno, indexing_seqno, 
                                  append_only_unsafe_up_to, 
                                  replication_request >>

GeneratorLoop == /\ pc["ReplicationRequestGenerator"] = "GeneratorLoop"
                 /\ IF Cardinality(replication_requests) < request_count
                       THEN /\ \E client_request \in {[type |-> UPDATE,  content |-> "A"]
                                                     ,[type |-> UPDATE,  content |-> "B"]
                                                     ,[type |-> DELETE]
                                                     }:
                                 \E replication_message_duplicates \in {1,2}:
                                   /\ IF client_request.type = UPDATE
                                         THEN /\ document' = [ seqno   |-> next_seqno
                                                             , content |-> client_request.content
                                                             ]
                                              /\ replication_requests' =                     replication_requests
                                                                         \union {[ seqno       |-> next_seqno
                                                                                 , content     |-> client_request.content
                                                                                 , type        |-> UPDATE
                                                                                 , count       |-> replication_message_duplicates
                                                                                 ]}
                                         ELSE /\ IF client_request.type = DELETE
                                                    THEN /\ document' = NULL
                                                         /\ replication_requests' =                     replication_requests
                                                                                    \union {[ seqno       |-> next_seqno
                                                                                            , type        |-> DELETE
                                                                                            , count       |-> replication_message_duplicates
                                                                                            ]}
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED << replication_requests, 
                                                                         document >>
                                   /\ next_seqno' = next_seqno + 1
                            /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "GeneratorLoop"]
                            /\ UNCHANGED isGeneratingRequests
                       ELSE /\ isGeneratingRequests' = FALSE
                            /\ pc' = [pc EXCEPT !["ReplicationRequestGenerator"] = "Done"]
                            /\ UNCHANGED << replication_requests, next_seqno, 
                                            document >>
                 /\ UNCHANGED << lucene, request_count, local_check_point, 
                                 seqnos_above_local_check_point, 
                                 deletion_seqno, indexing_seqno, 
                                 append_only_unsafe_up_to, replication_request >>

ReplicationRequestGeneratorProcess == GeneratorStart \/ GeneratorLoop

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF lucene.state /= CLOSED \/ lucene.buffered_operation /= NULL
                    THEN /\ lucene.buffered_operation /= NULL
                         /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneRefresh"]
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
              /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                              lucene, next_seqno, document, request_count, 
                              local_check_point, 
                              seqnos_above_local_check_point, deletion_seqno, 
                              indexing_seqno, append_only_unsafe_up_to, 
                              replication_request >>

LuceneRefresh == /\ pc["ReplicaLucene"] = "LuceneRefresh"
                 /\ Assert(lucene.buffered_operation.type = ADD => lucene.document = NULL, 
                           "Failure of assertion at line 94, column 9.")
                 /\ lucene' =       [lucene EXCEPT
                              !.document =
                                  CASE lucene.buffered_operation.type = UPDATE
                                  -> [ seqno   |-> lucene.buffered_operation.seqno
                                     , content |-> lucene.buffered_operation.content
                                     ]
                                    [] lucene.buffered_operation.type = ADD
                                  -> [ seqno   |-> lucene.buffered_operation.seqno
                                     , content |-> lucene.buffered_operation.content
                                     ]
                                    [] lucene.buffered_operation.type = DELETE
                                  -> NULL,
                              !.buffered_operation = NULL
                              ]
                 /\ indexing_seqno' = NULL
                 /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "LuceneLoop"]
                 /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                                 next_seqno, document, request_count, 
                                 local_check_point, 
                                 seqnos_above_local_check_point, 
                                 deletion_seqno, append_only_unsafe_up_to, 
                                 replication_request >>

LuceneProcess == LuceneLoop \/ LuceneRefresh

ReplicaStart == /\ pc["ReplicaEngine"] = "ReplicaStart"
                /\ ~ isGeneratingRequests
                /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                                lucene, next_seqno, document, request_count, 
                                local_check_point, 
                                seqnos_above_local_check_point, deletion_seqno, 
                                indexing_seqno, append_only_unsafe_up_to, 
                                replication_request >>

ReplicaLoop == /\ pc["ReplicaEngine"] = "ReplicaLoop"
               /\ IF replication_requests /= {}
                     THEN /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "GetReplicationRequest"]
                          /\ UNCHANGED lucene
                     ELSE /\ lucene' = [lucene EXCEPT !.state = CLOSED]
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Done"]
               /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                               next_seqno, document, request_count, 
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
                               /\ replication_request'.type = ADD
                               /\ replication_request'.seqno < append_only_unsafe_up_to
                               THEN /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "AwaitingRefresh"]
                               ELSE /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReadyToApplyToLucene"]
                         /\ UNCHANGED << isGeneratingRequests, lucene, 
                                         next_seqno, document, request_count, 
                                         local_check_point, 
                                         seqnos_above_local_check_point, 
                                         deletion_seqno, indexing_seqno, 
                                         append_only_unsafe_up_to >>

AwaitingRefresh == /\ pc["ReplicaEngine"] = "AwaitingRefresh"
                   /\ lucene.buffered_operation = NULL
                   /\ TRUE
                   /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReadyToApplyToLucene"]
                   /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                                   lucene, next_seqno, document, request_count, 
                                   local_check_point, 
                                   seqnos_above_local_check_point, 
                                   deletion_seqno, indexing_seqno, 
                                   append_only_unsafe_up_to, 
                                   replication_request >>

ReadyToApplyToLucene == /\ pc["ReplicaEngine"] = "ReadyToApplyToLucene"
                        /\ IF /\ local_check_point < replication_request.seqno
                              /\  replication_request.type = ADD
                                  =>  \/  append_only_unsafe_up_to < replication_request.seqno
                                      \/  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                                          /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                              
                              /\  replication_request.type /= ADD
                                  =>  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                                      /\  indexing_seqno  = NULL \/ indexing_seqno        < replication_request.seqno
                                      /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
                              THEN /\ IF replication_request.type = ADD
                                         THEN /\ lucene' = [lucene EXCEPT !.buffered_operation = [ type    |-> ADD
                                                                                                 , seqno   |-> replication_request.seqno
                                                                                                 , content |-> replication_request.content
                                                                                                 ]]
                                              /\ UNCHANGED << deletion_seqno, 
                                                              indexing_seqno, 
                                                              append_only_unsafe_up_to >>
                                         ELSE /\ IF replication_request.type = UPDATE
                                                    THEN /\ append_only_unsafe_up_to' = replication_request.seqno
                                                         /\ lucene' = [lucene EXCEPT !.buffered_operation = [ type    |-> UPDATE
                                                                                                            , seqno   |-> replication_request.seqno
                                                                                                            , content |-> replication_request.content
                                                                                                            ]]
                                                         /\ indexing_seqno' = replication_request.seqno
                                                         /\ UNCHANGED deletion_seqno
                                                    ELSE /\ IF replication_request.type = DELETE
                                                               THEN /\ append_only_unsafe_up_to' = replication_request.seqno
                                                                    /\ lucene' = [lucene EXCEPT !.buffered_operation = [ type |-> DELETE ]]
                                                                    /\ deletion_seqno' = replication_request.seqno
                                                               ELSE /\ TRUE
                                                                    /\ UNCHANGED << lucene, 
                                                                                    deletion_seqno, 
                                                                                    append_only_unsafe_up_to >>
                                                         /\ UNCHANGED indexing_seqno
                                   /\ IF replication_request.seqno > local_check_point + 1
                                         THEN /\ seqnos_above_local_check_point' =                               seqnos_above_local_check_point
                                                                                   \union {replication_request.seqno}
                                              /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                                         ELSE /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "AdvanceLocalCheckPoint"]
                                              /\ UNCHANGED seqnos_above_local_check_point
                              ELSE /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                                   /\ UNCHANGED << lucene, 
                                                   seqnos_above_local_check_point, 
                                                   deletion_seqno, 
                                                   indexing_seqno, 
                                                   append_only_unsafe_up_to >>
                        /\ UNCHANGED << replication_requests, 
                                        isGeneratingRequests, next_seqno, 
                                        document, request_count, 
                                        local_check_point, replication_request >>

AdvanceLocalCheckPoint == /\ pc["ReplicaEngine"] = "AdvanceLocalCheckPoint"
                          /\ local_check_point' = (CHOOSE n \in (local_check_point .. next_seqno):
                                                              /\ n > local_check_point
                                                              /\ (n + 1) \notin seqnos_above_local_check_point
                                                              /\ ((local_check_point + 2) .. n) \subseteq seqnos_above_local_check_point)
                          /\ seqnos_above_local_check_point' = { n \in seqnos_above_local_check_point: local_check_point' < n }
                          /\ IF deletion_seqno /= NULL /\ deletion_seqno <= local_check_point'
                                THEN /\ deletion_seqno' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED deletion_seqno
                          /\ IF indexing_seqno /= NULL /\ indexing_seqno <= local_check_point'
                                THEN /\ indexing_seqno' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED indexing_seqno
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                          /\ UNCHANGED << replication_requests, 
                                          isGeneratingRequests, lucene, 
                                          next_seqno, document, request_count, 
                                          append_only_unsafe_up_to, 
                                          replication_request >>

ReplicaEngineProcess == ReplicaStart \/ ReplicaLoop
                           \/ GetReplicationRequest \/ AwaitingRefresh
                           \/ ReadyToApplyToLucene
                           \/ AdvanceLocalCheckPoint

Next == ReplicationRequestGeneratorProcess \/ LuceneProcess
           \/ ReplicaEngineProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

NoClientRequestsAtTermination      == Terminated => ~ isGeneratingRequests
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
\* Last modified Fri Feb 16 16:41:26 GMT 2018 by davidturner
\* Created Tue Feb 13 13:02:51 GMT 2018 by davidturner
