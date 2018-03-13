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
        ],
    request_count \in 1..4,

process ReplicationRequestGeneratorProcess = "ReplicationRequestGenerator"
variables
    next_seqno = 1,
    document = NULL,
begin

    GeneratorLoop:
    while Cardinality(replication_requests) < request_count do
        with client_request \in {[type |-> UPDATE,  content |-> "A"]
                                ,[type |-> UPDATE,  content |-> "B"]
                                ,[type |-> DELETE]
                                } \union

                                IF \E req \in replication_requests : req.type = ADD \/ next_seqno /= 1
                                THEN {}
                                ELSE {[type |-> ADD, content |-> "NEW"]}

                                do

            if client_request.type = UPDATE \/ client_request.type = ADD
            then
                document := [ seqno   |-> next_seqno
                            , content |-> client_request.content
                            ];
                replication_requests := replication_requests
                    \union {[ seqno       |-> next_seqno
                            , content     |-> client_request.content
                            , type        |-> client_request.type
                            ]};

            else
                assert client_request.type = DELETE;
                document := NULL;
                replication_requests := replication_requests
                    \union {[ seqno       |-> next_seqno
                            , type        |-> DELETE
                            ]};
            end if;

            next_seqno := next_seqno + 1;
        end with;
    end while;

    isGeneratingRequests := FALSE;
end process

process LuceneProcess = "ReplicaLucene"
begin
    LuceneLoop:
    while lucene.state /= CLOSED \/ lucene.buffered_operation /= NULL do
        await lucene.buffered_operation /= NULL;
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

process LocalCheckpointTracker = "LocalCheckpointTracker"
variables
    local_check_point = 0, (* have processed _all_ operations <= local_check_point *)
    seqnos_above_local_check_point = {},
begin
    LocalCheckpointTrackerLoop:
    while TRUE do
        await local_check_point + 1 \in seqnos_above_local_check_point;
        seqnos_above_local_check_point := seqnos_above_local_check_point \ { local_check_point + 1};
        local_check_point := local_check_point + 1;
    end while;
end process;

process VersionMapCleaner = "VersionMapCleaner"
variables
    deletion_seqno = NULL,
    indexing_seqno = NULL,
begin
    VersionMapCleanerLoop:
    while TRUE do
        either
            await deletion_seqno /= NULL /\ deletion_seqno <= local_check_point;
            deletion_seqno := NULL;
        or
            await indexing_seqno /= NULL /\ indexing_seqno <= local_check_point;
            indexing_seqno := NULL;
        end either;
    end while;
end process;

process ReplicaEngineProcess = "ReplicaEngine"
variables
    append_only_unsafe_up_to = 0, (* greatest seqno of non-append-only ops *)
begin
    ReplicaStart:
    await ~ isGeneratingRequests;

    ReplicaLoop:
    while replication_requests /= {} do

        with replication_request \in replication_requests do

            either
                (* consume request *)
                replication_requests := replication_requests \ {replication_request};
            or
                skip;
            end either; 
    
            if  /\ local_check_point < replication_request.seqno
                /\ replication_request.type = ADD
                /\ replication_request.seqno < append_only_unsafe_up_to
            then
                (* Perform a refresh *)
                await lucene.buffered_operation = NULL;
            end if;
    
            if /\  local_check_point < replication_request.seqno
               /\  replication_request.type = ADD
                   =>  \/  /\  append_only_unsafe_up_to < replication_request.seqno
                           /\  replication_request.seqno \notin seqnos_above_local_check_point
                           (* ^ necessary if LCP is not advanced the first time an ADD is processed *)
                           
                       \/  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                           /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
    
               /\  replication_request.type /= ADD
                   =>  /\  deletion_seqno  = NULL \/ deletion_seqno        < replication_request.seqno
                       /\  indexing_seqno  = NULL \/ indexing_seqno        < replication_request.seqno
                       /\  lucene.document = NULL \/ lucene.document.seqno < replication_request.seqno
            then
                (* apply to Lucene -- otherwise, just drop it *)
    
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
    
                seqnos_above_local_check_point := seqnos_above_local_check_point
                    \union {replication_request.seqno};
    
            end if;
        end with;
    end while;
    lucene.state := CLOSED;
end process

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES replication_requests, isGeneratingRequests, lucene, request_count, 
          pc, next_seqno, document, local_check_point, 
          seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
          append_only_unsafe_up_to

vars == << replication_requests, isGeneratingRequests, lucene, request_count, 
           pc, next_seqno, document, local_check_point, 
           seqnos_above_local_check_point, deletion_seqno, indexing_seqno, 
           append_only_unsafe_up_to >>

ProcSet == {"ReplicationRequestGenerator"} \cup {"ReplicaLucene"} \cup {"LocalCheckpointTracker"} \cup {"VersionMapCleaner"} \cup {"ReplicaEngine"}

Init == (* Global variables *)
        /\ replication_requests = {}
        /\ isGeneratingRequests = TRUE
        /\ lucene = [ document           |-> NULL
                    , buffered_operation |-> NULL
                    , state              |-> OPEN
                    ]
        /\ request_count \in 1..4
        (* Process ReplicationRequestGeneratorProcess *)
        /\ next_seqno = 1
        /\ document = NULL
        (* Process LocalCheckpointTracker *)
        /\ local_check_point = 0
        /\ seqnos_above_local_check_point = {}
        (* Process VersionMapCleaner *)
        /\ deletion_seqno = NULL
        /\ indexing_seqno = NULL
        (* Process ReplicaEngineProcess *)
        /\ append_only_unsafe_up_to = 0
        /\ pc = [self \in ProcSet |-> CASE self = "ReplicationRequestGenerator" -> "GeneratorLoop"
                                        [] self = "ReplicaLucene" -> "LuceneLoop"
                                        [] self = "LocalCheckpointTracker" -> "LocalCheckpointTrackerLoop"
                                        [] self = "VersionMapCleaner" -> "VersionMapCleanerLoop"
                                        [] self = "ReplicaEngine" -> "ReplicaStart"]

GeneratorLoop == /\ pc["ReplicationRequestGenerator"] = "GeneratorLoop"
                 /\ IF Cardinality(replication_requests) < request_count
                       THEN /\ \E client_request \in {[type |-> UPDATE,  content |-> "A"]
                                                     ,[type |-> UPDATE,  content |-> "B"]
                                                     ,[type |-> DELETE]
                                                     } \union
                                                     
                                                     IF \E req \in replication_requests : req.type = ADD \/ next_seqno /= 1
                                                     THEN {}
                                                     ELSE {[type |-> ADD, content |-> "NEW"]}:
                                 /\ IF client_request.type = UPDATE \/ client_request.type = ADD
                                       THEN /\ document' = [ seqno   |-> next_seqno
                                                           , content |-> client_request.content
                                                           ]
                                            /\ replication_requests' =                     replication_requests
                                                                       \union {[ seqno       |-> next_seqno
                                                                               , content     |-> client_request.content
                                                                               , type        |-> client_request.type
                                                                               ]}
                                       ELSE /\ Assert(client_request.type = DELETE, 
                                                      "Failure of assertion at line 51, column 17.")
                                            /\ document' = NULL
                                            /\ replication_requests' =                     replication_requests
                                                                       \union {[ seqno       |-> next_seqno
                                                                               , type        |-> DELETE
                                                                               ]}
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
                                 append_only_unsafe_up_to >>

ReplicationRequestGeneratorProcess == GeneratorLoop

LuceneLoop == /\ pc["ReplicaLucene"] = "LuceneLoop"
              /\ IF lucene.state /= CLOSED \/ lucene.buffered_operation /= NULL
                    THEN /\ lucene.buffered_operation /= NULL
                         /\ Assert(lucene.buffered_operation.type = ADD => lucene.document = NULL, 
                                   "Failure of assertion at line 71, column 9.")
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
                    ELSE /\ pc' = [pc EXCEPT !["ReplicaLucene"] = "Done"]
                         /\ UNCHANGED << lucene, indexing_seqno >>
              /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                              request_count, next_seqno, document, 
                              local_check_point, 
                              seqnos_above_local_check_point, deletion_seqno, 
                              append_only_unsafe_up_to >>

LuceneProcess == LuceneLoop

LocalCheckpointTrackerLoop == /\ pc["LocalCheckpointTracker"] = "LocalCheckpointTrackerLoop"
                              /\ local_check_point + 1 \in seqnos_above_local_check_point
                              /\ seqnos_above_local_check_point' = seqnos_above_local_check_point \ { local_check_point + 1}
                              /\ local_check_point' = local_check_point + 1
                              /\ pc' = [pc EXCEPT !["LocalCheckpointTracker"] = "LocalCheckpointTrackerLoop"]
                              /\ UNCHANGED << replication_requests, 
                                              isGeneratingRequests, lucene, 
                                              request_count, next_seqno, 
                                              document, deletion_seqno, 
                                              indexing_seqno, 
                                              append_only_unsafe_up_to >>

LocalCheckpointTracker == LocalCheckpointTrackerLoop

VersionMapCleanerLoop == /\ pc["VersionMapCleaner"] = "VersionMapCleanerLoop"
                         /\ \/ /\ deletion_seqno /= NULL /\ deletion_seqno <= local_check_point
                               /\ deletion_seqno' = NULL
                               /\ UNCHANGED indexing_seqno
                            \/ /\ indexing_seqno /= NULL /\ indexing_seqno <= local_check_point
                               /\ indexing_seqno' = NULL
                               /\ UNCHANGED deletion_seqno
                         /\ pc' = [pc EXCEPT !["VersionMapCleaner"] = "VersionMapCleanerLoop"]
                         /\ UNCHANGED << replication_requests, 
                                         isGeneratingRequests, lucene, 
                                         request_count, next_seqno, document, 
                                         local_check_point, 
                                         seqnos_above_local_check_point, 
                                         append_only_unsafe_up_to >>

VersionMapCleaner == VersionMapCleanerLoop

ReplicaStart == /\ pc["ReplicaEngine"] = "ReplicaStart"
                /\ ~ isGeneratingRequests
                /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                /\ UNCHANGED << replication_requests, isGeneratingRequests, 
                                lucene, request_count, next_seqno, document, 
                                local_check_point, 
                                seqnos_above_local_check_point, deletion_seqno, 
                                indexing_seqno, append_only_unsafe_up_to >>

ReplicaLoop == /\ pc["ReplicaEngine"] = "ReplicaLoop"
               /\ IF replication_requests /= {}
                     THEN /\ \E replication_request \in replication_requests:
                               /\ \/ /\ replication_requests' = replication_requests \ {replication_request}
                                  \/ /\ TRUE
                                     /\ UNCHANGED replication_requests
                               /\ IF /\ local_check_point < replication_request.seqno
                                     /\ replication_request.type = ADD
                                     /\ replication_request.seqno < append_only_unsafe_up_to
                                     THEN /\ lucene.buffered_operation = NULL
                                     ELSE /\ TRUE
                               /\ IF /\  local_check_point < replication_request.seqno
                                     /\  replication_request.type = ADD
                                         =>  \/  /\  append_only_unsafe_up_to < replication_request.seqno
                                                 /\  replication_request.seqno \notin seqnos_above_local_check_point
                                     
                                     
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
                                                           ELSE /\ Assert(replication_request.type = DELETE, 
                                                                          "Failure of assertion at line 181, column 21.")
                                                                /\ append_only_unsafe_up_to' = replication_request.seqno
                                                                /\ lucene' = [lucene EXCEPT !.buffered_operation = [ type |-> DELETE ]]
                                                                /\ deletion_seqno' = replication_request.seqno
                                                                /\ UNCHANGED indexing_seqno
                                          /\ seqnos_above_local_check_point' =                               seqnos_above_local_check_point
                                                                               \union {replication_request.seqno}
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << lucene, 
                                                          seqnos_above_local_check_point, 
                                                          deletion_seqno, 
                                                          indexing_seqno, 
                                                          append_only_unsafe_up_to >>
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                     ELSE /\ lucene' = [lucene EXCEPT !.state = CLOSED]
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Done"]
                          /\ UNCHANGED << replication_requests, 
                                          seqnos_above_local_check_point, 
                                          deletion_seqno, indexing_seqno, 
                                          append_only_unsafe_up_to >>
               /\ UNCHANGED << isGeneratingRequests, request_count, next_seqno, 
                               document, local_check_point >>

ReplicaEngineProcess == ReplicaStart \/ ReplicaLoop

Next == ReplicationRequestGeneratorProcess \/ LuceneProcess
           \/ LocalCheckpointTracker \/ VersionMapCleaner \/ ReplicaEngineProcess

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Terminated == pc["ReplicaLucene"] = "Done"

NoClientRequestsAtTermination      == Terminated => ~ isGeneratingRequests
NoReplicationRequestsAtTermination == Terminated => replication_requests = {}
EmptyBuffersAtTermination          == Terminated => lucene.buffered_operation = NULL
EqualStatesAtTermination           == Terminated => lucene.document = document

=============================================================================
\* Modification History
\* Last modified Tue Mar 13 11:56:23 GMT 2018 by davidturner
\* Created Tue Feb 13 13:02:51 GMT 2018 by davidturner
