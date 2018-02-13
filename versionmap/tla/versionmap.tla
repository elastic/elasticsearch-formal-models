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

PrimaryLuceneName == "PrimaryLucene"
ReplicaLuceneName == "ReplicaLucene"
LuceneNames == {PrimaryLuceneName, ReplicaLuceneName}

InitialLuceneState ==
    [ document           |-> NULL
    , buffered_operation |-> NULL
    , state              |-> OPEN
    ]


(* --algorithm basic

variables
    initial_client_requests \in {x \in SUBSET ClientRequestType: Cardinality(x) <= 4},
    client_requests = initial_client_requests,
    replication_requests = {},
    primaryActive = TRUE,
    lucenes = [ PrimaryLucene |-> InitialLuceneState
              , ReplicaLucene |-> InitialLuceneState
              ]

process LuceneProcess \in LuceneNames
begin
    LuceneLoop:
    while lucenes[self].state /= CLOSED \/ lucenes[self].buffered_operation /= NULL do
        await lucenes[self].buffered_operation /= NULL;
        LuceneRefresh:
        lucenes[self] := [lucenes[self] EXCEPT
            !.document =
                CASE lucenes[self].buffered_operation.type = INDEX
                -> [ version |-> lucenes[self].buffered_operation.version
                   , seqno   |-> lucenes[self].buffered_operation.seqno
                   , content |-> lucenes[self].buffered_operation.content
                   ]
                  [] lucenes[self].buffered_operation.type = DELETE
                -> NULL,
            !.buffered_operation = NULL
            ];
    end while;
end process;

process PrimaryEngineProcess = "PrimaryEngine"
variables
    next_seqno = 0,
begin
    PrimaryLoop:
    while client_requests /= {} do
        HandleClientRequest:
        with client_request \in client_requests do
            client_requests := client_requests \ {client_request};
            if client_request.type = INDEX
            then
                lucenes[PrimaryLuceneName].buffered_operation :=
                    [ version |-> client_request.version
                    , content |-> client_request.content
                    , seqno   |-> next_seqno
                    , type    |-> INDEX
                    ];
                replication_requests := replication_requests
                    \union {lucenes[PrimaryLuceneName].buffered_operation};
            elsif client_request.type = DELETE
            then
                lucenes[PrimaryLuceneName].buffered_operation := [ type |-> DELETE ];
                replication_requests := replication_requests
                    \union { [ type |-> DELETE, seqno |-> next_seqno ]};
            end if;

            next_seqno := next_seqno + 1;
        end with;
    end while;
    lucenes[PrimaryLuceneName].state := CLOSED;
    primaryActive := FALSE;
end process

process ReplicaEngineProcess = "ReplicaEngine"
begin
    ReplicaLoop:
    while primaryActive \/ replication_requests /= {} do
        await replication_requests /= {};
        HandleReplicationRequest:
        with replication_request \in replication_requests do
            replication_requests := replication_requests \ {replication_request};
            if replication_request.type = INDEX
            then
                lucenes[ReplicaLuceneName].buffered_operation := replication_request;
            elsif replication_request.type = DELETE
            then
                lucenes[ReplicaLuceneName].buffered_operation := [ type |-> DELETE ];
            end if;
        end with;
    end while;
    lucenes[ReplicaLuceneName].state := CLOSED;
end process

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES initial_client_requests, client_requests, replication_requests, 
          primaryActive, lucenes, pc, next_seqno

vars == << initial_client_requests, client_requests, replication_requests, 
           primaryActive, lucenes, pc, next_seqno >>

ProcSet == (LuceneNames) \cup {"PrimaryEngine"} \cup {"ReplicaEngine"}

Init == (* Global variables *)
        /\ initial_client_requests \in {x \in SUBSET ClientRequestType: Cardinality(x) <= 4}
        /\ client_requests = initial_client_requests
        /\ replication_requests = {}
        /\ primaryActive = TRUE
        /\ lucenes = [ PrimaryLucene |-> InitialLuceneState
                     , ReplicaLucene |-> InitialLuceneState
                     ]
        (* Process PrimaryEngineProcess *)
        /\ next_seqno = 0
        /\ pc = [self \in ProcSet |-> CASE self \in LuceneNames -> "LuceneLoop"
                                        [] self = "PrimaryEngine" -> "PrimaryLoop"
                                        [] self = "ReplicaEngine" -> "ReplicaLoop"]

LuceneLoop(self) == /\ pc[self] = "LuceneLoop"
                    /\ IF lucenes[self].state /= CLOSED \/ lucenes[self].buffered_operation /= NULL
                          THEN /\ lucenes[self].buffered_operation /= NULL
                               /\ pc' = [pc EXCEPT ![self] = "LuceneRefresh"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << initial_client_requests, client_requests, 
                                    replication_requests, primaryActive, 
                                    lucenes, next_seqno >>

LuceneRefresh(self) == /\ pc[self] = "LuceneRefresh"
                       /\ lucenes' = [lucenes EXCEPT ![self] =              [lucenes[self] EXCEPT
                                                               !.document =
                                                                   CASE lucenes[self].buffered_operation.type = INDEX
                                                                   -> [ version |-> lucenes[self].buffered_operation.version
                                                                      , seqno   |-> lucenes[self].buffered_operation.seqno
                                                                      , content |-> lucenes[self].buffered_operation.content
                                                                      ]
                                                                     [] lucenes[self].buffered_operation.type = DELETE
                                                                   -> NULL,
                                                               !.buffered_operation = NULL
                                                               ]]
                       /\ pc' = [pc EXCEPT ![self] = "LuceneLoop"]
                       /\ UNCHANGED << initial_client_requests, 
                                       client_requests, replication_requests, 
                                       primaryActive, next_seqno >>

LuceneProcess(self) == LuceneLoop(self) \/ LuceneRefresh(self)

PrimaryLoop == /\ pc["PrimaryEngine"] = "PrimaryLoop"
               /\ IF client_requests /= {}
                     THEN /\ pc' = [pc EXCEPT !["PrimaryEngine"] = "HandleClientRequest"]
                          /\ UNCHANGED << primaryActive, lucenes >>
                     ELSE /\ lucenes' = [lucenes EXCEPT ![PrimaryLuceneName].state = CLOSED]
                          /\ primaryActive' = FALSE
                          /\ pc' = [pc EXCEPT !["PrimaryEngine"] = "Done"]
               /\ UNCHANGED << initial_client_requests, client_requests, 
                               replication_requests, next_seqno >>

HandleClientRequest == /\ pc["PrimaryEngine"] = "HandleClientRequest"
                       /\ \E client_request \in client_requests:
                            /\ client_requests' = client_requests \ {client_request}
                            /\ IF client_request.type = INDEX
                                  THEN /\ lucenes' = [lucenes EXCEPT ![PrimaryLuceneName].buffered_operation = [ version |-> client_request.version
                                                                                                               , content |-> client_request.content
                                                                                                               , seqno   |-> next_seqno
                                                                                                               , type    |-> INDEX
                                                                                                               ]]
                                       /\ replication_requests' =                     replication_requests
                                                                  \union {lucenes'[PrimaryLuceneName].buffered_operation}
                                  ELSE /\ IF client_request.type = DELETE
                                             THEN /\ lucenes' = [lucenes EXCEPT ![PrimaryLuceneName].buffered_operation = [ type |-> DELETE ]]
                                                  /\ replication_requests' =                     replication_requests
                                                                             \union { [ type |-> DELETE, seqno |-> next_seqno ]}
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << replication_requests, 
                                                                  lucenes >>
                            /\ next_seqno' = next_seqno + 1
                       /\ pc' = [pc EXCEPT !["PrimaryEngine"] = "PrimaryLoop"]
                       /\ UNCHANGED << initial_client_requests, primaryActive >>

PrimaryEngineProcess == PrimaryLoop \/ HandleClientRequest

ReplicaLoop == /\ pc["ReplicaEngine"] = "ReplicaLoop"
               /\ IF primaryActive \/ replication_requests /= {}
                     THEN /\ replication_requests /= {}
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "HandleReplicationRequest"]
                          /\ UNCHANGED lucenes
                     ELSE /\ lucenes' = [lucenes EXCEPT ![ReplicaLuceneName].state = CLOSED]
                          /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "Done"]
               /\ UNCHANGED << initial_client_requests, client_requests, 
                               replication_requests, primaryActive, next_seqno >>

HandleReplicationRequest == /\ pc["ReplicaEngine"] = "HandleReplicationRequest"
                            /\ \E replication_request \in replication_requests:
                                 /\ replication_requests' = replication_requests \ {replication_request}
                                 /\ IF replication_request.type = INDEX
                                       THEN /\ lucenes' = [lucenes EXCEPT ![ReplicaLuceneName].buffered_operation = replication_request]
                                       ELSE /\ IF replication_request.type = DELETE
                                                  THEN /\ lucenes' = [lucenes EXCEPT ![ReplicaLuceneName].buffered_operation = [ type |-> DELETE ]]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED lucenes
                            /\ pc' = [pc EXCEPT !["ReplicaEngine"] = "ReplicaLoop"]
                            /\ UNCHANGED << initial_client_requests, 
                                            client_requests, primaryActive, 
                                            next_seqno >>

ReplicaEngineProcess == ReplicaLoop \/ HandleReplicationRequest

Next == PrimaryEngineProcess \/ ReplicaEngineProcess
           \/ (\E self \in LuceneNames: LuceneProcess(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Terminated == \A self \in ProcSet: pc[self] = "Done"

NoClientRequestsAtTermination      == Terminated => client_requests = {}
NoReplicationRequestsAtTermination == Terminated => replication_requests = {}
EmptyBuffersAtTermination          == Terminated => (\A lucene \in LuceneNames: lucenes[lucene].buffered_operation = NULL)
EqualStatesAtTermination           == Terminated => (\A lucene \in LuceneNames: lucenes[lucene].document = lucenes[PrimaryLuceneName].document)


=============================================================================
\* Modification History
\* Last modified Wed Feb 14 11:10:10 GMT 2018 by davidturner
\* Created Tue Feb 13 13:02:51 GMT 2018 by davidturner
