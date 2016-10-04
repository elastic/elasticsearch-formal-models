------------------------------ MODULE elasticsearch ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of node ids (one for each data node in the cluster)
CONSTANTS Nodes

\* Set of document ids (i.e. possible values for "_id" field)
CONSTANTS DocumentIds

\* Shard states
\* Unassigned is used as special value when no shard is assigned to a node
\* (e.g. after shard failed and removed from the routing table)
CONSTANTS Primary, Replica, Unassigned

\* Replication responses
CONSTANTS Success, Failed

\* To denote a non-existing value (e.g. in store)
CONSTANTS Nil

\* Message types
CONSTANTS \* IndexRequest, IndexResponse, \* not used for now as reroute logic is not implemented
          ReplicationRequest, ReplicationResponse,
          TrimTranslogRequest, TrimTranslogResponse

\* Set of possible initial cluster states (to be defined by the model checker). A cluster state is
\* a record type containing a routing table (map from Nodes to {Primary, Replia, Unassigned})
\* and a primary term (natural number), for example:
\* [routingTable |-> [n1 |-> Primary, n2 |-> Replica, n3 |-> Unassigned], primaryTerm |-> 1]
CONSTANTS InitialClusterStates


----
\* Global variables

\* Set of requests and responses sent between data nodes.
\* Requests and responses are modeled as record types.
VARIABLE messages

\* current cluster state on master (the master is not explicitly modeled as a node)
VARIABLE clusterStateOnMaster

\* Each client (index) request uses a unique value so that we can distinguish between them
\* (this is just an natural number that we increment on each new client operation)
VARIABLE nextClientValue

\* The set of (acknowledged) client responses (stored so we can make assertions)
VARIABLE clientResponses

clientVars == <<nextClientValue, clientResponses>>

\* Replication requests for the same indexing request get a common unique id so that we can relate their responses
\* (this is just an natural number that we increment on each new client operation)
VARIABLE nextRequestId

\* map from request id to set of nodes we are waiting a response for. This is used e.g. when we
\* replicate an index request to two replicas and want to ensure that we only respond to the client
\* once both replicas have replied (see also nextRequestId)
VARIABLE waitForResponses

\* set of crashed nodes (used to denote a physical crash of the node)
VARIABLE crashedNodes

\* number of messages that have been dropped (used by model checker to restrict number of failures)
VARIABLE messageDrops


----
\* The following variables are all per (data) node (functions with domain Nodes).

\* map from node id to cluster state that is currently applied on this node
VARIABLE clusterStateOnNode

\* map from node id to next sequence number to use for indexing data
VARIABLE nextSeq

\* map from node id to map from document id to entry (containing seq number and value)
VARIABLE store

\* transaction log, map from node id to map from sequence number to document
VARIABLE tlog

\* current primary term, map from node id to term number
VARIABLE currentTerm

\* map from node id to node id to natural number
VARIABLE localCheckPoint

\* map from node id to natural number
VARIABLE globalCheckPoint

nodeVars == <<clusterStateOnNode, nextSeq, store, tlog, localCheckPoint, globalCheckPoint, currentTerm>>


----
\* General helper functions

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Helper functions for sending/receiving messages

\* Remove request from the set of messages and add response instead
Reply(response, request) ==
    messages' = {response} \cup (messages \ {request})

----
\* Helper functions on routing table
Primaries(routingTable) == {n \in Nodes : routingTable[n] = Primary}
Replicas(routingTable) == {n \in Nodes : routingTable[n] = Replica}
Assigned(routingTable) == {n \in Nodes : routingTable[n] /= Unassigned}

HasUniquePrimary(routingTable) == Cardinality(Primaries(routingTable)) = 1
ChoosePrimary(routingTable) == CHOOSE n \in Nodes : n \in Primaries(routingTable)
ChooseReplica(routingTable) == CHOOSE n \in Nodes : n \in Replicas(routingTable)

\* Helper function to determine if another node has become a primary on cluster state update
AnotherNodeWasPromotedToPrimary(n, incomingRoutingTable, myRoutingTable) ==
    LET newPrimaries == Primaries(incomingRoutingTable)
    IN  /\ n \notin newPrimaries
        /\ Cardinality(newPrimaries) = 1
        /\ newPrimaries /= Primaries(myRoutingTable)
        
NodeWasPromotedToPrimary(n, incomingRoutingTable, myRoutingTable) ==
    LET oldPrimaries == Primaries(myRoutingTable)
        newPrimaries == Primaries(incomingRoutingTable)
    IN  /\ n \notin oldPrimaries
        /\ n \in newPrimaries
        
RerouteWithFailedShard(n, cs) ==
    LET rt == cs.routingTable
    IN  IF rt[n] = Unassigned THEN
            cs
        ELSE
            LET primaryFailed == rt[n] = Primary
                primaryFailedWithReplicaAvailable == primaryFailed /\ Cardinality(Replicas(rt)) > 0
                \* increase primary term on primary failure
                newPrimaryTerm == IF primaryFailed THEN
                                     cs.primaryTerm + 1
                                  ELSE
                                     cs.primaryTerm
                newRoutingTable == IF primaryFailedWithReplicaAvailable THEN
                                      \* promote other copy to primary
                                      [rt EXCEPT ![n] = Unassigned, ![ChooseReplica(rt)] = Primary]
                                   ELSE
                                      [rt EXCEPT ![n] = Unassigned]
            IN  [clusterStateOnMaster EXCEPT
                    !.routingTable = newRoutingTable,
                    !.primaryTerm  = newPrimaryTerm] 

----
\* Define initial values for all variables

InitNodesVars == /\ nextSeq = [n \in Nodes |-> 1]
                 /\ clusterStateOnNode = [n \in Nodes |-> clusterStateOnMaster]
                 /\ store = [n \in Nodes |-> [id \in DocumentIds |-> Nil]]
                 /\ tlog = [n \in Nodes |-> << >>]
                 /\ localCheckPoint = [n1 \in Nodes |-> [n2 \in Nodes |-> 0]]
                 /\ globalCheckPoint = [n \in Nodes |-> 0]
                 /\ currentTerm = [n \in Nodes |-> clusterStateOnMaster.primaryTerm]
                 
Init == /\ messages = {}
        /\ clusterStateOnMaster \in InitialClusterStates
        /\ crashedNodes = {}
        /\ nextClientValue = 1
        /\ clientResponses = {}
        /\ nextRequestId = 1
        /\ waitForResponses = << >>
        /\ InitNodesVars
        /\ messageDrops = 0

----
\* Define next step relation


ValidEntry(ntlog, i) ==
    i \in DOMAIN ntlog /\ ntlog[i].safe

\* Highest sequence number without gaps in translog, yields 0 if no such number exists
MaxGaplessSeq(ntlog) ==
    LET domWithZero == DOMAIN ntlog \cup {0}
    IN  CHOOSE i \in domWithZero :
        /\ ValidEntry(ntlog, i+1) = FALSE
        /\ \A j \in 1..i : ValidEntry(ntlog, j)

\* Index request arrives on node n with document id docId
ClientRequest(n, docId) ==
    /\ n \notin crashedNodes \* only non-crashed nodes can accept client commands
    /\ LET routingTable == clusterStateOnNode[n].routingTable
           primaryTerm  == currentTerm[n]
       IN  /\ routingTable[n] = Primary \* node believes itself to be the primary
           /\ LET tlogEntry == [id    |-> docId,
                                term  |-> primaryTerm,
                                value |-> nextClientValue,
                                safe  |-> TRUE]
                  storeEntry == [seq   |-> nextSeq[n],
                                 value |-> nextClientValue]
                  replRequests == {([mtype    |-> ReplicationRequest,
                                     msource  |-> n,
                                     mdest    |-> rn,
                                     req      |-> nextRequestId,
                                     seq      |-> nextSeq[n],
                                     rterm    |-> primaryTerm, \* current term when issuing request
                                     sterm    |-> primaryTerm, \* term to be stored
                                     id       |-> docId,
                                     value    |-> nextClientValue,
                                     recovery |-> FALSE,
                                     globalCP |-> globalCheckPoint[n]]) : rn \in Replicas(routingTable)}
              IN  /\ store' = [store EXCEPT ![n][docId] = storeEntry]
                  /\ tlog' = [tlog EXCEPT ![n] = @ @@ (nextSeq[n] :> tlogEntry)]
                  /\ nextSeq' = [nextSeq EXCEPT ![n] = @ + 1]
                  /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = MaxGaplessSeq(tlog'[n])]
                  \* Make sure that each request is unique
                  /\ nextClientValue' = nextClientValue + 1
                  \* generate unique key for replication requests so that we can relate responses
                  /\ nextRequestId' = nextRequestId + 1
                  /\ messages' = messages \cup replRequests
                  /\ waitForResponses' = waitForResponses @@ (nextRequestId :> Replicas(routingTable))
    /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, clientResponses, crashedNodes,
                   globalCheckPoint, messageDrops, currentTerm>>
    
    
DefaultReplicationResponse(m) == [mtype     |-> ReplicationResponse,
                                  msource   |-> m.mdest,
                                  mdest     |-> m.msource,
                                  req       |-> m.req,
                                  id        |-> m.id,
                                  seq       |-> m.seq,
                                  rterm     |-> m.rterm,
                                  sterm     |-> m.sterm,
                                  value     |-> m.value,
                                  recovery  |-> m.recovery,
                                  localCP   |-> 0,
                                  result    |-> Success]
                       
FillGapsAndMarkSafe(ntlog, from, safe) ==
    [j \in 1..Max(DOMAIN ntlog \cup {0}) |-> 
        IF  j \in DOMAIN ntlog THEN
            IF j > from THEN
                [ntlog[j] EXCEPT !.safe = safe]
            ELSE
                ntlog[j]
        ELSE
            [id    |-> Nil,
             term  |-> 0,
             value |-> Nil,
             safe  |-> safe]]
             
MarkSafeUpTo(ntlog, to) ==
    [j \in DOMAIN ntlog |-> 
        IF j <= to THEN
            [ntlog[j] EXCEPT !.safe = TRUE]
        ELSE
            ntlog[j]]


\* Replication request arrives on node n with message m
HandleReplicationRequest(m) ==
   LET n == m.mdest
   IN  /\ n \notin crashedNodes
       /\ m.mtype = ReplicationRequest
       /\ IF m.rterm >= currentTerm[n] THEN
               /\ LET storeEntry == [seq   |-> m.seq,
                                     value |-> m.value]
                      newStore == [store[n] EXCEPT ![m.id] = storeEntry]
                      tlogEntry == [id    |-> m.id,
                                    term  |-> m.sterm,
                                    value |-> m.value,
                                    safe  |-> TRUE]
                      newGlobalCP == Max({globalCheckPoint[n], m.globalCP})
                      safeMarkedTlog == [tlog EXCEPT ![n] = MarkSafeUpTo(@, newGlobalCP)]
                      gapsFilledTlog ==
                          IF m.rterm > currentTerm[n] THEN
                              \* there is a new primary in town, cannot safely advance local checkpoint before resync done
                              \* take globalCP from replication request into account
                              [safeMarkedTlog EXCEPT ![n] = FillGapsAndMarkSafe(@, newGlobalCP, FALSE)]
                          ELSE
                              safeMarkedTlog             
                      newTlog == [gapsFilledTlog EXCEPT ![n] =
                              \* ignore if we already have an entry with higher term
                              IF m.seq \in DOMAIN @ /\ m.rterm < @[m.seq].term THEN
                                  @
                              ELSE 
                                  (m.seq :> tlogEntry) @@ @
                          ]
                      localCP == MaxGaplessSeq(newTlog[n])
                  IN  /\ store' = IF m.id /= Nil /\ (store[n][m.id] = Nil \/ m.seq > store[n][m.id].seq) THEN
                                      [store EXCEPT ![n] = newStore]
                                  ELSE
                                      store
                      /\ tlog' = newTlog
                      /\ nextSeq' = IF m.seq + 1 > nextSeq[n] THEN
                                        [nextSeq EXCEPT ![n] = m.seq + 1] 
                                    ELSE
                                        nextSeq
                      /\ currentTerm' = IF m.rterm > currentTerm[n] THEN
                                            [currentTerm EXCEPT ![n] = m.rterm]
                                        ELSE
                                            currentTerm
                      /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = newGlobalCP]
                      /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = localCP]
                      /\ Reply([DefaultReplicationResponse(m) EXCEPT !.localCP = localCP], m)
               /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, nextClientValue, nextRequestId,
                              clientResponses, waitForResponses, crashedNodes, messageDrops>>
           ELSE
               \* don't replicate entries with lower term than we have
               /\ Reply([DefaultReplicationResponse(m) EXCEPT !.result = Failed], m)
               /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, waitForResponses,
                              crashedNodes, nodeVars, messageDrops>>

\* Replication response arrives on node n with message m
HandleReplicationResponse(m) ==
   LET n == m.mdest
       req == m.req
       rn == m.msource
       finishIfNeeded ==
                /\  waitForResponses' = [waitForResponses EXCEPT ![req] = @ \ {rn}]
                /\  IF m.recovery = FALSE /\ waitForResponses[req] = {rn} THEN
                         \* last response, answer client
                         clientResponses' = clientResponses \cup {[id    |-> m.id,
                                                                   value |-> m.value,
                                                                   seq   |-> m.seq,
                                                                   term  |-> m.rterm]}
                    ELSE
                         UNCHANGED <<clientResponses>>
       finishAsFailed ==
                /\ waitForResponses' = [waitForResponses EXCEPT ![req] = {}]
                /\ UNCHANGED <<clientResponses>>
   IN  /\ n \notin crashedNodes
       /\ clusterStateOnNode[n].routingTable[n] /= Unassigned \* handled by CleanReplicationResponseToDeadNode
       /\ m.mtype = ReplicationResponse
       /\ IF req \in DOMAIN waitForResponses /\ rn \in waitForResponses[req] THEN
              \/ /\ m.result = Success
                 \* don't update local/global checkpoint if local checkpoint came from request with lower term
                 /\ IF m.rterm >= currentTerm[n] /\ m.localCP > localCheckPoint[n][rn] THEN
                        LET newLocalCheckPoint == [localCheckPoint EXCEPT ![n][rn] = m.localCP]
                            rt == clusterStateOnNode[n].routingTable
                            computedGlobalCP == Min({newLocalCheckPoint[n][i] : i \in Assigned(rt)})
                        IN  /\ localCheckPoint' = newLocalCheckPoint
                            \* also update global checkpoint if necessary
                            /\ globalCheckPoint' =
                                   [globalCheckPoint EXCEPT ![n] = computedGlobalCP]
                    ELSE
                        UNCHANGED <<localCheckPoint, globalCheckPoint>> 
                 /\ UNCHANGED <<clusterStateOnMaster>>
                 /\ finishIfNeeded
              \/ /\ m.result = Failed
                 /\ IF m.rterm < clusterStateOnMaster.primaryTerm THEN
                      \* term outdated, fail itself and don't ack client write
                      /\ finishAsFailed
                      /\ UNCHANGED <<clusterStateOnMaster>>
                    ELSE
                      \* fail shard and respond to client
                      /\ clusterStateOnMaster' = RerouteWithFailedShard(rn, clusterStateOnMaster)
                      /\ finishIfNeeded
                 /\ UNCHANGED <<localCheckPoint, globalCheckPoint>>
          ELSE
              UNCHANGED <<clusterStateOnMaster, clientResponses, waitForResponses, localCheckPoint,
                          globalCheckPoint>>
       /\ messages' = messages \ {m}       
       /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, store, tlog,
                      nextSeq, messageDrops, currentTerm>>
                      

DefaultTrimTranslogResponse(m) == [mtype     |-> TrimTranslogResponse,
                                   msource   |-> m.mdest,
                                   mdest     |-> m.msource,
                                   req       |-> m.req,
                                   maxseq    |-> m.maxseq,
                                   term      |-> m.term,
                                   result    |-> Success]
                                   
ElementsToKeep(ntlog, maxseq, minterm) ==
    {i \in DOMAIN ntlog : i <= maxseq \/ ntlog[i].term >= minterm}
                                   
TrimTlog(ntlog, maxseq, minterm) ==
    [j \in ElementsToKeep(ntlog, maxseq, minterm) |-> ntlog[j]]
                              
\* Trim translog request arrives on node n with message m
HandleTrimTranslogRequest(m) ==
   LET n == m.mdest
   IN  /\ n \notin crashedNodes
       /\ m.mtype = TrimTranslogRequest
       /\ IF m.term >= currentTerm[n] THEN
              LET newGlobalCP == globalCheckPoint[n]
                  gapsFilledTlog ==
                  IF m.term > currentTerm[n] THEN
                      \* there is a new primary in town, cannot safely advance local checkpoint before resync done
                      \* take globalCP from replication request into account
                      [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, newGlobalCP, FALSE)]
                  ELSE
                      tlog
              IN  /\ tlog' = [gapsFilledTlog EXCEPT ![n] = TrimTlog(@, m.maxseq, m.term)]
                  /\ currentTerm' = IF m.term > currentTerm[n] THEN
                                        [currentTerm EXCEPT ![n] = m.term]
                                    ELSE
                                        currentTerm
                  /\ Reply(DefaultTrimTranslogResponse(m), m)
          ELSE
              \* don't handle requests with lower term than we have
              /\ Reply([DefaultTrimTranslogResponse(m) EXCEPT !.result = Failed], m)
              /\ UNCHANGED <<tlog, currentTerm>>
       /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, waitForResponses,
                      clusterStateOnNode, nextClientValue, nextRequestId, clientResponses,
                      crashedNodes, messageDrops, nextSeq, store, globalCheckPoint,
                      localCheckPoint>>
                             
\* Trim translog response arrives on node n with message m
HandleTrimTranslogResponse(m) ==
   LET n == m.mdest
       req == m.req
       rn == m.msource
       finishIfNeeded == waitForResponses' = [waitForResponses EXCEPT ![req] = @ \ {rn}]
       finishAsFailed == waitForResponses' = [waitForResponses EXCEPT ![req] = {}]
   IN  /\ n \notin crashedNodes
       /\ m.mtype = TrimTranslogResponse
       /\ IF req \in DOMAIN waitForResponses /\ rn \in waitForResponses[req] THEN
              \/ /\ m.result = Success
                 /\ finishIfNeeded
                 /\ UNCHANGED <<clusterStateOnMaster, localCheckPoint, globalCheckPoint>>
              \/ /\ m.result = Failed
                 /\ IF m.term < clusterStateOnMaster.primaryTerm THEN
                        \* term outdated, fail itself
                        /\ finishAsFailed
                        /\ UNCHANGED <<clusterStateOnMaster>>
                    ELSE
                        \* fail shard
                        /\ clusterStateOnMaster' = RerouteWithFailedShard(rn, clusterStateOnMaster)
                        /\ finishIfNeeded
                 /\ UNCHANGED <<localCheckPoint, globalCheckPoint>>
          ELSE
              UNCHANGED <<clusterStateOnMaster, clientResponses, waitForResponses, localCheckPoint,
                          globalCheckPoint>>
       /\ messages' = messages \ {m}       
       /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, store, tlog,
                      nextSeq, messageDrops, clientResponses, currentTerm>>
       
CleanReplicationResponseToDeadNode(m) ==
    /\ m.mtype = ReplicationResponse
    /\ \/ m.mdest \in crashedNodes
       \/ clusterStateOnNode[m.mdest].routingTable[m.mdest] = Unassigned
    /\ messages' = messages \ {m}
    /\ waitForResponses' = [waitForResponses EXCEPT ![m.req] = @ \ {m.msource}]
    /\ UNCHANGED <<clusterStateOnMaster, clientResponses, nextClientValue, nextRequestId, nodeVars,
                   crashedNodes, messageDrops>>

FillGaps(ntlog) ==
    [j \in 1..Max(DOMAIN ntlog \cup {0}) |-> 
        IF  j \in DOMAIN ntlog THEN
            ntlog[j]
        ELSE
            [id    |-> Nil,
             term  |-> 0,
             value |-> Nil]]

\* Cluster state propagated from master is applied to node n
ApplyClusterStateFromMaster(n) ==
    /\ n \notin crashedNodes
    /\ clusterStateOnNode[n] /= clusterStateOnMaster
    /\ clusterStateOnNode' = [clusterStateOnNode EXCEPT ![n] = clusterStateOnMaster]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = Max({@, clusterStateOnMaster.primaryTerm})]
    /\ IF NodeWasPromotedToPrimary(n, clusterStateOnMaster.routingTable,
           clusterStateOnNode[n].routingTable) THEN
            LET newPrimaryTlog == tlog[n]
                globalCP == globalCheckPoint[n]
                replicas == Replicas(clusterStateOnMaster.routingTable)
                numReplicas == Cardinality(replicas)
                maxTlogPos == Max((DOMAIN newPrimaryTlog) \cup {0})
                numDocs == maxTlogPos - globalCP
                replRequests == {([mtype    |-> ReplicationRequest,
                             msource  |-> n,
                             mdest    |-> rn,
                             req      |-> nextRequestId + i - 1,
                             seq      |-> globalCP + i,
                             rterm    |-> currentTerm'[n], \* current term when issuing request
                             sterm    |-> IF (globalCP + i) \in DOMAIN newPrimaryTlog THEN
                                              newPrimaryTlog[globalCP + i].term
                                          ELSE
                                              0,
                             id       |-> IF (globalCP + i) \in DOMAIN newPrimaryTlog THEN
                                              newPrimaryTlog[globalCP + i].id
                                          ELSE
                                              Nil,
                             value    |-> IF (globalCP + i) \in DOMAIN newPrimaryTlog THEN
                                              newPrimaryTlog[globalCP + i].value
                                          ELSE
                                              Nil,
                             recovery |-> TRUE,
                             cut      |-> FALSE,
                             globalCP |-> globalCP]) : i \in 1..numDocs, rn \in replicas}
                  trimRequests == {[mtype    |-> TrimTranslogRequest,
                                    msource  |-> n,
                                    mdest    |-> rn,
                                    req      |-> nextRequestId + numDocs,
                                    maxseq   |-> maxTlogPos,
                                    term     |-> currentTerm'[n]] : rn \in replicas}
             IN  \* fill gaps in tlog
                 /\ tlog' = [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, globalCheckPoint[n], TRUE)]
                 \* reset local checkpoint for other nodes and calculate new one for current node
                 /\ localCheckPoint' = [localCheckPoint EXCEPT ![n] = [[n2 \in Nodes |-> 0] EXCEPT ![n] = MaxGaplessSeq(tlog'[n])]]
                 \* TODO advance global checkpoint marker here
                 /\ messages' = messages \cup replRequests \cup trimRequests
                 /\ nextRequestId' = nextRequestId + (numReplicas * (numDocs + 1))
                 /\ waitForResponses' = waitForResponses @@ 
                                            [i \in nextRequestId..(nextRequestId+numDocs-1) |-> replicas] @@
                                            ((nextRequestId+numDocs) :> replicas) 
      ELSE
          /\ IF  clusterStateOnMaster.routingTable[n] = Replica /\ clusterStateOnMaster.primaryTerm > currentTerm[n] THEN
                 tlog' = [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, globalCheckPoint[n], FALSE)]
             ELSE
                 UNCHANGED <<tlog>>
          /\ UNCHANGED <<localCheckPoint, messages, nextRequestId, waitForResponses>>
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextSeq, clientVars, store,
                   globalCheckPoint, messageDrops>>
                   
\* Node fault detection on master finds node n to be isolated from the cluster
NodeFaultDetectionKicksNodeOut(n) ==
    /\ n \notin crashedNodes
    /\ clusterStateOnMaster.routingTable[n] /= Unassigned
    /\ clusterStateOnMaster' = RerouteWithFailedShard(n, clusterStateOnMaster)
    /\ UNCHANGED <<crashedNodes, messages, nextRequestId, waitForResponses, clientVars, nodeVars, messageDrops>>

    
\* Node n crashes        
CrashNode(n) ==
    /\ n \notin crashedNodes
    /\ crashedNodes' = crashedNodes \cup {n}
    /\ UNCHANGED <<clusterStateOnMaster, messages, clientVars, nextRequestId, waitForResponses,
                   nodeVars, messageDrops>>

\* Drop replication request message    
DropReplicationRequestMessage(m) ==
    /\ m.mtype = ReplicationRequest
    /\ Reply([DefaultReplicationResponse(m) EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>

\* Drop trim translog request message                       
DropTrimTranslogRequestMessage(m) ==
    /\ m.mtype = TrimTranslogRequest
    /\ Reply([DefaultTrimTranslogResponse(m) EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>

\* Drop replication response message
DropReplicationResponseMessage(m) ==
    /\ m.mtype = ReplicationResponse
    /\ m.result = Success
    /\ Reply([m EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>
                   
\* Drop trim translog response message
DropTrimTranslogResponseMessage(m) ==
    /\ m.mtype = TrimTranslogResponse
    /\ m.result = Success
    /\ Reply([m EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>

\* Master removes crashed node n from its cluster state
RemoveCrashedNodeFromClusterState(n) ==
    /\ n \in crashedNodes
    /\ clusterStateOnMaster' = RerouteWithFailedShard(n, clusterStateOnMaster)
    /\ UNCHANGED <<crashedNodes, messages, nextRequestId, waitForResponses, clientVars, nodeVars, messageDrops>>

\* Defines how the variables may transition.
Next == \/ \E n \in Nodes : \E docId \in DocumentIds : ClientRequest(n, docId)
        \/ \E m \in messages : HandleReplicationRequest(m)
        \/ \E m \in messages : HandleReplicationResponse(m)
        \/ \E m \in messages : HandleTrimTranslogRequest(m)
        \/ \E m \in messages : HandleTrimTranslogResponse(m)
        \/ \E m \in messages : CleanReplicationResponseToDeadNode(m)
        \/ \E m \in messages : DropReplicationRequestMessage(m)
        \/ \E m \in messages : DropReplicationResponseMessage(m)
        \/ \E m \in messages : DropTrimTranslogRequestMessage(m)
        \/ \E m \in messages : DropTrimTranslogResponseMessage(m)
        \/ \E n \in Nodes : ApplyClusterStateFromMaster(n)
        \/ \E n \in Nodes : CrashNode(n)
        \/ \E n \in Nodes : RemoveCrashedNodeFromClusterState(n)
        \/ \E n \in Nodes : NodeFaultDetectionKicksNodeOut(n)

----
\* Helper functions / relations for making assertions


ActiveShard(n) ==
    clusterStateOnMaster.routingTable[n] /= Unassigned

UpToPoint(ntlog, i) ==
    [j \in 1..i |-> ntlog[j]]
    
ExceptSafe(ntlog) ==
    [j \in DOMAIN ntlog |-> [ntlog[j] EXCEPT !.safe = TRUE]]
    
SameTranslogUpToGlobalCheckPoint ==
    \A n1, n2 \in Nodes: n1 /= n2 /\ ActiveShard(n1) /\ ActiveShard(n2) =>
        ExceptSafe(UpToPoint(tlog[n1], globalCheckPoint[n1])) = ExceptSafe(UpToPoint(tlog[n2], globalCheckPoint[n1]))


\* all shard copies of non-crashed nodes contain same data
AllCopiesSameContents ==
    \* TODO: extend invariant to cover store as well
    \A n1, n2 \in Nodes: n1 /= n2 /\ ActiveShard(n1) /\ ActiveShard(n2) => ExceptSafe(tlog[n1]) = ExceptSafe(tlog[n2])
    
\* no active messages        
NoActiveMessages == messages = {}

\* for each replication request/response there must be a corresponding entry in waitForResponses
\* except if this already lead to a shard failure
CorrespondingResponses ==
    /\ \A m \in messages :
           m.mtype = ReplicationResponse \/ m.mtype = TrimTranslogResponse =>
               m.msource \in waitForResponses[m.req] \/ clusterStateOnMaster.routingTable[m.mdest] = Unassigned 
    /\ \A m \in messages :
           m.mtype = ReplicationRequest \/ m.mtype = TrimTranslogRequest =>
               m.mdest \in waitForResponses[m.req] \/ clusterStateOnMaster.routingTable[m.msource] = Unassigned

NotTooManyResponses ==
    \A n \in Nodes : \A r \in DOMAIN waitForResponses : n \in waitForResponses[r] =>
        \E m \in messages : \/ (m.mtype = ReplicationRequest \/ m.mtype = TrimTranslogRequest) /\ m.mdest \in waitForResponses[m.req]
                            \/ (m.mtype = ReplicationResponse \/ m.mtype = TrimTranslogResponse) /\ m.msource \in waitForResponses[m.req]

\* cluster state on master has been applied to non-crashed nodes
ClusterStateAppliedOnAllNodes ==
    \A n \in Nodes : n \notin crashedNodes => clusterStateOnNode[n] = clusterStateOnMaster

\* crashed node has been handled by master    
CrashHandled == \A n \in crashedNodes : clusterStateOnMaster.routingTable[n] = Unassigned

AllCopiesSameContentsOnQuietDown ==
    (/\ NoActiveMessages
     /\ CrashHandled
     /\ ClusterStateAppliedOnAllNodes)
    => AllCopiesSameContents

AllAckedResponsesStored ==
    \A r \in clientResponses : \A n \in Nodes :
       ActiveShard(n) => /\ store[n][r.id] /= Nil
                         /\ store[n][r.id].seq >= r.seq
                         /\ r.seq \in DOMAIN tlog[n]
                         /\ tlog[n][r.seq].id = r.id
                         /\ tlog[n][r.seq].value = r.value
                         /\ tlog[n][r.seq].term = r.term

WellformedRoutingTable(routingTable) == Cardinality(Primaries(routingTable)) <= 1
WellformedClusterState(clusterState) == WellformedRoutingTable(clusterState.routingTable) 

\* does not hold if NodeFaultDetectionKicksNodeOut rule is enabled
MaxOneNodeThinksItIsPrimary ==
    Cardinality({n \in Nodes : n \notin crashedNodes /\ clusterStateOnNode[n].routingTable[n] = Primary}) <= 1

GlobalCheckPointBelowLocalCheckPoints ==
    \A n \in Nodes : globalCheckPoint[n] <= localCheckPoint[n][n]

LocalCheckPointOnNodeHigherThanWhatOthersHave ==
    \A n1, n2 \in Nodes : localCheckPoint[n1][n1] >= localCheckPoint[n2][n1]


=============================================================================
