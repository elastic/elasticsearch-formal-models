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

\* Message RPC type
CONSTANTS Request, Response
\* Message RPC methods
CONSTANTS Replication, TrimTranslog \* Index not used for now as reroute logic is not implemented

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

\* map from request id to flag that determines if the request was successfully replicated.
\* Possible values {TRUE, FALSE, Nil}. The special value Nil means that outcome is not decided yet.
VARIABLE replicationStatus

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

\* Set of in-flight messages for the given node and request id
InflightRequestsFromNode(req, n, msgs) ==
    {m \in msgs : m.req = req /\ ((m.mtype = Request /\ m.msource = n) \/ (m.mtype = Response /\ m.mdest = n))}

DefaultReplicationResponse(m) == [mtype     |-> Response,
                                  mmethod   |-> m.mmethod,
                                  msource   |-> m.mdest,
                                  mdest     |-> m.msource,
                                  req       |-> m.req,
                                  id        |-> m.id,
                                  seq       |-> m.seq,
                                  rterm     |-> m.rterm,
                                  sterm     |-> m.sterm,
                                  value     |-> m.value,
                                  internal  |-> m.internal,
                                  localCP   |-> 0,
                                  result    |-> Success]

DefaultTrimTranslogResponse(m) == [mtype     |-> Response,
                                   mmethod   |-> m.mmethod,
                                   msource   |-> m.mdest,
                                   mdest     |-> m.msource,
                                   req       |-> m.req,
                                   maxseq    |-> m.maxseq,
                                   term      |-> m.term,
                                   internal  |-> m.internal,
                                   result    |-> Success]

DefaultResponse(m) ==
    IF m.mmethod = Replication THEN
        DefaultReplicationResponse(m)
    ELSE
        DefaultTrimTranslogResponse(m)

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
\* Helper functions on translog

\* Whether position in the translog is safe to advance local checkpoint
SafeTlogPosition(ntlog, i) ==
    i \in DOMAIN ntlog /\ ntlog[i].safe

\* Yields highest sequence number without gaps in translog, yields 0 if no such number exists
MaxGaplessSeq(ntlog) ==
    LET domWithZero == DOMAIN ntlog \cup {0}
    IN  CHOOSE i \in domWithZero :
        /\ SafeTlogPosition(ntlog, i+1) = FALSE
        /\ \A j \in 1..i : SafeTlogPosition(ntlog, j)

\* Fill gaps in translog and set safety marker "safe" for values at position strictly larger than "from"
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

\* Mark translog entries safe to advance local checkpoint up to position "to" included.
MarkSafeUpTo(ntlog, to) ==
    [j \in DOMAIN ntlog |->
        IF j <= to THEN
            [ntlog[j] EXCEPT !.safe = TRUE]
        ELSE
            ntlog[j]]

ElementsToKeep(ntlog, maxseq, minterm) ==
    {i \in DOMAIN ntlog : i <= maxseq \/ ntlog[i].term >= minterm}

\* Trim elements from translog with position strictly greater than maxseq and term strictly lower than minterm
TrimTlog(ntlog, maxseq, minterm) ==
    [j \in ElementsToKeep(ntlog, maxseq, minterm) |-> ntlog[j]]

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
        /\ replicationStatus = << >>
        /\ InitNodesVars
        /\ messageDrops = 0

----
\* Define next step relation

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
                  replRequests == {([mtype    |-> Request,
                                     mmethod  |-> Replication,
                                     msource  |-> n,
                                     mdest    |-> rn,
                                     req      |-> nextRequestId,
                                     seq      |-> nextSeq[n],
                                     rterm    |-> primaryTerm, \* current term when issuing request
                                     sterm    |-> primaryTerm, \* term to be stored
                                     id       |-> docId,
                                     value    |-> nextClientValue,
                                     internal |-> FALSE,
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
                  /\ IF Cardinality(Replicas(routingTable)) = 0 THEN
                         /\ clientResponses' = clientResponses \cup {[id    |-> docId,
                                                                   value |-> nextClientValue,
                                                                   seq   |-> nextSeq[n],
                                                                   term  |-> primaryTerm]}
                         /\ replicationStatus' = replicationStatus @@ (nextRequestId :> TRUE)
                     ELSE
                         /\ replicationStatus' = replicationStatus @@ (nextRequestId :> Nil)
                         /\ UNCHANGED <<clientResponses>>
    /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, crashedNodes,
                   globalCheckPoint, messageDrops, currentTerm>>
                       
\* Replication request arrives on node n with message m
HandleReplicationRequest(m) ==
   LET n == m.mdest
   IN  /\ n \notin crashedNodes
       /\ m.mtype = Request
       /\ m.mmethod = Replication
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
                              clientResponses, crashedNodes, messageDrops, replicationStatus>>
           ELSE
               \* don't replicate entries with lower term than we have
               /\ Reply([DefaultReplicationResponse(m) EXCEPT !.result = Failed], m)
               /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars,
                              replicationStatus, crashedNodes, nodeVars, messageDrops>>

FinishIfNeeded(m) ==
    IF InflightRequestsFromNode(m.req, m.mdest, messages) = {m} THEN
        /\ replicationStatus' = [replicationStatus EXCEPT ![m.req] = TRUE]
        /\ IF m.internal = FALSE THEN
               \* last response, answer client
               clientResponses' = clientResponses \cup {[id    |-> m.id,
                                                         value |-> m.value,
                                                         seq   |-> m.seq,
                                                         term  |-> m.rterm]}
           ELSE
               UNCHANGED <<clientResponses>>
     ELSE
         UNCHANGED <<clientResponses, replicationStatus>>

FinishAsFailed(m) ==
    /\ replicationStatus' = [replicationStatus EXCEPT ![m.req] = FALSE]
    /\ UNCHANGED <<clientResponses>>

\* Replication response arrives on node n with message m
HandleReplicationResponse(m) ==
   LET n == m.mdest
       req == m.req
       rn == m.msource
   IN  /\ n \notin crashedNodes
       /\ m.mtype = Response
       /\ m.mmethod = Replication
       /\ IF replicationStatus[req] = Nil THEN
              \/ /\ m.result = Success
                 \* don't update local/global checkpoint if local checkpoint came from request with lower term
                 /\ IF m.rterm >= currentTerm[n] /\ m.localCP > localCheckPoint[n][rn] /\ clusterStateOnNode[n].routingTable[n] /= Unassigned THEN
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
                 /\ FinishIfNeeded(m)
              \/ /\ m.result = Failed
                 /\ IF m.rterm < clusterStateOnMaster.primaryTerm THEN
                      \* term outdated, fail itself and don't ack client write
                      /\ FinishAsFailed(m)
                      /\ UNCHANGED <<clusterStateOnMaster>>
                    ELSE
                      \* fail shard and respond to client
                      /\ clusterStateOnMaster' = RerouteWithFailedShard(rn, clusterStateOnMaster)
                      /\ FinishIfNeeded(m)
                 /\ UNCHANGED <<localCheckPoint, globalCheckPoint>>
          ELSE
              UNCHANGED <<clusterStateOnMaster, clientResponses, replicationStatus, localCheckPoint,
                          globalCheckPoint>>
       /\ messages' = messages \ {m}       
       /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, store, tlog,
                      nextSeq, messageDrops, currentTerm>>

                                   
\* Trim translog request arrives on node n with message m
HandleTrimTranslogRequest(m) ==
   LET n == m.mdest
   IN  /\ n \notin crashedNodes
       /\ m.mtype = Request
       /\ m.mmethod = TrimTranslog
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
       /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars,
                      clusterStateOnNode, nextClientValue, nextRequestId, clientResponses,
                      crashedNodes, messageDrops, nextSeq, store, globalCheckPoint,
                      localCheckPoint, replicationStatus>>
                             
\* Trim translog response arrives on node n with message m
HandleTrimTranslogResponse(m) ==
   LET n == m.mdest
       req == m.req
       rn == m.msource
   IN  /\ n \notin crashedNodes
       /\ m.mtype = Response
       /\ m.mmethod = TrimTranslog
       /\ IF replicationStatus[req] = Nil THEN
              \/ /\ m.result = Success
                 /\ FinishIfNeeded(m)
                 /\ UNCHANGED <<clusterStateOnMaster, localCheckPoint, globalCheckPoint>>
              \/ /\ m.result = Failed
                 /\ IF m.term < clusterStateOnMaster.primaryTerm THEN
                        \* term outdated, fail itself
                        /\ FinishAsFailed(m)
                        /\ UNCHANGED <<clusterStateOnMaster>>
                    ELSE
                        \* fail shard
                        /\ clusterStateOnMaster' = RerouteWithFailedShard(rn, clusterStateOnMaster)
                        /\ FinishIfNeeded(m)
                 /\ UNCHANGED <<localCheckPoint, globalCheckPoint>>
          ELSE
              UNCHANGED <<clusterStateOnMaster, clientResponses, replicationStatus, localCheckPoint,
                          globalCheckPoint>>
       /\ messages' = messages \ {m}       
       /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, store, tlog,
                      nextSeq, messageDrops, clientResponses, currentTerm>>
       
CleanResponseToDeadNode(m) ==
    /\ m.mtype = Response
    /\ m.mdest \in crashedNodes
    /\ messages' = messages \ {m}
    /\ replicationStatus' = [replicationStatus EXCEPT ![m.req] = FALSE]
    /\ UNCHANGED <<clusterStateOnMaster, clientResponses, nextClientValue, nextRequestId, nodeVars,
                   crashedNodes, messageDrops>>

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
                replRequests == {([mtype    |-> Request,
                                   mmethod  |-> Replication,
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
                                   internal |-> TRUE,
                                   globalCP |-> globalCP]) : i \in 1..numDocs, rn \in replicas}
                  trimRequests == {[mtype    |-> Request,
                                    mmethod  |-> TrimTranslog,
                                    msource  |-> n,
                                    mdest    |-> rn,
                                    req      |-> nextRequestId + numDocs,
                                    maxseq   |-> maxTlogPos,
                                    term     |-> currentTerm'[n],
                                    internal |-> TRUE] : rn \in replicas}
             IN  \* fill gaps in tlog
                 /\ tlog' = [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, globalCheckPoint[n], TRUE)]
                 \* reset local checkpoint for other nodes and calculate new one for current node
                 /\ localCheckPoint' = [localCheckPoint EXCEPT ![n] = [[n2 \in Nodes |-> 0] EXCEPT ![n] = MaxGaplessSeq(tlog'[n])]]
                 \* TODO advance global checkpoint marker here
                 /\ messages' = messages \cup replRequests \cup trimRequests
                 /\ nextRequestId' = nextRequestId + (numReplicas * (numDocs + 1))
                 /\ IF replicas = {} THEN
                        UNCHANGED <<replicationStatus>>
                    ELSE
                        replicationStatus' = replicationStatus @@
                                            [i \in nextRequestId..(nextRequestId+numDocs-1) |-> Nil] @@
                                            ((nextRequestId+numDocs) :> Nil)
      ELSE
          /\ IF  clusterStateOnMaster.routingTable[n] = Replica /\ clusterStateOnMaster.primaryTerm > currentTerm[n] THEN
                 tlog' = [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, globalCheckPoint[n], FALSE)]
             ELSE
                 UNCHANGED <<tlog>>
          /\ UNCHANGED <<localCheckPoint, messages, nextRequestId, replicationStatus>>
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextSeq, clientVars, store,
                   globalCheckPoint, messageDrops>>
                   
\* Node fault detection on master finds node n to be isolated from the cluster
NodeFaultDetectionKicksNodeOut(n) ==
    /\ n \notin crashedNodes
    /\ clusterStateOnMaster.routingTable[n] /= Unassigned \* not already unassigned
    /\ clusterStateOnMaster' = RerouteWithFailedShard(n, clusterStateOnMaster)
    /\ UNCHANGED <<crashedNodes, messages, nextRequestId, replicationStatus, clientVars, nodeVars, messageDrops>>

    
\* Node n crashes        
CrashNode(n) ==
    /\ n \notin crashedNodes
    /\ crashedNodes' = crashedNodes \cup {n}
    /\ UNCHANGED <<clusterStateOnMaster, messages, clientVars, nextRequestId, replicationStatus,
                   nodeVars, messageDrops>>

\* Drop request message    
DropRequestMessage(m) ==
    /\ m.mtype = Request
    /\ Reply([DefaultResponse(m) EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, replicationStatus, clientVars,
                   nodeVars>>

\* Drop response message
DropResponseMessage(m) ==
    /\ m.mtype = Response
    /\ m.result = Success
    /\ Reply([m EXCEPT !.result = Failed], m)
    /\ messageDrops' = messageDrops + 1
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, replicationStatus, clientVars,
                   nodeVars>>

\* Master removes crashed node n from its cluster state
RemoveCrashedNodeFromClusterState(n) ==
    /\ n \in crashedNodes
    /\ clusterStateOnMaster' = RerouteWithFailedShard(n, clusterStateOnMaster)
    /\ UNCHANGED <<crashedNodes, messages, nextRequestId, replicationStatus, clientVars, nodeVars, messageDrops>>

\* Defines how the variables may transition.
Next == \/ \E n \in Nodes : \E docId \in DocumentIds : ClientRequest(n, docId)
        \/ \E m \in messages : HandleReplicationRequest(m)
        \/ \E m \in messages : HandleReplicationResponse(m)
        \/ \E m \in messages : HandleTrimTranslogRequest(m)
        \/ \E m \in messages : HandleTrimTranslogResponse(m)
        \/ \E m \in messages : CleanResponseToDeadNode(m)
        \/ \E m \in messages : DropRequestMessage(m)
        \/ \E m \in messages : DropResponseMessage(m)
        \/ \E n \in Nodes : ApplyClusterStateFromMaster(n)
        \/ \E n \in Nodes : CrashNode(n)
        \/ \E n \in Nodes : RemoveCrashedNodeFromClusterState(n)
        \/ \E n \in Nodes : NodeFaultDetectionKicksNodeOut(n)

----
\* Helper functions / relations for making assertions

\* shard that is considered active by the master
ActiveShard(n) ==
    clusterStateOnMaster.routingTable[n] /= Unassigned

\* everything in the translog up to i included
UpToPoint(ntlog, i) ==
    [j \in 1..i |-> ntlog[j]]

\* copy of translog, where we assume all entries are marked safe
ExceptSafe(ntlog) ==
    [j \in DOMAIN ntlog |-> [ntlog[j] EXCEPT !.safe = TRUE]]

\* checks if the translog for all nodes are equivalent up to their global checkpoint, only differing
\* in the safe marker (which can be false sometimes if global checkpoint on one shard is lower than on another one)
SameTranslogUpToGlobalCheckPoint ==
    \A n1, n2 \in Nodes: n1 /= n2 /\ ActiveShard(n1) /\ ActiveShard(n2) =>
        ExceptSafe(UpToPoint(tlog[n1], globalCheckPoint[n1])) = ExceptSafe(UpToPoint(tlog[n2], globalCheckPoint[n1]))


\* all shard copies of non-crashed nodes contain same data
AllCopiesSameContents ==
    \* TODO: extend invariant to cover store as well
    \A n1, n2 \in Nodes: n1 /= n2 /\ ActiveShard(n1) /\ ActiveShard(n2) => ExceptSafe(tlog[n1]) = ExceptSafe(tlog[n2])
    
\* no active messages        
NoActiveMessages == messages = {}

ReplicationStatusDeterminedAfterNoMessages == NoActiveMessages =>
    \A req \in DOMAIN replicationStatus : replicationStatus[req] = TRUE \/ replicationStatus[req] = FALSE

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
