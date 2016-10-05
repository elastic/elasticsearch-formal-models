------------------------------ MODULE elasticsearch ------------------------------

\* Imported modules
EXTENDS Naturals, FiniteSets, Sequences, TLC

----
\* Constants

\* Set of node ids (one for each data node in the cluster)
CONSTANTS Nodes

\* Set of document ids (i.e. possible values for "_id" field)
CONSTANTS DocumentIds

\* Shard states
\* Unassigned is used as special value when no shard is assigned to a node
\* (e.g. after shard failed and removed from the routing table)
CONSTANTS Primary, Replica, Unassigned

\* To denote a non-existing value (e.g. in transaction log)
CONSTANTS Nil

\* Message RPC type
CONSTANTS Request, Response
\* Message RPC methods
CONSTANTS Replication, TrimTranslog \* Index not used for now as reroute logic is not implemented
\* RPC status codes on responses
CONSTANTS Success, Failed

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
\* (this is just an natural number that we increment on each client operation)
VARIABLE nextClientValue

\* The set of (acknowledged) client responses (stored in a variable to make assertions)
VARIABLE clientResponses

clientVars == <<nextClientValue, clientResponses>>

\* Replication requests for the same indexing request get a common unique id so that we can relate their responses
\* (this is just an natural number that we increment on each new request operation)
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

\* transaction log, map from node id to map from sequence number to document
VARIABLE tlog

\* current primary term, map from node id to term number
VARIABLE currentTerm

\* map from node id to node id to natural number
VARIABLE localCheckPoint

\* map from node id to natural number
VARIABLE globalCheckPoint

nodeVars == <<clusterStateOnNode, nextSeq, tlog, localCheckPoint, globalCheckPoint, currentTerm>>


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

FailedResponse(m) == [DefaultResponse(m) EXCEPT !.result = Failed]


----
\* Helper functions on routing table

Primaries(routingTable) == {n \in Nodes : routingTable[n] = Primary}
Replicas(routingTable) == {n \in Nodes : routingTable[n] = Replica}
Assigned(routingTable) == {n \in Nodes : routingTable[n] /= Unassigned}

HasUniquePrimary(routingTable) == Cardinality(Primaries(routingTable)) = 1
ChoosePrimary(routingTable) == CHOOSE n \in Nodes : n \in Primaries(routingTable)
ChooseReplica(routingTable) == CHOOSE n \in Nodes : n \in Replicas(routingTable)

NodeWasPromotedToPrimary(n, incomingRoutingTable, myRoutingTable) ==
  LET oldPrimaries == Primaries(myRoutingTable)
      newPrimaries == Primaries(incomingRoutingTable)
  IN  /\ n \notin oldPrimaries
      /\ n \in newPrimaries

RerouteWithFailedShard(n, clusterState) ==
  LET rt == clusterState.routingTable
  IN  IF rt[n] = Unassigned THEN
        clusterState
      ELSE
        LET
          \* increase primary term on primary failure
          newPt == IF rt[n] = Primary THEN
                     clusterState.primaryTerm + 1
                   ELSE
                     clusterState.primaryTerm
          newRt == IF rt[n] = Primary /\ Cardinality(Replicas(rt)) > 0 THEN
                     \* promote other copy to primary
                     [rt EXCEPT ![n] = Unassigned, ![ChooseReplica(rt)] = Primary]
                   ELSE
                     [rt EXCEPT ![n] = Unassigned]
        IN  [clusterState EXCEPT !.routingTable = newRt, !.primaryTerm  = newPt]

----
\* Helper functions on translog

\* Whether position in the translog is safe to advance local checkpoint
SafeTlogPosition(ntlog, i) == i \in DOMAIN ntlog /\ ntlog[i].safe

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

InitNodesVars == /\ nextSeq            = [n \in Nodes |-> 1]
                 /\ clusterStateOnNode = [n \in Nodes |-> clusterStateOnMaster]
                 /\ tlog               = [n \in Nodes |-> << >>]
                 /\ localCheckPoint    = [n1 \in Nodes |-> [n2 \in Nodes |-> 0]]
                 /\ globalCheckPoint   = [n \in Nodes |-> 0]
                 /\ currentTerm        = [n \in Nodes |-> clusterStateOnMaster.primaryTerm]

Init == /\ messages          = {}
        /\ crashedNodes      = {}
        /\ nextClientValue   = 1
        /\ clientResponses   = {}
        /\ nextRequestId     = 1
        /\ replicationStatus = << >>
        /\ messageDrops      = 0
        /\ clusterStateOnMaster \in InitialClusterStates
        /\ InitNodesVars

----
\* Define next step relation

\* Index request arrives on node n with document id docId
ClientRequest(n, docId) ==
  /\ n \notin crashedNodes \* only non-crashed nodes can accept client commands
  /\ clusterStateOnNode[n].routingTable[n] = Primary \* node believes itself to be the primary
  /\ LET 
       replicas     == Replicas(clusterStateOnNode[n].routingTable)
       primaryTerm  == currentTerm[n]
       tlogEntry    == [id    |-> docId,
                        term  |-> primaryTerm,
                        value |-> nextClientValue,
                        safe  |-> TRUE]
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
                          globalCP |-> globalCheckPoint[n]]) : rn \in replicas}
     IN /\ tlog' = [tlog EXCEPT ![n] = (nextSeq[n] :> tlogEntry) @@ @]
        /\ nextSeq' = [nextSeq EXCEPT ![n] = @ + 1]
        /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = MaxGaplessSeq(tlog'[n])]
        \* Make sure that each request is unique
        /\ nextClientValue' = nextClientValue + 1
        \* generate unique key for replication requests so that we can relate responses
        /\ nextRequestId' = nextRequestId + 1
        /\ messages' = messages \cup replRequests
        /\ IF replicas = {} THEN
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
HandleReplicationRequest(n, m) ==
   /\ n \notin crashedNodes
   /\ m.mtype = Request
   /\ m.mmethod = Replication
   /\ IF m.rterm < currentTerm[n] THEN
       \* don't accept replication requests with lower term than we have
        /\ Reply(FailedResponse(m), m)
        /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, replicationStatus,
                       crashedNodes, nodeVars, messageDrops>>
      ELSE
        /\ LET
             tlogEntry      == [id    |-> m.id,
                                term  |-> m.sterm,
                                value |-> m.value,
                                safe  |-> TRUE]
             newGlobalCP    == Max({globalCheckPoint[n], m.globalCP})
             safeMarkedTlog == [tlog EXCEPT ![n] = MarkSafeUpTo(@, newGlobalCP)]
             gapsFilledTlog == IF m.rterm > currentTerm[n] THEN
                                 \* there is a new primary, cannot safely advance local checkpoint
                                 \* before resync done, take globalCP from request into account
                                 [safeMarkedTlog EXCEPT ![n] =
                                   FillGapsAndMarkSafe(@, newGlobalCP, FALSE)]
                               ELSE
                                 safeMarkedTlog
              newTlog       == [gapsFilledTlog EXCEPT ![n] =
                                 \* ignore if we already have an entry with higher term
                                 IF m.seq \in DOMAIN @ /\ m.rterm < @[m.seq].term THEN
                                   @
                                 ELSE 
                                   (m.seq :> tlogEntry) @@ @
                               ]
              localCP       == MaxGaplessSeq(newTlog[n])
           IN 
             /\ tlog' = newTlog
             /\ nextSeq' = [nextSeq EXCEPT ![n] = Max({@, m.seq + 1})]
             /\ currentTerm' = [currentTerm EXCEPT ![n] = Max({@, m.rterm})]
             /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = newGlobalCP]
             /\ localCheckPoint'  = [localCheckPoint EXCEPT ![n][n] = localCP]
             /\ Reply([DefaultResponse(m) EXCEPT !.localCP = localCP], m)
        /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, nextClientValue, nextRequestId,
                       clientResponses, crashedNodes, messageDrops, replicationStatus>>

\* Trim translog request arrives on node n with message m
HandleTrimTranslogRequest(n, m) ==
  /\ n \notin crashedNodes
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
       IN
         /\ tlog' = [gapsFilledTlog EXCEPT ![n] = TrimTlog(@, m.maxseq, m.term)]
         /\ currentTerm' = IF m.term > currentTerm[n] THEN
                             [currentTerm EXCEPT ![n] = m.term]
                           ELSE
                              currentTerm
         /\ Reply(DefaultResponse(m), m)
     ELSE
       \* don't handle requests with lower term than we have
       /\ Reply(FailedResponse(m), m)
       /\ UNCHANGED <<tlog, currentTerm>>
  /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars,
                 clusterStateOnNode, nextClientValue, nextRequestId, clientResponses,
                 crashedNodes, messageDrops, nextSeq, globalCheckPoint,
                 localCheckPoint, replicationStatus>>

FinishIfNeeded(m) ==
  IF { ms \in messages : ms.req = m.req } = {m} THEN
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

\* Replication response arrives on node n from node rn with message m
HandleReplicationResponse(n, rn, m) ==
  /\ n \notin crashedNodes
  /\ m.mtype = Response
  /\ m.mmethod = Replication
  /\ IF replicationStatus[m.req] = Nil THEN
       \/ /\ m.result = Success
          \* don't update checkpoints if local checkpoint came from request with lower term
          /\ IF m.rterm >= currentTerm[n] /\
                m.localCP > localCheckPoint[n][rn] /\
                clusterStateOnNode[n].routingTable[n] /= Unassigned THEN
               LET
                 newLocalCheckPoint == [localCheckPoint EXCEPT ![n][rn] = m.localCP]
                 assigned           == Assigned(clusterStateOnNode[n].routingTable)
                 computedGlobalCP   == Min({newLocalCheckPoint[n][i] : i \in assigned})
               IN
                 /\ localCheckPoint'  = newLocalCheckPoint
                 \* also update global checkpoint if necessary
                 /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = computedGlobalCP]
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
  /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, tlog,
                 nextSeq, messageDrops, currentTerm>>


\* Trim translog response arrives on node n from node rn with message m
HandleTrimTranslogResponse(n, rn, m) ==
   /\ n \notin crashedNodes
   /\ m.mtype = Response
   /\ m.mmethod = TrimTranslog
   /\ IF replicationStatus[m.req] = Nil THEN
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
   /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, tlog,
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
       LET
         ntlog          == tlog[n]
         globalCP       == globalCheckPoint[n]
         replicas       == Replicas(clusterStateOnMaster.routingTable)
         numReplicas    == Cardinality(replicas)
         maxTlogPos     == Max((DOMAIN ntlog) \cup {0})
         numDocs        == maxTlogPos - globalCP
         replRequests   == {([mtype    |-> Request,
                              mmethod  |-> Replication,
                              msource  |-> n,
                              mdest    |-> rn,
                              req      |-> nextRequestId + i - 1,
                              seq      |-> globalCP + i,
                              rterm    |-> currentTerm'[n], \* current term when issuing request
                              sterm    |-> IF (globalCP + i) \in DOMAIN ntlog THEN
                                             ntlog[globalCP + i].term
                                          ELSE
                                             0,
                              id       |-> IF (globalCP + i) \in DOMAIN ntlog THEN
                                             ntlog[globalCP + i].id
                                           ELSE
                                             Nil,
                              value    |-> IF (globalCP + i) \in DOMAIN ntlog THEN
                                             ntlog[globalCP + i].value
                                           ELSE
                                             Nil,
                              internal |-> TRUE,
                              globalCP |-> globalCP]) : i \in 1..numDocs, rn \in replicas}
         trimRequests   == {[mtype    |-> Request,
                             mmethod  |-> TrimTranslog,
                             msource  |-> n,
                             mdest    |-> rn,
                             req      |-> nextRequestId + numDocs,
                             maxseq   |-> maxTlogPos,
                             term     |-> currentTerm'[n],
                             internal |-> TRUE] : rn \in replicas}
         \* fill gaps in tlog
         newTlog        == FillGapsAndMarkSafe(tlog[n], globalCheckPoint[n], TRUE)
         \* reset local checkpoint for other nodes and calculate new one for current node
         localCPs       == [[n2 \in Nodes |-> 0] EXCEPT ![n] = MaxGaplessSeq(newTlog)]
       IN 
         /\ tlog' = [tlog EXCEPT ![n] = newTlog]
         /\ localCheckPoint' = [localCheckPoint EXCEPT ![n] = localCPs]
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
      /\ IF  clusterStateOnMaster.routingTable[n] = Replica /\
             clusterStateOnMaster.primaryTerm > currentTerm[n] THEN
           tlog' = [tlog EXCEPT ![n] = FillGapsAndMarkSafe(@, globalCheckPoint[n], FALSE)]
         ELSE
           UNCHANGED <<tlog>>
      /\ UNCHANGED <<localCheckPoint, messages, nextRequestId, replicationStatus>>
  /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextSeq, clientVars,
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

\* Fail request message    
FailRequestMessage(m) ==
  /\ m.mtype = Request
  /\ Reply(FailedResponse(m), m)
  /\ messageDrops' = messageDrops + 1
  /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, replicationStatus, clientVars,
                 nodeVars>>

\* Fail response message
FailResponseMessage(m) ==
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
        \/ \E m \in messages : HandleReplicationRequest(m.mdest, m)
        \/ \E m \in messages : HandleReplicationResponse(m.mdest, m.msource, m)
        \/ \E m \in messages : HandleTrimTranslogRequest(m.mdest, m)
        \/ \E m \in messages : HandleTrimTranslogResponse(m.mdest, m.msource, m)
        \/ \E m \in messages : CleanResponseToDeadNode(m)
        \/ \E m \in messages : FailRequestMessage(m)
        \/ \E m \in messages : FailResponseMessage(m)
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
       ActiveShard(n) => /\ r.seq \in DOMAIN tlog[n]
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
