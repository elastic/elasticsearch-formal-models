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
          ReplicationRequest, ReplicationResponse

\* Set of possible initial cluster states (to be defined by the model checker). A cluster state is
\* a record type containing a routing table (map from Nodes to {Primary, Replia, Unassigned})
\* and a primary term (natural number), for example:
\* [routingTable |-> [n1 |-> Primary, n2 |-> Replica, n3 |-> Unassigned], primaryTerm |-> 1]
CONSTANTS InitialClusterStates


----
\* Global variables

\* A bag of records representing requests and responses sent from one data node
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat (TODO: check if this is still the case).
VARIABLE messages

\* current cluster state on master (the master is not explicitly modeled as a node)
VARIABLE clusterStateOnMaster

\* Each client (index) request uses a unique value so that we can distinguish between them
\* (this is just an natural number that we increment on each new client operation)
VARIABLE nextClientValue

\* The set of (acknowledged) client responses (stored so we can make assertions)
VARIABLE clientResponses

clientVars == <<nextClientValue, clientResponses>>

\* Each replication request gets a unique id so that we can relate responses
\* (this is just an natural number that we increment on each new client operation)
VARIABLE nextRequestId

\* map from request id to set of nodes we are waiting a response for. This is used e.g. when we
\* replicate an index request to two replicas and want to ensure that we only respond to the client
\* once both replicas have replied
VARIABLE waitForResponses

\* set of crashed nodes (used to denote a physical crash of the node)
VARIABLE crashedNodes


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

\* sequence of log entries (used for debugging purposes)
VARIABLE log

\* map from node id to node id to natural number
VARIABLE localCheckPoint

\* map from node id to natural number
VARIABLE globalCheckPoint

nodeVars == <<clusterStateOnNode, nextSeq, store, log, tlog, localCheckPoint, globalCheckPoint>>


----
\* General helper functions

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Helper functions for sending/receiving messages
\* Note that messages is a function mapping Message to Nat (number of times message occurs)

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it. Limits the number of duplicates to 2
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = Min({msgs[m] + 1, 2}) ]
    ELSE
        msgs @@ (m :> 1)

\* Given a set of messages ms and a bag of messages msgs, return a new bag of messages with all
\* messages ms in it. Limits the number of duplicates to 2
WithMessages(ms, msgs) == 
    [m \in DOMAIN msgs \cup ms |-> (
        IF m \in ms THEN
            IF m \in DOMAIN msgs THEN
                Min({msgs[m] + 1, 2})
            ELSE 1
        ELSE msgs[m])]

\* Helper for Discard and Reply. Given a message m and bag of messages msgs, return a new bag of
\* messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        IF msgs[m] > 1 THEN
            [msgs EXCEPT ![m] = @ - 1]
        ELSE
            [n \in (DOMAIN msgs \ {m}) |-> msgs[n]]
    ELSE
        msgs

\* Helper relations for sending/receiving messages

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a node is done processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))
    
\* Combination of Send and Discard
MultiReply(responses, request) ==
    messages' = WithoutMessage(request, WithMessages(responses, messages))
    

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
        
RerouteWithFailedShard(n, cs) ==
    LET rt == cs.routingTable
       IN 
        IF rt[n] = Unassigned THEN
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
             IN [clusterStateOnMaster EXCEPT
                     !.routingTable = newRoutingTable,
                     !.primaryTerm  = newPrimaryTerm] 

----
\* Define initial values for all variables

InitNodesVars == /\ nextSeq = [n \in Nodes |-> 1]
                 /\ clusterStateOnNode = [n \in Nodes |-> clusterStateOnMaster]
                 /\ store = [n \in Nodes |-> [id \in DocumentIds |-> Nil]]
                 /\ tlog = [n \in Nodes |-> << >>]
                 /\ log = [n \in Nodes |-> << >>]
                 /\ localCheckPoint = [n1 \in Nodes |-> [n2 \in Nodes |-> 0]]
                 /\ globalCheckPoint = [n \in Nodes |-> 0]
                 
Init == /\ messages = << >>
        /\ clusterStateOnMaster \in InitialClusterStates
        /\ crashedNodes = {}
        /\ nextClientValue = 1
        /\ clientResponses = {}
        /\ nextRequestId = 1
        /\ waitForResponses = << >>
        /\ InitNodesVars

----
\* Define next step relation

\* Highest sequence number without gaps in translog, yields 0 if no such number exists
MaxGaplessSeq(ntlog) ==
    LET domWithZero == DOMAIN ntlog \cup {0}
    IN  CHOOSE i \in domWithZero : (i+1) \notin domWithZero /\ \A j \in 0..i : j \in domWithZero

\* Index request arrives on node n with document id docId
ClientRequest(n, docId) ==
    /\ n \notin crashedNodes \* only non-crashed nodes can accept client commands
    /\ LET routingTable == clusterStateOnNode[n].routingTable
           primaryTerm == clusterStateOnNode[n].primaryTerm
       IN  /\ routingTable[n] = Primary \* node believes itself to be the primary
           /\ LET storeEntry == [seq   |-> nextSeq[n],
                                 value |-> nextClientValue]
                  tlogEntry == [id    |-> docId,
                                seq   |-> nextSeq[n],
                                value |-> nextClientValue]
                  newTlog == [tlog EXCEPT ![n] = @ @@ (nextSeq[n] :> tlogEntry)]
                  logEntry == [seq   |-> nextSeq[n],
                               id    |-> docId,
                               term  |-> primaryTerm,
                               value |-> nextClientValue]
                  replRequests == {([mtype    |-> ReplicationRequest,
                                     msource  |-> n,
                                     mdest    |-> rn,
                                     req      |-> nextRequestId,
                                     seq      |-> nextSeq[n],
                                     term     |-> primaryTerm,
                                     id       |-> docId,
                                     value    |-> nextClientValue,
                                     globalCP |-> globalCheckPoint[n]]) : rn \in Replicas(routingTable)}
              IN  /\ store' = [store EXCEPT ![n][docId] = storeEntry]
                  /\ tlog' = newTlog
                  /\ nextSeq' = [nextSeq EXCEPT ![n] = @ + 1]
                  /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = MaxGaplessSeq(newTlog[n])]
                  \* Make sure that each request is unique
                  /\ nextClientValue' = nextClientValue + 1
                  \* generate unique key for replication requests so that we can relate responses
                  /\ nextRequestId' = nextRequestId + 1
                  /\ messages' = WithMessages(replRequests, messages)
                  /\ waitForResponses' = waitForResponses @@ (nextRequestId :> Replicas(routingTable))
                  /\ log' = [log EXCEPT ![n] = Append(log[n], logEntry)]
    /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, clientResponses, crashedNodes,
                   globalCheckPoint>>
    
    
DefaultResponse(m) == [mtype     |-> ReplicationResponse,
                       msource   |-> m.mdest,
                       mdest     |-> m.msource,
                       req       |-> m.req,
                       id        |-> m.id,
                       seq       |-> m.seq,
                       term      |-> m.term,
                       localCP   |-> 0,
                       result    |-> Success]

\* Replication request arrives on node n with message m
HandleReplicationRequest(m) ==
   LET n == m.mdest
       currentTerm == clusterStateOnNode[n].primaryTerm
   IN  /\ n \notin crashedNodes
       /\ m.mtype = ReplicationRequest
       /\ IF m.term >= currentTerm THEN
               /\ LET storeEntry == [seq   |-> m.seq,
                                     value |-> m.value]
                      newStore == [store[n] EXCEPT ![m.id] = storeEntry]
                      tlogEntry == [id    |-> m.id,
                                    seq   |-> m.seq,
                                    value |-> m.value]
                      newTlog == [tlog EXCEPT ![n] = @ @@ (m.seq :> tlogEntry)]
                      logEntry == [seq  |-> m.seq,
                                   term |-> m.term,
                                   myterm |-> clusterStateOnNode[n].primaryTerm,
                                   id |-> m.id,
                                   value |-> m.value]
                      newLog == Append(log[n], logEntry)
                  IN  /\ log' = [log EXCEPT ![n] = newLog]
                      /\ store' = IF store[n][m.id] = Nil \/ m.seq > store[n][m.id].seq THEN
                                      [store EXCEPT ![n] = newStore]
                                  ELSE
                                      store
                      /\ tlog' = newTlog
                      /\ nextSeq' = IF m.seq + 1 > nextSeq[n] THEN
                                        [nextSeq EXCEPT ![n] = m.seq + 1] 
                                    ELSE
                                        nextSeq
                      /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = Max({@, m.globalCP})]
                      /\ Reply([DefaultResponse(m) EXCEPT !.localCP = MaxGaplessSeq(newTlog[n])], m)
               /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, nextClientValue, nextRequestId,
                              clientResponses, waitForResponses, crashedNodes, localCheckPoint>>
           ELSE
               \* don't replicate entries with lower term than we have
               /\ Reply([DefaultResponse(m) EXCEPT !.result = Failed], m)
               /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, waitForResponses,
                              crashedNodes, nodeVars>>                                 

\* Replication response arrives on node n with message m
HandleReplicationResponse(m) ==
   LET n == m.mdest
       req == m.req
       rn == m.msource
       finishIfNeeded ==
                /\  waitForResponses' = [waitForResponses EXCEPT ![req] = @ \ {rn}]
                /\  IF (waitForResponses[req] = {rn}) THEN
                         \* last response, answer client
                         clientResponses' = clientResponses \cup {[req  |-> req,
                                                                   seq  |-> m.seq,
                                                                   term |-> m.term,
                                                                   id   |-> m.id]}
                    ELSE
                         UNCHANGED <<clientResponses>>
       finishAsFailed ==
                /\ waitForResponses' = [waitForResponses EXCEPT ![req] = {}]
                /\ UNCHANGED <<clientResponses>>
   IN  /\ n \notin crashedNodes
       /\ m.mtype = ReplicationResponse
       /\ IF req \in DOMAIN waitForResponses /\ rn \in waitForResponses[req] THEN
              \/ /\ m.result = Success
                 /\ IF m.localCP > localCheckPoint[n][rn] THEN
                        LET newLocalCheckPoint == [localCheckPoint EXCEPT ![n][rn] = m.localCP]
                            rt == clusterStateOnNode[n].routingTable
                            computedGlobalCP == Min({newLocalCheckPoint[n][i] : i \in Assigned(rt)})
                        IN  /\ localCheckPoint' = newLocalCheckPoint
                            \* also update global checkpoint if necessary
                            /\ globalCheckPoint' =
                                   [globalCheckPoint EXCEPT ![n] = Max({@, computedGlobalCP})]
                    ELSE
                        UNCHANGED <<localCheckPoint, globalCheckPoint>> 
                 /\ UNCHANGED <<clusterStateOnMaster>>
                 /\ finishIfNeeded
              \/ /\ m.result = Failed
                 /\ IF m.term < clusterStateOnMaster.primaryTerm THEN
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
       /\ Discard(m)       
       /\ UNCHANGED <<nextClientValue, nextRequestId, crashedNodes, clusterStateOnNode, store, tlog,
                      log, nextSeq>>
       
CleanReplicationResponseToDeadNode(m) ==
    /\ m.mtype = ReplicationResponse
    /\ m.mdest \in crashedNodes
    /\ Discard(m)
    /\ waitForResponses' = [waitForResponses EXCEPT ![m.req] = @ \ {m.msource}]
    /\ UNCHANGED <<clusterStateOnMaster, clientResponses, nextClientValue, nextRequestId, nodeVars,
                   crashedNodes>>

\* Take transaction log ntlog1 up to point i and fill the rest with entries from ntlog2
\* Used for quick resync when replica notices that another replica was promoted to primary                    
FillMissingFromCP(ntlog1, ntlog2, i) ==
    [j \in (DOMAIN ntlog1 \cap 1..i) \cup (DOMAIN ntlog2 \ 1..i) |->
        IF j <= i THEN ntlog1[j] ELSE ntlog2[j]]

\* Cluster state propagated from master is applied to node n
ApplyClusterStateFromMaster(n) ==
    /\ n \notin crashedNodes
    /\ clusterStateOnNode[n] /= clusterStateOnMaster
    /\ clusterStateOnNode' = [clusterStateOnNode EXCEPT ![n] = clusterStateOnMaster]
    /\ IF AnotherNodeWasPromotedToPrimary(n, clusterStateOnMaster.routingTable,
              clusterStateOnNode[n].routingTable) THEN
          \* do a quick resync from that node
          LET newPrimary == ChoosePrimary(clusterStateOnMaster.routingTable)
              newPrimaryStore == store[newPrimary]
              existingDocumentKeys == {docId \in DOMAIN newPrimaryStore : newPrimaryStore[docId] /= Nil} 
              globalCP == localCheckPoint[newPrimary][newPrimary] \* Min({globalCheckPoint[n], globalCheckPoint[newPrimary]})
          IN  /\ store' = [store EXCEPT ![n] = store[newPrimary]]
              /\ tlog' =  [tlog EXCEPT ![n] = FillMissingFromCP(tlog[n], tlog[newPrimary], globalCP)]
       ELSE
           UNCHANGED <<store, tlog>>
    /\ UNCHANGED <<messages, crashedNodes, clusterStateOnMaster, log, nextSeq, clientVars,
                   nextRequestId, waitForResponses, localCheckPoint, globalCheckPoint>>
    
\* Node n crashes        
CrashNode(n) ==
    /\ n \notin crashedNodes
    /\ crashedNodes' = crashedNodes \cup {n}
    /\ UNCHANGED <<clusterStateOnMaster, messages, clientVars, nextRequestId, waitForResponses,
                   nodeVars>>

\* Drop replication response message that goes to a crashed node (and clean up waitForResponses)
DropReplicationResponseMessage(m) ==
    /\ m.mtype = ReplicationResponse
    /\ m.result = Success
    /\ Reply([m EXCEPT !.result = Failed], m)
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>

\* Drop replication request message    
DropReplicationRequestMessage(m) ==
    /\ m.mtype = ReplicationRequest
    /\ Reply([DefaultResponse(m) EXCEPT !.result = Failed], m)
    /\ UNCHANGED <<crashedNodes, clusterStateOnMaster, nextRequestId, waitForResponses, clientVars,
                   nodeVars>>


\* Master removes crashed node n from its cluster state
RemoveCrashedNodeFromClusterState(n) ==
    /\ n \in crashedNodes
    /\ clusterStateOnMaster' = RerouteWithFailedShard(n, clusterStateOnMaster)
    /\ UNCHANGED <<crashedNodes, messages, nextRequestId, waitForResponses, clientVars, nodeVars>>

\* Defines how the variables may transition.
Next == \/ \E n \in Nodes : \E docId \in DocumentIds : ClientRequest(n, docId)
        \/ \E m \in DOMAIN messages : HandleReplicationRequest(m)
        \/ \E m \in DOMAIN messages : HandleReplicationResponse(m)
        \/ \E m \in DOMAIN messages : CleanReplicationResponseToDeadNode(m)
        \/ \E m \in DOMAIN messages : DropReplicationRequestMessage(m)
        \/ \E m \in DOMAIN messages : DropReplicationResponseMessage(m)
        \/ \E n \in Nodes : ApplyClusterStateFromMaster(n)
        \/ \E n \in Nodes : CrashNode(n)
        \/ \E n \in Nodes : RemoveCrashedNodeFromClusterState(n)

----
\* Helper functions / relations for making assertions


ActiveShard(n) ==
    n \notin crashedNodes /\ clusterStateOnMaster.routingTable[n] /= Unassigned

\* all shard copies of non-crashed nodes contain same data
AllCopiesSameContents ==
    \A n1, n2 \in Nodes: ActiveShard(n1) /\ ActiveShard(n2) => store[n1] = store[n2] /\ tlog[n1] = tlog[n2]

\* no active messages        
NoActiveMessages == DOMAIN messages = {}

\* for each replication request/response there must be a corresponding entry in waitForResponses
CorrespondingResponses ==
    /\ \A m \in DOMAIN messages :
           m.mtype = ReplicationResponse => m.req = Nil \/ m.msource \in waitForResponses[m.req]
    /\ \A m \in DOMAIN messages :
           m.mtype = ReplicationRequest => m.req = Nil \/ m.mdest \in waitForResponses[m.req]

NotTooManyResponses ==
    NoActiveMessages => (\A n \in Nodes : \A r \in DOMAIN waitForResponses : n \notin waitForResponses[r])

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
    (/\ NoActiveMessages
     /\ CrashHandled
     /\ ClusterStateAppliedOnAllNodes)
    => \A r \in clientResponses : \A n \in Nodes :
           ActiveShard(n) => /\ store[n][r.id] /= Nil
                             /\ store[n][r.id].seq >= r.seq
                             /\ r.seq \in DOMAIN tlog[n]
                             /\ tlog[n][r.seq].id = r.id

WellFormedMessages(msgs) == \A m \in (DOMAIN msgs) : (msgs[m] > 0) /\ (msgs[m] <= 2)

WellformedRoutingTable(routingTable) == Cardinality(Primaries(routingTable)) <= 1
WellformedClusterState(clusterState) == WellformedRoutingTable(clusterState.routingTable) 


\* don't explore states where replica has applied cluster state but primary has not
OnlyStatesWherePrimaryAppliesCSbeforeReplica ==
    \A n1, n2 \in Nodes :
        (/\ n1 /= n2
         /\ n1 \notin crashedNodes
         /\ n2 \notin crashedNodes
         /\ clusterStateOnMaster.routingTable[n1] = Primary
         /\ clusterStateOnNode[n1] /= clusterStateOnMaster)
        => clusterStateOnNode[n2] /= clusterStateOnMaster

MaxOneNodeThinksItIsPrimary ==
    Cardinality({n \in Nodes : n \notin crashedNodes /\ clusterStateOnNode[n].routingTable[n] = Primary}) <= 1


UncrashedNodeIsFailed ==
    \A n \in Nodes : n \notin crashedNodes => clusterStateOnMaster.routingTable[n] /= Unassigned


=============================================================================
