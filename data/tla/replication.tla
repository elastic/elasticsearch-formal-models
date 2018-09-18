`^\Large\bf
TLA+ Model of the Elasticsearch data replication approach ^'
-------------------------------------------------------------------------------------

This file provides a formal specification of how data replication will work in future versions of
Elasticsearch. We consider this work-in-progress: Model as well as implementation are still evolving
and might differ in substantial ways.

Introduction
------------

An index, which is a collection of documents, can be divided into multiple pieces, known as shards,
each of which can be stored on different machines. This approach of horizontal scaling enables Elasticsearch
to store much larger indices than could fit on a single machine. To ensure high availability and 
scale out read access, shards are usually also replicated onto multiple machines. The main copy 
is called the primary, all other copies are simply called replicas. The number of primary shards 
for an index is fixed at creation time, which allows to deterministically route requests for specific 
documents to the right shard, based on a hash of the document key (called the document "_id"). In the 
context of data replication, shards do their work independently from each other. The specification 
therefore only considers a single primary shard together with its copies, the replicas. It assumes a 
fixed set of nodes, each of which can host either the primary or one of the replicas. Shard allocation 
(i.e. which node has which shard) is dynamic and determined by the master, a process in the cluster 
that is backed by a consensus module. The TLA+ specification does not model the consensus module, it 
assumes that this component is working correctly. It shows however how data replication integrates with 
the consensus module to achieve its guarantees.

How data is replicated
----------------------

Clients send requests to an arbitrary node in the cluster. The node then routes the request to the
node in the cluster that has the primary shard for the corresponding document id. The document is
indexed at the primary and then replicated concurrently to the replicas. The replicas index the
document and confirm successful replication to the primary. The primary then acknowledges successful
replication to the client.

What's covered / not covered in this model
------------------------------------------

Failures covered by the model:

- node crashes

- disconnects between nodes on a per request basis

Also covered:

- cluster state batching / asynchronous application (each node applies the cluster state, which is
the state backed by the consensus model, at different points in time)

- network delays: messages can arrive out-of-order and be delayed

Limitations of the model:

- shard initialization / recovery is not modeled: the model initially assumes shards to be started.
When a shard fails, it is not reallocated / reassigned to another node but stays unassigned.
When a primary shard fails, a random replica is promoted to primary (if replica exists).

- only the transaction log is modeled. Lucene store as an optimistic consumer of the transaction log
is not modeled.

- adding nodes to the cluster is not modeled, whereas in Elasticsearch, nodes can dynamically 
be added to the cluster and those nodes will share in the hosting of shard data (shard data is 
moved to the new node through the process of recovery, mentioned above, which is also not modeled).

Other differences between model and current Java implementation:

- the Java implementation uses zero-based numbering for sequence numbers whereas the TLA+ model
starts from one, as this is the natural way to access the first element of a sequence in TLA+.

- ...


------------------------------ MODULE replication ---------------------------------

\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

\* `^\Large\bf Constants ^'

\* The specification first defines the constants of the model, which amount to values or sets of
\* values that are fixed.

\* Set of node ids uniquely representing each data node in the cluster
CONSTANTS Nodes

\* Set of possible document ids (i.e. values for "_id" field)
CONSTANTS DocumentIds

(* Communication between the nodes is done using an RPC-like mechanism.
   For each request there is an associated response. In-flight requests / responses are modeled
   using messages, which are represented in TLA+ as record types. To distinguish requests from
   responses, the message record type contains a field "request" that denotes whether the message is
   a request or a response (takes as value one of {TRUE, FALSE}). It also contains the node id of
   the sender and receiver of the call (in the fields "source" and "dest"). The procedure that is
   called is found under the field "method".

   For example, sending a replication request from node n1 to n2 would yield the following message:
      [request   |-> TRUE,
       method    |-> Replication,
       source    |-> n1,
       dest      |-> n2]

   Responses also have a field "success" which indicates whether the call was successful
   or not (one of {TRUE, FALSE}).

   The model currently supports two RPC methods, one to replicate data from the primary to the 
   replicas and another one to trim the translog (explained later). The reroute logic for rerouting
   requests to the primary is not modeled as it has no impact on consistency/durability guarantees.
*) 
CONSTANTS Replication, TrimTranslog

(* Shard allocation is determined by the master and broadcasted to the data nodes in the form of a
   routing table, which is a map from node id to one of {Primary, Replica, Unassigned}, denoting 
   whether the respective node has the primary shard, a replica shard or no shard assigned at all.
*)
CONSTANTS Primary, Replica, Unassigned

\* The constant "Nil" denotes a non-existing value (e.g. in transaction log) or a place-holder for
\* a value that is to be computed.
CONSTANTS Nil

----

\* `^\Large\bf Variables ^'

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between data nodes.
VARIABLE messages

(* Beside managing and broadcasting the routing table, the master also tracks if
   a primary failed and/or a replica was promoted to primary, incrementing a number called the 
   "primary term" whenever this happens. Each new primary operates under a new term, allowing nodes
   to reject replication requests that come from a primary that has been demoted by the master.
   The routing table and primary term together form the cluster state, which is simply a record type
   containing both:

      [routingTable |->
          [n1 |-> Primary,
           n2 |-> Replica,
           n3 |-> Unassigned],
       primaryTerm |-> 1]

   The following variable represents the current cluster state on the master, which is not
   explicitly modeled as a node.
*)
VARIABLE clusterStateOnMaster

\* For simplicity we assume that each client (index) request uses a new unique value to be indexed.
\* This is just a natural number incremented on each client operation.
VARIABLE nextClientValue

\* The set of (acknowledged) client responses. Stored in a variable so that we can make assertions
\* about successfully acknowledged requests (e.g. that they've been successfully stored).
VARIABLE clientResponses

\* To improve readibility of the specification, the following placeholder clientVars can be used
\* instead of explicitly writing the two variables on the right hand side.
clientVars == <<nextClientValue, clientResponses>>

(* After indexing a document into the primary, it is replicated concurrently to the replicas.
   Writes are only acknowledged to the client after all replicas have acknowledged their writes to
   the primary. To correlate acknowledgements from multiple replicas for the same write on the
   primary, we use a unique request id that is shared by the concurrent replication requests going
   out to the replicas for each specific indexing operation on the primary. The responses carry the
   same request id as the requests they were originating from.

   This is just a natural number denoting the next available request id. It is incremented whenever
   a request id is used.
*)
VARIABLE nextRequestId


\* The following variables capture state on a per-node basis (maps with domain nodes).

(* Cluster states are determined by the master and broadcasted to nodes. Due to the distributed
   nature of the system, they can arrive and be applied at different times on the nodes. ES only
   guarantees that an older state is not applied on a node after a new one has been applied on the
   same node. It supports batching, however, so cluster states can be skipped if a newer has
   already arrived on a node before the old one has been processed on that node.

   Cluster states applied on each node are represented as a map from node id to cluster state that
   is currently applied on this node 
*)
VARIABLE clusterStateOnNode

(* The cluster state contains the current term number. Nodes might learn about the highest primary
   term number not only through cluster state updates, but also through other node-to-node
   communication such as replication requests. They store the most recent information (highest term
   they've heard about). The variable "currentTerm" is a map from node id to primary term number,
   representing the highest primary term number that is known to the node.
*)
VARIABLE currentTerm

(* The transaction log is a history of operations. The primary shard determines the order in which
   operations occur by assigning consecutive sequence numbers to the operations that are indexed.
   The sequence number represents a slot in the transaction log that is occupied by the operation.
   When a write on a primary is replicated to replicas, the replication request contains the sequence
   number that was assigned to this operation on the primary. The replica then assigns the operation
   to the same slot in its transaction log. Due to the concurrent nature of replication, replicas
   might fill these slots out-of-order. If the primary crashes or some replication requests don't make
   it to the replica, the replica can end up in a state where its transaction log has holes in it
   (slots that are not filled while subsequent slots are filled).

   Example of a transaction log on the primary and a replica:
   `.
                ---------------------
                | 1 | 2 | 3 | 4 | 5 |
      primary   |-------------------|
                | x | x | x | x |   |
                ---------------------

                ---------------------
                | 1 | 2 | 3 | 4 | 5 |
      replica   |-------------------|  (request for slot 2 is still in-flight)
                | x |   | x | x |   |
                ---------------------
   .'

   The transaction log is modeled as a map from node id to map from sequence number to record type
   consisting of document id, value to be stored, primary term and "pending confirmation" marker
   (more on that later).
*)
VARIABLE tlog

(* Having a transaction log in place, it is useful to know about the highest slot in the transaction
   log where all slots below it have been successfully replicated to all replicas, i.e. the common
   history shared by all in-sync shard copies. It is useful because in the case where a primary
   fails, a replica which is promoted to primary knows that it has to only worry about being out of sync
   with other replicas on slots that are beyond this slot. The primary is in charge of tracking
   this information, also called global checkpoint. For this, replica shards share information with the
   primary on the highest slot they have filled where all lower slots are filled as well, called the
   local checkpoint. The primary then establishes the global checkpoint as the minimum of the local
   checkpoint value received from all shard copies (including its own local checkpoint) and broadcasts 
   this information to the replicas.

   The global checkpoint is modeled as a map from node id to sequence number.
*)
VARIABLE globalCheckPoint

(* The local checkpoint is modeled as a map from node id (node that is doing the tracking)
   to node id (node for which the local checkpoint is being tracked) to sequence number.

   Only the primary maintains the local checkpoints from all replicas, but because of the possibility of 
   the primary changing over time, and in order to separate the state for each node more clearly, we maintain 
   a node id to local checkpoint map for each node in the cluster.
*)
VARIABLE localCheckPoint

\* The placeholder "nodeVars" is used as a shorthand for all node variables
nodeVars == <<clusterStateOnNode, tlog, localCheckPoint, globalCheckPoint, currentTerm>>


----

\* `^\Large\bf General helper functions ^'

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----

\* `^\Large\bf Helper functions on routing table ^'

(* Note, in this section, the terms "shard" and "node id" are conflated, because
   we are only considering one shard and all its copies, so each shard can be 
   uniquely identified by the node it resides on. The term "shard" or "node" is chosen 
   solely based on the context of what is being explained or specified.
*)

\* Returns shards that are marked as Primary in routing table
Primaries(routingTable) == {n \in DOMAIN routingTable : routingTable[n] = Primary}

\* Returns shards that are marked as Replica in routing table
Replicas(routingTable) == {n \in DOMAIN routingTable : routingTable[n] = Replica}

\* Returns shards that are marked as Primary or Replica in routing table
Assigned(routingTable) == {n \in DOMAIN routingTable : routingTable[n] /= Unassigned}

\* Determines whether the shard on node n was promoted to primary when a cluster state update occurs
ShardWasPromotedToPrimary(n, incomingRoutingTable, localRoutingTable) ==
  LET oldPrimaries == Primaries(localRoutingTable)
      newPrimaries == Primaries(incomingRoutingTable)
  IN  /\ n \notin oldPrimaries
      /\ n \in newPrimaries

\* Calculates new cluster state based on shard failure on node n
FailShardOnMaster(n) ==
  LET rt == clusterStateOnMaster.routingTable
  IN
    IF rt[n] = Unassigned THEN
      UNCHANGED <<clusterStateOnMaster>>
    ELSE
      \* increase primary term on primary failure
      LET newPt == IF rt[n] = Primary THEN
                     clusterStateOnMaster.primaryTerm + 1
                   ELSE
                     clusterStateOnMaster.primaryTerm
      IN
        IF rt[n] = Primary /\ Cardinality(Replicas(rt)) > 0 THEN
          \* promote replica to primary
          \E r \in Replicas(rt):
            clusterStateOnMaster' = [clusterStateOnMaster EXCEPT
              !.routingTable = [rt EXCEPT ![n] = Unassigned, ![r] = Primary],
              !.primaryTerm  = newPt]
        ELSE
          clusterStateOnMaster' = [clusterStateOnMaster EXCEPT
            !.routingTable[n] = Unassigned,
            !.primaryTerm  = newPt]

----

\* `^\Large\bf Helper functions for sending/receiving messages ^'

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* Generate default replication response based on replication request m
\* Copies most of the fields over for convenience (to restore caller information upon return)
DefaultReplicationResponse(m) == [request   |-> FALSE,
                                  method    |-> m.method,
                                  source    |-> m.dest,
                                  dest      |-> m.source,
                                  req       |-> m.req,
                                  id        |-> m.id,
                                  seq       |-> m.seq,
                                  rterm     |-> m.rterm,
                                  sterm     |-> m.sterm,
                                  value     |-> m.value,
                                  client    |-> m.client,
                                  localCP   |-> 0,
                                  success   |-> TRUE]

\* Generate default trim translog response based on trim translog request m
DefaultTrimTranslogResponse(m) == [request   |-> FALSE,
                                   method    |-> m.method,
                                   source    |-> m.dest,
                                   dest      |-> m.source,
                                   req       |-> m.req,
                                   maxseq    |-> m.maxseq, \* trim above this sequence number
                                   term      |-> m.term, \* trim entries with term lower than this
                                   success   |-> TRUE]

\* Generate default response based on request m
DefaultResponse(m) == IF m.method = Replication THEN
                        DefaultReplicationResponse(m)
                      ELSE
                        DefaultTrimTranslogResponse(m)

\* Generate default failure response based on request m
FailedResponse(m) == [DefaultResponse(m) EXCEPT !.success = FALSE]

----

\* `^\Large\bf Helper functions on translog ^'

(* When a request comes to a primary, it has to select a slot (the sequence number) to put the
   request into. It corresponds to the slot in the transaction log right after the highest slot
   that's filled.
   The following function yields the highest slot that's filled in the transaction log, or 0 if
   no such slot exists.
*)
MaxSeq(ntlog) == Max(DOMAIN ntlog \cup {0})

(* `^\bf\large MaxConfirmedSeq ^'
   The local checkpoint is defined as the highest slot in the translog, where all lower slots
   are filled. It is not only holes in the translog that prevent the local checkpoint from moving foward. 
   We actually want to prevent the local checkpoint from moving past slots which are filled but marked as 
   pending confirmation. Pending entries in the translog are entries that appear after the global checkpoint that are not
   allowed to contribute to the advancement of the local checkpoint until a resyncing phase happens due to 
   the primary shard changing nodes. Translog entries thus have a "pc" (pending confirmation) marker
   (\in {TRUE, FALSE}) that says whether the local checkpoint can move past them.
   This function yields highest sequence number which are not pending confirmation and where
   all lower slots are not pending confirmation either.
   Yields 0 if no such number exists.

   Examples: (T stands for TRUE, F for FALSE) 
   `.
                  ---------------------
                  | 1 | 2 | 3 | 4 | 5 |
                  |-------------------|     MaxConfirmedSeq = 1
                  | x | x | x | x |   |
      pc markers: | F | T | T | F |   |
                  ---------------------

                  ---------------------
                  | 1 | 2 | 3 | 4 | 5 |
                  |-------------------|     MaxConfirmedSeq = 2
                  | x | x |   | x |   |
      pc markers: | F | F |   | F |   |
                  ---------------------
   .'
*)
MaxConfirmedSeq(ntlog) ==
  LET ConfirmedTlogSlot(i) == i \in DOMAIN ntlog /\ ntlog[i].pc = FALSE
  IN  CHOOSE i \in (DOMAIN ntlog \cup {0}) : /\ ConfirmedTlogSlot(i+1) = FALSE
                                             /\ \A j \in 1..i : ConfirmedTlogSlot(j)

(* `^\bf\large MarkPC ^'
   Yields translog where all entries at position strictly larger than "globalCP" (representing the
   global checkpoint) are marked as "pending confirmation".

   Example: 
   `.
      ---------------------   MarkPC          ---------------------
      | 1 | 2 | 3 | 4 | 5 |   ----------->    | 1 | 2 | 3 | 4 | 5 |
      |-------------------|   globalCP = 1    |-------------------|
      | x | x |   | x |   |                   | x | x |   | x |   |
      | F | F |   | F |   |                   | F | T |   | T |   |
      ---------------------                   ---------------------
   .'
*)
MarkPC(ntlog, globalCP) ==
  [j \in DOMAIN ntlog |-> [ntlog[j] EXCEPT !.pc = IF j > globalCP THEN TRUE ELSE @]]

(* `^\bf\large FillAndUnmarkPC ^'
   Yields translog where all gaps are filled and the pending confirmation marker is set to FALSE
   for values at position strictly larger than "globalCP" representing the global checkpoint

   Example: 
   `.
      ---------------------   FillAndUnmarkPC ---------------------
      | 1 | 2 | 3 | 4 | 5 |   ----------->    | 1 | 2 | 3 | 4 | 5 |
      |-------------------|   globalCP = 1    |-------------------|
      | x | x |   | x |   |                   | x | x | x | x |   |
      | T | T |   | F |   |                   | T | F | F | F |   |
      ---------------------                   ---------------------
   .'
*)
FillAndUnmarkPC(ntlog, storedTerm, globalCP) ==
  [j \in 1..Max(DOMAIN ntlog \cup {0}) |->
    IF j > globalCP THEN
      IF j \in DOMAIN ntlog THEN
        [ntlog[j] EXCEPT !.pc = FALSE]
      ELSE
        [id    |-> Nil,
         term  |-> storedTerm,
         value |-> Nil,
         pc    |-> FALSE]
    ELSE
      ntlog[j]]

(* `^\bf\large TrimTlog ^'
   Trim elements from translog with position strictly greater than maxseq and
   term strictly lower than minterm.

   Example: 
   `.
          ---------------------   TrimTlog        ---------------------
          | 1 | 2 | 3 | 4 | 5 |   ----------->    | 1 | 2 | 3 | 4 | 5 |
          |-------------------|   maxseq = 2      |-------------------|
          | x | x | x | x | x |   minterm = 2     | x | x | x |   | x |
          | T | T | T | F | T |                   | T | T | T |   | F |
   terms: | 1 | 1 | 2 | 1 | 2 |                   | 1 | 1 | 2 |   | 2 |
          ---------------------                   ---------------------
   .'
*)
TrimTlog(ntlog, maxseq, minterm) ==
  [j \in {i \in DOMAIN ntlog : i <= maxseq \/ ntlog[i].term >= minterm} |-> ntlog[j]]

----

\* `^\Large\bf Initial states ^'

\* All possible routing tables where there is one primary
RoutingTablesWithPrimary ==
  UNION {
    {
      [n \in {pn} |-> Primary] @@ \* pn has the primary
      [n \in rs |-> Replica] @@ \* rs is the subset of nodes having replicas
      [n \in ((Nodes \ rs) \ {pn}) |-> Unassigned] \* remaining nodes have unassigned shards
        : rs \in SUBSET (Nodes \ {pn})
    } : pn \in Nodes
  }

\* Possible initial routing tables are those which have a primary or where all shards are unassigned
InitialRoutingTables == RoutingTablesWithPrimary \cup {[n \in Nodes |-> Unassigned]}

\* The following constant denotes the set of possible initial cluster states that are to be
\* considered for exploring the model, containing cluster states such as
\* [ routingTable |-> [n1 |-> Primary, n2 |-> Replica, n3 |-> Replica], primaryTerm |-> 1 ]
InitialClusterStates == { [routingTable |-> rt, primaryTerm |-> 1] : rt \in InitialRoutingTables }

Init == /\ clusterStateOnMaster \in InitialClusterStates
        /\ messages           = {}
        /\ nextClientValue    = 1
        /\ clientResponses    = {}
        /\ nextRequestId      = 1
        /\ tlog               = [n \in Nodes |-> << >>]
        /\ localCheckPoint    = [n1 \in Nodes |-> [n2 \in Nodes |-> 0]]
        /\ globalCheckPoint   = [n \in Nodes |-> 0]
        /\ clusterStateOnNode = [n \in Nodes |-> clusterStateOnMaster]
        /\ currentTerm        = [n \in Nodes |-> clusterStateOnMaster.primaryTerm]

----

\* `^\Large\bf Next-step relations ^'

\* Index request arrives on node n with document id docId
ClientRequest(n, docId) ==
  /\ clusterStateOnNode[n].routingTable[n] = Primary \* node believes itself to be the primary
  /\ LET
       replicas     == Replicas(clusterStateOnNode[n].routingTable)
       primaryTerm  == currentTerm[n]
       tlogEntry    == [id    |-> docId,
                        term  |-> primaryTerm,
                        value |-> nextClientValue,
                        pc    |-> FALSE]
       seq          == MaxSeq(tlog[n]) + 1
       \* create replication requests for each replica that the primary knows about
       replRequests == {([request  |-> TRUE,
                          method   |-> Replication,
                          source   |-> n,
                          dest     |-> rn,
                          req      |-> nextRequestId,
                          id       |-> docId,
                          value    |-> nextClientValue,
                          seq      |-> seq,
                          rterm    |-> primaryTerm, \* current term when issuing request
                          sterm    |-> primaryTerm, \* term to be stored (differs for fast resync)
                          client   |-> TRUE, \* it's a replication request initiated by client
                          globalCP |-> globalCheckPoint[n]]) : rn \in replicas}
     IN 
       \* put entry into translog
       /\ tlog' = [tlog EXCEPT ![n] = (seq :> tlogEntry) @@ @]
       \* Make sure that each client request uses a unique value
       /\ nextClientValue' = nextClientValue + 1
       \* set next unique key to use for replication requests so that we can relate responses
       /\ nextRequestId' = nextRequestId + 1
       \* update local checkpoint
       /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = seq]
       /\ Assert(localCheckPoint'[n][n] = localCheckPoint[n][n] + 1, "localCheckPoint incremented")
       \* send out replication requests
       /\ messages' = messages \cup replRequests
       /\ IF replicas = {} THEN
            \* no replicas, directly acknowledge to the client
            /\ clientResponses' = clientResponses \cup {[success |-> TRUE,
                                                         id      |-> docId,
                                                         value   |-> nextClientValue,
                                                         seq     |-> seq,
                                                         term    |-> primaryTerm]}
          ELSE
            \* replication requests sent out, wait for responses before acking to client
            /\ UNCHANGED <<clientResponses>>
  /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, globalCheckPoint, currentTerm>>

\* Helper function for marking translog entries as pending confirmation if incoming term is higher
\* than current term on node n.
MaybeMarkPC(incomingTerm, n, globalCP) ==
  IF incomingTerm > currentTerm[n] THEN
    \* there is a new primary, cannot safely advance local checkpoint
    \* before resync done, move it back to global checkpoint and add
    \* pending confirmation marker to all entries above global checkpoint
    MarkPC(tlog[n], globalCP)
  ELSE
    tlog[n]
    
(* 
`^\bf Note on handling replication requests with higher primary terms^'
If a replica receives a replication request with a primary term greater than its current primary term, 
it means that new primary was promoted. The `^na\"ive^' handling of this case would be to forget all translog
operations above global checkpoint, reset local checkpoint to global checkpoint and await replay 
of operations above global checkpoint from the newly promoted primary.
However, this approach does not work, because newly promoted primary might fail during resync process
and if our replica is promoted to primary - it may miss operations above global checkpoint, effectively 
losing acknowledged writes.

That's why we preserve existing entries in translog above global checkpoint but mark them as 
pending confirmation. During operations replay, replica replaces its translog entry with the entry received 
from the primary (which can be noop) and resets pending confirmation flag. 
*)
\* Replication request arrives on node n with message m
HandleReplicationRequest(n, m) ==
   /\ m.request = TRUE
   /\ m.method = Replication
   /\ IF m.rterm < currentTerm[n] THEN
        \* don't accept replication requests with lower term than we have
        \* lower term means that it's coming from a primary that has since been demoted
        /\ Reply(FailedResponse(m), m)
        /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, nodeVars>>
      ELSE
        /\ LET
             tlogEntry     == [id    |-> m.id,
                               term  |-> m.sterm,
                               value |-> m.value,
                               pc    |-> FALSE]
             newGlobalCP   == Max({m.globalCP, globalCheckPoint[n]})
             \* mark translog entries as pending if higher term and write request into translog
             newTlog       == (m.seq :> tlogEntry) @@ MaybeMarkPC(m.rterm, n, newGlobalCP)
             \* recompute local checkpoint
             localCP       == MaxConfirmedSeq(newTlog)
           IN 
             /\ tlog' = [tlog EXCEPT ![n] = newTlog]
             /\ currentTerm' = [currentTerm EXCEPT ![n] = m.rterm]
             /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = newGlobalCP]
             /\ Reply([DefaultResponse(m) EXCEPT !.localCP = localCP], m)
        /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode, nextClientValue, nextRequestId,
                       clientResponses, localCheckPoint>>

\* Trim translog request arrives on node n with message m
HandleTrimTranslogRequest(n, m) ==
  /\ m.request = TRUE
  /\ m.method = TrimTranslog
  /\ IF m.term < currentTerm[n] THEN
       \* don't handle requests with lower term than we have
       \* lower term means that it's coming from a primary that has since been demoted
       /\ Reply(FailedResponse(m), m)
       /\ UNCHANGED <<tlog, globalCheckPoint, currentTerm>>
     ELSE
       /\ LET
            newGlobalCP   == Max({m.globalCP, globalCheckPoint[n]})
            \* mark translog entries as pending if higher term and trim translog
            newTlog       == TrimTlog(MaybeMarkPC(m.term, n, newGlobalCP), m.maxseq, m.term)
          IN
            /\ tlog' = [tlog EXCEPT ![n] = newTlog]
            /\ globalCheckPoint' = [globalCheckPoint EXCEPT ![n] = newGlobalCP]
            /\ currentTerm' = [currentTerm EXCEPT ![n] = m.term]
            /\ Reply(DefaultResponse(m), m)
  /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, localCheckPoint,
                 clusterStateOnNode>>

\* Helper function for handling replication responses
FinishIfNeeded(m) ==
  \* check if this is the last response we're waiting for
  IF /\ m.client
     /\ { ms \in messages : ms.req = m.req } = {m}
     \* check if the request has not been failed already to the client
     /\ { cr \in clientResponses : cr.success = FALSE /\ cr.req = m.req } = {} THEN
    clientResponses' = clientResponses \cup {[success |-> TRUE,
                                              id      |-> m.id,
                                              value   |-> m.value,
                                              seq     |-> m.seq,
                                              term    |-> m.rterm]}
  ELSE
    UNCHANGED <<clientResponses>>

\* Helper function for handling replication responses
FinishAsFailed(m) ==
  /\ clientResponses' = clientResponses \cup {[success |-> FALSE,
                                               req     |-> m.req]}

\* Replication response arrives on node n from node rn with message m
HandleReplicationResponse(n, rn, m) ==
  /\ m.request = FALSE
  /\ m.method = Replication
  \* are we still interested in the response or already marked the overall client request as failed?
  /\ IF m.success THEN
       \* is it a newer local checkpoint than we have?
       /\ IF m.localCP > localCheckPoint[n][rn] /\
             \* is the shard still active on this node?
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
       /\ UNCHANGED <<clusterStateOnMaster, clusterStateOnNode>>
       /\ FinishIfNeeded(m)
     ELSE
       \* replication failed, ask master to fail shard
       /\ IF m.rterm < clusterStateOnMaster.primaryTerm THEN
            \* term outdated, fail itself and don't ack client write
            /\ FinishAsFailed(m)
            /\ UNCHANGED <<clusterStateOnMaster>>
          ELSE
            \* fail shard and respond to client
            /\ FailShardOnMaster(rn)
            /\ FinishIfNeeded(m)
       /\ UNCHANGED <<localCheckPoint, globalCheckPoint>>
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, nextRequestId, tlog, clusterStateOnNode,
                 currentTerm>>


\* Trim translog response arrives on node n from node rn with message m
HandleTrimTranslogResponse(n, rn, m) ==
   /\ m.request = FALSE
   /\ m.method = TrimTranslog
   /\ messages' = messages \ {m}
   /\ IF m.success = FALSE /\ m.term >= clusterStateOnMaster.primaryTerm THEN
        \* fail shard
        FailShardOnMaster(rn)
      ELSE
        UNCHANGED <<clusterStateOnMaster>>
   /\ UNCHANGED <<nextClientValue, nextRequestId, nodeVars, clientResponses>>

\* Cluster state propagated from master is applied to node n
ApplyClusterStateFromMaster(n) ==
  /\ clusterStateOnNode[n] /= clusterStateOnMaster
  /\ clusterStateOnNode' = [clusterStateOnNode EXCEPT ![n] = clusterStateOnMaster]
  /\ IF ShardWasPromotedToPrimary(n, clusterStateOnMaster.routingTable,
         clusterStateOnNode[n].routingTable) THEN
       \* shard promoted to primary, resync with replicas
       LET
         ntlog          == tlog[n]
         globalCP       == globalCheckPoint[n]
         newTerm        == clusterStateOnMaster.primaryTerm
         \* fill gaps in tlog and remove pending confirmation marker
         newTlog        == FillAndUnmarkPC(ntlog, newTerm, globalCP)
         replicas       == Replicas(clusterStateOnMaster.routingTable)
         numReplicas    == Cardinality(replicas)
         startSeq       == globalCP + 1
         endSeq         == Max((DOMAIN ntlog) \cup {0})
         numDocs        == endSeq + 1 - startSeq
         \* resend all translog entries above global checkpoint to replicas
         replRequests   == {([request  |-> TRUE,
                              method   |-> Replication,
                              source   |-> n,
                              dest     |-> rn,
                              req      |-> nextRequestId + (i - startSeq),
                              seq      |-> i,
                              rterm    |-> newTerm, \* new term when issuing request
                              sterm    |-> newTlog[i].term, \* stored term for entry
                              id       |-> newTlog[i].id,
                              value    |-> newTlog[i].value,
                              client   |-> FALSE, \* request not initiated by client
                              globalCP |-> globalCP]) : i \in startSeq..endSeq, rn \in replicas}
         \* send trim request to replicas
         trimRequests   == {[request  |-> TRUE,
                             method   |-> TrimTranslog,
                             source   |-> n,
                             dest     |-> rn,
                             req      |-> nextRequestId + numDocs,
                             maxseq   |-> endSeq,
                             term     |-> newTerm,
                             client   |-> FALSE,
                             globalCP |-> globalCP] : rn \in replicas}
       IN
         /\ currentTerm' = [currentTerm EXCEPT ![n] = newTerm]
         /\ tlog' = [tlog EXCEPT ![n] = newTlog]
         /\ localCheckPoint' = [localCheckPoint EXCEPT ![n][n] = MaxConfirmedSeq(newTlog)]
         /\ messages' = messages \cup replRequests \cup trimRequests
         /\ nextRequestId' = nextRequestId + numDocs + 1
    ELSE
      /\ UNCHANGED <<messages, nextRequestId, currentTerm, localCheckPoint, tlog>>
  /\ UNCHANGED <<clusterStateOnMaster, clientVars,
                 globalCheckPoint>>


\* Fail request message
FailRequestMessage(m) ==
  /\ m.request = TRUE
  /\ Reply(FailedResponse(m), m)
  /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, nodeVars>>

\* Fail response message
FailResponseMessage(m) ==
  /\ m.request = FALSE
  /\ m.success = TRUE
  /\ Reply([m EXCEPT !.success = FALSE], m)
  /\ UNCHANGED <<clusterStateOnMaster, nextRequestId, clientVars, nodeVars>>

\* Node fault detection on master finds node n to be isolated from the cluster or crashed
NodeFaultDetectionKicksNodeOut(n) ==
  /\ clusterStateOnMaster.routingTable[n] /= Unassigned \* not already unassigned
  /\ FailShardOnMaster(n) 
  /\ UNCHANGED <<messages, nextRequestId, clientVars, nodeVars>>

\* Defines how the variables may transition.
Next == \/ \E n \in Nodes : \E docId \in DocumentIds : ClientRequest(n, docId)
        \/ \E m \in messages : HandleReplicationRequest(m.dest, m)
        \/ \E m \in messages : HandleReplicationResponse(m.dest, m.source, m)
        \/ \E m \in messages : HandleTrimTranslogRequest(m.dest, m)
        \/ \E m \in messages : HandleTrimTranslogResponse(m.dest, m.source, m)
        \/ \E m \in messages : FailRequestMessage(m)
        \/ \E m \in messages : FailResponseMessage(m)
        \/ \E n \in Nodes : ApplyClusterStateFromMaster(n)
        \/ \E n \in Nodes : NodeFaultDetectionKicksNodeOut(n)

----

\* `^\Large\bf Helper functions for making assertions ^'

\* no active messages
NoActiveMessages == messages = {}

\* shard that is considered active by the master
ActiveShard(n) == clusterStateOnMaster.routingTable[n] /= Unassigned

\* cluster state on master has been applied to all nodes that are still supposed to have an active shard
ClusterStateAppliedOnAllNodesWithActiveShards ==
  \A n \in Nodes : ActiveShard(n) => clusterStateOnNode[n] = clusterStateOnMaster

\* everything in the translog up to and including slot i
UpToSlot(ntlog, i) == [j \in 1..i |-> ntlog[j]]

\* copy of translog, where we ignore the pending confirmation marker
ExceptPC(ntlog) == [j \in DOMAIN ntlog |-> [r \in DOMAIN ntlog[j] \ {"pc"} |-> ntlog[j][r] ]]

\* all shard copies contain same data
AllCopiesSameContents ==
  \A n1, n2 \in Nodes:
       /\ n1 /= n2
       /\ ActiveShard(n1)
       /\ ActiveShard(n2) 
    => ExceptPC(tlog[n1]) = ExceptPC(tlog[n2])

----

\* `^\Large\bf Main invariants ^'

\* checks if the translog for all nodes are equivalent up to their global checkpoint, only differing
\* in the safety marker (which can be false sometimes if the global checkpoint on one shard is lower
\* than on another one)
SameTranslogUpToGlobalCheckPoint ==
  \A n1, n2 \in Nodes:
       /\ n1 /= n2
       /\ ActiveShard(n1)
       /\ ActiveShard(n2)
    => ExceptPC(UpToSlot(tlog[n1], globalCheckPoint[n1])) = 
         ExceptPC(UpToSlot(tlog[n2], globalCheckPoint[n1]))

\* checks if the translog for all nodes is eventually the same
AllCopiesSameContentsOnQuietDown ==
      (/\ NoActiveMessages
       /\ ClusterStateAppliedOnAllNodesWithActiveShards)
    => AllCopiesSameContents

\* checks if all (acked) responses to client are successfully and correctly stored 
AllAckedResponsesStored ==
    \A r \in clientResponses : \A n \in Nodes :
      /\ r.success = TRUE
      /\ ActiveShard(n)
      => /\ r.seq \in DOMAIN tlog[n]
         /\ tlog[n][r.seq].id = r.id
         /\ tlog[n][r.seq].value = r.value
         /\ tlog[n][r.seq].term = r.term

\* checks that the global checkpoint is the same as or below the local checkpoint on each node
GlobalCheckPointBelowLocalCheckPoints ==
    \A n \in Nodes : globalCheckPoint[n] <= MaxConfirmedSeq(tlog[n])

\* local checkpoint always corresponds to MaxSeq and MaxConfirmedSeq on the primary node
LocalCheckPointMatchesMaxConfirmedSeq ==
  \A n \in Nodes : clusterStateOnNode[n].routingTable[n] = Primary
    => /\ localCheckPoint[n][n] = MaxConfirmedSeq(tlog[n])
       /\ MaxSeq(tlog[n]) = MaxConfirmedSeq(tlog[n])

\* routing table is well-formed (has at most one primary, and has no replicas if no primaries)
WellFormedRoutingTable(routingTable) ==
  /\ Cardinality(Primaries(routingTable)) <= 1
  /\ (   Cardinality(Primaries(routingTable)) = 0
      => Cardinality(Assigned (routingTable)) = 0)

StateConstraint ==
  /\ nextClientValue <= 3
  /\ Cardinality(messages) <= 5
  /\ 0 < Cardinality(Assigned (clusterStateOnMaster.routingTable))

=============================================================================
