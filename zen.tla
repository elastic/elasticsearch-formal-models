-------------------------------------------- MODULE zen --------------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

CONSTANTS
  RequestVote,
  AppendEntries,
  Apply \* in contrast to Raft, we don't piggyback on the AppendEntries request to advance the commit index

CONSTANTS
  Follower,
  Candidate,
  Master

----

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between nodes.
VARIABLE messages

\* For simplicity we assume that each cluster state update chooses a new unique value to be added
\* to the cluster state. This allows us to check that nodes have a consistent view on CS updates.
VARIABLE nextClientValue

\* The following variables capture state on a per-node basis (maps with domain nodes).

(*
  Possible discovery states:
  - follower
  - candidate
  - master
*)
VARIABLE discoState

(*
  cluster state: record containing
    subset of nodes that are part of cluster, and a master node field which is either a node id or Nil
    also a field for some data that is currently stored, maybe a sequence of client events (which are just a number increased on every client request)
    and cluster state version field (and make sure version is incremented...)
    as well as the term with which this CS was published
*)
VARIABLE publishedState \* used by disco module, persisted whenever updated
VARIABLE term \* used by disco module, persisted
VARIABLE votedFor \* used by disco module, persisted
VARIABLE appliedState \* state visible to the other modules on the node

----

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y 

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* minimum_master_nodes configured to quorum of nodes
MinMasterNodes == (Cardinality(Nodes) \div 2) + 1

InitialDiscoState == [n \in Nodes |-> Follower]

\* initial cluster state for node n
InitialClusterState(n) == [nodes   |-> {n},
                           master  |-> Nil,
                           version |-> 0,
                           term    |-> 0,
                           data    |-> << >>]

Init == /\ messages           = {}
        /\ nextClientValue    = 1
        /\ publishedState     = [n \in Nodes |-> InitialClusterState(n)]
        /\ appliedState       = publishedState
        /\ discoState         = InitialDiscoState
        /\ term               = [n \in Nodes |-> 0]
        /\ votedFor           = [n \in Nodes |-> Nil]

\* become candidate and send out votes (every new round of votes by the same node is done under a new term)
BecomeCandidate(n) ==
  /\ discoState[n] \in {Candidate, Follower}
  /\ discoState' = [discoState EXCEPT ![n] = Candidate]
  /\ term' = [term EXCEPT ![n] = @ + 1] \* increase term
  /\ votedFor' = [votedFor EXCEPT ![n] = n] \* vote for myself
  /\ LET requests == {([method  |-> RequestVote,
                        request |-> TRUE,
                        source  |-> n,
                        dest    |-> on,
                        term    |-> term'[n],
                        stTerm  |-> publishedState[n].term, \* term of last published state (lastLogTerm in Raft)
                        version |-> publishedState[n].version]) : on \in (Nodes \ {n})} \* lastLogIndex in Raft
     IN
       messages' = messages \cup requests
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>


HandleRequestVoteRequest(n, m) ==
  /\ m.method = RequestVote
  /\ m.request = TRUE
  /\ LET
       success == /\ m.term >= term[n]
                  \* (locally stored state not newer than the one that the requester has)
                  /\ \/ m.stTerm > publishedState[n].term
                     \/ /\ m.stTerm = publishedState[n].term
                        /\ m.version >= publishedState[n].version
                  /\ \/ m.term > term[n] \* this resets votedFor
                     \/ votedFor[n] \in {Nil, m.source} \* not voted already for another node
       response == [method  |-> RequestVote,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> success,
                    term    |-> term'[n]]
     IN
       \* check if incoming term is newer. If so, reset votedFor and switch to follower mode
       /\ IF m.term >= term[n]
          THEN
            /\ term' = [term EXCEPT ![n] = m.term]
            /\ discoState' = [discoState EXCEPT ![n] = IF m.term > term[n] THEN Follower ELSE @]
            /\ votedFor' = [votedFor EXCEPT ![n] = IF success THEN m.source ELSE @]
          ELSE
            UNCHANGED <<term, discoState, votedFor>>
       /\ Reply(response, m)
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>


BecomeMaster(n) ==
  /\ discoState[n] = Candidate
  /\ LET
       voteResponses == { m \in messages : m.method = RequestVote /\ m.request = FALSE /\ m.dest = n /\ m.term = term[n] }
       successfullResponses == { m \in voteResponses : m.success }
       voteGrantingNodes == { m.source : m \in successfullResponses }
       newState == [publishedState[n] EXCEPT !.master = n, !.nodes = @ \cup voteGrantingNodes, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextClientValue)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ Cardinality(voteGrantingNodes) + 1 >= MinMasterNodes \* +1 as we don't send a vote request to ourselves
       /\ discoState' = [discoState EXCEPT ![n] = Master]
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ nextClientValue' = nextClientValue + 1
       /\ messages' = (messages \ voteResponses) \cup publishRequests
       /\ UNCHANGED <<appliedState, term, votedFor>>


CommitState(n) ==
  LET
    publishResponses == { m \in messages :
                            /\ m.method = AppendEntries
                            /\ m.request = FALSE
                            /\ m.dest = n
                            /\ m.term = term[n] \* can only commit stuff from my term
                            /\ m.version = publishedState[n].version }
    successResponses == { pr \in publishResponses : pr.success }
    applyRequests == { [method  |-> Apply,
                        request |-> TRUE,
                        source  |-> n,
                        dest    |-> ns,
                        state   |-> publishedState[n]] : ns \in (publishedState[n].nodes \ {n}) }
  IN
    /\ Cardinality(successResponses) + 1 >= MinMasterNodes \* +1 as we don't publish to ourselves
    /\ messages' = (messages \ publishResponses) \cup applyRequests
    /\ appliedState' = [appliedState EXCEPT ![n] = publishedState[n]]
    /\ UNCHANGED <<nextClientValue, discoState, publishedState, term, votedFor>>


ClientRequest(n) ==
  /\ discoState[n] = Master
  /\ publishedState[n] = appliedState[n] \* previous round was committed
  /\ LET
       newState == [publishedState[n] EXCEPT !.data = Append(@, nextClientValue), !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> AppendEntries,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ nextClientValue' = nextClientValue + 1
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<appliedState, discoState, term, votedFor>>


HandleAppendEntriesRequest(n, m) ==
  /\ m.method = AppendEntries
  /\ m.request = TRUE
  /\ IF m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoState' = [discoState EXCEPT ![n] = Follower]
       /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
     ELSE
       IF m.term = term[n] /\ discoState[n] = Candidate
       THEN
         /\ discoState' = [discoState EXCEPT ![n] = Follower]
         /\ UNCHANGED <<term, votedFor>>
       ELSE
         UNCHANGED <<term, discoState, votedFor>>
  /\ LET
       success == \/ m.term > publishedState[n].term
                  \/ /\ m.term = publishedState[n].term
                     /\ m.state.version > publishedState[n].version 
       response == [method  |-> AppendEntries,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> success,
                    term    |-> term'[n],
                    version |-> m.state.version]
     IN
       \* fail request
       \/ /\ \/ m.term < term'[n]
             \/ /\ m.term = term'[n]
                /\ discoState'[n] = Follower
                /\ \lnot success
          /\ Reply([response EXCEPT !.success = FALSE], m)
          /\ UNCHANGED <<appliedState, publishedState, nextClientValue>>
       \* successful request
       \/ /\ m.term = term'[n]
          /\ discoState'[n] = Follower
          /\ success
          /\ publishedState' = [publishedState EXCEPT ![n] = m.state]
          /\ Reply(response, m)
          /\ UNCHANGED <<appliedState, nextClientValue>>


\* apply committed CS to node
HandleApplyRequest(n, m) ==
  /\ m.method = Apply
  /\ m.request = TRUE
  /\ appliedState' = [appliedState EXCEPT ![n] = IF m.state.version > @.version THEN m.state ELSE @]
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<publishedState, nextClientValue, votedFor, discoState, term>>


\* drop request
DropRequest(m) ==
  /\ m.request = TRUE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term, votedFor>>

\* drop response
DropResponse(m) ==
  /\ m.request = FALSE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term, votedFor>>

\* handle response with higher term than we currently have
HandleResponseWithHigherTerm(n, m) ==
  /\ m.request = FALSE
  /\ m.term > term[n]
  /\ messages' = messages \ {m}
  /\ term' = [term EXCEPT ![n] = m.term]
  /\ discoState' = [discoState EXCEPT ![n] = Follower]
  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* crash/restart node n
RestartNode(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Follower]
  /\ publishedState' = [publishedState EXCEPT ![n] = [@ EXCEPT !.master = Nil, !.nodes = {n}]]
  /\ appliedState' = [appliedState EXCEPT ![n] = InitialClusterState(n)]
  /\ UNCHANGED <<nextClientValue, messages, term, votedFor>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : BecomeCandidate(n)
  \/ \E n \in Nodes : BecomeMaster(n)
  \/ \E n \in Nodes : CommitState(n)
  \/ \E n \in Nodes : ClientRequest(n)
  \/ \E m \in messages : HandleRequestVoteRequest(m.dest, m)
  \/ \E m \in messages : HandleAppendEntriesRequest(m.dest, m)
  \/ \E m \in messages : HandleApplyRequest(m.dest, m)
  \/ \E m \in messages : HandleResponseWithHigherTerm(m.dest, m)
  \/ \E m \in messages : DropRequest(m)
  \/ \E m \in messages : DropResponse(m)
  \/ \E n \in Nodes : RestartNode(n)

----


\* returns true if seq1 is a prefix of seq2
PrefixOf(seq1, seq2) ==
  LET
    len1 == Len(seq1)
    len2 == Len(seq2)
  IN
    len1 <= len2 /\ seq1 = SubSeq(seq2, 1, len1)

\* main invariant:
\* if node n1 has an applied cluster state with version v1 and node n2 has an applied cluster state with version v2:
\*   if v1 <= v2: state1.data must be a prefix of state2.data
\* in particular, when both have the same version, the content must be the same
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    LET
      state1 == appliedState[n1]
      state2 == appliedState[n2]
    IN
      state1.version <= state2.version => PrefixOf(state1.data, state2.data)

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    n1 /= n2 /\ discoState[n1] = Master /\ discoState[n2] = Master => term[n1] /= term[n2]

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ publishedState[n1].version = publishedState[n2].version
    /\ publishedState[n1].term = publishedState[n2].term
    => publishedState[n1].data = publishedState[n2].data

====================================================================================================
