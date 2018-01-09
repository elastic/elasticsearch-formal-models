`^\Large\bf
TLA+ Model of an improved Zen consensus algorithm with reconfiguration capabilities ^'
-------------------------------------------------------------------------------------

-------------------------------- MODULE consensus -----------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

\* `^\Large\bf Constants ^'

\* The specification first defines the constants of the model, which amount to values or sets of
\* values that are fixed.

CONSTANTS Values

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

\* RPC message types
CONSTANTS
  Join, \* only request is modeled
  PublishRequest,
  PublishResponse,
  Commit, \* only request is modeled
  Catchup \* only response is modeled

\* Publish request types
CONSTANTS
  Reconfigure,
  ApplyCSDiff  

----

\* `^\Large\bf Variables ^'

\* The following describes the variable state of the model.

\* Set of requests and responses sent between nodes.
VARIABLE messages

\* node state (map from node id to state)
VARIABLE firstUncommittedSlot
VARIABLE currentTerm
VARIABLE currentConfiguration
VARIABLE currentClusterState
VARIABLE lastAcceptedTerm
VARIABLE lastAcceptedValue
VARIABLE joinVotes
VARIABLE electionWon
VARIABLE publishPermitted
VARIABLE publishVotes

----

\* set of valid configurations (i.e. the set of all non-empty subsets of Nodes)
ValidConfigs == SUBSET(Nodes) \ {{}}

\* quorums correspond to majority of votes in a config
IsQuorum(votes, config) == Cardinality(votes \cap config) * 2 > Cardinality(config)

\* checks whether two configurations only have intersecting quorums
IntersectingQuorums(config1, config2) ==
  /\ \lnot IsQuorum(config1 \ config2, config1)
  /\ \lnot IsQuorum(config2 \ config1, config2)

\* initial model state
Init == /\ messages = {}
        /\ firstUncommittedSlot = [n \in Nodes |-> 0]
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ currentConfiguration \in {[n \in Nodes |-> vc] : vc \in ValidConfigs} \* all agree on initial config
        /\ currentClusterState \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedTerm = [n \in Nodes |-> Nil]
        /\ lastAcceptedValue = [n \in Nodes |-> Nil]
        /\ joinVotes = [n \in Nodes |-> {}]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ publishPermitted = [n \in Nodes |-> FALSE]
        /\ publishVotes = [n \in Nodes |-> {}]

\* Send join request from node n to node nm for term t
HandleStartJoin(n, nm, t) ==
  /\ t > currentTerm[n]
  /\ LET
       joinRequest == [method  |-> Join,
                       source  |-> n,
                       dest    |-> nm,
                       slot    |-> firstUncommittedSlot[n],
                       term    |-> t,
                       laTerm  |-> lastAcceptedTerm[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<currentClusterState, currentConfiguration,
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>

\* node n handles a join request and checks if it has received enough joins (= votes)
\* for its term to be elected as master
HandleJoinRequest(n, m) ==
  /\ m.method = Join
  /\ m.term = currentTerm[n]
  /\ \/ /\ m.slot < firstUncommittedSlot[n]
     \/ /\ m.slot = firstUncommittedSlot[n]
        /\ (m.laTerm /= Nil => lastAcceptedTerm[n] /= Nil /\ m.laTerm <= lastAcceptedTerm[n])
  /\ joinVotes' = [joinVotes EXCEPT ![n] = @ \cup { m.source }]
  /\ electionWon' = [electionWon EXCEPT ![n] = IsQuorum(joinVotes'[n], currentConfiguration[n])]
  /\ IF electionWon'[n] /\ publishPermitted[n] /\ lastAcceptedTerm[n] /= Nil 
     THEN LET publishRequests == { [method  |-> PublishRequest,
                                    source  |-> n,
                                    dest    |-> ns,
                                    term    |-> currentTerm[n],
                                    slot    |-> firstUncommittedSlot[n],
                                    value   |-> lastAcceptedValue[n]] : ns \in Nodes }
     IN
       /\ messages' = messages \cup publishRequests
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
     ELSE
       /\ UNCHANGED <<messages, publishPermitted>>
  /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, publishVotes,
                 firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>

\* client causes a cluster state change v
ClientRequest(n, v) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ LET
       publishRequests == { [method  |-> PublishRequest,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> ApplyCSDiff, 
                                          val  |-> (currentClusterState[n] :> v)]
                            ] : ns \in Nodes }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon,
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, joinVotes, publishVotes>>

\* change the set of voters
ChangeVoters(n, vs) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ LET
       publishRequests == { [method  |-> PublishRequest,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> Reconfigure, val |-> vs]] : ns \in Nodes }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon,
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, joinVotes, publishVotes>>

\* handle publish request m on node n
HandlePublishRequest(n, m) ==
  /\ m.method = PublishRequest
  /\ m.slot = firstUncommittedSlot[n]
  /\ m.term = currentTerm[n]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ LET
       response == [method  |-> PublishResponse,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> TRUE,
                    term    |-> m.term,
                    slot    |-> m.slot]
     IN
       /\ messages' = messages \cup {response}
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm,
                      electionWon, firstUncommittedSlot, publishPermitted, joinVotes, publishVotes>>

\* node n commits a change
HandlePublishResponse(n, m) ==
  /\ m.method = PublishResponse
  /\ m.slot = firstUncommittedSlot[n]
  /\ m.term = currentTerm[n]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = @ \cup {m.source}]
  /\ IF IsQuorum(publishVotes'[n], currentConfiguration[n])
     THEN
       LET
         commitRequests == { [method  |-> Commit,
                              source  |-> n,
                              dest    |-> ns,
                              term    |-> currentTerm[n],
                              slot    |-> firstUncommittedSlot[n]] : ns \in Nodes }
       IN
         /\ messages' = messages \cup commitRequests
     ELSE
       UNCHANGED <<messages>>
  /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon,
                   firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm,
                   publishPermitted, joinVotes>>

\* apply committed change to node n
HandleCommitRequest(n, m) ==
  /\ m.method = Commit
  /\ m.slot = firstUncommittedSlot[n]
  /\ m.term = lastAcceptedTerm[n]
  /\ firstUncommittedSlot' = [firstUncommittedSlot EXCEPT ![n] = @ + 1]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = Nil]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = Nil]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ IF lastAcceptedValue[n].type = Reconfigure THEN
       /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = lastAcceptedValue[n].val]
       /\ electionWon' = [electionWon EXCEPT ![n] = IsQuorum(joinVotes[n], currentConfiguration'[n])]
       /\ UNCHANGED <<currentClusterState>>
     ELSE
       /\ Assert(lastAcceptedValue[n].type = ApplyCSDiff, "unexpected type")
       /\ Assert(DOMAIN(lastAcceptedValue[n].val) = {currentClusterState[n]}, "diff mismatch")
       /\ currentClusterState' = [currentClusterState EXCEPT ![n] = lastAcceptedValue[n].val[@]] \* apply diff
       /\ UNCHANGED <<currentConfiguration, electionWon>>
  /\ UNCHANGED <<currentTerm, joinVotes, messages>>

\* node n captures current state and sends a catch up message
SendCatchupResponse(n) ==
  /\ LET
       catchupMessage == [method  |-> Catchup,
                          slot    |-> firstUncommittedSlot[n],
                          config  |-> currentConfiguration[n],
                          state   |-> currentClusterState[n]]
     IN
       /\ messages' = messages \cup { catchupMessage }
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, 
                      lastAcceptedValue, electionWon, firstUncommittedSlot, publishPermitted,
                      joinVotes, lastAcceptedTerm, publishVotes>>

\* node n handles a catchup message
HandleCatchupResponse(n, m) ==
  /\ m.method = Catchup
  /\ m.slot > firstUncommittedSlot[n]
  /\ firstUncommittedSlot' = [firstUncommittedSlot EXCEPT ![n] = m.slot]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = Nil]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = Nil]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = m.config]
  /\ currentClusterState' = [currentClusterState EXCEPT ![n] = m.state]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<currentTerm, messages>>
  

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<messages, firstUncommittedSlot, currentTerm, currentConfiguration, 
                 currentClusterState, lastAcceptedTerm, lastAcceptedValue>>

\* next-step relation
Next ==
  \/ \E n, nm \in Nodes : HandleStartJoin(n, nm, currentTerm[n] + 1)
  \/ \E m \in messages : HandleJoinRequest(m.dest, m)
  \/ \E n \in Nodes : \E v \in Values : ClientRequest(n, v)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : HandlePublishResponse(m.dest, m)
  \/ \E m \in messages : HandleCommitRequest(m.dest, m)
  \/ \E n \in Nodes : RestartNode(n)
  \/ \E n \in Nodes : \E vs \in ValidConfigs : ChangeVoters(n, vs)
  \/ \E n \in Nodes : SendCatchupResponse(n)
  \/ \E n \in Nodes : \E m \in messages : HandleCatchupResponse(n, m)

----

\* main invariant:
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    firstUncommittedSlot[n1] = firstUncommittedSlot[n2] => 
      /\ currentClusterState[n1] = currentClusterState[n2]
      /\ currentConfiguration[n1] = currentConfiguration[n2]

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    /\ electionWon[n1]
    /\ electionWon[n2]
    /\ currentTerm[n1] = currentTerm[n2]
    /\ IntersectingQuorums(currentConfiguration[n1], currentConfiguration[n2])
    => n1 = n2

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ firstUncommittedSlot[n1] = firstUncommittedSlot[n2]
    /\ lastAcceptedTerm[n1] = lastAcceptedTerm[n2]
    => lastAcceptedValue[n1] = lastAcceptedValue[n2]

SingleNodeInvariant ==
  \A n \in Nodes :
    /\ (lastAcceptedTerm[n] = Nil) = (lastAcceptedValue[n] = Nil)
    /\ lastAcceptedTerm[n] /= Nil => (lastAcceptedTerm[n] <= currentTerm[n])
    /\ electionWon[n] = IsQuorum(joinVotes[n], currentConfiguration[n]) \* cached value is consistent
    /\ electionWon[n] /\ publishPermitted[n] => lastAcceptedValue[n] = Nil

LogMatchingMessages ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.slot = m2.slot
    /\ m1.term = m2.term
    => m1.value = m2.value

SafeCatchupMessages ==
  \A m1, m2 \in messages:
    /\ m1.method = Catchup
    /\ m2.method = Catchup
    /\ m1.slot = m2.slot
    => m1.config = m2.config /\ m1.state = m2.state

\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: currentTerm[n] <= 3
  /\ \A n \in Nodes: firstUncommittedSlot[n] <= 2
  /\ Cardinality(messages) <= 15

====================================================================================================
