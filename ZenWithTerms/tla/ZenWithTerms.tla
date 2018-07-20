-------------------------------------------------------------------------------------

-------------------------------- MODULE ZenWithTerms --------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

CONSTANTS Values

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* RPC message types
CONSTANTS
  Join,
  PublishRequest,
  PublishResponse,
  Commit

----

\* Set of requests and responses sent between nodes.
VARIABLE messages

\* Transitive closure of value updates as done by leaders 
VARIABLE descendant

\* Values to bootstrap the cluster
VARIABLE initialConfiguration
VARIABLE initialValue

\* node state (map from node id to state)
VARIABLE currentTerm
VARIABLE lastCommittedConfiguration
VARIABLE lastAcceptedTerm
VARIABLE lastAcceptedVersion
VARIABLE lastAcceptedValue
VARIABLE lastAcceptedConfiguration
VARIABLE joinVotes
VARIABLE startedJoinSinceLastReboot
VARIABLE electionWon
VARIABLE lastPublishedVersion
VARIABLE lastPublishedConfiguration
VARIABLE publishVotes

----

Terms == Nat

Versions == Nat

\* set of valid configurations (i.e. the set of all non-empty subsets of Nodes)
ValidConfigs == SUBSET(Nodes) \ {{}}

\* quorums correspond to majority of votes in a config
IsQuorum(votes, config) == Cardinality(votes \cap config) * 2 > Cardinality(config)

IsElectionQuorum(n, votes) ==
  /\ IsQuorum(votes, lastCommittedConfiguration[n])
  /\ IsQuorum(votes, lastAcceptedConfiguration[n])

IsPublishQuorum(n, votes) ==
  /\ IsQuorum(votes, lastCommittedConfiguration[n])
  /\ IsQuorum(votes, lastPublishedConfiguration[n])

\* initial model state
Init == /\ messages = {}
        /\ descendant = {}
        /\ initialConfiguration \in ValidConfigs
        /\ initialValue \in Values
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ lastCommittedConfiguration = [n \in Nodes |-> {}] \* empty config
        /\ lastAcceptedTerm = [n \in Nodes |-> 0]
        /\ lastAcceptedVersion = [n \in Nodes |-> 0]
        /\ lastAcceptedValue \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedConfiguration = [n \in Nodes |-> lastCommittedConfiguration[n]]
        /\ joinVotes = [n \in Nodes |-> {}]
        /\ startedJoinSinceLastReboot = [n \in Nodes |-> FALSE]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ lastPublishedVersion = [n \in Nodes |-> 0]
        /\ lastPublishedConfiguration = [n \in Nodes |-> lastCommittedConfiguration[n]]
        /\ publishVotes = [n \in Nodes |-> {}]

\* Bootstrap node n with the initial state and config 
SetInitialState(n) ==
  /\ lastAcceptedVersion[n] = 0 \* have not accepted any previous state
  /\ Assert(lastAcceptedTerm[n] = 0, "lastAcceptedTerm should be 0")
  /\ Assert(lastAcceptedConfiguration[n] = {}, "lastAcceptedConfiguration should be empty")
  /\ Assert(lastCommittedConfiguration[n] = {}, "lastCommittedConfiguration should be empty")
  /\ Assert(lastPublishedVersion[n] = 0, "lastPublishedVersion should be 0")
  /\ Assert(lastPublishedConfiguration[n] = {}, "lastPublishedConfiguration should be empty")
  /\ Assert(electionWon[n] = FALSE, "electionWon should be FALSE")
  /\ Assert(joinVotes[n] = {}, "joinVotes should be empty")
  /\ Assert(publishVotes[n] = {}, "publishVotes should be empty")
  /\ lastAcceptedVersion' = [lastAcceptedVersion EXCEPT ![n] = @ + 1]
  /\ lastAcceptedConfiguration' = [lastAcceptedConfiguration EXCEPT ![n] = initialConfiguration]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = initialValue]
  /\ lastCommittedConfiguration' = [lastCommittedConfiguration EXCEPT ![n] = initialConfiguration]
  /\ Assert(lastAcceptedTerm[n] = 0, "lastAcceptedTerm should be 0")
  /\ Assert(lastAcceptedVersion'[n] = 1, "lastAcceptedVersion should be 1")
  /\ Assert(lastAcceptedConfiguration'[n] /= {}, "lastAcceptedConfiguration should be non-empty")
  /\ Assert(lastCommittedConfiguration'[n] /= {}, "lastCommittedConfiguration should be non-empty")
  /\ UNCHANGED <<descendant, initialConfiguration, initialValue, messages, lastAcceptedTerm,
                 lastPublishedVersion, lastPublishedConfiguration, electionWon, joinVotes, publishVotes,
                 startedJoinSinceLastReboot, currentTerm>>

\* Send join request from node n to node nm for term t
HandleStartJoin(n, nm, t) ==
  /\ t > currentTerm[n]
  /\ LET
       joinRequest == [method     |-> Join,
                       source     |-> n,
                       dest       |-> nm,
                       term       |-> t,
                       laTerm     |-> lastAcceptedTerm[n],
                       laVersion  |-> lastAcceptedVersion[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ lastPublishedVersion' = [lastPublishedVersion EXCEPT ![n] = 0]
       /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
       /\ startedJoinSinceLastReboot' = [startedJoinSinceLastReboot EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<lastCommittedConfiguration, lastAcceptedConfiguration, lastAcceptedVersion,
                      lastAcceptedValue, lastAcceptedTerm, descendant, initialConfiguration, initialValue>>

\* node n handles a join request and checks if it has received enough joins (= votes)
\* for its term to be elected as master
HandleJoin(n, m) ==
  /\ m.method = Join
  /\ m.term = currentTerm[n]
  /\ startedJoinSinceLastReboot[n]
  /\ \/ m.laTerm < lastAcceptedTerm[n]
     \/ /\ m.laTerm = lastAcceptedTerm[n]
        /\ m.laVersion <= lastAcceptedVersion[n]
  /\ lastAcceptedVersion[n] > 0 \* initial state is set
  /\ joinVotes' = [joinVotes EXCEPT ![n] = @ \cup { m.source }]
  /\ electionWon' = [electionWon EXCEPT ![n] = IsElectionQuorum(n, joinVotes'[n])]
  /\ IF electionWon[n] = FALSE /\ electionWon'[n]
     THEN
       \* initiating publish version with last accepted version to enable client requests
       /\ lastPublishedVersion' = [lastPublishedVersion EXCEPT ![n] = lastAcceptedVersion[n]]
     ELSE
       UNCHANGED <<lastPublishedVersion>>
  /\ UNCHANGED <<lastCommittedConfiguration, currentTerm, publishVotes, messages, descendant,
                 lastAcceptedVersion, lastAcceptedValue, lastAcceptedConfiguration,
                 lastAcceptedTerm, startedJoinSinceLastReboot, lastPublishedConfiguration,
                 initialConfiguration, initialValue>>

\* client causes a cluster state change val with configuration cfg
HandleClientValue(n, t, v, val, cfg) ==
  /\ electionWon[n]
  /\ lastPublishedVersion[n] = lastAcceptedVersion[n] \* means we have the last published value / config (useful for CAS operations, where we need to read the previous value first)
  /\ t = currentTerm[n]
  /\ v > lastPublishedVersion[n]
  /\ cfg /= lastAcceptedConfiguration[n] => lastCommittedConfiguration[n] = lastAcceptedConfiguration[n] \* only allow reconfiguration if there is not already a reconfiguration in progress
  /\ IsQuorum(joinVotes[n], cfg) \* only allow reconfiguration if we have a quorum of (join) votes for the new config
  /\ LET
       publishRequests == { [method   |-> PublishRequest,
                             source   |-> n,
                             dest     |-> ns,
                             term     |-> t,
                             version  |-> v,
                             value    |-> val,
                             config   |-> cfg,
                             commConf |-> lastCommittedConfiguration[n]] : ns \in Nodes }
        newEntry == [prevT |-> lastAcceptedTerm[n],
                     prevV |-> lastAcceptedVersion[n],
                     nextT |-> t,
                     nextV |-> v]
        matchingElems == { e \in descendant : 
                                /\ e.nextT = newEntry.prevT
                                /\ e.nextV = newEntry.prevV }
        newTransitiveElems == { [prevT |-> e.prevT,
                     prevV |-> e.prevV,
                     nextT |-> newEntry.nextT,
                     nextV |-> newEntry.nextV] : e \in matchingElems }
     IN
       /\ descendant' = descendant \cup {newEntry} \cup newTransitiveElems
       /\ lastPublishedVersion' = [lastPublishedVersion EXCEPT ![n] = v]
       /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = cfg]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}] \* publishVotes are only counted per publish version
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<startedJoinSinceLastReboot, lastCommittedConfiguration, currentTerm, electionWon,
                      lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                      joinVotes, initialConfiguration, initialValue>>

\* handle publish request m on node n
HandlePublishRequest(n, m) ==
  /\ m.method = PublishRequest
  /\ m.term = currentTerm[n]
  /\ (m.term = lastAcceptedTerm[n]) => (m.version > lastAcceptedVersion[n])
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedVersion' = [lastAcceptedVersion EXCEPT ![n] = m.version]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ lastAcceptedConfiguration' = [lastAcceptedConfiguration EXCEPT ![n] = m.config]
  /\ lastCommittedConfiguration' = [lastCommittedConfiguration EXCEPT ![n] = m.commConf] 
  /\ LET
       response == [method   |-> PublishResponse,
                    source   |-> n,
                    dest     |-> m.source,
                    term     |-> m.term,
                    version  |-> m.version]
     IN
       /\ messages' = messages \cup {response}
       /\ UNCHANGED <<startedJoinSinceLastReboot, currentTerm, descendant, lastPublishedConfiguration,
                      electionWon, lastPublishedVersion, joinVotes, publishVotes, initialConfiguration,
                      initialValue>>

\* node n commits a change
HandlePublishResponse(n, m) ==
  /\ m.method = PublishResponse
  /\ electionWon[n]
  /\ m.term = currentTerm[n]
  /\ m.version = lastPublishedVersion[n]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = @ \cup {m.source}]
  /\ IF
       IsPublishQuorum(n, publishVotes'[n])
     THEN
       LET
         commitRequests == { [method   |-> Commit,
                              source   |-> n,
                              dest     |-> ns,
                              term     |-> currentTerm[n],
                              version  |-> lastPublishedVersion[n]] : ns \in Nodes }
       IN
         /\ messages' = messages \cup commitRequests
     ELSE
       UNCHANGED <<messages>>
  /\ UNCHANGED <<startedJoinSinceLastReboot, lastCommittedConfiguration, currentTerm, electionWon, descendant,
                   lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                   lastPublishedVersion, lastPublishedConfiguration, joinVotes, initialConfiguration,
                   initialValue>>

\* apply committed configuration to node n
HandleCommit(n, m) ==
  /\ m.method = Commit
  /\ m.term = currentTerm[n]
  /\ m.term = lastAcceptedTerm[n]
  /\ m.version = lastAcceptedVersion[n]
  /\ (electionWon[n] => lastAcceptedVersion[n] = lastPublishedVersion[n])
  /\ lastCommittedConfiguration' = [lastCommittedConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
  /\ UNCHANGED <<currentTerm, joinVotes, messages, lastAcceptedTerm, lastAcceptedValue, startedJoinSinceLastReboot, descendant,
                 electionWon, lastAcceptedConfiguration, lastAcceptedVersion, lastPublishedVersion, publishVotes,
                 lastPublishedConfiguration, initialConfiguration, initialValue>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ startedJoinSinceLastReboot' = [startedJoinSinceLastReboot EXCEPT ![n] = FALSE]
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ lastPublishedVersion' = [lastPublishedVersion EXCEPT ![n] = 0]
  /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<messages, lastAcceptedVersion, currentTerm, lastCommittedConfiguration, descendant,
                 lastAcceptedTerm, lastAcceptedValue, lastAcceptedConfiguration, initialConfiguration,
                 initialValue>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : SetInitialState(n)
  \/ \E n, nm \in Nodes : \E t \in Terms : HandleStartJoin(n, nm, t)
  \/ \E m \in messages : HandleJoin(m.dest, m)
  \/ \E n \in Nodes : \E t \in Terms : \E v \in Versions : \E val \in Values : \E vs \in ValidConfigs : HandleClientValue(n, t, v, val, vs)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : HandlePublishResponse(m.dest, m)
  \/ \E m \in messages : HandleCommit(m.dest, m)
  \/ \E n \in Nodes : RestartNode(n)

----

\* Invariants

SingleNodeInvariant ==
  \A n \in Nodes :
    /\ lastAcceptedTerm[n] <= currentTerm[n]
    /\ electionWon[n] = IsElectionQuorum(n, joinVotes[n]) \* cached value is consistent
    /\ IF electionWon[n] THEN lastPublishedVersion[n] >= lastAcceptedVersion[n] ELSE lastPublishedVersion[n] = 0
    /\ electionWon[n] => startedJoinSinceLastReboot[n]
    /\ publishVotes[n] /= {} => electionWon[n]

OneMasterPerTerm ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    => m1.source = m2.source

LogMatching ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    /\ m1.version = m2.version
    => m1.value = m2.value

CommittedPublishRequest(mp) ==
  /\ mp.method = PublishRequest
  /\ \E mc \in messages:
       /\ mc.method = Commit
       /\ mp.term = mc.term
       /\ mp.version = mc.version

DescendantRelationIsStrictlyOrdered ==
  /\ \A d \in descendant:
       /\ d.prevT <= d.nextT
       /\ d.prevV < d.nextV
  \* relation is transitive
  /\ \A d1, d2 \in descendant:
       d1.nextT = d2.prevT /\ d1.nextV = d2.prevV 
       => [prevT |-> d1.prevT, prevV |-> d1.prevV, nextT |-> d2.nextT, nextV |-> d2.nextV] \in descendant

NewerOpsBasedOnOlderCommittedOps ==
  \A m1, m2 \in messages :
      /\ CommittedPublishRequest(m1)
      /\ m2.method = PublishRequest
      /\ m2.term >= m1.term
      /\ m2.version > m1.version
      => [prevT |-> m1.term, prevV |-> m1.version, nextT |-> m2.term, nextV |-> m2.version] \in descendant

\* main invariant (follows from NewerOpsBasedOnOlderCommittedOps):
CommittedValuesDescendantsFromCommittedValues ==
  \A m1, m2 \in messages : 
      /\ CommittedPublishRequest(m1)
      /\ CommittedPublishRequest(m2)
      /\ \/ m1.term /= m2.term
         \/ m1.version /= m2.version
    =>
      \/ [prevT |-> m1.term, prevV |-> m1.version, nextT |-> m2.term, nextV |-> m2.version] \in descendant 
      \/ [prevT |-> m2.term, prevV |-> m2.version, nextT |-> m1.term, nextV |-> m1.version] \in descendant

CommittedValuesDescendantsFromInitialValue ==
  \A m \in messages : 
      CommittedPublishRequest(m)
    =>
      [prevT |-> 0, prevV |-> 1, nextT |-> m.term, nextV |-> m.version] \in descendant

CommitHasQuorumVsPreviousCommittedConfiguration ==
  \A mc \in messages: mc.method = Commit
    => (\A mprq \in messages: (/\ mprq.method  = PublishRequest
                               /\ mprq.term    = mc.term
                               /\ mprq.version = mc.version) 

          => IsQuorum({mprs.source: mprs \in {mprs \in messages: /\ mprs.method = PublishResponse
                                                                 /\ mprs.term = mprq.term
                                                                 /\ mprs.version = mprq.version
                      }}, mprq.commConf))

P2bInvariant ==
  \A mc \in messages: mc.method = Commit
    => (\A mprq \in messages: mprq.method = PublishRequest
            => (mprq.term > mc.term => mprq.version > mc.version))

\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: IF currentTerm[n] <= 1 THEN lastPublishedVersion[n] <= 2 ELSE lastPublishedVersion[n] <= 3
  /\ Cardinality(messages) <= 15

====================================================================================================
