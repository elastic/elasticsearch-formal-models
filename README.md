# Formal models of core Elasticsearch algorithms

This repository contains formal models of core [Elasticsearch](https://github.com/elastic/elasticsearch) algorithms and is directly related to implementation efforts around [data replication](https://github.com/elastic/elasticsearch/issues/10708) and [cluster coordination](https://github.com/elastic/elasticsearch/issues/32006). The models in this repository might represent past, current and future designs of Elasticsearch and can differ to their implementations in substantial ways. The formal models mainly serve to illustrate some of the high-level concepts and help to validate resiliency-related aspects.

## Models

### Cluster coordination model

The cluster coordination TLA+ model ensures the consistency of cluster state updates and represents the core [cluster coordination](https://github.com/elastic/elasticsearch/issues/32006) and metadata replication algorithm implemented in Elasticsearch 7.0. It consists of two files:

- [TLA+ specification](ZenWithTerms/tla/ZenWithTerms.tla) which has a [direct one-to-one implementation in Elasticsearch](https://github.com/elastic/elasticsearch/blob/master/server/src/main/java/org/elasticsearch/cluster/coordination/CoordinationState.java)
- [TLC model checking configuration](ZenWithTerms/tla/ZenWithTerms.toolbox/ZenWithTerms___model.launch)

### Data replication model

The data replication TLA+ model describes the Elasticsearch [sequence number](https://github.com/elastic/elasticsearch/issues/10708) based data replication approach, implemented since Elasticsearch 6.0, which consists of two files:

- [TLA+ specification](data/tla/replication.tla)
- [TLC model checking configuration](data/tla/replication.toolbox/replication___model.launch)

### Replica engine

A TLA+ model of how the
[engine](https://github.com/elastic/elasticsearch/blob/00fd73acc4a2991f96438f8c1948016c5b9eefb2/server/src/main/java/org/elasticsearch/index/engine/InternalEngine.java)
handles replication requests.

- [TLA+ specification](ReplicaEngine/tla/ReplicaEngine.tla)
- [TLC model checking configuration](ReplicaEngine/tla/ReplicaEngine.toolbox/ReplicaEngine___model.launch)

### Alternative cluster coordination model

The alternative cluster coordination TLA+ model consists of two files:

- [TLA+ specification](cluster/tla/consensus.tla)
- [TLC model checking configuration](cluster/tla/consensus.toolbox/consensus___model.launch)

The alternative cluster consensus Isabelle model consists of the following theories:

- [Basic definitions](cluster/isabelle/Preliminaries.thy)
- [An implementation in functional style](cluster/isabelle/Implementation.thy)
- [An implementation in monadic style, along with a proof it's equivalent to the previous](cluster/isabelle/Monadic.thy)
- [The proof that each slot is consistent, based on Lamport's Synod algorithm](cluster/isabelle/OneSlot.thy)
- [The proof that the implementation ensures consistency](cluster/isabelle/Zen.thy)

## How to edit/run TLA+:

- Install the [TLA Toolbox](http://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)
  - If on Mac OS, [move the downloaded app to the Applications folder first](https://groups.google.com/forum/#!topic/tlaplus/bL04c6BiYxo)
- Read some [documentation](http://research.microsoft.com/en-us/um/people/lamport/tla/book.html)

How to run the model checker in headless mode:

- Download [tla2tools.jar](http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html)
- Run the model checker once in TLA+ Toolbox on desktop (can be aborted once started). This generates the folder `elasticsearch.toolbox/model/` that contains all model files that are required to run the model checker in headless mode.
- Copy the above folder and `tla2tools.jar` to the server running in headless mode.
- `cd` to the folder and run `java -Xmx30G -cp ../tla2tools.jar tlc2.TLC MC -deadlock -workers 12`. The setting `-Xmx30G` denotes the amount of memory to allocate to the model checker and `-workers 12` the number of worker threads (should be equal to the number of cores on machine). The setting `-deadlock` ensures that TLC explores the full reachable state space, not searching for deadlocks.
