# Formal models of core Elasticsearch algorithms

This repository contains formal models of core [Elasticsearch](https://github.com/elastic/elasticsearch) algorithms and is directly related to ongoing implementation efforts around [data replication](https://github.com/elastic/elasticsearch/issues/10708) and cluster consensus. We consider this work-in-progress: Models as well as implementations are still evolving and might differ in substantial ways. The formal models mainly serve to illustrate some of the high-level concepts and help to validate resiliency-related aspects.

## Models

### Data replication

The data replication model consists of two files:

- [TLA+ specification](data/tla/replication.tla)
- [TLC model checking configuration](data/tla/replication.toolbox/replication___model.launch)

### Cluster consensus

The cluster consensus TLA+ model consists of two files:

- [TLA+ specification](cluster/tla/consensus.tla)
- [TLC model checking configuration](cluster/tla/consensus.toolbox/consensus___model.launch)

The cluster consensus Isabelle model consists of the following theories:

- [Basic definitions](cluster/isabelle/Preliminaries.thy)
- [An implementation in functional style](cluster/isabelle/Implementation.thy)
- [An implementation in monadic style, along with a proof it's equivalent to the previous](cluster/isabelle/Monadic.thy)
- [The proof that each slot is consistent, based on Lamport's Synod algorithm](cluster/isabelle/OneSlot.thy)
- [The proof that the implementation ensures consistency](cluster/isabelle/Zen.thy)

### Replica engine

A TLA+ model of how the
[engine](https://github.com/elastic/elasticsearch/blob/00fd73acc4a2991f96438f8c1948016c5b9eefb2/server/src/main/java/org/elasticsearch/index/engine/InternalEngine.java)
handles replication requests.

- [TLA+ specification](ReplicaEngine/tla/ReplicaEngine.tla)
- [TLC model checking configuration](ReplicaEngine/tla/ReplicaEngine.toolbox/ReplicaEngine___model.launch)

### Zen with terms

An alternative idea for improving the consistency of cluster state updates,
effectively by adding the notion of a _term_ to the existing Zen algorithm.

- [TLA+ specification](ZenWithTerms/tla/ZenWithTerms.tla)
- [TLC model checking configuration](ZenWithTerms/tla/ZenWithTerms.toolbox/ZenWithTerms___model.launch)

## How to edit/run TLA+:

- Install the [TLA Toolbox](http://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)
  - If on Mac OS, [move the downloaded app to the Applications folder first](https://groups.google.com/forum/#!topic/tlaplus/bL04c6BiYxo)
- Read some [documentation](http://research.microsoft.com/en-us/um/people/lamport/tla/book.html)

How to run the model checker in headless mode:

- Download [tla2tools.jar](http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html)
- Run the model checker once in TLA+ Toolbox on desktop (can be aborted once started). This generates the folder `elasticsearch.toolbox/model/` that contains all model files that are required to run the model checker in headless mode.
- Copy the above folder and `tla2tools.jar` to the server running in headless mode.
- `cd` to the folder and run `java -Xmx30G -cp ../tla2tools.jar tlc2.TLC MC -deadlock -workers 12`. The setting `-Xmx30G` denotes the amount of memory to allocate to the model checker and `-workers 12` the number of worker threads (should be equal to the number of cores on machine). The setting `-deadlock` ensures that TLC explores the full reachable state space, not searching for deadlocks.
