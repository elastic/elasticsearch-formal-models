# TLA+ Model of the Elasticsearch data replication approach

The repository formalizes research done as to how data replication will work in future versions of [Elasticsearch](https://github.com/elastic/elasticsearch) and is directly related to [ongoing implementation efforts](https://github.com/elastic/elasticsearch/issues/10708). We consider this work-in-progress: Model as well as implementation are still evolving and might differ in substantial ways. The formal model mainly serves to illustrate some of the high-level concepts and helps to validate resiliency-related aspects of the approach.

The model consists of two files:

- [TLA+ specification](elasticsearch.tla)
- [TLC model checking configuration](elasticsearch.toolbox/elasticsearch___model.launch)

How to edit/run:

- Install the [TLA Toolbox](http://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)
- Read some [documentation](http://research.microsoft.com/en-us/um/people/lamport/tla/book.html)

How to run the model checker in headless mode:

- Download [tla2tools.jar](http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html)
- Run the model checker once in TLA+ Toolbox on desktop (can be aborted once started). This generates the folder `elasticsearch.toolbox/model/` that contains all model files that are required to run the model checker in headless mode.
- Copy the above folder and `tla2tools.jar` to the server running in headless mode.
- `cd` to the folder and run `java -Xmx30G -cp ../tla2tools.jar tlc2.TLC MC -deadlock -workers 12`. The setting `-Xmx30G` denotes the amount of memory to allocate to the model checker and `-workers 12` the number of worker threads (should be equal to the number of cores on machine). The setting `-deadlock` ensures that TLC explores the full reachable state space, not searching for deadlocks.
