# TLA+ Model of the Elasticsearch data replication approach

This repository mainly consists of two files:

- [TLA+ specification](elasticsearch.tla)
- [TLC model checking configuration](elasticsearch.toolbox/elasticsearch___model.launch)

How to edit/run:

- Install the [TLA Toolbox](http://research.microsoft.com/en-us/um/people/lamport/tla/toolbox.html)
- Read some [documentation](http://research.microsoft.com/en-us/um/people/lamport/tla/book.html)

How to run model checker in headless mode:

- Download [tla2tools.jar](http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html)
- Run model checker once in TLA+ Toolbox on desktop (can be aborted once started). This generates the folder `elasticsearch.toolbox/model/` that contains all model files that are required to run the model checker in headless mode.
- Copy the above folder and `tla2tools.jar` to the server running in headless mode.
- `cd` to the folder and run `java -Xmx30G -cp ../tla2tools.jar tlc2.TLC MC -workers 12`. The setting `-Xmx30G` denotes the amount of memory to allocate to the model checker and `-workers 12` the number of worker threads (should be equal to the number of cores on machine).
