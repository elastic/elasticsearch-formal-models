------------------------------ MODULE Storage ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    MaxNewMeta, \* maximum generation of newMeta to limit the state space
    MetaDataContent \* content that is written to the metadata file
    
VARIABLES
    metadata,      \* metaData[i] = MetaDataContent if metadata of generation i is present
    manifest,      \* manifest[j] is generation of metadata j-th manifest is referencing
    newMeta,       \* generation of newly created metadata file
    newManifest,   \* generation of newly created manifest file
    state,         \* current state, describes what to do next
    possibleStates \* set of generations of metadata that limits what can be read from disk

--------------------------------------------------------------------------
(*************************************************************************)
(* First we define some helper functions to work with files abstraction. *)
(* Files is a function from file generation to some content.             *)
(*************************************************************************)

(*************************************************************************)
(* CurrentGeneration returns the maximum file generation. If there are   *)
(* no files then -1 is returned.                                         *)                                              
(*************************************************************************)
CurrentGeneration(files) == 
    IF DOMAIN files = {} 
        THEN -1 
    ELSE 
        CHOOSE gen \in DOMAIN files : 
            \A otherGen \in DOMAIN files : gen \geq otherGen

(*************************************************************************)
(* DeleteFile removes file with generation delGen.                        *)
(*************************************************************************)
DeleteFile(files, delGen) == [gen \in DOMAIN files \ {delGen} |-> files[gen]]

(*************************************************************************)
(* DeleteFilesExcept removes all files except keepGen.                 *)
(*************************************************************************)
DeleteFilesExcept(files, keepGen) == (keepGen :> files[keepGen])

(*************************************************************************)
(* WriteFile creates new file with specified generation and content.     *)
(*************************************************************************)
WriteFile(files, gen, content) == (gen :> content) @@ files
  
--------------------------------------------------------------------------
(*************************************************************************)
(* Now we define functions to emulate write and cleanup of the metadata. *)
(*************************************************************************)
WriteMetaOk(gen) == 
    /\ metadata' = WriteFile(metadata, gen, MetaDataContent)
    /\ state' = "writeManifest"

WriteMetaFail(gen) == 
    /\ metadata' = metadata
    /\ state' = "writeMeta"
                
WriteMetaDirty(gen) == 
    /\ \/ metadata' = WriteFile(metadata, gen, MetaDataContent)
       \/ metadata' = metadata
    /\ state' = "deleteNewMeta"

DeleteNewMeta == 
    /\ \/ metadata' = DeleteFile(metadata, newMeta) 
       \/ metadata' = metadata
    /\ state' = "writeMeta"
    /\ UNCHANGED <<newMeta, newManifest, manifest, possibleStates>> 

DeleteOldMeta ==
    /\ \/ metadata' = DeleteFilesExcept(metadata, newMeta) 
       \/ metadata' = metadata
    /\ state' = "writeMeta"
    /\ UNCHANGED <<newMeta, newManifest, manifest, possibleStates>>

WriteMeta == 
    LET gen == CurrentGeneration(metadata) + 1 IN 
        /\ newMeta' = gen
        /\ \/ WriteMetaOk(gen) 
           \/ WriteMetaFail(gen) 
           \/ WriteMetaDirty(gen)
        /\ UNCHANGED <<newManifest, manifest, possibleStates>>

--------------------------------------------------------------------------
(*************************************************************************)
(* Now we define functions to emulate write and cleanup of the manifest  *)
(* file.                                                                 *)
(*************************************************************************)      
WriteManifestOk(gen) == 
    /\ manifest' = WriteFile(manifest, gen, newMeta)
    /\ state' = "deleteOldManifest"
    /\ possibleStates' = {newMeta}

WriteManifestFail(gen) == 
    /\ manifest' = manifest
    /\ state' = "deleteNewMeta"
    /\ possibleStates' = possibleStates
                
WriteManifestDirty(gen) == 
    /\ \/ manifest' = WriteFile(manifest, gen, newMeta)
       \/ manifest' = manifest
    /\ state' = "deleteNewManifest"
    /\ possibleStates' = possibleStates \union {newMeta}
          
WriteManifest == 
    LET gen == CurrentGeneration(manifest) + 1 IN
        /\ newManifest' = gen
        /\ \/ WriteManifestOk(gen)
           \/ WriteManifestFail(gen)
           \/ WriteManifestDirty(gen)
        /\ UNCHANGED <<newMeta, metadata>>

DeleteOldManifest ==
    /\ \/ manifest' = DeleteFilesExcept(manifest, newManifest)
       \/ manifest' = manifest
    /\ state' = "deleteOldMeta"
    /\ UNCHANGED <<newMeta, newManifest, metadata, possibleStates>>

--------------------------------------------------------------------------
(*************************************************************************)
(* Below are 3 versions of the same function, that is called when        *)
(* manifest write was dirty. The buggy one was initially implemented and *)
(* was caught by https://github.com/elastic/elasticsearch/issues/39077.  *)
(* Pick one and use in Next function.                                    *)
(* https://github.com/elastic/elasticsearch/pull/40519 implements        *)
(* DeleteNewManifestEasy.                                                *)
(*************************************************************************)    
DeleteNewManifestBuggy == 
    /\ \/ manifest' = DeleteFile(manifest, newManifest)
       \/ manifest' = manifest
    /\ state' = "deleteNewMeta"
    /\ UNCHANGED <<newMeta, newManifest, metadata, possibleStates>>

DeleteNewManifestEasy == 
    /\ \/ manifest' = DeleteFile(manifest, newManifest)
       \/ manifest' = manifest
    /\ state' = "writeMeta"
    /\ UNCHANGED <<newMeta, newManifest, possibleStates, metadata>>
    
DeleteNewManifestHard == 
    /\ \/ /\ manifest' = DeleteFile(manifest, newManifest)
          /\ state' = "deleteNewMeta"
       \/ /\ manifest' = manifest
          /\ state' = "writeMeta"
    /\ UNCHANGED <<newMeta, newManifest, metadata, possibleStates>>
--------------------------------------------------------------------------
(*************************************************************************)
(* We can define Init and Next functions now.                            *)
(*************************************************************************)   
Init == 
    /\ metadata = <<>>
    /\ manifest = <<>>
    /\ newMeta = -1 \* no latest metadata file
    /\ newManifest = -1 \* no latest manifest file
    /\ state = "writeMeta" \* we start with writing metadata file
    /\ possibleStates = {} \* no metadata can be read from disk
    
Next == 
    \/ (state = "writeMeta"         /\ WriteMeta)
    \/ (state = "writeManifest"     /\ WriteManifest)
    \/ (state = "deleteOldManifest" /\ DeleteOldManifest)
    \/ (state = "deleteOldMeta"     /\ DeleteOldMeta)
    \/ (state = "deleteNewManifest" /\ DeleteNewManifestEasy) \* try DeleteNewBuggy and DeleteNewHard
    \/ (state = "deleteNewMeta"     /\ DeleteNewMeta)
--------------------------------------------------------------------------
(*************************************************************************)
(* Our model has 2 invariants.                                           *)
(*************************************************************************)
MetadataFileReferencedByManifestExists ==
    CurrentGeneration(manifest) /= -1 
        => 
    manifest[CurrentGeneration(manifest)] \in DOMAIN metadata
    
MetadataReferencedByManifestIsValid ==
    CurrentGeneration(manifest) /= -1 
        =>
    \E meta \in possibleStates : meta = manifest[CurrentGeneration(manifest)]
============