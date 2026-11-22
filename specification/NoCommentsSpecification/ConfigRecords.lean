module

public import LeanIntent.Record
public import NoCommentsSpecification.ConfigSpec

@[expose] public section

namespace NoCommentsSpecification.ConfigRecords

open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.ConfigSpec

def parseConfigRecord : IntentRecord ParseConfigFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_valid_repo_config", fun f => ∀ text cfg, f text = .ok cfg → ValidConfigJson text cfg⟩
    , ⟨"refusal_sound", fun f => ∀ text msg, f text = .error msg → ConfigRefusal text⟩ ]
  vocab :=
    [ ⟨"ValidConfigJson", String × Config.RepoConfig, fun p => ValidConfigJson p.1 p.2⟩
    , ⟨"ConfigRefusal", String, ConfigRefusal⟩ ]

def classifyFileRecord : IntentRecord ClassifyFileFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_unique_classification", fun f =>
        ∀ cfg relPath out, f cfg relPath = .ok out → ClassifyOutcome cfg relPath out⟩
    , ⟨"refusal_sound", fun f =>
        ∀ cfg relPath msg, f cfg relPath = .error msg → ClassifyRefusal cfg relPath⟩ ]
  vocab :=
    [ ⟨"ClassifyOutcome",
        Config.RepoConfig × String × Config.ClassifiedFile,
        fun p => ClassifyOutcome p.1 p.2.1 p.2.2⟩
    , ⟨"ClassifyRefusal", Config.RepoConfig × String, fun p => ClassifyRefusal p.1 p.2⟩ ]

def classifyTrackedRecord : IntentRecord ClassifyTrackedFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_all_classified_in_order", fun f =>
        ∀ cfg tracked out, f cfg tracked = .ok out → ClassifyTrackedOutcome cfg tracked out⟩
    , ⟨"refusal_sound", fun f =>
        ∀ cfg tracked msg, f cfg tracked = .error msg → ClassifyTrackedRefusal cfg tracked⟩ ]
  vocab :=
    [ ⟨"ClassifyTrackedOutcome",
        Config.RepoConfig × Array String × Array Config.ClassifiedFile,
        fun p => ClassifyTrackedOutcome p.1 p.2.1 p.2.2⟩
    , ⟨"ClassifyTrackedRefusal",
        Config.RepoConfig × Array String,
        fun p => ClassifyTrackedRefusal p.1 p.2⟩ ]

end NoCommentsSpecification.ConfigRecords
