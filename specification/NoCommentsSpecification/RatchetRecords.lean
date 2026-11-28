module

public import LeanIntent.Record
public import NoCommentsSpecification.RatchetSpec

@[expose] public section

namespace NoCommentsSpecification.RatchetRecords

open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.RatchetSpec

def analyzeCommentsRecord : IntentRecord AnalyzeCommentsFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"exact_file_comments_lines_fingerprints", fun f =>
        ∀ file comments, AnalyzeCommentsSpec file comments (f file comments)⟩ ]
  vocab :=
    [ ⟨"AnalyzeCommentsSpec",
        String × Array Core.Comment × RatchetCore.FileAnalysis,
        fun p => AnalyzeCommentsSpec p.1 p.2.1 p.2.2⟩ ]

def parseRatchetRecord : IntentRecord ParseRatchetFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_valid_ratchet_map", fun f => ∀ json m, f json = .ok m → ValidRatchetJson json m⟩
    , ⟨"refusal_sound", fun f => ∀ json msg, f json = .error msg → RatchetRefusal json⟩ ]
  vocab :=
    [ ⟨"ValidRatchetJson",
        Lean.Json × Std.HashMap String RatchetCore.RatchetEntry,
        fun p => ValidRatchetJson p.1 p.2⟩
    , ⟨"RatchetRefusal", Lean.Json, RatchetRefusal⟩ ]

def checkExactSyncRecord : IntentRecord CheckExactSyncFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"empty_errors_iff_exact_sync", fun f =>
        ∀ analysis entry?, (f analysis entry?).isEmpty = true ↔ ExactSyncOk analysis entry?⟩ ]
  vocab :=
    [ ⟨"ExactSyncOk",
        RatchetCore.FileAnalysis × Option RatchetCore.RatchetEntry,
        fun p => ExactSyncOk p.1 p.2⟩ ]

def checkMonotonicFileRecord : IntentRecord CheckMonotonicFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"empty_errors_iff_monotonic", fun f =>
        ∀ file liveFps liveComments liveLines baseEntry?,
          (f file liveFps liveComments liveLines baseEntry?).isEmpty = true ↔
            MonotonicOk liveFps liveLines baseEntry?⟩ ]
  vocab :=
    [ ⟨"MonotonicOk",
        Core.SortedFingerprints × Nat × Option RatchetCore.RatchetEntry,
        fun p => MonotonicOk p.1 p.2.1 p.2.2⟩ ]

def validateCheckRecord : IntentRecord ValidateCheckFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_only_when_valid", fun f =>
        ∀ analyses checked excluded cur base? target?,
          f analyses checked excluded cur base? target? = .ok () →
            ValidateOk analyses checked excluded cur base? target?⟩
    , ⟨"refusal_sound", fun f =>
        ∀ analyses checked excluded cur base? target? msg,
          f analyses checked excluded cur base? target? = .error msg →
            ValidateRefusal analyses checked excluded cur base? target?⟩ ]
  vocab :=
    [ ⟨"ValidateOk",
        Array RatchetCore.FileAnalysis × Array String × Array String ×
          Std.HashMap String RatchetCore.RatchetEntry ×
          Option (Std.HashMap String RatchetCore.RatchetEntry) × Option String,
        fun p => ValidateOk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2⟩
    , ⟨"ValidateRefusal",
        Array RatchetCore.FileAnalysis × Array String × Array String ×
          Std.HashMap String RatchetCore.RatchetEntry ×
          Option (Std.HashMap String RatchetCore.RatchetEntry) × Option String,
        fun p => ValidateRefusal p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2⟩ ]

end NoCommentsSpecification.RatchetRecords
