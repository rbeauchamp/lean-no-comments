module

public import Lean.Data.Json
public import NoCommentsSpecification.CoreSpec
public import NoCommentsSpecification.ConfigSpec

@[expose] public section

namespace NoCommentsSpecification.RatchetSpec

open Lean
open NoComments
open NoCommentsSpecification

def ValidRatchetEntryJson (j : Json) (e : RatchetCore.RatchetEntry) : Prop :=
  ∃ obj fileRaw fpsJson,
    j = Json.obj obj ∧
    (∀ k _v, obj.get? k = some _v → k ∈ ["file", "comments", "lines", "fingerprints"]) ∧
    obj.get? "file" = some (Json.str fileRaw) ∧
    ConfigSpec.NormRelFile fileRaw e.file ∧
    obj.get? "comments" = some (.num ⟨e.comments, 0⟩) ∧
    e.comments > 0 ∧
    obj.get? "lines" = some (.num ⟨e.lines, 0⟩) ∧
    e.lines > 0 ∧
    obj.get? "fingerprints" = some (Json.arr fpsJson) ∧
    fpsJson.toList = e.fingerprints.values.toList.map Json.str ∧
    e.fingerprints.values.size = e.comments ∧
    (∀ fp ∈ e.fingerprints.values.toList, CoreSpec.IsFingerprint fp)

def ValidRatchetJson (text : String) (m : Std.HashMap String RatchetCore.RatchetEntry) : Prop :=
  ∃ arr, ∃ entries : List RatchetCore.RatchetEntry,
    Json.parse text = .ok (Json.arr arr) ∧
    entries.length = arr.size ∧
    (∀ (i : Nat) (_h : i < arr.size),
      ∃ (_he : i < entries.length), ValidRatchetEntryJson arr[i] entries[i]) ∧
    (entries.map (·.file)).Nodup ∧
    (∀ k, m[k]? = entries.find? (·.file == k))

inductive RatchetRefusal (text : String) : Prop where
  | badJson : (∀ j, Json.parse text ≠ .ok j) → RatchetRefusal text
  | notArray {j} : Json.parse text = .ok j → (∀ arr, j ≠ Json.arr arr) → RatchetRefusal text
  | invalidEntry {arr i} (hi : i < arr.size) :
      Json.parse text = .ok (Json.arr arr) →
      (∀ e, ¬ ValidRatchetEntryJson arr[i] e) →
      RatchetRefusal text
  | duplicateFile {arr i j e1 e2} (hi : i < arr.size) (hj : j < arr.size) :
      Json.parse text = .ok (Json.arr arr) →
      i ≠ j →
      ValidRatchetEntryJson arr[i] e1 →
      ValidRatchetEntryJson arr[j] e2 →
      e1.file = e2.file →
      RatchetRefusal text

def AnalyzeCommentsSpec (file : String) (comments : Array Core.Comment)
    (out : RatchetCore.FileAnalysis) : Prop :=
  out.file = file ∧
  out.comments = comments ∧
  CoreSpec.DistinctLines comments out.lines ∧
  CoreSpec.MultisetEq out.fingerprints.values.toList (comments.toList.map (·.fingerprint))

def ExactSyncOk (analysis : RatchetCore.FileAnalysis)
    (entry? : Option RatchetCore.RatchetEntry) : Prop :=
  match entry? with
  | none => analysis.comments.isEmpty = true ∧ analysis.lines = 0
  | some entry =>
    entry.comments = analysis.comments.size ∧
    entry.lines = analysis.lines ∧
    CoreSpec.MultisetEq analysis.fingerprints.values.toList entry.fingerprints.values.toList

def MonotonicOk (liveFps : Core.SortedFingerprints) (liveLines : Nat)
    (baseEntry? : Option RatchetCore.RatchetEntry) : Prop :=
  let expFps := match baseEntry? with | some e => e.fingerprints.values.toList | none => []
  let expLines := match baseEntry? with | some e => e.lines | none => 0
  (∀ a, liveFps.values.toList.count a ≤ expFps.count a) ∧ liveLines ≤ expLines

def ValidateOk (analyses : Array RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (targetFile? : Option String) : Prop :=
  (∀ f e, currentRatchet[f]? = some e → f ∉ excludedFiles.toList ∧ f ∈ checkedFiles.toList) ∧
  (match baseRatchet? with
    | some base => ∀ f e, base[f]? = some e → f ∉ excludedFiles.toList
    | none => True) ∧
  match targetFile? with
  | some target =>
    ∃ live, analyses.find? (·.file == target) = some live ∧
      ExactSyncOk live currentRatchet[target]? ∧
      match baseRatchet? with
      | some base => MonotonicOk live.fingerprints live.lines base[target]?
      | none => True
  | none =>
    ∀ a ∈ analyses.toList,
      ExactSyncOk a currentRatchet[a.file]? ∧
      match baseRatchet? with
      | some base => MonotonicOk a.fingerprints a.lines base[a.file]?
      | none => True

inductive ValidateRefusal (analyses : Array RatchetCore.FileAnalysis)
    (checkedFiles excludedFiles : Array String)
    (currentRatchet : Std.HashMap String RatchetCore.RatchetEntry)
    (baseRatchet? : Option (Std.HashMap String RatchetCore.RatchetEntry))
    (targetFile? : Option String) : Prop where
  | currentRatchetExcluded {f e} :
      currentRatchet[f]? = some e → f ∈ excludedFiles.toList →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | currentRatchetUnknown {f e} :
      currentRatchet[f]? = some e → f ∉ checkedFiles.toList →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | baseRatchetExcluded {base f e} :
      baseRatchet? = some base → base[f]? = some e → f ∈ excludedFiles.toList →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | missingTargetAnalysis {target} :
      targetFile? = some target →
      analyses.find? (·.file == target) = none →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | targetSyncFailed {target live} :
      targetFile? = some target →
      analyses.find? (·.file == target) = some live →
      ¬ ExactSyncOk live currentRatchet[target]? →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | targetMonotonicFailed {target live base} :
      targetFile? = some target →
      baseRatchet? = some base →
      analyses.find? (·.file == target) = some live →
      ¬ MonotonicOk live.fingerprints live.lines base[target]? →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | analysisSyncFailed {a} :
      targetFile? = none →
      a ∈ analyses.toList →
      ¬ ExactSyncOk a currentRatchet[a.file]? →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
  | analysisMonotonicFailed {a base} :
      targetFile? = none →
      baseRatchet? = some base →
      a ∈ analyses.toList →
      ¬ MonotonicOk a.fingerprints a.lines base[a.file]? →
      ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?

end NoCommentsSpecification.RatchetSpec
