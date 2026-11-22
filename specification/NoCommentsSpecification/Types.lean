module

public import LeanIntent.Declared
public import LeanIntent.Degenerate
public import NoComments.Core
public import NoComments.Config
public import NoComments.RatchetCore

@[expose] public section

deriving instance LeanIntent.HasCode for NoComments.Core.Comment

namespace NoCommentsSpecification

open Lean
open NoComments

abbrev IsFingerprintFn : Type := String → Bool

abbrev FingerprintFn : Type := String → String

abbrev CheckTokenFn : Type :=
  Parser.ParserContextCore → Syntax → String → Char → String.Pos.Raw → Except String Unit

abbrev CollectRangesFn : Type :=
  List Core.CommandRange → Core.CommentAcc → Except String Core.CommentAcc

abbrev SourceOrderFn : Type :=
  Core.CommentAcc → Array Core.Comment

abbrev DistinctLinesFn : Type :=
  Array Core.Comment → Nat

abbrev FirstOutOfOrderFn : Type :=
  List String → Option String

abbrev SortFingerprintsFn : Type :=
  Array String → Core.SortedFingerprints

abbrev MissingFromFn : Type :=
  Core.SortedFingerprints → Core.SortedFingerprints → Array String

abbrev ParseConfigFn : Type :=
  String → Except String Config.RepoConfig

abbrev ClassifyFileFn : Type :=
  Config.RepoConfig → String → Except String Config.ClassifiedFile

abbrev ClassifyTrackedFn : Type :=
  Config.RepoConfig → Array String → Except String (Array Config.ClassifiedFile)

abbrev AnalyzeCommentsFn : Type :=
  String → Array Core.Comment → RatchetCore.FileAnalysis

abbrev ParseRatchetFn : Type :=
  String → Except String (Std.HashMap String RatchetCore.RatchetEntry)

abbrev CheckExactSyncFn : Type :=
  RatchetCore.FileAnalysis → Option RatchetCore.RatchetEntry → Array String

abbrev CheckMonotonicFn : Type :=
  String → Core.SortedFingerprints → Nat → Nat → Option RatchetCore.RatchetEntry → Array String

abbrev ValidateCheckFn : Type :=
  Array RatchetCore.FileAnalysis →
    Array String →
    Array String →
    Std.HashMap String RatchetCore.RatchetEntry →
    Option (Std.HashMap String RatchetCore.RatchetEntry) →
    Option String →
    Except String Unit

end NoCommentsSpecification
