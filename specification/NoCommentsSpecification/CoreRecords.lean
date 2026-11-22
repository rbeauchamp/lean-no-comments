module

public import LeanIntent.Record
public import NoCommentsSpecification.CoreSpec

@[expose] public section

namespace NoCommentsSpecification.CoreRecords

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.CoreSpec

def isFingerprintRecord : IntentRecord IsFingerprintFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"exact_16_lowercase_hex", fun f => ∀ s, (f s = true) ↔ IsFingerprint s⟩ ]
  vocab :=
    [ ⟨"IsFingerprint", String, IsFingerprint⟩ ]

def fingerprintRecord : IntentRecord FingerprintFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"outputs_valid_fingerprint", fun f => ∀ text, IsFingerprint (f text)⟩
    , ⟨"non_constant_digest", fun f => ∃ a b, f a ≠ f b⟩ ]
  vocab :=
    [ ⟨"IsFingerprint", String, IsFingerprint⟩ ]

def checkTokenRecord : IntentRecord CheckTokenFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ok_only_when_token_safe", fun f =>
        ∀ ctx tok raw next start, f ctx tok raw next start = .ok () → TokenSafe ctx tok raw next⟩
    , ⟨"refusal_only_when_unsafe", fun f =>
        ∀ ctx tok raw next start msg,
          f ctx tok raw next start = .error msg → TokenRefusal ctx tok raw next⟩ ]
  vocab :=
    [ ⟨"TokenSafe",
        Parser.ParserContextCore × Syntax × String × Char,
        fun p => TokenSafe p.1 p.2.1 p.2.2.1 p.2.2.2⟩
    , ⟨"TokenRefusal",
        Parser.ParserContextCore × Syntax × String × Char,
        fun p => TokenRefusal p.1 p.2.1 p.2.2.1 p.2.2.2⟩ ]

def collectRangesRecord : IntentRecord CollectRangesFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"preserves_prior_spans", fun f =>
        ∀ ranges acc acc', f ranges acc = .ok acc' →
          ∀ (sb eb : Nat) (c : Core.Comment), acc.spans[sb]? = some (eb, c) → acc'.spans[sb]? = some (eb, c)⟩
    , ⟨"contiguous_byte_coverage", fun f =>
        ∀ ranges start endPos acc acc',
          ContiguousFrom start endPos ranges →
          f ranges acc = .ok acc' →
          ∀ b, start.byteIdx ≤ b → b < endPos.byteIdx →
            ∃ r ∈ ranges,
              r.prevPos.byteIdx ≤ b ∧ b < r.nextPos.byteIdx ∧
                ByteAccounted r.ctx r.stx acc' r.prevPos.byteIdx r.nextPos.byteIdx b⟩
    , ⟨"range_byte_coverage", fun f =>
        ∀ ranges acc acc', f ranges acc = .ok acc' →
          ∀ r ∈ ranges, ∀ b, r.prevPos.byteIdx ≤ b → b < r.nextPos.byteIdx →
            ByteAccounted r.ctx r.stx acc' r.prevPos.byteIdx r.nextPos.byteIdx b⟩
    , ⟨"exact_scanner_spans", fun f =>
        ∀ ranges acc acc', f ranges acc = .ok acc' →
          RangesStep ranges (stateOfAcc acc) (stateOfAcc acc')⟩
    , ⟨"genuine_new_spans", fun f =>
        ∀ ranges acc acc', f ranges acc = .ok acc' →
          ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
            acc.spans[sb]? = some (eb, c) ∨
              ∃ r ∈ ranges,
                r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
                  GenuineCommentSpan r.ctx r.stx sb eb c⟩
    , ⟨"source_linked_fingerprints", fun f =>
        ∃ fp : FingerprintFn,
          (∀ text, IsFingerprint (fp text)) ∧
          (∃ a b, fp a ≠ fp b) ∧
          ∀ ranges acc acc', f ranges acc = .ok acc' →
            ∀ (sb eb : Nat) (c : Core.Comment), acc'.spans[sb]? = some (eb, c) →
              acc.spans[sb]? = some (eb, c) ∨
                ∃ r ∈ ranges,
                  r.prevPos.byteIdx ≤ sb ∧ eb ≤ r.nextPos.byteIdx ∧
                    c.fingerprint = fp (commentText r.ctx.fileMap sb eb)⟩
    , ⟨"refusal_sound", fun f =>
        ∀ ranges acc msg, f ranges acc = .error msg → CollectRefusal ranges acc⟩ ]
  vocab :=
    [ ⟨"ByteAccounted",
        Parser.ParserContextCore × Syntax × Core.CommentAcc × Nat × Nat × Nat,
        fun p => ByteAccounted p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2⟩
    , ⟨"GenuineCommentSpan",
        Parser.ParserContextCore × Syntax × Nat × Nat × Core.Comment,
        fun p => GenuineCommentSpan p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2⟩
    , ⟨"RangesStep",
        List Core.CommandRange × SpanState × SpanState,
        fun p => RangesStep p.1 p.2.1 p.2.2⟩
    , ⟨"CollectRefusal",
        List Core.CommandRange × Core.CommentAcc,
        fun p => CollectRefusal p.1 p.2⟩ ]

def sourceOrderRecord : IntentRecord SourceOrderFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"ascending_source_order", fun f => ∀ acc, SourceOrdered acc (f acc)⟩ ]
  vocab :=
    [ ⟨"SourceOrdered", Core.CommentAcc × Array Core.Comment, fun p => SourceOrdered p.1 p.2⟩ ]

def distinctCommentLinesRecord : IntentRecord DistinctLinesFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"exact_distinct_comment_line_count", fun f =>
        ∀ comments, DistinctLines comments (f comments)⟩ ]
  vocab :=
    [ ⟨"DistinctLines", Array Core.Comment × Nat, fun p => DistinctLines p.1 p.2⟩ ]

def firstOutOfOrderRecord : IntentRecord FirstOutOfOrderFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"first_descending_neighbor", fun f => ∀ l, FirstOutOfOrderSpec l (f l)⟩ ]
  vocab :=
    [ ⟨"FirstOutOfOrderSpec", List String × Option String, fun p => FirstOutOfOrderSpec p.1 p.2⟩ ]

def sortFingerprintsRecord : IntentRecord SortFingerprintsFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"preserves_fingerprint_multiset", fun f =>
        ∀ xs, MultisetEq (f xs).values.toList xs.toList⟩ ]
  vocab :=
    [ ⟨"MultisetEq", List String × List String, fun p => MultisetEq p.1 p.2⟩ ]

def missingFromRecord : IntentRecord MissingFromFn where
  shape := .function _ _
  dom := []
  props :=
    [ ⟨"exact_multiset_difference", fun f =>
        ∀ xs ys, MultisetDiff xs.values.toList ys.values.toList (f xs ys).toList⟩ ]
  vocab :=
    [ ⟨"MultisetDiff",
        List String × List String × List String,
        fun p => MultisetDiff p.1 p.2.1 p.2.2⟩ ]

end NoCommentsSpecification.CoreRecords
