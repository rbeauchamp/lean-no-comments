module

import all Init.Data.String.Search
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.Range.Basic
import all Lean.Data.Json.Basic
import all NoComments.Config
public import LeanIntent.Refinement
public import NoCommentsSpecification.ConfigRecords

@[expose] public section

namespace NoCommentsSpecification.Refinement.Config

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.ConfigSpec
open NoCommentsSpecification.ConfigRecords

theorem hasControlOrSlashIssue_eq (s : String) :
    NoComments.Config.hasControlOrSlashIssue s = !ConfigSpec.cleanStr s := by
  unfold NoComments.Config.hasControlOrSlashIssue ConfigSpec.cleanStr
  have h :
      String.any s (fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x00' || c == '\\') =
        s.toList.any
          (fun c => c == '\n' || c == '\r' || c == '\t' || c == '\x00' || c == '\\') := by
    unfold String.any
    exact String.contains_bool_eq
  rw [h, Bool.not_not]

private theorem stripDotSlashChars_eq :
    ∀ cs : List Char,
      NoComments.Config.stripLeadingDotSlashChars cs = ConfigSpec.stripDotSlashChars cs
  | [] => rfl
  | [a] => by
    conv => lhs; unfold NoComments.Config.stripLeadingDotSlashChars
    conv => rhs; unfold ConfigSpec.stripDotSlashChars
    by_cases ha : a = '.'
    · subst ha; rfl
    · simp
  | a :: b :: rest => by
    by_cases h : a = '.' ∧ b = '/'
    · rcases h with ⟨rfl, rfl⟩
      exact stripDotSlashChars_eq rest
    · conv => lhs; unfold NoComments.Config.stripLeadingDotSlashChars
      conv => rhs; unfold ConfigSpec.stripDotSlashChars
      simp only [not_and] at h
      by_cases ha : a = '.'
      · subst ha; simp [h rfl]
      · simp [ha]

theorem stripLeadingDotSlash_eq (s : String) :
    NoComments.Config.stripLeadingDotSlash s = ConfigSpec.stripDotSlash s := by
  unfold NoComments.Config.stripLeadingDotSlash ConfigSpec.stripDotSlash
  rw [stripDotSlashChars_eq]

private theorem stripTrailingSlashRev_eq :
    ∀ cs : List Char,
      NoComments.Config.stripTrailingSlashRev cs = ConfigSpec.stripTrailingSlashRev cs
  | [] => by
    conv => lhs; unfold NoComments.Config.stripTrailingSlashRev
    conv => rhs; unfold ConfigSpec.stripTrailingSlashRev
  | [a] => by
    conv => lhs; unfold NoComments.Config.stripTrailingSlashRev
    conv => rhs; unfold ConfigSpec.stripTrailingSlashRev
    by_cases ha : a = '/'
    · subst ha; rfl
    · simp
  | a :: b :: rest => by
    conv => lhs; unfold NoComments.Config.stripTrailingSlashRev
    conv => rhs; unfold ConfigSpec.stripTrailingSlashRev
    by_cases ha : a = '/'
    · subst ha
      exact stripTrailingSlashRev_eq (b :: rest)
    · simp [ha]

theorem stripTrailingSlashes_eq (s : String) :
    NoComments.Config.stripTrailingSlashes s = ConfigSpec.stripTrailingSlashes s := by
  unfold NoComments.Config.stripTrailingSlashes ConfigSpec.stripTrailingSlashes
  rw [stripTrailingSlashRev_eq]

theorem startsWith_slash_iff (s : String) :
    s.startsWith "/" = true ↔ (s.toList.head? == some '/') = true := by
  rw [String.startsWith_eq_startsWith_toSlice, String.Slice.startsWith_string_iff,
    String.copy_toSlice]
  have hsl : "/".toList = ['/'] := rfl
  rw [hsl]
  cases s.toList with
  | nil => simp
  | cons c cs =>
    simp only [List.head?_cons, Option.some.injEq, beq_iff_eq]
    constructor
    · rintro ⟨t, ht⟩
      injection ht with hc
      exact hc.symm
    · intro hc
      subst hc
      exact ⟨cs, rfl⟩

theorem endsWith_slash_iff (s : String) :
    s.endsWith "/" = true ↔ (s.toList.getLast? == some '/') = true := by
  rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_iff, String.copy_toSlice]
  have hsl : "/".toList = ['/'] := rfl
  rw [hsl, beq_iff_eq, List.getLast?_eq_some_iff]
  constructor
  · rintro ⟨ys, hys⟩
    exact ⟨ys, hys.symm⟩
  · rintro ⟨ys, hys⟩
    exact ⟨ys, hys.symm⟩

theorem startsWith_string_iff (s pat : String) :
    s.startsWith pat = true ↔ pat.toList.isPrefixOf s.toList = true := by
  rw [String.startsWith_eq_startsWith_toSlice, String.Slice.startsWith_string_iff,
    String.copy_toSlice, List.isPrefixOf_iff_prefix]

theorem validateSegments_iff (ctx raw : String) (segs : List String) :
    NoComments.Config.validateSegments ctx raw segs = .ok () ↔
      (segs.all fun seg => seg != "" && seg != "." && seg != "..") = true := by
  induction segs with
  | nil =>
    unfold NoComments.Config.validateSegments
    rw [List.forIn_nil]
    constructor
    · intro _; rfl
    · intro _; rfl
  | cons seg rest ih =>
    have hstep :
        NoComments.Config.validateSegments ctx raw (seg :: rest) =
          (if (seg == "" || seg == "." || seg == "..") = true then
            .error s!"{ctx} '{raw}' contains invalid path segment '{seg}'"
          else
            NoComments.Config.validateSegments ctx raw rest) := by
      unfold NoComments.Config.validateSegments
      rw [List.forIn_cons]
      cases (seg == "" || seg == "." || seg == "..")
      · simp [bind, Except.bind, pure, Except.pure]
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [hstep, List.all_cons]
    by_cases hbad : (seg == "" || seg == "." || seg == "..") = true
    · have hbad2 : ((seg == "") = true ∨ (seg == ".") = true) ∨ (seg == "..") = true := by
        simpa [Bool.or_eq_true] using hbad
      have hnot : (seg != "" && seg != "." && seg != "..") = false := by
        rcases hbad2 with (h1 | h1) | h1
        · simp [bne, h1]
        · simp [bne, h1]
        · simp [bne, h1]
      simp [hbad, hnot]
    · have hf : (seg == "" || seg == "." || seg == "..") = false := Bool.eq_false_iff.mpr hbad
      have hf' := hf
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hf'
      have hgood : (seg != "" && seg != "." && seg != "..") = true := by
        simp [bne, hf'.1.1, hf'.1.2, hf'.2]
      simp only [hf, Bool.false_eq_true, ↓reduceIte, hgood, Bool.true_and]
      exact ih

theorem normalizeRelDir_iff (ctx raw out : String) :
    NoComments.Config.normalizeRelDir ctx raw = .ok out ↔ ConfigSpec.NormRelDir raw out := by
  unfold NoComments.Config.normalizeRelDir ConfigSpec.NormRelDir
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases hemp : (raw == "") = true
  · have hraw : raw = "" := beq_iff_eq.mp hemp
    simp [hraw]
  · have hf1 : (raw == "") = false := Bool.eq_false_iff.mpr hemp
    have hne : raw ≠ "" := fun h => hemp (beq_iff_eq.mpr h)
    by_cases hbad : (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/") = true
    · simp only [hf1, Bool.false_eq_true, ↓reduceIte, hbad]
      constructor
      · intro h; cases h
      · rintro ⟨_, hclean, hhead, _⟩
        rw [hasControlOrSlashIssue_eq, hclean, Bool.not_true, Bool.false_or, startsWith_slash_iff,
          hhead] at hbad
        cases hbad
    · have hf2 : (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/") = false :=
        Bool.eq_false_iff.mpr hbad
      have hnotor :
          NoComments.Config.hasControlOrSlashIssue raw = false ∧ raw.startsWith "/" = false :=
        Bool.or_eq_false_iff.mp hf2
      have hclean : ConfigSpec.cleanStr raw = true := by
        have h := hnotor.1
        rw [hasControlOrSlashIssue_eq] at h
        cases hc : ConfigSpec.cleanStr raw
        · rw [hc] at h; cases h
        · rfl
      have hhead : (raw.toList.head? == some '/') = false := by
        have h := hnotor.2
        exact Bool.eq_false_iff.mpr fun ht => by rw [(startsWith_slash_iff raw).mpr ht] at h; cases h
      simp only [hf1, Bool.false_eq_true, ↓reduceIte, hf2, stripLeadingDotSlash_eq,
        stripTrailingSlashes_eq]
      generalize ConfigSpec.stripTrailingSlashes (ConfigSpec.stripDotSlash raw) = cleaned
      by_cases hdot : (cleaned == "." || cleaned == "") = true
      · have hdot' : cleaned = "." ∨ cleaned = "" := by
          simpa [Bool.or_eq_true, beq_iff_eq] using hdot
        simp only [hdot, ↓reduceIte, Except.ok.injEq, hne, hclean, hhead, true_and, ne_eq, not_false_eq_true]
        constructor
        · intro h
          left
          exact h.symm
        · rintro (h2 | ⟨hc1, hc2, _⟩)
          · exact h2.symm
          · rcases hdot' with rfl | rfl <;> contradiction
      · have hf3 : (cleaned == "." || cleaned == "") = false := Bool.eq_false_iff.mpr hdot
        have hcne : cleaned ≠ "." ∧ cleaned ≠ "" := by
          simpa [Bool.or_eq_true, not_or, beq_iff_eq] using hdot
        simp only [hf3, Bool.false_eq_true, ↓reduceIte, hne, hclean, hhead, true_and, ne_eq,
          not_false_eq_true]
        cases hval : NoComments.Config.validateSegments ctx raw (cleaned.splitOn "/") with
        | error e =>
          have hv : ConfigSpec.validSegmentsBool cleaned = false := by
            cases hv' : ConfigSpec.validSegmentsBool cleaned
            · rfl
            · have hok := (validateSegments_iff ctx raw (cleaned.splitOn "/")).mpr hv'
              rw [hval] at hok
              cases hok
          constructor
          · intro h; cases h
          · rintro (⟨h1, _⟩ | ⟨_, _, h3, _⟩)
            · cases h1
            · rw [hv] at h3; cases h3
        | ok u =>
          cases u
          have hv : ConfigSpec.validSegmentsBool cleaned = true :=
            (validateSegments_iff ctx raw (cleaned.splitOn "/")).mp hval
          dsimp only
          simp only [Except.ok.injEq]
          constructor
          · intro h
            right
            exact ⟨hcne.1, hcne.2, hv, h.symm⟩
          · rintro (⟨h1, _⟩ | ⟨_, _, _, h4⟩)
            · cases h1
            · exact h4.symm

theorem normalizeRelFile_iff (ctx raw out : String) :
    NoComments.Config.normalizeRelFile ctx raw = .ok out ↔ ConfigSpec.NormRelFile raw out := by
  unfold NoComments.Config.normalizeRelFile ConfigSpec.NormRelFile
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases hemp : (raw == "") = true
  · have hraw : raw = "" := beq_iff_eq.mp hemp
    simp [hraw]
  · have hf1 : (raw == "") = false := Bool.eq_false_iff.mpr hemp
    have hne : raw ≠ "" := fun h => hemp (beq_iff_eq.mpr h)
    by_cases hbad :
        (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/" ||
          raw.endsWith "/") = true
    · simp only [hf1, Bool.false_eq_true, ↓reduceIte, hbad]
      constructor
      · intro h; cases h
      · rintro ⟨_, hclean, hhead, hlast, _⟩
        have hcs := hasControlOrSlashIssue_eq raw
        have hsw := (startsWith_slash_iff raw)
        have hew := (endsWith_slash_iff raw)
        rw [hcs, hclean, Bool.not_true] at hbad
        simp only [Bool.false_or] at hbad
        cases hsw_b : raw.startsWith "/"
        · rw [hsw_b, Bool.false_or] at hbad
          rw [hbad] at hew
          rw [hew.mp rfl] at hlast
          cases hlast
        · rw [hsw.mp hsw_b] at hhead
          cases hhead
    · have hf2 :
          (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/" ||
            raw.endsWith "/") = false :=
        Bool.eq_false_iff.mpr hbad
      have hnotor1 :
          (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/") = false ∧
            raw.endsWith "/" = false :=
        Bool.or_eq_false_iff.mp hf2
      have hnotor2 :
          NoComments.Config.hasControlOrSlashIssue raw = false ∧ raw.startsWith "/" = false :=
        Bool.or_eq_false_iff.mp hnotor1.1
      have hclean : ConfigSpec.cleanStr raw = true := by
        have h := hnotor2.1
        rw [hasControlOrSlashIssue_eq] at h
        cases hc : ConfigSpec.cleanStr raw
        · rw [hc] at h; cases h
        · rfl
      have hhead : (raw.toList.head? == some '/') = false := by
        have h := hnotor2.2
        exact Bool.eq_false_iff.mpr fun ht => by rw [(startsWith_slash_iff raw).mpr ht] at h; cases h
      have hlast : (raw.toList.getLast? == some '/') = false := by
        have h := hnotor1.2
        exact Bool.eq_false_iff.mpr fun ht => by rw [(endsWith_slash_iff raw).mpr ht] at h; cases h
      simp only [hf1, Bool.false_eq_true, ↓reduceIte, hf2, stripLeadingDotSlash_eq]
      generalize ConfigSpec.stripDotSlash raw = cleaned
      by_cases hcbad : (cleaned == "" || cleaned == ".") = true
      · have hcor : cleaned = "" ∨ cleaned = "." := by
          simpa [Bool.or_eq_true, beq_iff_eq] using hcbad
        simp only [hcbad, ↓reduceIte]
        constructor
        · intro h; cases h
        · rintro ⟨_, _, _, _, hcne1, hcne2, _⟩
          rcases hcor with rfl | rfl <;> contradiction
      · have hf3 : (cleaned == "" || cleaned == ".") = false := Bool.eq_false_iff.mpr hcbad
        have hcne : cleaned ≠ "" ∧ cleaned ≠ "." := by
          simpa [Bool.or_eq_true, not_or, beq_iff_eq] using hcbad
        simp only [hf3, Bool.false_eq_true, ↓reduceIte, hne, hclean, hhead, hlast, hcne.1,
          hcne.2, true_and, ne_eq, not_false_eq_true]
        cases hval : NoComments.Config.validateSegments ctx raw (cleaned.splitOn "/") with
        | error e =>
          have hv : ConfigSpec.validSegmentsBool cleaned = false := by
            cases hv' : ConfigSpec.validSegmentsBool cleaned
            · rfl
            · have hok := (validateSegments_iff ctx raw (cleaned.splitOn "/")).mpr hv'
              rw [hval] at hok
              cases hok
          constructor
          · intro h; cases h
          · rintro ⟨hv', _⟩
            rw [hv] at hv'
            cases hv'
        | ok u =>
          cases u
          have hv : ConfigSpec.validSegmentsBool cleaned = true :=
            (validateSegments_iff ctx raw (cleaned.splitOn "/")).mp hval
          dsimp only
          simp only [Except.ok.injEq]
          constructor
          · intro h; exact ⟨hv, h.symm⟩
          · rintro ⟨_, h4⟩; exact h4.symm

theorem dropEnd_one_eq_dropLast (s : String) (hs : (s.toList.getLast? == some '/') = true) :
    (s.dropEnd 1).toString = String.ofList s.toList.dropLast := by
  have hlast : ∃ ys, s.toList = ys ++ ['/'] := List.getLast?_eq_some_iff.mp (beq_iff_eq.mp hs)
  rcases hlast with ⟨ys, hys⟩
  apply String.ext
  have h1 : (s.dropEnd 1).toString = (s.dropEnd 1).copy := rfl
  rw [h1, String.toList_copy_dropEnd, String.toList_ofList, hys]
  simp

theorem normalizePrefix_iff (ctx raw out : String) :
    NoComments.Config.normalizePrefix ctx raw = .ok out ↔ ConfigSpec.NormPrefix raw out := by
  unfold NoComments.Config.normalizePrefix ConfigSpec.NormPrefix
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases hemp : (raw == "") = true
  · have hraw : raw = "" := beq_iff_eq.mp hemp
    simp [hraw]
  · have hf1 : (raw == "") = false := Bool.eq_false_iff.mpr hemp
    have hne : raw ≠ "" := fun h => hemp (beq_iff_eq.mpr h)
    by_cases hbad : (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/") = true
    · simp only [hf1, Bool.false_eq_true, ↓reduceIte, hbad]
      constructor
      · intro h; cases h
      · rintro ⟨_, hclean, hhead, _⟩
        rw [hasControlOrSlashIssue_eq, hclean, Bool.not_true, Bool.false_or, startsWith_slash_iff,
          hhead] at hbad
        cases hbad
    · have hf2 : (NoComments.Config.hasControlOrSlashIssue raw || raw.startsWith "/") = false :=
        Bool.eq_false_iff.mpr hbad
      have hnotor :
          NoComments.Config.hasControlOrSlashIssue raw = false ∧ raw.startsWith "/" = false :=
        Bool.or_eq_false_iff.mp hf2
      have hclean : ConfigSpec.cleanStr raw = true := by
        have h := hnotor.1
        rw [hasControlOrSlashIssue_eq] at h
        cases hc : ConfigSpec.cleanStr raw
        · rw [hc] at h; cases h
        · rfl
      have hhead : (raw.toList.head? == some '/') = false := by
        have h := hnotor.2
        exact Bool.eq_false_iff.mpr fun ht => by rw [(startsWith_slash_iff raw).mpr ht] at h; cases h
      simp only [hf1, Bool.false_eq_true, ↓reduceIte, hf2, stripLeadingDotSlash_eq]
      generalize ConfigSpec.stripDotSlash raw = cleaned
      by_cases hcbad : (cleaned == "" || cleaned == "." || cleaned == "./") = true
      · have hcor : (cleaned = "" ∨ cleaned = ".") ∨ cleaned = "./" := by
          simpa [Bool.or_eq_true, beq_iff_eq] using hcbad
        simp only [hcbad, ↓reduceIte]
        constructor
        · intro h; cases h
        · rintro ⟨_, _, _, hcne1, hcne2, hcne3, _⟩
          rcases hcor with (rfl | rfl) | rfl <;> contradiction
      · have hf3 : (cleaned == "" || cleaned == "." || cleaned == "./") = false :=
          Bool.eq_false_iff.mpr hcbad
        have hcne : cleaned ≠ "" ∧ cleaned ≠ "." ∧ cleaned ≠ "./" := by
          simpa [Bool.or_eq_true, not_or, beq_iff_eq, and_assoc] using hcbad
        simp only [hf3, Bool.false_eq_true, ↓reduceIte, endsWith_slash_iff, hne, hclean, hhead,
          hcne.1, hcne.2.1, hcne.2.2, true_and, ne_eq, not_false_eq_true]
        have hbody :
            (if (cleaned.toList.getLast? == some '/') = true then
              (cleaned.dropEnd 1).toString
            else cleaned) =
              (if (cleaned.toList.getLast? == some '/') = true then
                String.ofList cleaned.toList.dropLast
              else cleaned) := by
          split
          · exact dropEnd_one_eq_dropLast cleaned ‹_›
          · rfl
        rw [hbody]
        generalize
            (if (cleaned.toList.getLast? == some '/') = true then
              String.ofList cleaned.toList.dropLast
            else cleaned) = body
        by_cases hbe : (body == "") = true
        · have hb : body = "" := beq_iff_eq.mp hbe
          simp [hb]
        · have hf4 : (body == "") = false := Bool.eq_false_iff.mpr hbe
          have hbne : body ≠ "" := fun h => hbe (beq_iff_eq.mpr h)
          simp only [hf4, Bool.false_eq_true, ↓reduceIte, hbne, true_and, not_false_eq_true]
          cases hval : NoComments.Config.validateSegments ctx raw (body.splitOn "/") with
          | error e =>
            have hv : ConfigSpec.validSegmentsBool body = false := by
              cases hv' : ConfigSpec.validSegmentsBool body
              · rfl
              · have hok := (validateSegments_iff ctx raw (body.splitOn "/")).mpr hv'
                rw [hval] at hok
                cases hok
            constructor
            · intro h; cases h
            · rintro ⟨hv', _⟩
              rw [hv] at hv'
              cases hv'
          | ok u =>
            cases u
            have hv : ConfigSpec.validSegmentsBool body = true :=
              (validateSegments_iff ctx raw (body.splitOn "/")).mp hval
            dsimp only
            simp only [Except.ok.injEq]
            constructor
            · intro h; exact ⟨hv, h.symm⟩
            · rintro ⟨_, h4⟩; exact h4.symm

theorem prefixMatches_eq (path pfx : String) :
    NoComments.Config.prefixMatches path pfx = ConfigSpec.PrefixMatches path pfx := by
  unfold NoComments.Config.prefixMatches ConfigSpec.PrefixMatches
  have h1 : (pfx.endsWith "/" = true) ↔ ((pfx.toList.getLast? == some '/') = true) :=
    endsWith_slash_iff pfx
  cases he : pfx.endsWith "/" with
  | true =>
    have he' : (pfx.toList.getLast? == some '/') = true := h1.mp he
    simp only [↓reduceIte, he']
    rw [Bool.eq_iff_iff, startsWith_string_iff]
  | false =>
    have he' : (pfx.toList.getLast? == some '/') = false :=
      Bool.eq_false_iff.mpr fun h => by rw [h1.mpr h] at he; cases he
    simp only [Bool.false_eq_true, ↓reduceIte, he']
    rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq,
      startsWith_string_iff, String.toList_append]
    rfl

theorem checkAllowedKeysLoop_iff (ctx : String) (allowed : Array String)
    (l : List (String × Json)) :
    (do
      for x in l do
        unless allowed.contains x.1 do
          throw s!"unknown key '{x.1}' in {ctx}"
      pure () : Except String Unit) = Except.ok () ↔
      ∀ kv ∈ l, kv.1 ∈ allowed.toList := by
  induction l with
  | nil =>
    rw [List.forIn_nil]
    constructor
    · intro _ _ h; cases h
    · intro _; rfl
  | cons kv rest ih =>
    have hstep :
        (do
          for x in kv :: rest do
            unless allowed.contains x.1 do
              throw s!"unknown key '{x.1}' in {ctx}"
          pure () : Except String Unit) =
          (if (!allowed.contains kv.1) = true then
            Except.error s!"unknown key '{kv.1}' in {ctx}"
          else
            do
              for x in rest do
                unless allowed.contains x.1 do
                  throw s!"unknown key '{x.1}' in {ctx}"
              pure ()) := by
      rw [List.forIn_cons]
      cases allowed.contains kv.1
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · simp [bind, Except.bind, pure, Except.pure]
    rw [hstep]
    by_cases hmem : kv.1 ∈ allowed.toList
    · have hc : allowed.contains kv.1 = true :=
        Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hmem)
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · intro h y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hmem
        · exact h y hy
      · intro h y hy
        exact h y (List.mem_cons_of_mem kv hy)
    · have hc : allowed.contains kv.1 = false :=
        Bool.eq_false_iff.mpr fun h =>
          hmem (Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp h))
      simp only [hc, Bool.not_false, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro h; exact absurd (h kv (List.mem_cons_self ..)) hmem

private theorem checkAllowedKeys_iff (ctx : String) (obj : Std.TreeMap.Raw String Json compare)
    (allowed : Array String) :
    NoComments.Config.checkAllowedKeys ctx obj allowed = .ok () ↔
      ∀ kv ∈ obj.toList, kv.1 ∈ allowed.toList := by
  unfold NoComments.Config.checkAllowedKeys
  exact checkAllowedKeysLoop_iff ctx allowed obj.toList

private theorem getRequiredField_iff (ctx : String) (obj : Std.TreeMap.Raw String Json compare)
    (key : String) (v : Json) :
    NoComments.Config.getRequiredField ctx obj key = .ok v ↔ obj.get? key = some v := by
  unfold NoComments.Config.getRequiredField
  cases obj.get? key <;> simp

theorem getObj_iff (j : Json) (obj : Std.TreeMap.Raw String Json compare) :
    j.getObj? = .ok obj ↔ j = .obj obj := by
  unfold Lean.Json.getObj?
  cases j <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem getArr_iff (j : Json) (arr : Array Json) :
    j.getArr? = .ok arr ↔ j = .arr arr := by
  unfold Lean.Json.getArr?
  cases j <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem getStr_iff (j : Json) (s : String) :
    j.getStr? = .ok s ↔ j = .str s := by
  unfold Lean.Json.getStr?
  cases j <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem getNat_iff (j : Json) (n : Nat) :
    j.getNat? = .ok n ↔ j = .num ⟨Int.ofNat n, 0⟩ := by
  unfold Lean.Json.getNat?
  cases j with
  | num m =>
    cases m with
    | mk mantissa exponent =>
      cases mantissa with
      | ofNat k =>
        cases exponent with
        | zero =>
          simp only [pure, Except.pure, Except.ok.injEq, Json.num.injEq, JsonNumber.mk.injEq,
            Int.ofNat.injEq, and_true]
        | succ e =>
          simp [throw, throwThe, MonadExceptOf.throw]
      | negSucc k =>
        simp [throw, throwThe, MonadExceptOf.throw]
  | _ => simp [throw, throwThe, MonadExceptOf.throw]

private theorem list_foldlM_push_iff {α β : Type} (f : α → Except String β)
    (l : List α) (init out : Array β) :
    l.foldlM (fun bs a => bs.push <$> f a) init = .ok out ↔
      ∃ (bs : List β),
        bs.length = l.length ∧
        (∀ (i : Nat) (h : i < l.length),
          ∃ (hb : i < bs.length), f l[i] = .ok bs[i]) ∧
        out = init ++ bs.toArray := by
  induction l generalizing init out with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, List.length_nil]
    constructor
    · intro h
      refine ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero i), by simpa using h.symm⟩
    · rintro ⟨bs, hlen, _, hout⟩
      cases bs with
      | nil => simpa using hout.symm
      | cons _ _ => simp at hlen
  | cons a rest ih =>
    simp only [List.foldlM_cons]
    cases hfa : f a with
    | error e =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      constructor
      · intro h; cases h
      · rintro ⟨bs, hlen, hidx, _⟩
        have h0 : 0 < (a :: rest).length := by simp
        rcases hidx 0 h0 with ⟨hb0, hf0⟩
        simp only [List.getElem_cons_zero] at hf0
        rw [hfa] at hf0
        cases hf0
    | ok b =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      change rest.foldlM (fun bs x => bs.push <$> f x) (init.push b) = .ok out ↔ _
      rw [ih (init.push b) out]
      constructor
      · rintro ⟨bs, hlen, hidx, hout⟩
        refine ⟨b :: bs, by simp [hlen], fun i hi => ?_, ?_⟩
        · cases i with
          | zero => exact ⟨by simp, by simp [hfa]⟩
          | succ i' =>
            have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
            rcases hidx i' hi' with ⟨hb', hf'⟩
            exact ⟨Nat.succ_lt_succ hb', hf'⟩
        · rw [hout, List.toArray_cons, Array.push_eq_append, Array.append_assoc]
      · rintro ⟨bs, hlen, hidx, hout⟩
        cases bs with
        | nil => simp at hlen
        | cons b' bs' =>
          have h0 : 0 < (a :: rest).length := by simp
          rcases hidx 0 h0 with ⟨_, hf0⟩
          simp only [List.getElem_cons_zero] at hf0
          rw [hfa] at hf0
          injection hf0 with hbeq
          subst hbeq
          refine ⟨bs', by simpa using hlen, fun i hi => ?_, ?_⟩
          · have hi' : i + 1 < (a :: rest).length := Nat.succ_lt_succ hi
            rcases hidx (i + 1) hi' with ⟨hb', hf'⟩
            exact ⟨Nat.lt_of_succ_lt_succ hb', hf'⟩
          · rw [hout, List.toArray_cons, Array.push_eq_append, Array.append_assoc]

theorem array_mapM_iff {α β : Type} (f : α → Except String β)
    (arr : Array α) (out : Array β) :
    arr.mapM f = .ok out ↔
      out.size = arr.size ∧
      ∀ (i : Nat) (h : i < arr.size), ∃ (ho : i < out.size), f arr[i] = .ok out[i] := by
  rw [Array.mapM_eq_foldlM, ← Array.foldlM_toList, list_foldlM_push_iff]
  constructor
  · rintro ⟨bs, hlen, hidx, hout⟩
    subst hout
    simp only [Array.empty_append, List.size_toArray, hlen, Array.length_toList, true_and]
    intro i hi
    have hi' : i < arr.toList.length := by simpa using hi
    rcases hidx i hi' with ⟨hb, hf⟩
    refine ⟨by simpa [hlen] using hi, ?_⟩
    simpa [Array.getElem_toList] using hf
  · rintro ⟨hsz, hidx⟩
    refine ⟨out.toList, by simpa using hsz, fun i hi => ?_, by simp⟩
    have hi' : i < arr.size := by simpa using hi
    rcases hidx i hi' with ⟨ho, hf⟩
    refine ⟨by simpa using ho, ?_⟩
    simpa using hf

private theorem parseStringItem_iff (ctx : String) (item : Json) (s : String) :
    (do
      let s' ← item.getStr?
      if NoComments.Config.hasControlOrSlashIssue s' then
        throw s!"invalid control character in {ctx} entry"
      return s') = .ok s ↔
      item = Json.str s ∧ ConfigSpec.cleanStr s = true := by
  cases item with
  | str s' =>
    dsimp only [Lean.Json.getStr?, bind, Except.bind, pure, Except.pure]
    by_cases hbad : NoComments.Config.hasControlOrSlashIssue s' = true
    · have hclean : ConfigSpec.cleanStr s' = false := by
        rw [hasControlOrSlashIssue_eq] at hbad
        exact Bool.eq_false_iff.mpr fun ht => by rw [ht] at hbad; cases hbad
      simp only [hbad, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
      constructor
      · intro h; cases h
      · rintro ⟨heq, hcl⟩
        injection heq with hs
        subst hs
        rw [hclean] at hcl
        cases hcl
    · have hf : NoComments.Config.hasControlOrSlashIssue s' = false := Bool.eq_false_iff.mpr hbad
      have hclean : ConfigSpec.cleanStr s' = true := by
        rw [hasControlOrSlashIssue_eq] at hf
        cases hc : ConfigSpec.cleanStr s'
        · rw [hc] at hf; cases hf
        · rfl
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Json.str.injEq]
      constructor
      · intro h; subst h; exact ⟨rfl, hclean⟩
      · rintro ⟨heq, _⟩; exact heq
  | _ =>
    simp [Lean.Json.getStr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem parseStringArray_iff (ctx : String) (j : Json) (out : Array String) :
    NoComments.Config.parseStringArray ctx j = .ok out ↔
      ConfigSpec.ValidCleanStringArray j out := by
  unfold NoComments.Config.parseStringArray ConfigSpec.ValidCleanStringArray
  cases j with
  | arr arr =>
    dsimp only [Lean.Json.getArr?]
    change
      (match Lean.Json.getArr? (.arr arr) with
      | Except.error err => Except.error err
      | Except.ok v => v.mapM (fun (item : Json) => do
          let s' ← item.getStr?
          if NoComments.Config.hasControlOrSlashIssue s' then
            throw s!"invalid control character in {ctx} entry"
          return s')) = .ok out ↔ _
    change
      (Array.mapM (fun (item : Json) => do
        let s' ← item.getStr?
        if NoComments.Config.hasControlOrSlashIssue s' then
          throw s!"invalid control character in {ctx} entry"
        return s') arr) = .ok out ↔ _
    rw [array_mapM_iff]
    constructor
    · rintro ⟨hsz, hidx⟩
      refine ⟨arr, rfl, hsz, fun i hi => ?_⟩
      rcases hidx i hi with ⟨ho, hitem⟩
      rw [parseStringItem_iff] at hitem
      exact ⟨ho, hitem⟩
    · rintro ⟨arr', heq, hsz, hidx⟩
      injection heq with ha
      subst ha
      refine ⟨hsz, fun i hi => ?_⟩
      rcases hidx i hi with ⟨ho, harr, hclean⟩
      exact ⟨ho, (parseStringItem_iff ctx arr[i] out[i]).mpr ⟨harr, hclean⟩⟩
  | _ =>
    simp [Lean.Json.getArr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem parsePrefixArray_iff (ctx : String) (j : Json) (out : Array String) :
    (do
      let rawArr ← NoComments.Config.parseStringArray ctx j
      rawArr.mapM (NoComments.Config.normalizePrefix ctx)) = .ok out ↔
      ConfigSpec.ValidPrefixArray j out := by
  dsimp only [bind, Except.bind]
  cases hraw : NoComments.Config.parseStringArray ctx j with
  | error e =>
    dsimp only
    constructor
    · intro h; cases h
    · rintro ⟨arr, rfl, hsz, hidx⟩
      let rawArr : Array String := arr.map fun item =>
        match item with
        | .str s => s
        | _ => ""
      have hrawArr_sz : rawArr.size = arr.size := Array.size_map ..
      have hvalid_raw : ConfigSpec.ValidCleanStringArray (Json.arr arr) rawArr := by
        refine ⟨arr, rfl, hrawArr_sz, fun i hi => ?_⟩
        rcases hidx i hi with ⟨_, raw, harr, hnp⟩
        have ho : i < rawArr.size := by omega
        have hraw_i : rawArr[i] = raw := by simp [rawArr, harr]
        refine ⟨ho, ?_, ?_⟩
        · rw [hraw_i]; exact harr
        · rw [hraw_i]; exact hnp.2.1
      have hok := (parseStringArray_iff ctx (Json.arr arr) rawArr).mpr hvalid_raw
      rw [hraw] at hok
      cases hok
  | ok rawArr =>
    dsimp only
    rw [parseStringArray_iff] at hraw
    rcases hraw with ⟨arr, rfl, hsz1, hidx1⟩
    rw [array_mapM_iff]
    constructor
    · rintro ⟨hsz2, hidx2⟩
      refine ⟨arr, rfl, hsz2.trans hsz1, fun i hi => ?_⟩
      have hi1 : i < rawArr.size := by omega
      rcases hidx1 i hi with ⟨_, harr, _⟩
      rcases hidx2 i hi1 with ⟨ho, hnp⟩
      rw [normalizePrefix_iff] at hnp
      exact ⟨ho, rawArr[i], harr, hnp⟩
    · rintro ⟨arr', heq, hsz, hidx⟩
      injection heq with ha
      subst ha
      refine ⟨hsz.trans hsz1.symm, fun i hi => ?_⟩
      have hi' : i < arr.size := by omega
      rcases hidx1 i hi' with ⟨_, harr1, _⟩
      rcases hidx i hi' with ⟨ho, raw, harr, hnp⟩
      rw [harr1] at harr
      injection harr with hraw_eq
      subst hraw_eq
      exact ⟨ho, (normalizePrefix_iff ctx rawArr[i] out[i]).mpr hnp⟩

theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem except_bind_err {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem except_bind_assoc {α β γ : Type} (a : Except String α)
    (f : α → Except String β) (g : β → Except String γ) :
    (a >>= fun x => f x >>= g) = ((a >>= f) >>= g) := by
  cases a <;> rfl

private theorem except_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (pure a >>= f) = f a := rfl

private theorem parseWorkspace_iff (idx : Nat) (j : Json) (ws : NoComments.Config.WorkspaceConfig) :
    NoComments.Config.parseWorkspace idx j = .ok ws ↔ ConfigSpec.ValidWorkspaceJson j ws := by
  unfold NoComments.Config.parseWorkspace ConfigSpec.ValidWorkspaceJson
  generalize s!"workspaces[{idx}]" = ctx
  dsimp only
  cases j with
  | obj obj =>
    rw [show (Json.obj obj).getObj? = .ok obj from rfl, except_bind_ok]
    cases hkeys : NoComments.Config.checkAllowedKeys ctx obj
        #["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"] with
    | error e =>
      rw [except_bind_err]
      constructor
      · intro h; cases h
      · rintro ⟨obj', dirRaw, heq, hkeys', _⟩
        injection heq with hobj
        subst hobj
        have hok := (checkAllowedKeys_iff ctx obj
          #["dir", "srcDir", "lakeArgs", "toolPrefixes", "excludePrefixes"]).mpr hkeys'
        rw [hkeys] at hok
        cases hok
    | ok u =>
      cases u
      rw [except_bind_ok]
      cases hdirReq : NoComments.Config.getRequiredField ctx obj "dir" with
      | error e =>
        rw [except_bind_err]
        constructor
        · intro h; cases h
        · rintro ⟨obj', dirRaw, heq, _, hreq', _⟩
          injection heq with hobj
          subst hobj
          have hok := (getRequiredField_iff ctx obj "dir" (.str dirRaw)).mpr hreq'
          rw [hdirReq] at hok
          cases hok
      | ok dirJson =>
        rw [except_bind_ok]
        rw [getRequiredField_iff] at hdirReq
        cases dirJson with
        | str dirRaw =>
          rw [show (Json.str dirRaw).getStr? = .ok dirRaw from rfl, except_bind_ok]
          cases hdirNorm : NoComments.Config.normalizeRelDir s!"{ctx}.dir" dirRaw with
          | error e =>
            rw [except_bind_err]
            constructor
            · intro h; cases h
            · rintro ⟨obj', dirRaw', heq, _, hreq', hnorm', _⟩
              injection heq with hobj
              subst hobj
              rw [hdirReq] at hreq'
              injection hreq' with hj
              injection hj with hr
              subst hr
              have hok := (normalizeRelDir_iff s!"{ctx}.dir" dirRaw ws.dir).mpr hnorm'
              rw [hdirNorm] at hok
              cases hok
          | ok dir =>
            rw [except_bind_ok]
            rw [normalizeRelDir_iff] at hdirNorm
            have hsrcOpt_iff :
                ∀ x,
                  (match obj.get? "srcDir" with
                    | some v => v.getStr? >>= NoComments.Config.normalizeRelDir s!"{ctx}.srcDir"
                    | none => pure ".") = .ok x ↔
                  match obj.get? "srcDir" with
                  | some v => ∃ srcRaw, v = Json.str srcRaw ∧ ConfigSpec.NormRelDir srcRaw x
                  | none => x = "." := by
              intro x
              cases obj.get? "srcDir" with
              | none => simp [pure, Except.pure, eq_comm]
              | some v =>
                dsimp only
                cases v with
                | str s =>
                  rw [show (Json.str s).getStr? = .ok s from rfl, except_bind_ok, normalizeRelDir_iff]
                  constructor
                  · intro h; exact ⟨s, rfl, h⟩
                  · rintro ⟨srcRaw, heq, h⟩; injection heq with hs; subst hs; exact h
                | _ =>
                  simp only [Lean.Json.getStr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
                  constructor
                  · intro h; cases h
                  · rintro ⟨_, h, _⟩; cases h
            have hlakeOpt_iff :
                ∀ x,
                  (match obj.get? "lakeArgs" with
                    | some v => NoComments.Config.parseStringArray s!"{ctx}.lakeArgs" v
                    | none => pure #[]) = .ok x ↔
                  match obj.get? "lakeArgs" with
                  | some v => ConfigSpec.ValidCleanStringArray v x
                  | none => x = #[] := by
              intro x
              cases obj.get? "lakeArgs" with
              | none => simp [pure, Except.pure, eq_comm]
              | some v => exact parseStringArray_iff s!"{ctx}.lakeArgs" v x
            have htoolOpt_iff :
                ∀ x,
                  (match obj.get? "toolPrefixes" with
                    | some v =>
                      NoComments.Config.parseStringArray s!"{ctx}.toolPrefixes" v >>= fun rawArr =>
                      rawArr.mapM (NoComments.Config.normalizePrefix s!"{ctx}.toolPrefixes")
                    | none => pure #[]) = .ok x ↔
                  match obj.get? "toolPrefixes" with
                  | some v => ConfigSpec.ValidPrefixArray v x
                  | none => x = #[] := by
              intro x
              cases obj.get? "toolPrefixes" with
              | none => simp [pure, Except.pure, eq_comm]
              | some v => exact parsePrefixArray_iff s!"{ctx}.toolPrefixes" v x
            have hexclOpt_iff :
                ∀ x,
                  (match obj.get? "excludePrefixes" with
                    | some v =>
                      NoComments.Config.parseStringArray s!"{ctx}.excludePrefixes" v >>= fun rawArr =>
                      rawArr.mapM (NoComments.Config.normalizePrefix s!"{ctx}.excludePrefixes")
                    | none => pure #[]) = .ok x ↔
                  match obj.get? "excludePrefixes" with
                  | some v => ConfigSpec.ValidPrefixArray v x
                  | none => x = #[] := by
              intro x
              cases obj.get? "excludePrefixes" with
              | none => simp [pure, Except.pure, eq_comm]
              | some v => exact parsePrefixArray_iff s!"{ctx}.excludePrefixes" v x
            apply Iff.trans (b :=
              ws.dir = dir ∧
              (match obj.get? "srcDir" with
                | some v => ∃ srcRaw, v = Json.str srcRaw ∧ ConfigSpec.NormRelDir srcRaw ws.srcDir
                | none => ws.srcDir = ".") ∧
              (match obj.get? "lakeArgs" with
                | some v => ConfigSpec.ValidCleanStringArray v ws.lakeArgs
                | none => ws.lakeArgs = #[]) ∧
              (match obj.get? "toolPrefixes" with
                | some v => ConfigSpec.ValidPrefixArray v ws.toolPrefixes
                | none => ws.toolPrefixes = #[]) ∧
              (match obj.get? "excludePrefixes" with
                | some v => ConfigSpec.ValidPrefixArray v ws.excludePrefixes
                | none => ws.excludePrefixes = #[]))
            · cases hs : obj.get? "srcDir" <;>
                first
                | (dsimp only
                   first | rw [except_bind_ok] | rw [except_pure_bind])
                | (rename_i vSrc
                   dsimp only
                   rw [except_bind_assoc]
                   cases h1 : (vSrc.getStr? >>= NoComments.Config.normalizeRelDir s!"{ctx}.srcDir") <;>
                     first
                     | (rw [except_bind_err]
                        have hiff := hsrcOpt_iff ws.srcDir
                        rw [hs] at hiff
                        dsimp only at hiff
                        rw [h1] at hiff
                        constructor
                        · intro h; cases h
                        · rintro ⟨_, hbad, _⟩
                          cases (hiff.mpr hbad))
                     | rw [except_bind_ok])
              all_goals
                cases hl : obj.get? "lakeArgs" <;>
                  first
                  | (dsimp only
                     first | rw [except_bind_ok] | rw [except_pure_bind])
                  | (rename_i vLake
                     dsimp only
                     cases h2 : NoComments.Config.parseStringArray s!"{ctx}.lakeArgs" vLake <;>
                       first
                       | (rw [except_bind_err]
                          have hiff := hlakeOpt_iff ws.lakeArgs
                          rw [hl] at hiff
                          dsimp only at hiff
                          rw [h2] at hiff
                          constructor
                          · intro h; cases h
                          · rintro ⟨_, _, hbad, _⟩
                            cases (hiff.mpr hbad))
                       | rw [except_bind_ok])
              all_goals
                cases ht : obj.get? "toolPrefixes" <;>
                  first
                  | (dsimp only
                     first | rw [except_bind_ok] | rw [except_pure_bind])
                  | (rename_i vTool
                     dsimp only
                     rw [except_bind_assoc]
                     cases h3 : (NoComments.Config.parseStringArray s!"{ctx}.toolPrefixes" vTool >>= fun rawArr =>
                         rawArr.mapM (NoComments.Config.normalizePrefix s!"{ctx}.toolPrefixes")) <;>
                       first
                       | (rw [except_bind_err]
                          have hiff := htoolOpt_iff ws.toolPrefixes
                          rw [ht] at hiff
                          dsimp only at hiff
                          rw [h3] at hiff
                          constructor
                          · intro h; cases h
                          · rintro ⟨_, _, _, hbad, _⟩
                            cases (hiff.mpr hbad))
                       | rw [except_bind_ok])
              all_goals
                cases he : obj.get? "excludePrefixes" <;>
                  first
                  | (dsimp only
                     first | rw [except_bind_ok] | rw [except_pure_bind])
                  | (rename_i vExcl
                     dsimp only
                     rw [except_bind_assoc]
                     cases h4 : (NoComments.Config.parseStringArray s!"{ctx}.excludePrefixes" vExcl >>= fun rawArr =>
                         rawArr.mapM (NoComments.Config.normalizePrefix s!"{ctx}.excludePrefixes")) <;>
                       first
                       | (rw [except_bind_err]
                          have hiff := hexclOpt_iff ws.excludePrefixes
                          rw [he] at hiff
                          dsimp only at hiff
                          rw [h4] at hiff
                          constructor
                          · intro h; cases h
                          · rintro ⟨_, _, _, _, hbad⟩
                            cases (hiff.mpr hbad))
                       | rw [except_bind_ok])
              all_goals
                simp only [pure, Except.pure, Except.ok.injEq]
                cases ws
                constructor
                · intro h
                  injection h with hd h_s h_l h_t h_e
                  rw [← hd, ← h_s, ← h_l, ← h_t, ← h_e]
                  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
                  all_goals dsimp only
                  all_goals
                    first
                    | rfl
                    | (have hm := (hsrcOpt_iff _).mp (by rw [hs]; assumption); rw [hs] at hm; exact hm)
                    | (have hm := (hlakeOpt_iff _).mp (by rw [hl]; assumption); rw [hl] at hm; exact hm)
                    | (have hm := (htoolOpt_iff _).mp (by rw [ht]; assumption); rw [ht] at hm; exact hm)
                    | (have hm := (hexclOpt_iff _).mp (by rw [he]; assumption); rw [he] at hm; exact hm)
                · rintro ⟨hd, hs', hl', ht', he'⟩
                  dsimp only at hd hs' hl' ht' he'
                  rw [hd]
                  first | rw [hs'] | (have hok := (hsrcOpt_iff _).mpr (by rw [hs]; exact hs'); rw [hs] at hok; dsimp only at hok; rw [h1] at hok; rw [Except.ok.inj hok])
                  first | rw [hl'] | (have hok := (hlakeOpt_iff _).mpr (by rw [hl]; exact hl'); rw [hl] at hok; dsimp only at hok; rw [h2] at hok; rw [Except.ok.inj hok])
                  first | rw [ht'] | (have hok := (htoolOpt_iff _).mpr (by rw [ht]; exact ht'); rw [ht] at hok; dsimp only at hok; rw [h3] at hok; rw [Except.ok.inj hok])
                  first | rw [he'] | (have hok := (hexclOpt_iff _).mpr (by rw [he]; exact he'); rw [he] at hok; dsimp only at hok; rw [h4] at hok; rw [Except.ok.inj hok])
            · constructor
              · rintro ⟨hdir_eq, h1, h2, h3, h4⟩
                refine ⟨obj, dirRaw, rfl, (checkAllowedKeys_iff _ _ _).mp hkeys, hdirReq,
                  ?_, h1, h2, h3, h4⟩
                simpa [hdir_eq] using hdirNorm
              · rintro ⟨obj', dirRaw', heq, _, hreq', hnorm', h1, h2, h3, h4⟩
                injection heq with hobj
                subst hobj
                rw [hdirReq] at hreq'
                injection hreq' with hj
                injection hj with hr
                subst hr
                have hdir_eq : dir = ws.dir := by
                  have h1' := (normalizeRelDir_iff s!"{ctx}.dir" dirRaw dir).mpr hdirNorm
                  have h2' := (normalizeRelDir_iff s!"{ctx}.dir" dirRaw ws.dir).mpr hnorm'
                  rw [h1'] at h2'
                  exact Except.ok.inj h2'
                exact ⟨hdir_eq.symm, h1, h2, h3, h4⟩
        | _ =>
          simp only [Lean.Json.getStr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          constructor
          · intro h; cases h
          · rintro ⟨obj', dirRaw', heq, _, hreq', _⟩
            injection heq with hobj
            subst hobj
            rw [hdirReq] at hreq'
            cases hreq'
  | _ =>
    simp [Lean.Json.getObj?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem parseExcludeRule_iff (idx : Nat) (j : Json) (r : NoComments.Config.ExcludeRule) :
    NoComments.Config.parseExcludeRule idx j = .ok r ↔ ConfigSpec.ValidExcludeJson j r := by
  unfold NoComments.Config.parseExcludeRule ConfigSpec.ValidExcludeJson
  let ctx := s!"exclude[{idx}]"
  change
    (do
      let obj ← j.getObj?
      NoComments.Config.checkAllowedKeys ctx obj #["prefix", "reason"]
      let pfxRaw ← (← NoComments.Config.getRequiredField ctx obj "prefix").getStr?
      let prefix_ ← NoComments.Config.normalizePrefix s!"{ctx}.prefix" pfxRaw
      let reasonRaw ← (← NoComments.Config.getRequiredField ctx obj "reason").getStr?
      let reason := reasonRaw.trimAscii.toString
      if reason == "" then
        throw s!"{ctx}.reason must not be empty"
      return ({ prefix_, reason } : NoComments.Config.ExcludeRule)) = .ok r ↔ _
  cases j with
  | obj obj =>
    dsimp only [Lean.Json.getObj?, bind, Except.bind, pure, Except.pure]
    cases hkeys : NoComments.Config.checkAllowedKeys ctx obj #["prefix", "reason"] with
    | error e =>
      dsimp only
      constructor
      · intro h; cases h
      · rintro ⟨obj', _, _, heq, hkeys', _⟩
        injection heq with hobj
        subst hobj
        have hok := (checkAllowedKeys_iff ctx obj #["prefix", "reason"]).mpr hkeys'
        rw [hkeys] at hok
        cases hok
    | ok u =>
      cases u
      dsimp only
      cases hpfxReq : NoComments.Config.getRequiredField ctx obj "prefix" with
      | error e =>
        dsimp only
        constructor
        · intro h; cases h
        · rintro ⟨obj', pfxRaw, _, heq, _, hpfxReq', _⟩
          injection heq with hobj
          subst hobj
          have hok := (getRequiredField_iff ctx obj "prefix" (.str pfxRaw)).mpr hpfxReq'
          rw [hpfxReq] at hok
          cases hok
      | ok pfxJson =>
        dsimp only
        rw [getRequiredField_iff] at hpfxReq
        cases pfxJson with
        | str pfxRaw =>
          dsimp only [Lean.Json.getStr?, pure, Except.pure]
          cases hpfxNorm : NoComments.Config.normalizePrefix s!"{ctx}.prefix" pfxRaw with
          | error e =>
            dsimp only
            constructor
            · intro h; cases h
            · rintro ⟨obj', pfxRaw', _, heq, _, hpfxReq', hpfxNorm', _⟩
              injection heq with hobj
              subst hobj
              rw [hpfxReq] at hpfxReq'
              injection hpfxReq' with hj
              injection hj with hr
              subst hr
              have hok := (normalizePrefix_iff s!"{ctx}.prefix" pfxRaw r.prefix_).mpr hpfxNorm'
              rw [hpfxNorm] at hok
              cases hok
          | ok pfx =>
            dsimp only
            rw [normalizePrefix_iff] at hpfxNorm
            cases hreasonReq : NoComments.Config.getRequiredField ctx obj "reason" with
            | error e =>
              dsimp only
              constructor
              · intro h; cases h
              · rintro ⟨obj', _, reasonRaw, heq, _, _, _, hreasonReq', _⟩
                injection heq with hobj
                subst hobj
                have hok := (getRequiredField_iff ctx obj "reason" (.str reasonRaw)).mpr hreasonReq'
                rw [hreasonReq] at hok
                cases hok
            | ok reasonJson =>
              dsimp only
              rw [getRequiredField_iff] at hreasonReq
              cases reasonJson with
              | str reasonRaw =>
                dsimp only [Lean.Json.getStr?, pure, Except.pure]
                by_cases hemp : (reasonRaw.trimAscii.toString == "") = true
                · have htr : reasonRaw.trimAscii.toString = "" := beq_iff_eq.mp hemp
                  simp only [hemp, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
                  constructor
                  · intro h; cases h
                  · rintro ⟨obj', _, reasonRaw', heq, _, _, _, hreasonReq', htrim, hne⟩
                    injection heq with hobj
                    subst hobj
                    rw [hreasonReq] at hreasonReq'
                    injection hreasonReq' with hj
                    injection hj with hr
                    subst hr
                    rw [← htrim] at hne
                    exact False.elim (hne htr)
                · have hf : (reasonRaw.trimAscii.toString == "") = false :=
                    Bool.eq_false_iff.mpr hemp
                  have hne : reasonRaw.trimAscii.toString ≠ "" :=
                    fun h => hemp (beq_iff_eq.mpr h)
                  simp only [hf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq]
                  constructor
                  · intro h
                    subst h
                    exact ⟨obj, pfxRaw, reasonRaw, rfl, (checkAllowedKeys_iff _ _ _).mp hkeys,
                      hpfxReq, hpfxNorm, hreasonReq, rfl, hne⟩
                  · rintro ⟨obj', pfxRaw', reasonRaw', heq, _, hpfxReq', hpfxNorm',
                      hreasonReq', htrim, _⟩
                    injection heq with hobj
                    subst hobj
                    rw [hpfxReq] at hpfxReq'
                    injection hpfxReq' with hj1
                    injection hj1 with hr1
                    subst hr1
                    rw [hreasonReq] at hreasonReq'
                    injection hreasonReq' with hj2
                    injection hj2 with hr2
                    subst hr2
                    have hpfx_eq : pfx = r.prefix_ := by
                      have h1 := (normalizePrefix_iff s!"{ctx}.prefix" pfxRaw pfx).mpr hpfxNorm
                      have h2 := (normalizePrefix_iff s!"{ctx}.prefix" pfxRaw r.prefix_).mpr hpfxNorm'
                      rw [h1] at h2
                      exact Except.ok.inj h2
                    cases r
                    dsimp only at hpfx_eq htrim ⊢
                    rw [hpfx_eq, htrim]
              | _ =>
                simp only [throw, throwThe, MonadExceptOf.throw]
                constructor
                · intro h; cases h
                · rintro ⟨obj', _, reasonRaw, heq, _, _, _, hreasonReq', _⟩
                  injection heq with hobj
                  subst hobj
                  rw [hreasonReq] at hreasonReq'
                  cases hreasonReq'
        | _ =>
          simp only [Lean.Json.getStr?, throw, throwThe, MonadExceptOf.throw]
          constructor
          · intro h; cases h
          · rintro ⟨obj', pfxRaw, _, heq, _, hpfxReq', _⟩
            injection heq with hobj
            subst hobj
            rw [hpfxReq] at hpfxReq'
            cases hpfxReq'
  | _ =>
    simp [Lean.Json.getObj?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem workspacesLoop_ok_or_err (wsArr : Array Json)
    (idxs : List Nat) (hidxs : ∀ idx ∈ idxs, idx < wsArr.size)
    (initWs : Array NoComments.Config.WorkspaceConfig) (initSeen : Array String)
    (hseen_len : initSeen.size = initWs.size)
    (hseen_eq : initSeen.toList = initWs.toList.map (·.dir))
    (hnodup : initSeen.toList.Nodup) :
    match forIn' idxs (initWs, initSeen) fun idx h state => do
        let ws ← NoComments.Config.parseWorkspace idx (wsArr[idx]'(hidxs idx h))
        if state.2.contains ws.dir then
          throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
        let seen' := state.2.push ws.dir
        let ws' := state.1.push ws
        return ForInStep.yield (ws', seen') with
    | .ok (ws, seen) =>
      ∃ added : List NoComments.Config.WorkspaceConfig,
        added.length = idxs.length ∧
        (∀ (k : Nat) (hk : k < idxs.length),
          ∃ (ha : k < added.length),
            let idx := idxs[k]
            have hlt : idx < wsArr.size := hidxs idx (List.getElem_mem hk)
            NoComments.Config.parseWorkspace idx wsArr[idx] = .ok added[k]) ∧
        ws.toList = initWs.toList ++ added ∧
        seen.toList = (initWs.toList ++ added).map (·.dir) ∧
        seen.toList.Nodup
    | .error _ =>
      (∃ (k : Nat) (hk : k < idxs.length),
        let idx := idxs[k]
        have hlt : idx < wsArr.size := hidxs idx (List.getElem_mem hk)
        ∀ ws, ¬ ConfigSpec.ValidWorkspaceJson wsArr[idx] ws) ∨
      (∃ (ws : NoComments.Config.WorkspaceConfig) (k : Nat) (hk : k < idxs.length),
        let idx := idxs[k]
        have hlt : idx < wsArr.size := hidxs idx (List.getElem_mem hk)
        ConfigSpec.ValidWorkspaceJson wsArr[idx] ws ∧
        (∃ (prev : NoComments.Config.WorkspaceConfig),
          prev ∈ initWs.toList ∧ prev.dir = ws.dir)) ∨
      (∃ (k1 k2 : Nat) (hk1 : k1 < idxs.length) (hk2 : k2 < idxs.length)
        (ws1 ws2 : NoComments.Config.WorkspaceConfig),
        let idx1 := idxs[k1]
        let idx2 := idxs[k2]
        have hlt1 : idx1 < wsArr.size := hidxs idx1 (List.getElem_mem hk1)
        have hlt2 : idx2 < wsArr.size := hidxs idx2 (List.getElem_mem hk2)
        k1 ≠ k2 ∧
        ConfigSpec.ValidWorkspaceJson wsArr[idx1] ws1 ∧
        ConfigSpec.ValidWorkspaceJson wsArr[idx2] ws2 ∧
        ws1.dir = ws2.dir) := by
  induction idxs generalizing initWs initSeen with
  | nil =>
    simp only [List.forIn'_nil, pure, Except.pure]
    refine ⟨[], rfl, fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
    exact ⟨by simp, by simp [hseen_eq], hnodup⟩
  | cons idx rest ih =>
    have hidx_lt : idx < wsArr.size := hidxs idx (List.mem_cons_self ..)
    have hrest : ∀ j ∈ rest, j < wsArr.size := fun j hj => hidxs j (List.mem_cons_of_mem idx hj)
    have hstep :
        (forIn' (idx :: rest) (initWs, initSeen) fun idx' h state => do
          let ws ← NoComments.Config.parseWorkspace idx' (wsArr[idx']'(hidxs idx' h))
          if state.2.contains ws.dir then
            throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
          let seen' := state.2.push ws.dir
          let ws' := state.1.push ws
          return ForInStep.yield (ws', seen')) =
        ((do
          let ws ← NoComments.Config.parseWorkspace idx wsArr[idx]
          if initSeen.contains ws.dir then
            throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
          let seen' := initSeen.push ws.dir
          let ws' := initWs.push ws
          return (ws', seen')) >>= fun nextState =>
            forIn' rest nextState fun idx' h state => do
              let ws ← NoComments.Config.parseWorkspace idx' (wsArr[idx']'(hrest idx' h))
              if state.2.contains ws.dir then
                throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
              let seen' := state.2.push ws.dir
              let ws' := state.1.push ws
              return ForInStep.yield (ws', seen')) := by
      rw [List.forIn'_cons]
      cases NoComments.Config.parseWorkspace idx wsArr[idx] with
      | error e => simp [bind, Except.bind]
      | ok ws =>
        cases hcond : initSeen.contains ws.dir
        · simp only [hcond, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
        · simp only [hcond, ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [hstep]
    cases hp : NoComments.Config.parseWorkspace idx wsArr[idx] with
    | error e =>
      dsimp only [bind, Except.bind]
      left
      refine ⟨0, Nat.zero_lt_succ rest.length, fun ws hval => ?_⟩
      have hok := (parseWorkspace_iff idx wsArr[idx] ws).mpr hval
      rw [hp] at hok
      cases hok
    | ok ws =>
      dsimp only [bind, Except.bind]
      by_cases hdup : initSeen.contains ws.dir = true
      · simp only [hdup, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
        have hmem_seen : ws.dir ∈ initSeen.toList :=
          Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hdup)
        rw [hseen_eq, List.mem_map] at hmem_seen
        rcases hmem_seen with ⟨prev, hprev_mem, hprev_dir⟩
        right; left
        refine ⟨ws, 0, Nat.zero_lt_succ rest.length, ?_⟩
        exact ⟨(parseWorkspace_iff idx wsArr[idx] ws).mp hp, ⟨prev, hprev_mem, hprev_dir⟩⟩
      · have hnot_mem : ws.dir ∉ initSeen.toList := fun hm =>
          hdup (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hm))
        have hf : initSeen.contains ws.dir = false := Bool.eq_false_iff.mpr hdup
        simp only [hf, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
        have hih := ih hrest (initWs.push ws) (initSeen.push ws.dir)
          (by simp [hseen_len])
          (by simp [hseen_eq, Array.toList_push, List.map_append])
          (by
            rw [Array.toList_push, List.nodup_append]
            refine ⟨hnodup, by simp, fun a ha b hb heq => ?_⟩
            rcases List.mem_singleton.mp hb with rfl
            subst heq
            exact hnot_mem ha)
        cases hloop :
            (forIn' rest (initWs.push ws, initSeen.push ws.dir) fun idx' h state => do
              let ws' ← NoComments.Config.parseWorkspace idx' (wsArr[idx']'(hrest idx' h))
              if state.2.contains ws'.dir then
                throw s!"duplicate workspace dir '{ws'.dir}' in config.workspaces"
              let seen' := state.2.push ws'.dir
              let ws'' := state.1.push ws'
              return ForInStep.yield (ws'', seen')) with
        | ok res =>
          rw [hloop] at hih
          dsimp only [bind, Except.bind, pure, Except.pure] at hloop
          rw [hloop]
          rcases hih with ⟨added, hlen, hidx, hws, hseen, hnd⟩
          refine ⟨ws :: added, by simp [hlen], fun k hk => ?_, ?_, ?_, hnd⟩
          · cases k with
            | zero => exact ⟨Nat.zero_lt_succ added.length, by simpa using hp⟩
            | succ k' =>
              have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
              rcases hidx k' hk' with ⟨ha', hpk⟩
              exact ⟨Nat.succ_lt_succ ha', hpk⟩
          · rw [hws, Array.toList_push]
            simp [List.append_assoc]
          · rw [hseen, Array.toList_push]
            simp [List.append_assoc]
        | error e =>
          rw [hloop] at hih
          dsimp only [bind, Except.bind, pure, Except.pure] at hloop
          rw [hloop]
          rcases hih with ⟨k, hk, herr⟩ | ⟨ws', k, hk, hval', prev, hprev_mem, hprev_dir⟩ |
              ⟨k1, k2, hk1, hk2, ws1, ws2, hne, hv1, hv2, hdir⟩
          · left
            exact ⟨k + 1, Nat.succ_lt_succ hk, herr⟩
          · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hprev_mem
            rcases hprev_mem with hprev_init | hprev_eq
            · right; left
              exact ⟨ws', k + 1, Nat.succ_lt_succ hk, hval', prev, hprev_init, hprev_dir⟩
            · right; right
              exact ⟨0, k + 1, Nat.zero_lt_succ rest.length, Nat.succ_lt_succ hk,
                ws, ws', Nat.zero_ne_add_one k, (parseWorkspace_iff idx wsArr[idx] ws).mp hp,
                hval', hprev_eq ▸ hprev_dir⟩
          · right; right
            exact ⟨k1 + 1, k2 + 1, Nat.succ_lt_succ hk1, Nat.succ_lt_succ hk2,
              ws1, ws2, by omega, hv1, hv2, hdir⟩

private theorem excludeLoop_ok_or_err (exclArr : Array Json)
    (idxs : List Nat) (hidxs : ∀ idx ∈ idxs, idx < exclArr.size)
    (initRules : Array NoComments.Config.ExcludeRule) :
    match forIn' idxs initRules fun idx h rules => do
        return ForInStep.yield
          (rules.push (← NoComments.Config.parseExcludeRule idx (exclArr[idx]'(hidxs idx h)))) with
    | .ok rules =>
      ∃ added : List NoComments.Config.ExcludeRule,
        added.length = idxs.length ∧
        (∀ (k : Nat) (hk : k < idxs.length),
          ∃ (ha : k < added.length),
            let idx := idxs[k]
            have hlt : idx < exclArr.size := hidxs idx (List.getElem_mem hk)
            NoComments.Config.parseExcludeRule idx exclArr[idx] = .ok added[k]) ∧
        rules.toList = initRules.toList ++ added
    | .error _ =>
      ∃ (k : Nat) (hk : k < idxs.length),
        let idx := idxs[k]
        have hlt : idx < exclArr.size := hidxs idx (List.getElem_mem hk)
        ∀ r, ¬ ConfigSpec.ValidExcludeJson exclArr[idx] r := by
  induction idxs generalizing initRules with
  | nil =>
    simp only [List.forIn'_nil, pure, Except.pure]
    exact ⟨[], rfl, fun k hk => absurd hk (Nat.not_lt_zero k), by simp⟩
  | cons idx rest ih =>
    have hidx_lt : idx < exclArr.size := hidxs idx (List.mem_cons_self ..)
    have hrest : ∀ j ∈ rest, j < exclArr.size := fun j hj => hidxs j (List.mem_cons_of_mem idx hj)
    have hstep :
        (forIn' (idx :: rest) initRules fun idx' h rules => do
          return ForInStep.yield
            (rules.push (← NoComments.Config.parseExcludeRule idx' (exclArr[idx']'(hidxs idx' h))))) =
        ((do
          let r ← NoComments.Config.parseExcludeRule idx exclArr[idx]
          return initRules.push r) >>= fun nextRules =>
            forIn' rest nextRules fun idx' h rules => do
              return ForInStep.yield
                (rules.push (← NoComments.Config.parseExcludeRule idx' (exclArr[idx']'(hrest idx' h))))) := by
      rw [List.forIn'_cons]
      cases NoComments.Config.parseExcludeRule idx exclArr[idx]
      · simp [bind, Except.bind]
      · simp [bind, Except.bind, pure, Except.pure]
    rw [hstep]
    cases hp : NoComments.Config.parseExcludeRule idx exclArr[idx] with
    | error e =>
      dsimp only [bind, Except.bind]
      refine ⟨0, Nat.zero_lt_succ rest.length, fun r hval => ?_⟩
      have hok := (parseExcludeRule_iff idx exclArr[idx] r).mpr hval
      rw [hp] at hok
      cases hok
    | ok r =>
      dsimp only [bind, Except.bind, pure, Except.pure]
      have hih := ih hrest (initRules.push r)
      cases hloop :
          (forIn' rest (initRules.push r) fun idx' h rules => do
            return ForInStep.yield
              (rules.push (← NoComments.Config.parseExcludeRule idx' (exclArr[idx']'(hrest idx' h))))) with
      | ok res =>
        rw [hloop] at hih
        dsimp only [bind, Except.bind, pure, Except.pure] at hloop
        rw [hloop]
        rcases hih with ⟨added, hlen, hidx, hrules⟩
        refine ⟨r :: added, by simp [hlen], fun k hk => ?_, ?_⟩
        · cases k with
          | zero => exact ⟨Nat.zero_lt_succ added.length, by simpa using hp⟩
          | succ k' =>
            have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
            rcases hidx k' hk' with ⟨ha', hpk⟩
            exact ⟨Nat.succ_lt_succ ha', hpk⟩
        · rw [hrules, Array.toList_push]
          simp [List.append_assoc]
      | error e =>
        rw [hloop] at hih
        dsimp only [bind, Except.bind, pure, Except.pure] at hloop
        rw [hloop]
        rcases hih with ⟨k, hk, herr⟩
        exact ⟨k + 1, Nat.succ_lt_succ hk, herr⟩

theorem range'_zero_getElem (n k : Nat) (hk : k < (List.range' 0 n 1).length) :
    (List.range' 0 n 1)[k] = k := by
  rw [List.getElem_range']
  simp

theorem range'_zero_mem {n idx : Nat} (h : idx ∈ List.range' 0 n 1) : idx < n := by
  rw [List.mem_range'_1] at h
  omega

private theorem parseConfigWorkspaces_extract (wsArr : Array Json)
    (body : (idx : Nat) → idx ∈ [:wsArr.size] →
      Array NoComments.Config.WorkspaceConfig × Array String →
      Except String (ForInStep (Array NoComments.Config.WorkspaceConfig × Array String)))
    (k : Array NoComments.Config.WorkspaceConfig × Array String →
      Except String NoComments.Config.RepoConfig)
    (res : Except String NoComments.Config.RepoConfig)
    (heq :
      (forIn' [:wsArr.size] (Array.emptyWithCapacity wsArr.size, (#[] : Array String)) body >>= k) =
        res)
    (hbody : ∀ idx h __s,
      body idx h __s = do
        let ws ← NoComments.Config.parseWorkspace idx wsArr[idx]
        if __s.2.contains ws.dir then
          throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
        let seen' := __s.2.push ws.dir
        let ws' := __s.1.push ws
        return ForInStep.yield (ws', seen')) :
    ((forIn' (List.range' 0 wsArr.size 1) (Array.emptyWithCapacity wsArr.size, (#[] : Array String))
      fun idx h state => do
        let ws ← NoComments.Config.parseWorkspace idx (wsArr[idx]'(range'_zero_mem h))
        if state.2.contains ws.dir then
          throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
        let seen' := state.2.push ws.dir
        let ws' := state.1.push ws
        return ForInStep.yield (ws', seen')) >>= k) = res := by
  rw [← heq]
  congr 1
  have hbase := @Std.Legacy.Range.forIn'_eq_forIn'_range'
  rw [hbase]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  funext idx h __s
  exact (hbody idx _ __s).symm

private theorem parseConfigExclude_extract (exclArr : Array Json)
    (body : (idx : Nat) → idx ∈ [:exclArr.size] →
      Array NoComments.Config.ExcludeRule →
      Except String (ForInStep (Array NoComments.Config.ExcludeRule)))
    (k : Array NoComments.Config.ExcludeRule → Except String NoComments.Config.RepoConfig)
    (res : Except String NoComments.Config.RepoConfig)
    (heq : (forIn' [:exclArr.size] (Array.emptyWithCapacity exclArr.size) body >>= k) = res)
    (hbody : ∀ idx h __s,
      body idx h __s = do
        return ForInStep.yield (__s.push (← NoComments.Config.parseExcludeRule idx exclArr[idx]))) :
    ((forIn' (List.range' 0 exclArr.size 1) (Array.emptyWithCapacity exclArr.size)
      fun idx h rules => do
        return ForInStep.yield
          (rules.push (← NoComments.Config.parseExcludeRule idx (exclArr[idx]'(range'_zero_mem h))))) >>=
        k) = res := by
  rw [← heq]
  congr 1
  have hbase := @Std.Legacy.Range.forIn'_eq_forIn'_range'
  rw [hbase]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  funext idx h __s
  exact (hbody idx _ __s).symm

private theorem parseConfigRatchetSuffix_ok (obj : Std.TreeMap.Raw String Json compare)
    (workspaces : Array NoComments.Config.WorkspaceConfig)
    (exclude : Array NoComments.Config.ExcludeRule) (cfg : NoComments.Config.RepoConfig)
    (hok :
      (do
        let __do_lift ← NoComments.Config.getRequiredField "config" obj "ratchet"
        let ratchetRaw ← __do_lift.getStr?
        let ratchet ← NoComments.Config.normalizeRelFile "config.ratchet" ratchetRaw
        pure ({ workspaces := workspaces, exclude := exclude, ratchet := ratchet } :
          NoComments.Config.RepoConfig)) = .ok cfg) :
    ∃ ratchetRaw,
      obj.get? "ratchet" = some (Json.str ratchetRaw) ∧
      ConfigSpec.NormRelFile ratchetRaw cfg.ratchet ∧
      cfg.workspaces = workspaces ∧
      cfg.exclude = exclude := by
  dsimp only [bind, Except.bind] at hok
  cases hratReq : NoComments.Config.getRequiredField "config" obj "ratchet" with
  | error e => rw [hratReq] at hok; cases hok
  | ok ratJson =>
    rw [hratReq] at hok
    dsimp only at hok
    rw [getRequiredField_iff] at hratReq
    cases ratJson with
    | str ratchetRaw =>
      dsimp only [Lean.Json.getStr?, pure, Except.pure] at hok
      cases hnorm : NoComments.Config.normalizeRelFile "config.ratchet" ratchetRaw with
      | error e => rw [hnorm] at hok; cases hok
      | ok ratchet =>
        rw [hnorm] at hok
        simp only [Except.ok.injEq] at hok
        subst hok
        rw [normalizeRelFile_iff] at hnorm
        exact ⟨ratchetRaw, hratReq, hnorm, rfl, rfl⟩
    | _ => simp [Lean.Json.getStr?, throw, throwThe, MonadExceptOf.throw] at hok

private theorem parseConfigRatchetSuffix_err (text msg : String)
    (obj : Std.TreeMap.Raw String Json compare)
    (workspaces : Array NoComments.Config.WorkspaceConfig)
    (exclude : Array NoComments.Config.ExcludeRule)
    (hparse : Json.parse text = .ok (Json.obj obj))
    (herr :
      (do
        let __do_lift ← NoComments.Config.getRequiredField "config" obj "ratchet"
        let ratchetRaw ← __do_lift.getStr?
        let ratchet ← NoComments.Config.normalizeRelFile "config.ratchet" ratchetRaw
        pure ({ workspaces := workspaces, exclude := exclude, ratchet := ratchet } :
          NoComments.Config.RepoConfig)) = .error msg) :
    ConfigSpec.ConfigRefusal text := by
  dsimp only [bind, Except.bind] at herr
  cases hratReq : NoComments.Config.getRequiredField "config" obj "ratchet" with
  | error e =>
    exact ConfigRefusal.badRatchetField hparse fun raw out h _ => by
      have hok := (getRequiredField_iff "config" obj "ratchet" (.str raw)).mpr h
      rw [hratReq] at hok
      cases hok
  | ok ratJson =>
    rw [hratReq] at herr
    dsimp only at herr
    rw [getRequiredField_iff] at hratReq
    cases ratJson with
    | str ratRaw =>
      dsimp only [Lean.Json.getStr?, pure, Except.pure] at herr
      cases hnorm : NoComments.Config.normalizeRelFile "config.ratchet" ratRaw with
      | ok rat => rw [hnorm] at herr; cases herr
      | error e =>
        exact ConfigRefusal.badRatchetField hparse fun raw out h hno => by
          rw [hratReq] at h
          injection h with hs
          injection hs with hr
          subst hr
          have hok := (normalizeRelFile_iff "config.ratchet" ratRaw out).mpr hno
          rw [hnorm] at hok
          cases hok
    | _ =>
      exact ConfigRefusal.badRatchetField hparse fun raw out h _ => by
        rw [hratReq] at h
        cases h

theorem parseConfigJson_ok (text : String) (cfg : NoComments.Config.RepoConfig)
    (hok : NoComments.Config.parseConfigJson text = .ok cfg) :
    ConfigSpec.ValidConfigJson text cfg := by
  unfold NoComments.Config.parseConfigJson at hok
  cases hparse : Json.parse text with
  | error e =>
    rw [hparse, except_bind_err] at hok
    cases hok
  | ok json =>
    rw [hparse, except_bind_ok] at hok
    cases json with
    | obj obj =>
      rw [show (Json.obj obj).getObj? = .ok obj from rfl, except_bind_ok] at hok
      cases hkeys : NoComments.Config.checkAllowedKeys "config" obj #["workspaces", "exclude", "ratchet"] with
      | error e =>
        rw [hkeys, except_bind_err] at hok
        cases hok
      | ok u =>
        cases u
        rw [hkeys, except_bind_ok] at hok
        rw [checkAllowedKeys_iff] at hkeys
        cases hwsReq : NoComments.Config.getRequiredField "config" obj "workspaces" with
        | error e =>
          rw [hwsReq, except_bind_err] at hok
          cases hok
        | ok wsJson =>
          rw [hwsReq, except_bind_ok] at hok
          rw [getRequiredField_iff] at hwsReq
          cases wsJson with
          | arr wsArr =>
            rw [show (Json.arr wsArr).getArr? = .ok wsArr from rfl, except_bind_ok] at hok
            by_cases hemp : wsArr.isEmpty = true
            · simp only [hemp, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
                except_bind_err] at hok
              cases hok
            · have hne_emp : wsArr.isEmpty = false := Bool.eq_false_iff.mpr hemp
              have hws_pos : wsArr.size > 0 := by
                rw [Array.isEmpty_iff] at hemp
                have hne0 : wsArr.size ≠ 0 := fun h => hemp (Array.size_eq_zero_iff.mp h)
                omega
              simp only [hne_emp, Bool.false_eq_true, ↓reduceIte] at hok
              have hokWs := parseConfigWorkspaces_extract wsArr _ _ _ hok (fun _ _ _ => rfl)
              cases hloopWs :
                  (forIn' (List.range' 0 wsArr.size 1)
                    (Array.emptyWithCapacity wsArr.size, (#[] : Array String))
                    fun idx h state => do
                      let ws ← NoComments.Config.parseWorkspace idx (wsArr[idx]'(range'_zero_mem h))
                      if state.2.contains ws.dir then
                        throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
                      let seen' := state.2.push ws.dir
                      let ws' := state.1.push ws
                      return ForInStep.yield (ws', seen')) with
              | error e =>
                rw [hloopWs, except_bind_err] at hokWs
                cases hokWs
              | ok stateWs =>
                have hspecWs := workspacesLoop_ok_or_err wsArr (List.range' 0 wsArr.size 1)
                  (fun _ h => range'_zero_mem h) (Array.emptyWithCapacity wsArr.size) #[]
                  (by simp [Array.emptyWithCapacity])
                  (by simp [Array.emptyWithCapacity]) (by simp)
                rw [hloopWs] at hspecWs
                rcases hspecWs with ⟨addedWs, haddedLen, haddedIdx, hwsList, hseenList, hnodup⟩
                rw [hloopWs, except_bind_ok] at hokWs
                have hwsEmptyList :
                    (Array.emptyWithCapacity (α := NoComments.Config.WorkspaceConfig) wsArr.size).toList = [] := by
                  simp [Array.emptyWithCapacity]
                have hwsList' : stateWs.1.toList = addedWs := by
                  simpa [hwsEmptyList] using hwsList
                have hwsSize : stateWs.1.size = wsArr.size := by
                  rw [← Array.length_toList, hwsList', haddedLen, List.length_range']
                have hwsNodup : (stateWs.1.toList.map (·.dir)).Nodup := by
                  have hseen' : stateWs.2.toList = stateWs.1.toList.map (·.dir) := by
                    simpa [hwsList', hwsEmptyList] using hseenList
                  rwa [← hseen']
                have hwsIdxValid :
                    ∀ (i : Nat) (_h : i < wsArr.size),
                      ∃ (_hc : i < stateWs.1.size), ConfigSpec.ValidWorkspaceJson wsArr[i] stateWs.1[i] := by
                  intro i hi
                  have hiRange : i < (List.range' 0 wsArr.size 1).length := by simp [hi]
                  rcases haddedIdx i hiRange with ⟨ha, hpk⟩
                  have hgi : (List.range' 0 wsArr.size 1)[i] = i := range'_zero_getElem _ _ hiRange
                  have hc : i < stateWs.1.size := by omega
                  refine ⟨hc, ?_⟩
                  have hel : stateWs.1[i] = addedWs[i] := by
                    rw [← Array.getElem_toList]
                    simp [hwsList']
                  rw [hel]
                  rw [parseWorkspace_iff] at hpk
                  simpa [hgi] using hpk
                cases hopt : obj.get? "exclude" with
                | none =>
                  rw [hopt] at hokWs
                  rw [show (pure #[] : Except String (Array NoComments.Config.ExcludeRule)) = .ok #[] from rfl,
                    except_bind_ok] at hokWs
                  dsimp only at hokWs
                  rcases parseConfigRatchetSuffix_ok obj stateWs.1 #[] cfg hokWs with
                    ⟨ratchetRaw, hratReq, hnorm, hwsEq, hexEq⟩
                  refine ⟨obj, wsArr, ratchetRaw, hparse, hkeys, hwsReq, hws_pos, ?_, ?_, ?_,
                    ?_, hratReq, hnorm⟩
                  · simpa [hwsEq] using hwsSize
                  · simpa [hwsEq] using hwsIdxValid
                  · simpa [hwsEq] using hwsNodup
                  · simp [hopt, hexEq]
                | some v =>
                  rw [hopt] at hokWs
                  cases v with
                  | arr exclArr =>
                    dsimp only at hokWs
                    rw [show (Json.arr exclArr).getArr? = .ok exclArr from rfl, except_bind_ok] at hokWs
                    have hokEx := parseConfigExclude_extract exclArr _ _ _ hokWs
                      (fun idx h __s => rfl)
                    cases hloopEx :
                        (forIn' (List.range' 0 exclArr.size 1) (Array.emptyWithCapacity exclArr.size)
                          fun idx h rules => do
                            return ForInStep.yield
                              (rules.push (← NoComments.Config.parseExcludeRule idx
                                (exclArr[idx]'(range'_zero_mem h))))) with
                    | error e =>
                      rw [hloopEx, except_bind_err] at hokEx
                      cases hokEx
                    | ok rules =>
                      have hspecEx := excludeLoop_ok_or_err exclArr (List.range' 0 exclArr.size 1)
                        (fun _ h => range'_zero_mem h) (Array.emptyWithCapacity exclArr.size)
                      rw [hloopEx] at hspecEx
                      rcases hspecEx with ⟨addedEx, hlenEx, hidxEx, hlistEx⟩
                      rw [hloopEx, except_bind_ok] at hokEx
                      rw [show (pure rules : Except String (Array NoComments.Config.ExcludeRule)) = .ok rules from rfl,
                        except_bind_ok] at hokEx
                      have hexEmpty :
                          (Array.emptyWithCapacity (α := NoComments.Config.ExcludeRule) exclArr.size).toList = [] := by
                        simp [Array.emptyWithCapacity]
                      have hlistEx' : rules.toList = addedEx := by
                        simpa [hexEmpty] using hlistEx
                      have hszEx : rules.size = exclArr.size := by
                        rw [← Array.length_toList, hlistEx', hlenEx, List.length_range']
                      have hexIdxValid :
                          ∀ (i : Nat) (_h : i < exclArr.size),
                            ∃ (_hc : i < rules.size), ConfigSpec.ValidExcludeJson exclArr[i] rules[i] := by
                        intro i hi
                        have hiRange : i < (List.range' 0 exclArr.size 1).length := by simp [hi]
                        rcases hidxEx i hiRange with ⟨ha, hpk⟩
                        have hgi : (List.range' 0 exclArr.size 1)[i] = i := range'_zero_getElem _ _ hiRange
                        have hc : i < rules.size := by omega
                        refine ⟨hc, ?_⟩
                        have hel : rules[i] = addedEx[i] := by
                          rw [← Array.getElem_toList]
                          simp [hlistEx']
                        rw [hel]
                        rw [parseExcludeRule_iff] at hpk
                        simpa [hgi] using hpk
                      rcases parseConfigRatchetSuffix_ok obj stateWs.1 rules cfg hokEx with
                        ⟨ratchetRaw, hratReq, hnorm, hwsEq, hexEq⟩
                      refine ⟨obj, wsArr, ratchetRaw, hparse, hkeys, hwsReq, hws_pos, ?_, ?_, ?_,
                        ?_, hratReq, hnorm⟩
                      · simpa [hwsEq] using hwsSize
                      · simpa [hwsEq] using hwsIdxValid
                      · simpa [hwsEq] using hwsNodup
                      · rw [hopt]
                        refine ⟨?_, ?_⟩
                        · simpa [hexEq] using hszEx
                        · simpa [hexEq] using hexIdxValid
                  | _ =>
                    simp [Lean.Json.getArr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hokWs
          | _ =>
            simp [Lean.Json.getArr?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    | _ =>
      simp [Lean.Json.getObj?, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok

private theorem exists_not_mem_of_not_forall (l : List (String × Json)) (allowed : List String)
    (hnot : ¬ ∀ kv ∈ l, kv.1 ∈ allowed) :
    ∃ kv ∈ l, kv.1 ∉ allowed := by
  induction l with
  | nil => exact absurd (fun _ h => nomatch h) hnot
  | cons kv rest ih =>
    by_cases h : kv.1 ∈ allowed
    · have ⟨x, hx, hxn⟩ := ih fun hrest => hnot fun y hy =>
        (List.mem_cons.mp hy).elim (fun he => he ▸ h) (hrest y)
      exact ⟨x, List.mem_cons_of_mem kv hx, hxn⟩
    · exact ⟨kv, List.mem_cons_self .., h⟩

theorem parseConfigJson_err (text msg : String)
    (herr : NoComments.Config.parseConfigJson text = .error msg) :
    ConfigSpec.ConfigRefusal text := by
  unfold NoComments.Config.parseConfigJson at herr
  cases hparse : Json.parse text with
  | error e =>
    exact ConfigRefusal.badJson fun j h => by rw [hparse] at h; cases h
  | ok json =>
    rw [hparse, except_bind_ok] at herr
    cases json with
    | obj obj =>
      rw [show (Json.obj obj).getObj? = .ok obj from rfl, except_bind_ok] at herr
      cases hkeys : NoComments.Config.checkAllowedKeys "config" obj #["workspaces", "exclude", "ratchet"] with
      | error e =>
        have hnot : ¬ ∀ kv ∈ obj.toList, kv.1 ∈ ["workspaces", "exclude", "ratchet"] := fun h => by
          have hok := (checkAllowedKeys_iff "config" obj #["workspaces", "exclude", "ratchet"]).mpr h
          rw [hkeys] at hok
          cases hok
        rcases exists_not_mem_of_not_forall obj.toList ["workspaces", "exclude", "ratchet"] hnot with
          ⟨⟨k, v⟩, hkv, hk⟩
        exact ConfigRefusal.unknownRootKey hparse hkv hk
      | ok u =>
        cases u
        rw [hkeys, except_bind_ok] at herr
        cases hwsReq : NoComments.Config.getRequiredField "config" obj "workspaces" with
        | error e =>
          exact ConfigRefusal.badWorkspacesField hparse fun wsArr h => by
            have hok := (getRequiredField_iff "config" obj "workspaces" (.arr wsArr)).mpr h
            rw [hwsReq] at hok
            cases hok
        | ok wsJson =>
          rw [hwsReq, except_bind_ok] at herr
          rw [getRequiredField_iff] at hwsReq
          cases wsJson with
          | arr wsArr =>
            rw [show (Json.arr wsArr).getArr? = .ok wsArr from rfl, except_bind_ok] at herr
            by_cases hemp : wsArr.isEmpty = true
            · exact ConfigRefusal.badWorkspacesField hparse fun wsArr' h => by
                rw [hwsReq] at h
                injection h with hw
                injection hw with ha
                subst ha
                rw [Array.isEmpty_iff] at hemp
                exact Array.size_eq_zero_iff.mpr hemp
            · have hne_emp : wsArr.isEmpty = false := Bool.eq_false_iff.mpr hemp
              simp only [hne_emp, Bool.false_eq_true, ↓reduceIte] at herr
              have herrWs := parseConfigWorkspaces_extract wsArr _ _ _ herr (fun _ _ _ => rfl)
              cases hloopWs :
                  (forIn' (List.range' 0 wsArr.size 1)
                    (Array.emptyWithCapacity wsArr.size, (#[] : Array String))
                    fun idx h state => do
                      let ws ← NoComments.Config.parseWorkspace idx (wsArr[idx]'(range'_zero_mem h))
                      if state.2.contains ws.dir then
                        throw s!"duplicate workspace dir '{ws.dir}' in config.workspaces"
                      let seen' := state.2.push ws.dir
                      let ws' := state.1.push ws
                      return ForInStep.yield (ws', seen')) with
              | error e =>
                have hspecWs := workspacesLoop_ok_or_err wsArr (List.range' 0 wsArr.size 1)
                  (fun _ h => range'_zero_mem h) (Array.emptyWithCapacity wsArr.size) #[]
                  (by simp [Array.emptyWithCapacity])
                  (by simp [Array.emptyWithCapacity]) (by simp)
                rw [hloopWs] at hspecWs
                rcases hspecWs with ⟨k, hk, hbadWs⟩ | ⟨ws', k, hk, _, prev, hprev, _⟩ |
                    ⟨k1, k2, hk1, hk2, ws1, ws2, hne, hv1, hv2, hdir⟩
                · have hk' : k < wsArr.size := by simpa using hk
                  have hgi : (List.range' 0 wsArr.size 1)[k] = k := range'_zero_getElem _ _ hk
                  dsimp only at hbadWs
                  exact ConfigRefusal.invalidWorkspace hk' hparse hwsReq
                    (by simpa [hgi] using hbadWs)
                · simp [Array.emptyWithCapacity] at hprev
                · have hk1' : k1 < wsArr.size := by simpa using hk1
                  have hk2' : k2 < wsArr.size := by simpa using hk2
                  have hg1 : (List.range' 0 wsArr.size 1)[k1] = k1 := range'_zero_getElem _ _ hk1
                  have hg2 : (List.range' 0 wsArr.size 1)[k2] = k2 := range'_zero_getElem _ _ hk2
                  exact ConfigRefusal.duplicateWorkspaceDir hk1' hk2' hparse hwsReq hne
                    (by simpa [hg1] using hv1) (by simpa [hg2] using hv2) hdir
              | ok stateWs =>
                rw [hloopWs, except_bind_ok] at herrWs
                cases hopt : obj.get? "exclude" with
                | none =>
                  rw [hopt] at herrWs
                  rw [show (pure #[] : Except String (Array NoComments.Config.ExcludeRule)) = .ok #[] from rfl,
                    except_bind_ok] at herrWs
                  dsimp only at herrWs
                  exact parseConfigRatchetSuffix_err text msg obj stateWs.1 #[] hparse herrWs
                | some v =>
                  rw [hopt] at herrWs
                  cases v with
                  | arr exclArr =>
                    dsimp only at herrWs
                    rw [show (Json.arr exclArr).getArr? = .ok exclArr from rfl, except_bind_ok] at herrWs
                    have herrEx := parseConfigExclude_extract exclArr _ _ _ herrWs
                      (fun idx h __s => rfl)
                    have hspecEx := excludeLoop_ok_or_err exclArr (List.range' 0 exclArr.size 1)
                      (fun _ h => range'_zero_mem h) (Array.emptyWithCapacity exclArr.size)
                    cases hloopEx :
                        (forIn' (List.range' 0 exclArr.size 1) (Array.emptyWithCapacity exclArr.size)
                          fun idx h rules => do
                            return ForInStep.yield
                              (rules.push (← NoComments.Config.parseExcludeRule idx
                                (exclArr[idx]'(range'_zero_mem h))))) with
                    | ok rules =>
                      rw [hloopEx, except_bind_ok] at herrEx
                      rw [show (pure rules : Except String (Array NoComments.Config.ExcludeRule)) = .ok rules from rfl,
                        except_bind_ok] at herrEx
                      exact parseConfigRatchetSuffix_err text msg obj stateWs.1 rules hparse herrEx
                    | error e'' =>
                      rw [hloopEx] at hspecEx
                      rcases hspecEx with ⟨k, hk, hbadEx⟩
                      have hk' : k < exclArr.size := by simpa using hk
                      have hgi : (List.range' 0 exclArr.size 1)[k] = k := range'_zero_getElem _ _ hk
                      dsimp only at hbadEx
                      exact ConfigRefusal.invalidExcludeRule hk' hparse hopt
                        (by simpa [hgi] using hbadEx)
                  | _ =>
                    exact ConfigRefusal.badExcludeField hparse hopt fun arr h => by cases h
          | _ =>
            exact ConfigRefusal.badWorkspacesField hparse fun wsArr h => by
              rw [hwsReq] at h
              cases h
    | _ =>
      exact ConfigRefusal.notObject hparse fun obj h => by cases h

theorem parseConfigJson_meets :
    parseConfigRecord.Meets NoComments.Config.parseConfigJson := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact parseConfigJson_ok
  rcases List.mem_cons.mp hp with rfl | hp
  · exact parseConfigJson_err
  exact nomatch hp

theorem parseConfigJson_refines :
    Refines parseConfigRecord (fun f => f) (· = NoComments.Config.parseConfigJson) :=
  fun _ hf _ => hf ▸ parseConfigJson_meets.2

theorem parseConfigJson_fulfilled :
    parseConfigRecord.Fulfilled NoComments.Config.parseConfigJson :=
  fulfils parseConfigJson_refines rfl

theorem matchWorkspace_eq (w : NoComments.Config.WorkspaceConfig) (relPath : String) :
    NoComments.Config.matchWorkspace w relPath = ConfigSpec.MatchWorkspace w relPath := by
  unfold NoComments.Config.matchWorkspace ConfigSpec.MatchWorkspace
  dsimp only [bind, Option.bind]
  cases hd : (w.dir == ".") with
  | true =>
    simp only [↓reduceIte]
    have hany :
        (w.excludePrefixes.any fun x => NoComments.Config.prefixMatches relPath x) =
          (w.excludePrefixes.any fun x => ConfigSpec.PrefixMatches relPath x) := by
      congr 1
      funext x
      exact prefixMatches_eq relPath x
    rw [hany]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hp : relPath.startsWith (w.dir ++ "/") =
        (w.dir.toList ++ ['/']).isPrefixOf relPath.toList := by
      rw [Bool.eq_iff_iff, startsWith_string_iff, String.toList_append]
      rfl
    rw [hp]
    cases (w.dir.toList ++ ['/']).isPrefixOf relPath.toList with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      have hws : (relPath.drop (w.dir ++ "/").length).toString =
          String.ofList (relPath.toList.drop (w.dir.toList ++ ['/']).length) := by
        apply String.ext
        have hslice : (relPath.drop (w.dir ++ "/").length).toString =
            (relPath.drop (w.dir ++ "/").length).copy := rfl
        have hlen : (w.dir ++ "/").length = (w.dir.toList ++ ['/']).length := by
          rw [← String.length_toList, String.toList_append]
          rfl
        rw [hslice, String.toList_copy_drop, String.toList_ofList, hlen]
      rw [hws]
      have hany :
          (w.excludePrefixes.any fun x =>
            NoComments.Config.prefixMatches
              (String.ofList (relPath.toList.drop (w.dir.toList ++ ['/']).length)) x) =
            (w.excludePrefixes.any fun x =>
              ConfigSpec.PrefixMatches
                (String.ofList (relPath.toList.drop (w.dir.toList ++ ['/']).length)) x) := by
        congr 1
        funext x
        exact prefixMatches_eq _ x
      rw [hany]

private theorem exclMatchesLoop_eq (relPath : String)
    (rules : List NoComments.Config.ExcludeRule)
    (init : Array NoComments.Config.ExcludeRule) :
    ∃ out : Array NoComments.Config.ExcludeRule,
      (forIn rules init fun rule __s =>
        if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
          pure (ForInStep.yield (__s.push rule))
        else
          pure (ForInStep.yield __s) :
            Except String (Array NoComments.Config.ExcludeRule)) = .ok out ∧
      out.toList =
        init.toList ++ (rules.filter fun r => ConfigSpec.PrefixMatches relPath r.prefix_) := by
  induction rules generalizing init with
  | nil =>
    refine ⟨init, ?_, by simp⟩
    rw [List.forIn_nil]
    rfl
  | cons r rest ih =>
    have hstep :
        (forIn (r :: rest) init fun rule __s =>
          if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
            pure (ForInStep.yield (__s.push rule))
          else
            pure (ForInStep.yield __s) :
            Except String (Array NoComments.Config.ExcludeRule)) =
        (forIn rest
          (if NoComments.Config.prefixMatches relPath r.prefix_ = true then init.push r else init)
          fun rule __s =>
            if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
              pure (ForInStep.yield (__s.push rule))
            else
              pure (ForInStep.yield __s)) := by
      rw [List.forIn_cons]
      cases NoComments.Config.prefixMatches relPath r.prefix_ <;> rfl
    rw [hstep]
    rcases ih (if NoComments.Config.prefixMatches relPath r.prefix_ = true then init.push r else init) with
      ⟨out, hok, hlist⟩
    refine ⟨out, hok, ?_⟩
    rw [hlist, prefixMatches_eq]
    by_cases hpm : ConfigSpec.PrefixMatches relPath r.prefix_ = true
    · simp [hpm, Array.toList_push, List.append_assoc]
    · have hf : ConfigSpec.PrefixMatches relPath r.prefix_ = false := Bool.eq_false_iff.mpr hpm
      simp [hf]

private theorem wsMatchesLoop_eq (wsArr : Array NoComments.Config.WorkspaceConfig) (relPath : String)
    (idxs : List Nat) (hidxs : ∀ i ∈ idxs, i < wsArr.size)
    (init : Array (NoComments.Config.WorkspaceConfig × Nat × String)) :
    ∃ out : Array (NoComments.Config.WorkspaceConfig × Nat × String),
      (forIn' idxs init fun idx h __s =>
        match NoComments.Config.matchWorkspace (wsArr[idx]'(hidxs idx h)) relPath with
        | some wsRel => pure (ForInStep.yield (__s.push (wsArr[idx]'(hidxs idx h), idx, wsRel)))
        | none => pure (ForInStep.yield __s) :
          Except String (Array (NoComments.Config.WorkspaceConfig × Nat × String))) = .ok out ∧
      out.toList =
        init.toList ++
          idxs.filterMap fun idx =>
            if h : idx < wsArr.size then
              (ConfigSpec.MatchWorkspace wsArr[idx] relPath).map fun r => (wsArr[idx], idx, r)
            else none := by
  induction idxs generalizing init with
  | nil =>
    refine ⟨init, ?_, by simp⟩
    rw [List.forIn'_nil]
    rfl
  | cons idx rest ih =>
    have hidx_lt : idx < wsArr.size := hidxs idx (List.mem_cons_self ..)
    have hrest : ∀ j ∈ rest, j < wsArr.size := fun j hj => hidxs j (List.mem_cons_of_mem idx hj)
    have hstep :
        (forIn' (idx :: rest) init fun idx' h __s =>
          match NoComments.Config.matchWorkspace (wsArr[idx']'(hidxs idx' h)) relPath with
          | some wsRel => pure (ForInStep.yield (__s.push (wsArr[idx']'(hidxs idx' h), idx', wsRel)))
          | none => pure (ForInStep.yield __s) :
            Except String (Array (NoComments.Config.WorkspaceConfig × Nat × String))) =
        (forIn' rest
          (match NoComments.Config.matchWorkspace wsArr[idx] relPath with
          | some wsRel => init.push (wsArr[idx], idx, wsRel)
          | none => init)
          fun idx' h __s =>
            match NoComments.Config.matchWorkspace (wsArr[idx']'(hrest idx' h)) relPath with
            | some wsRel =>
              pure (ForInStep.yield (__s.push (wsArr[idx']'(hrest idx' h), idx', wsRel)))
            | none => pure (ForInStep.yield __s)) := by
      rw [List.forIn'_cons]
      cases NoComments.Config.matchWorkspace wsArr[idx] relPath <;>
        simp [bind, Except.bind, pure, Except.pure]
    rw [hstep]
    rcases ih hrest
      (match NoComments.Config.matchWorkspace wsArr[idx] relPath with
      | some wsRel => init.push (wsArr[idx], idx, wsRel)
      | none => init) with ⟨out, hok, hlist⟩
    refine ⟨out, hok, ?_⟩
    rw [hlist, matchWorkspace_eq]
    simp only [hidx_lt, ↓reduceDIte, List.filterMap_cons]
    cases ConfigSpec.MatchWorkspace wsArr[idx] relPath with
    | none => simp
    | some wsRel => simp [Array.toList_push, List.append_assoc]

private theorem list_filterMap_congr {α β : Type} (l : List α) (f g : α → Option β)
    (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.filterMap_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem zipIdx_eq_range_getElem {α β : Type} (arr : Array α) (f : α → Nat → Option β) :
    (arr.toList.zipIdx.filterMap fun (w, idx) => f w idx) =
      (List.range' 0 arr.size 1).filterMap fun idx =>
        if h : idx < arr.size then f arr[idx] idx else none := by
  have haux :
      ∀ (k : Nat) (l : List α),
        (l.zipIdx k).filterMap (fun (w, idx) => f w idx) =
          (List.range' k l.length 1).filterMap fun idx =>
            if h : idx - k < l.length then f l[idx - k] idx else none := by
    intro k l
    induction l generalizing k with
    | nil => simp
    | cons a rest ih =>
      simp only [List.zipIdx_cons, List.filterMap_cons, List.length_cons, List.range'_succ]
      have h0 : 0 < rest.length + 1 := Nat.zero_lt_succ rest.length
      simp only [Nat.sub_self, h0, ↓reduceDIte, List.getElem_cons_zero]
      cases f a k with
      | none =>
        dsimp only
        rw [ih (k + 1)]
        apply list_filterMap_congr
        intro idx hmem
        rw [List.mem_range'_1] at hmem
        have hlt1 : idx - (k + 1) < rest.length := by omega
        have hdiff : idx - k = (idx - (k + 1)) + 1 := by omega
        simp [hlt1, hdiff]
      | some v =>
        dsimp only
        congr 1
        rw [ih (k + 1)]
        apply list_filterMap_congr
        intro idx hmem
        rw [List.mem_range'_1] at hmem
        have hlt1 : idx - (k + 1) < rest.length := by omega
        have hdiff : idx - k = (idx - (k + 1)) + 1 := by omega
        simp [hlt1, hdiff]
  have hz := haux 0 arr.toList
  change (arr.toList.zipIdx.filterMap fun (w, idx) => f w idx) = _
  simp only [Array.length_toList, Nat.sub_zero] at hz
  rw [hz]
  apply list_filterMap_congr
  intro idx _
  by_cases hi : idx < arr.size <;> simp [hi]

private theorem classifyWorkspaces_extract
    (wsArr : Array NoComments.Config.WorkspaceConfig) (relPath : String)
    (body : (idx : Nat) → idx ∈ [:wsArr.size] →
      Array (NoComments.Config.WorkspaceConfig × Nat × String) →
      Except String (ForInStep (Array (NoComments.Config.WorkspaceConfig × Nat × String))))
    (k : Array (NoComments.Config.WorkspaceConfig × Nat × String) →
      Except String NoComments.Config.ClassifiedFile)
    (res : Except String NoComments.Config.ClassifiedFile)
    (heq : (forIn' [:wsArr.size] #[] body >>= k) = res)
    (hbody : ∀ idx h __s,
      body idx h __s =
        match NoComments.Config.matchWorkspace wsArr[idx] relPath with
        | some wsRel => pure (ForInStep.yield (__s.push (wsArr[idx], idx, wsRel)))
        | none => pure (ForInStep.yield __s)) :
    ∃ out : Array (NoComments.Config.WorkspaceConfig × Nat × String),
      k out = res ∧
      out.toList =
        wsArr.toList.zipIdx.filterMap fun (w, idx) =>
          (ConfigSpec.MatchWorkspace w relPath).map fun r => (w, idx, r) := by
  rcases wsMatchesLoop_eq wsArr relPath (List.range' 0 wsArr.size 1)
    (fun _ h => range'_zero_mem h) #[] with ⟨out, hwsOk, hwsList⟩
  refine ⟨out, ?_, ?_⟩
  · have hloop : forIn' [:wsArr.size] #[] body = .ok out := by
      have hbase := @Std.Legacy.Range.forIn'_eq_forIn'_range'
      rw [hbase]
      simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      rw [← hwsOk]
      congr 1
      funext idx h __s
      exact hbody idx _ __s
    rw [hloop, except_bind_ok] at heq
    exact heq
  · rw [hwsList]
    simp only [List.nil_append]
    exact (zipIdx_eq_range_getElem wsArr
      (fun w idx => (ConfigSpec.MatchWorkspace w relPath).map fun r => (w, idx, r))).symm

theorem classifyFile_ok (cfg : NoComments.Config.RepoConfig) (relPath : String)
    (out : NoComments.Config.ClassifiedFile)
    (hok : NoComments.Config.classifyFile cfg relPath = .ok out) :
    ConfigSpec.ClassifyOutcome cfg relPath out := by
  unfold NoComments.Config.classifyFile at hok
  unfold ConfigSpec.ClassifyOutcome
  dsimp only at hok
  rcases exclMatchesLoop_eq relPath cfg.exclude.toList #[] with ⟨exclMatches, hexOk, hexList⟩
  have hexFor :
      (forIn cfg.exclude #[] fun rule __s =>
        if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
          pure (ForInStep.yield (__s.push rule))
        else
          pure (ForInStep.yield __s) :
            Except String (Array NoComments.Config.ExcludeRule)) = .ok exclMatches := by
    rw [← Array.forIn_toList]
    exact hexOk
  have hforEx' :
      (forIn cfg.exclude #[] fun rule __s =>
        have exclMatches := __s
        if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
          have exclMatches := exclMatches.push rule
          pure (ForInStep.yield exclMatches)
        else
          pure (ForInStep.yield exclMatches) :
            Except String (Array NoComments.Config.ExcludeRule)) = .ok exclMatches :=
    hexFor
  rw [hforEx', except_bind_ok] at hok
  simp only [List.nil_append] at hexList
  cases hlistEx : exclMatches.toList with
  | cons rule tail =>
    cases tail with
    | nil =>
      rw [hlistEx] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst hok
      left
      refine ⟨rule, ?_, rfl⟩
      rw [← hexList, hlistEx]
    | cons rule2 tail2 =>
      rw [hlistEx] at hok
      simp [throw, throwThe, MonadExceptOf.throw] at hok
  | nil =>
    have hexEmpty : (cfg.exclude.toList.filter fun r => ConfigSpec.PrefixMatches relPath r.prefix_) = [] := by
      rw [← hexList, hlistEx]
    rw [hlistEx] at hok
    dsimp only at hok
    rcases classifyWorkspaces_extract cfg.workspaces relPath _ _ _ hok
      (fun idx _ _ => by cases NoComments.Config.matchWorkspace cfg.workspaces[idx] relPath <;> rfl) with
      ⟨wsMatches, hok', hzip⟩
    cases hlistWs : wsMatches.toList with
    | nil =>
      rw [hlistWs] at hok'
      simp [throw, throwThe, MonadExceptOf.throw] at hok'
    | cons hit tail =>
      cases tail with
      | nil =>
        rcases hit with ⟨ws, wsIdx, wsRel⟩
        rw [hlistWs] at hok'
        simp only [pure, Except.pure, Except.ok.injEq] at hok'
        subst hok'
        right
        refine ⟨hexEmpty, ws, wsIdx, wsRel, ?_, ?_⟩
        · rw [← hzip, hlistWs]
        · congr 1
          congr 1
          funext x
          exact prefixMatches_eq wsRel x
      | cons hit2 tail2 =>
        rw [hlistWs] at hok'
        simp [throw, throwThe, MonadExceptOf.throw] at hok'

private theorem filterMap_zipIdx_len {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → Nat → β → γ) :
    (l.filterMap f).length =
      (l.zipIdx.filterMap fun (a, i) => (f a).map (g a i)).length := by
  have haux :
      ∀ k (xs : List α),
        (xs.filterMap f).length =
          ((xs.zipIdx k).filterMap fun (a, i) => (f a).map (g a i)).length := by
    intro k xs
    induction xs generalizing k with
    | nil => simp
    | cons a rest ih =>
      simp only [List.filterMap_cons, List.zipIdx_cons]
      cases f a with
      | none => simp [ih (k + 1)]
      | some b => simp [ih (k + 1)]
  exact haux 0 l

theorem classifyFile_err (cfg : NoComments.Config.RepoConfig) (relPath msg : String)
    (herr : NoComments.Config.classifyFile cfg relPath = .error msg) :
    ConfigSpec.ClassifyRefusal cfg relPath := by
  unfold NoComments.Config.classifyFile at herr
  dsimp only at herr
  rcases exclMatchesLoop_eq relPath cfg.exclude.toList #[] with ⟨exclMatches, hexOk, hexList⟩
  have hexFor :
      (forIn cfg.exclude #[] fun rule __s =>
        if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
          pure (ForInStep.yield (__s.push rule))
        else
          pure (ForInStep.yield __s) :
            Except String (Array NoComments.Config.ExcludeRule)) = .ok exclMatches := by
    rw [← Array.forIn_toList]
    exact hexOk
  have hforEx' :
      (forIn cfg.exclude #[] fun rule __s =>
        have exclMatches := __s
        if NoComments.Config.prefixMatches relPath rule.prefix_ = true then
          have exclMatches := exclMatches.push rule
          pure (ForInStep.yield exclMatches)
        else
          pure (ForInStep.yield exclMatches) :
            Except String (Array NoComments.Config.ExcludeRule)) = .ok exclMatches :=
    hexFor
  rw [hforEx', except_bind_ok] at herr
  simp only [List.nil_append] at hexList
  cases hlistEx : exclMatches.toList with
  | cons rule tail =>
    cases tail with
    | nil =>
      rw [hlistEx] at herr
      cases herr
    | cons rule2 tail2 =>
      apply ClassifyRefusal.ambiguousExclude
      rw [← hexList, hlistEx]
      simp
  | nil =>
    have hexEmpty : (cfg.exclude.toList.filter fun r => ConfigSpec.PrefixMatches relPath r.prefix_) = [] := by
      rw [← hexList, hlistEx]
    rw [hlistEx] at herr
    dsimp only at herr
    rcases classifyWorkspaces_extract cfg.workspaces relPath _ _ _ herr
      (fun idx _ _ => by cases NoComments.Config.matchWorkspace cfg.workspaces[idx] relPath <;> rfl) with
      ⟨wsMatches, herr', hzip⟩
    have hlenWs :
        (cfg.workspaces.toList.filterMap fun w => ConfigSpec.MatchWorkspace w relPath).length =
          wsMatches.toList.length := by
      rw [hzip]
      exact filterMap_zipIdx_len cfg.workspaces.toList
        (fun w => ConfigSpec.MatchWorkspace w relPath) (fun w idx r => (w, idx, r))
    cases hlistWs : wsMatches.toList with
    | nil =>
      apply ClassifyRefusal.unmatched hexEmpty
      rw [← List.length_eq_zero_iff, hlenWs, hlistWs]
      rfl
    | cons hit tail =>
      cases tail with
      | nil =>
        rw [hlistWs] at herr'
        cases herr'
      | cons hit2 tail2 =>
        apply ClassifyRefusal.ambiguousWorkspace hexEmpty
        rw [hlenWs, hlistWs]
        simp

theorem classifyFile_meets :
    classifyFileRecord.Meets NoComments.Config.classifyFile := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact classifyFile_ok
  rcases List.mem_cons.mp hp with rfl | hp
  · exact classifyFile_err
  exact nomatch hp

theorem classifyFile_refines :
    Refines classifyFileRecord (fun f => f) (· = NoComments.Config.classifyFile) :=
  fun _ hf _ => hf ▸ classifyFile_meets.2

theorem classifyFile_fulfilled :
    classifyFileRecord.Fulfilled NoComments.Config.classifyFile :=
  fulfils classifyFile_refines rfl

private theorem mapM_ok_or_err {α β : Type} (f : α → Except String β) (l : List α)
    (init : Array β) :
    match l.foldlM (fun bs a => bs.push <$> f a) init with
    | .ok out =>
      ∃ added : List β,
        added.length = l.length ∧
        (∀ (i : Nat) (h : i < l.length), ∃ (ha : i < added.length), f l[i] = .ok added[i]) ∧
        out.toList = init.toList ++ added
    | .error msg =>
      ∃ a ∈ l, f a = .error msg := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure]
    exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero i), by simp⟩
  | cons a rest ih =>
    simp only [List.foldlM_cons]
    cases hfa : f a with
    | error e =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      exact ⟨a, List.mem_cons_self .., hfa⟩
    | ok b =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      change
        match rest.foldlM (fun bs x => bs.push <$> f x) (init.push b) with
        | .ok out => _
        | .error msg => _
      have hih := ih (init.push b)
      cases hfold : rest.foldlM (fun bs x => bs.push <$> f x) (init.push b) with
      | error e =>
        rw [hfold] at hih
        rcases hih with ⟨x, hx, hfx⟩
        exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩
      | ok out =>
        rw [hfold] at hih
        rcases hih with ⟨added, hlen, hidx, hout⟩
        refine ⟨b :: added, by simp [hlen], fun i hi => ?_, ?_⟩
        · cases i with
          | zero => exact ⟨Nat.zero_lt_succ added.length, by simpa using hfa⟩
          | succ i' =>
            have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
            rcases hidx i' hi' with ⟨ha', hfi⟩
            exact ⟨Nat.succ_lt_succ ha', hfi⟩
        · rw [hout, Array.toList_push, List.append_assoc]
          rfl

theorem classifyTrackedFiles_ok (cfg : NoComments.Config.RepoConfig) (tracked : Array String)
    (out : Array NoComments.Config.ClassifiedFile)
    (hok : NoComments.Config.classifyTrackedFiles cfg tracked = .ok out) :
    ConfigSpec.ClassifyTrackedOutcome cfg tracked out := by
  unfold NoComments.Config.classifyTrackedFiles at hok
  rw [array_mapM_iff] at hok
  refine ⟨hok.1, fun i hi => ?_⟩
  rcases hok.2 i hi with ⟨ho, hfi⟩
  exact ⟨ho, classifyFile_ok cfg tracked[i] out[i] hfi⟩

theorem classifyTrackedFiles_err (cfg : NoComments.Config.RepoConfig) (tracked : Array String)
    (msg : String)
    (herr : NoComments.Config.classifyTrackedFiles cfg tracked = .error msg) :
    ConfigSpec.ClassifyTrackedRefusal cfg tracked := by
  unfold NoComments.Config.classifyTrackedFiles at herr
  rw [Array.mapM_eq_foldlM, ← Array.foldlM_toList] at herr
  have hspec := mapM_ok_or_err (NoComments.Config.classifyFile cfg) tracked.toList #[]
  rw [herr] at hspec
  rcases hspec with ⟨relPath, hmem, herr1⟩
  exact ⟨relPath, hmem, classifyFile_err cfg relPath msg herr1⟩

theorem classifyTrackedFiles_meets :
    classifyTrackedRecord.Meets NoComments.Config.classifyTrackedFiles := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact classifyTrackedFiles_ok
  rcases List.mem_cons.mp hp with rfl | hp
  · exact classifyTrackedFiles_err
  exact nomatch hp

theorem classifyTrackedFiles_refines :
    Refines classifyTrackedRecord (fun f => f) (· = NoComments.Config.classifyTrackedFiles) :=
  fun _ hf _ => hf ▸ classifyTrackedFiles_meets.2

theorem classifyTrackedFiles_fulfilled :
    classifyTrackedRecord.Fulfilled NoComments.Config.classifyTrackedFiles :=
  fulfils classifyTrackedFiles_refines rfl

end NoCommentsSpecification.Refinement.Config
