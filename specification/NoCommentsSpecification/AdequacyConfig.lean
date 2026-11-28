module

import all Init.Data.String.Legacy
import all Init.Data.String.Basic
public import LeanIntent.Obligations
public import LeanIntent.Pairs
public import LeanIntent.Progress
public import NoCommentsSpecification.Healthy
public import NoCommentsSpecification.ConfigRecords

@[expose] public section

namespace NoCommentsSpecification.AdequacyConfig

open Lean
open LeanIntent
open NoComments
open NoCommentsSpecification
open NoCommentsSpecification.ConfigSpec
open NoCommentsSpecification.ConfigRecords

theorem healthy_cleanStr_eq (s : String) : Healthy.cleanStr s = cleanStr s := rfl

theorem healthy_stripDotSlashChars_eq (cs : List Char) :
    Healthy.stripDotSlashChars cs = stripDotSlashChars cs := by
  cases cs with
  | nil => simp [Healthy.stripDotSlashChars, stripDotSlashChars]
  | cons c1 rest1 =>
    cases rest1 with
    | nil => simp [Healthy.stripDotSlashChars, stripDotSlashChars]
    | cons c2 rest2 =>
      by_cases h1 : c1 = '.'
      · subst h1
        by_cases h2 : c2 = '/'
        · subst h2
          simpa [Healthy.stripDotSlashChars, stripDotSlashChars] using
            healthy_stripDotSlashChars_eq rest2
        · simp [Healthy.stripDotSlashChars, stripDotSlashChars, h2]
      · simp [Healthy.stripDotSlashChars, stripDotSlashChars, h1]

theorem healthy_stripTrailingSlashRev_eq (cs : List Char) :
    Healthy.stripTrailingSlashRev cs = stripTrailingSlashRev cs := by
  cases cs with
  | nil => simp [Healthy.stripTrailingSlashRev, stripTrailingSlashRev]
  | cons c1 rest1 =>
    cases rest1 with
    | nil => simp [Healthy.stripTrailingSlashRev, stripTrailingSlashRev]
    | cons c2 rest2 =>
      by_cases h : c1 = '/'
      · subst h
        simpa [Healthy.stripTrailingSlashRev, stripTrailingSlashRev] using
          healthy_stripTrailingSlashRev_eq (c2 :: rest2)
      · simp [Healthy.stripTrailingSlashRev, stripTrailingSlashRev, h]

theorem healthy_stripDotSlash_eq (s : String) :
    Healthy.stripDotSlash s = stripDotSlash s := by
  dsimp [Healthy.stripDotSlash, stripDotSlash]
  rw [healthy_stripDotSlashChars_eq]

theorem healthy_stripTrailingSlashes_eq (s : String) :
    Healthy.stripTrailingSlashes s = stripTrailingSlashes s := by
  dsimp [Healthy.stripTrailingSlashes, stripTrailingSlashes]
  rw [healthy_stripTrailingSlashRev_eq]

theorem healthy_validSegmentsBool_eq (s : String) :
    Healthy.validSegmentsBool s = validSegmentsBool s := rfl

theorem healthy_validRelDir_iff (raw out : String) :
    Healthy.ValidRelDir raw out ↔ NormRelDir raw out := by
  simp only [Healthy.ValidRelDir, NormRelDir, healthy_cleanStr_eq,
    healthy_stripDotSlash_eq, healthy_stripTrailingSlashes_eq, healthy_validSegmentsBool_eq]

theorem healthy_validRelFile_iff (raw out : String) :
    Healthy.ValidRelFile raw out ↔ NormRelFile raw out := by
  simp only [Healthy.ValidRelFile, NormRelFile, healthy_cleanStr_eq,
    healthy_stripDotSlash_eq, healthy_validSegmentsBool_eq]

theorem healthy_validPrefix_iff (raw out : String) :
    Healthy.ValidPrefix raw out ↔ NormPrefix raw out := by
  simp only [Healthy.ValidPrefix, NormPrefix, healthy_cleanStr_eq,
    healthy_stripDotSlash_eq, healthy_validSegmentsBool_eq]

theorem healthy_prefixMatches_eq (path pfx : String) :
    Healthy.prefixMatches path pfx = PrefixMatches path pfx := rfl

theorem healthy_matchWsRel_eq (w : Config.WorkspaceConfig) (relPath : String) :
    Healthy.matchWsRel w relPath = MatchWorkspace w relPath := rfl

theorem normRelDir_unique {raw out1 out2 : String}
    (h1 : NormRelDir raw out1) (h2 : NormRelDir raw out2) : out1 = out2 := by
  rcases h1 with ⟨_, _, _, (⟨hc1, rfl⟩ | ⟨hne1, hne2, _, rfl⟩)⟩ <;>
    rcases h2 with ⟨_, _, _, (⟨hc2, rfl⟩ | ⟨hne3, hne4, _, rfl⟩)⟩
  · rfl
  · simp only [Bool.or_eq_true, beq_iff_eq] at hc1
    rcases hc1 with hc1 | hc1
    · exact absurd hc1 hne3
    · exact absurd hc1 hne4
  · simp only [Bool.or_eq_true, beq_iff_eq] at hc2
    rcases hc2 with hc2 | hc2
    · exact absurd hc2 hne1
    · exact absurd hc2 hne2
  · rfl

theorem normRelFile_unique {raw out1 out2 : String}
    (h1 : NormRelFile raw out1) (h2 : NormRelFile raw out2) : out1 = out2 := by
  rcases h1 with ⟨_, _, _, _, _, _, _, rfl⟩
  rcases h2 with ⟨_, _, _, _, _, _, _, rfl⟩
  rfl

theorem validWorkspaceJson_dir_unique {j : Json} {w1 w2 : Config.WorkspaceConfig}
    (h1 : ValidWorkspaceJson j w1) (h2 : ValidWorkspaceJson j w2) : w1.dir = w2.dir := by
  rcases h1 with ⟨obj1, dir1, rfl, _, hd1, hnr1, _⟩
  rcases h2 with ⟨obj2, dir2, heq, _, hd2, hnr2, _⟩
  cases heq
  rw [hd1] at hd2
  cases hd2
  exact normRelDir_unique hnr1 hnr2

theorem list_not_nodup_iff_dup_idx {α : Type} [DecidableEq α] (xs : List α) :
    ¬ xs.Nodup ↔ ∃ (i j : Nat), ∃ (hi : i < xs.length) (hj : j < xs.length), i ≠ j ∧ xs[i] = xs[j] := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact absurd List.nodup_nil h
    · rintro ⟨i, _, hi, _⟩; simp at hi
  | cons x rest ih =>
    constructor
    · intro hnd
      rw [List.nodup_cons] at hnd
      by_cases hx : x ∈ rest
      · obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
        exact ⟨0, j + 1, by simp, by simp [hj], by omega, by simpa using hxj.symm⟩
      · have hrest : ¬ rest.Nodup := fun h => hnd ⟨hx, h⟩
        obtain ⟨i, j, hi, hj, hne, heq⟩ := ih.mp hrest
        exact ⟨i + 1, j + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hj, by omega, by simpa using heq⟩
    · rintro ⟨i, j, hi, hj, hne, heq⟩ hnd
      rw [List.nodup_cons] at hnd
      cases i with
      | zero =>
        cases j with
        | zero => exact hne rfl
        | succ j' =>
          have hmem : rest[j']'(Nat.lt_of_succ_lt_succ hj) ∈ rest := List.getElem_mem _
          have hx : x = rest[j']'(Nat.lt_of_succ_lt_succ hj) := by simpa using heq
          rw [← hx] at hmem
          exact hnd.1 hmem
      | succ i' =>
        cases j with
        | zero =>
          have hmem : rest[i']'(Nat.lt_of_succ_lt_succ hi) ∈ rest := List.getElem_mem _
          have hx : rest[i']'(Nat.lt_of_succ_lt_succ hi) = x := by simpa using heq
          rw [hx] at hmem
          exact hnd.1 hmem
        | succ j' =>
          exact (ih.mpr ⟨i', j', Nat.lt_of_succ_lt_succ hi, Nat.lt_of_succ_lt_succ hj,
            by omega, by simpa using heq⟩) hnd.2

theorem validConfigJson_total (json : Json) :
    (∃ cfg, ValidConfigJson json cfg) ∨ ConfigRefusal json := by
  cases json with
  | obj obj =>
    by_cases hkeys : ∀ kv ∈ obj.toList, kv.1 ∈ ["workspaces", "exclude", "ratchet"]
    · by_cases hwsf : ∃ wsArr, obj.get? "workspaces" = some (Json.arr wsArr) ∧ wsArr.size > 0
      · rcases hwsf with ⟨wsArr, hwsEq, hwsPos⟩
        by_cases hwsElts : ∀ (i : Nat) (_ : i < wsArr.size), ∃ ws, ValidWorkspaceJson wsArr[i] ws
        · let wss : Array Config.WorkspaceConfig :=
            Array.ofFn fun (idx : Fin wsArr.size) =>
              Classical.choose (hwsElts idx.1 idx.2)
          have hwssSize : wss.size = wsArr.size := Array.size_ofFn
          have hwssValid : ∀ (i : Nat) (h : i < wsArr.size),
              ∃ (hc : i < wss.size), ValidWorkspaceJson wsArr[i] wss[i] := by
            intro i hi
            refine ⟨by omega, ?_⟩
            simpa [wss] using Classical.choose_spec (hwsElts i hi)
          by_cases hnodup : (wss.toList.map (·.dir)).Nodup
          · have hexclCase :
              (∃ excl : Array Config.ExcludeRule,
                match obj.get? "exclude" with
                | some (Json.arr exclArr) =>
                  excl.size = exclArr.size ∧
                    ∀ (i : Nat) (_h : i < exclArr.size),
                      ∃ (_hc : i < excl.size), ValidExcludeJson exclArr[i] excl[i]
                | some _ => False
                | none => excl = #[]) ∨ ConfigRefusal (Json.obj obj) := by
              cases hexcl : obj.get? "exclude" with
              | none => exact .inl ⟨#[], rfl⟩
              | some ev =>
                cases ev with
                | arr exclArr =>
                  by_cases hexElts : ∀ (i : Nat) (_ : i < exclArr.size), ∃ r, ValidExcludeJson exclArr[i] r
                  · let excl : Array Config.ExcludeRule :=
                      Array.ofFn fun (idx : Fin exclArr.size) =>
                        Classical.choose (hexElts idx.1 idx.2)
                    refine .inl ⟨excl, Array.size_ofFn, fun i hi => ⟨by simp [excl]; exact hi, ?_⟩⟩
                    simpa [excl] using Classical.choose_spec (hexElts i hi)
                  · have hexNot : ∃ i, ∃ (_ : i < exclArr.size), ∀ r, ¬ ValidExcludeJson exclArr[i] r := by
                      obtain ⟨i, hni⟩ := Classical.not_forall.mp hexElts
                      obtain ⟨hi, hnr⟩ := Classical.not_forall.mp hni
                      exact ⟨i, hi, fun r hr => hnr ⟨r, hr⟩⟩
                    obtain ⟨i, hi, hnr⟩ := hexNot
                    exact .inr (.invalidExcludeRule hi rfl hexcl hnr)
                | _ =>
                  refine .inr (.badExcludeField rfl hexcl fun _ h => by cases h)
            rcases hexclCase with ⟨excl, hexclOk⟩ | href
            · by_cases hrat : ∃ rRaw rOut, obj.get? "ratchet" = some (Json.str rRaw) ∧ NormRelFile rRaw rOut
              · rcases hrat with ⟨rRaw, rOut, hrEq, hrNorm⟩
                exact .inl ⟨{ workspaces := wss, exclude := excl, ratchet := rOut },
                  obj, wsArr, rRaw, rfl, hkeys, hwsEq, hwsPos, hwssSize, hwssValid, hnodup,
                  hexclOk, hrEq, hrNorm⟩
              · refine .inr (.badRatchetField rfl fun raw out hget hnorm => hrat ⟨raw, out, hget, hnorm⟩)
            · exact .inr href
          · obtain ⟨i, j, hi, hj, hne, heq⟩ := (list_not_nodup_iff_dup_idx (wss.toList.map (·.dir))).mp hnodup
            simp only [List.length_map, Array.length_toList, hwssSize] at hi hj
            have hiw : i < wss.size := by omega
            have hjw : j < wss.size := by omega
            have hv1 : ValidWorkspaceJson wsArr[i] wss[i] := (hwssValid i hi).2
            have hv2 : ValidWorkspaceJson wsArr[j] wss[j] := (hwssValid j hj).2
            have hdirEq : wss[i].dir = wss[j].dir := by
              simpa [List.getElem_map] using heq
            exact .inr (.duplicateWorkspaceDir hi hj rfl hwsEq hne hv1 hv2 hdirEq)
        · have hnot : ∃ i, ∃ (_ : i < wsArr.size), ∀ ws, ¬ ValidWorkspaceJson wsArr[i] ws := by
            obtain ⟨i, hni⟩ := Classical.not_forall.mp hwsElts
            obtain ⟨hi, hnw⟩ := Classical.not_forall.mp hni
            exact ⟨i, hi, fun ws hw => hnw ⟨ws, hw⟩⟩
          obtain ⟨i, hi, hnw⟩ := hnot
          exact .inr (.invalidWorkspace hi rfl hwsEq hnw)
      · refine .inr (.badWorkspacesField rfl fun wsArr hget => Classical.byContradiction fun hnz => ?_)
        exact hwsf ⟨wsArr, hget, Nat.pos_of_ne_zero hnz⟩
    · have hbad : ∃ kv ∈ obj.toList, kv.1 ∉ ["workspaces", "exclude", "ratchet"] := by
        obtain ⟨⟨k, v⟩, hnk⟩ := Classical.not_forall.mp hkeys
        have ⟨hm, hk⟩ := Classical.not_imp.mp hnk
        exact ⟨(k, v), hm, hk⟩
      obtain ⟨⟨k, v⟩, hmem, hk⟩ := hbad
      exact .inr (.unknownRootKey rfl hmem hk)
  | _ => exact .inr (.notObject fun _ h => by cases h)

theorem validConfigJson_and_refusal_disjoint {json : Json} {cfg : Config.RepoConfig}
    (hv : ValidConfigJson json cfg) (hr : ConfigRefusal json) : False := by
  rcases hv with ⟨obj, wsArr, rRaw, rfl, hkeys, hwsEq, hwsPos, hwssSize, hwssValid, hnodup,
    hexcl, hrEq, hrNorm⟩
  cases hr with
  | notObject hno => exact hno obj rfl
  | unknownRootKey heq hget hnin =>
    cases heq
    exact hnin (hkeys _ hget)
  | badWorkspacesField heq hbad =>
    cases heq
    have := hbad wsArr hwsEq
    omega
  | @invalidWorkspace _ _ i hi heq hws2 hnw =>
    cases heq
    rw [hwsEq] at hws2; cases hws2
    obtain ⟨_, hvw⟩ := hwssValid i hi
    exact hnw _ hvw
  | @duplicateWorkspaceDir _ _ i j ws1 ws2 hi hj heq hws2 hne hv1 hv2 hdirEq =>
    cases heq
    rw [hwsEq] at hws2; cases hws2
    obtain ⟨hci, hvi⟩ := hwssValid i hi
    obtain ⟨hcj, hvj⟩ := hwssValid j hj
    have hd1 : ws1.dir = cfg.workspaces[i].dir := validWorkspaceJson_dir_unique hv1 hvi
    have hd2 : ws2.dir = cfg.workspaces[j].dir := validWorkspaceJson_dir_unique hv2 hvj
    have hdup := (list_not_nodup_iff_dup_idx (cfg.workspaces.toList.map (·.dir))).mpr
      ⟨i, j, by simpa [hwssSize] using hi, by simpa [hwssSize] using hj, hne,
        by simp [List.getElem_map, ← hd1, ← hd2, hdirEq]⟩
    exact hdup hnodup
  | badExcludeField heq hget hnot =>
    cases heq
    rw [hget] at hexcl
    cases ‹Json› with
    | arr exclArr => exact hnot exclArr rfl
    | _ => exact hexcl.elim
  | @invalidExcludeRule _ exclArr i hi heq hex2 hnr =>
    cases heq
    rw [hex2] at hexcl
    obtain ⟨_, hve⟩ := hexcl.2 i hi
    exact hnr _ hve
  | badRatchetField heq hbad =>
    cases heq
    exact hbad rRaw cfg.ratchet hrEq hrNorm

theorem healthy_cleanStringList_of_valid {j : Json} {out : Array String}
    (h : ValidCleanStringArray j out) : Healthy.cleanStringList j := by
  rcases h with ⟨arr, rfl, hsz, helts⟩
  refine ⟨arr, rfl, fun item hmem => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < arr.size := by simpa using hi
  obtain ⟨ho, hs, hcl⟩ := helts i hi'
  exact ⟨out[i], by simpa using hs, by simpa [healthy_cleanStr_eq] using hcl⟩

theorem validCleanStringArray_of_healthy {j : Json}
    (h : Healthy.cleanStringList j) : ∃ out, ValidCleanStringArray j out := by
  rcases h with ⟨arr, rfl, helts⟩
  let f : Fin arr.size → String := fun idx =>
    Classical.choose (helts arr[idx.1] (Array.getElem_mem_toList idx.2))
  let out : Array String := Array.ofFn f
  refine ⟨out, arr, rfl, Array.size_ofFn, fun i hi => ⟨by simp [out]; exact hi, ?_⟩⟩
  have hspec := Classical.choose_spec (helts arr[i] (Array.getElem_mem_toList hi))
  have hout : out[i]'(by simp [out]; exact hi) = f ⟨i, hi⟩ := by simp [out]
  rw [hout]
  dsimp [f]
  exact ⟨hspec.1, by simpa [healthy_cleanStr_eq] using hspec.2⟩

theorem healthy_validPrefixList_of_valid {j : Json} {out : Array String}
    (h : ValidPrefixArray j out) : Healthy.validPrefixList j := by
  rcases h with ⟨arr, rfl, _, helts⟩
  refine ⟨arr, rfl, fun item hmem => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < arr.size := by simpa using hi
  obtain ⟨_, raw, hstr, hnp⟩ := helts i hi'
  exact ⟨raw, out[i], by simpa using hstr, (healthy_validPrefix_iff _ _).mpr hnp⟩

theorem validPrefixArray_of_healthy {j : Json}
    (h : Healthy.validPrefixList j) : ∃ out, ValidPrefixArray j out := by
  rcases h with ⟨arr, rfl, helts⟩
  have helts' : ∀ (i : Nat) (_ : i < arr.size), ∃ (p : String × String),
      arr[i] = Json.str p.1 ∧ NormPrefix p.1 p.2 := by
    intro i hi
    obtain ⟨raw, pfx, h1, h2⟩ := helts arr[i] (Array.getElem_mem_toList hi)
    exact ⟨(raw, pfx), h1, (healthy_validPrefix_iff _ _).mp h2⟩
  let out : Array String := Array.ofFn fun idx : Fin arr.size =>
    (Classical.choose (helts' idx.1 idx.2)).2
  refine ⟨out, arr, rfl, Array.size_ofFn, fun i hi => ⟨by simp [out]; exact hi, ?_⟩⟩
  have hspec := Classical.choose_spec (helts' i hi)
  have hout : out[i]'(by simp [out]; exact hi) = (Classical.choose (helts' i hi)).2 := by simp [out]
  rw [hout]
  exact ⟨(Classical.choose (helts' i hi)).1, hspec.1, hspec.2⟩

theorem healthy_workspace_of_valid {j : Json} {ws : Config.WorkspaceConfig}
    (h : ValidWorkspaceJson j ws) : Healthy.ValidWorkspaceJson j ws.dir := by
  rcases h with ⟨obj, dirRaw, rfl, hkeys, hd, hnd, hsrc, hla, htp, hep⟩
  refine ⟨obj, rfl, hkeys, ⟨dirRaw, hd, (healthy_validRelDir_iff _ _).mpr hnd⟩, ?_, ?_, ?_, ?_⟩
  · cases hs : obj.get? "srcDir" with
    | none => trivial
    | some v =>
      rw [hs] at hsrc
      rcases hsrc with ⟨s, rfl, hn⟩
      exact ⟨s, ws.srcDir, rfl, (healthy_validRelDir_iff _ _).mpr hn⟩
  · cases hl : obj.get? "lakeArgs" with
    | none => trivial
    | some v =>
      rw [hl] at hla
      exact healthy_cleanStringList_of_valid hla
  · cases ht : obj.get? "toolPrefixes" with
    | none => trivial
    | some v =>
      rw [ht] at htp
      exact healthy_validPrefixList_of_valid htp
  · cases he : obj.get? "excludePrefixes" with
    | none => trivial
    | some v =>
      rw [he] at hep
      exact healthy_validPrefixList_of_valid hep

theorem validWorkspace_of_healthy {j : Json} {dirOut : String}
    (h : Healthy.ValidWorkspaceJson j dirOut) :
    ∃ ws, ValidWorkspaceJson j ws ∧ ws.dir = dirOut := by
  rcases h with ⟨obj, rfl, hkeys, ⟨dirRaw, hd, hnd⟩, hsrc, hla, htp, hep⟩
  have hsrc' : ∃ srcDir : String, match obj.get? "srcDir" with
      | some v => ∃ srcRaw, v = Json.str srcRaw ∧ NormRelDir srcRaw srcDir
      | none => srcDir = "." := by
    cases hs : obj.get? "srcDir" with
    | none => exact ⟨".", rfl⟩
    | some v =>
      rw [hs] at hsrc
      rcases hsrc with ⟨s, out, rfl, hn⟩
      exact ⟨out, s, rfl, (healthy_validRelDir_iff _ _).mp hn⟩
  have hla' : ∃ lakeArgs : Array String, match obj.get? "lakeArgs" with
      | some v => ValidCleanStringArray v lakeArgs
      | none => lakeArgs = #[] := by
    cases hl : obj.get? "lakeArgs" with
    | none => exact ⟨#[], rfl⟩
    | some v =>
      rw [hl] at hla
      exact validCleanStringArray_of_healthy hla
  have htp' : ∃ toolPrefixes : Array String, match obj.get? "toolPrefixes" with
      | some v => ValidPrefixArray v toolPrefixes
      | none => toolPrefixes = #[] := by
    cases ht : obj.get? "toolPrefixes" with
    | none => exact ⟨#[], rfl⟩
    | some v =>
      rw [ht] at htp
      exact validPrefixArray_of_healthy htp
  have hep' : ∃ excludePrefixes : Array String, match obj.get? "excludePrefixes" with
      | some v => ValidPrefixArray v excludePrefixes
      | none => excludePrefixes = #[] := by
    cases he : obj.get? "excludePrefixes" with
    | none => exact ⟨#[], rfl⟩
    | some v =>
      rw [he] at hep
      exact validPrefixArray_of_healthy hep
  rcases hsrc' with ⟨srcDir, hsrcOk⟩
  rcases hla' with ⟨lakeArgs, hlaOk⟩
  rcases htp' with ⟨toolPrefixes, htpOk⟩
  rcases hep' with ⟨excludePrefixes, hepOk⟩
  let ws : Config.WorkspaceConfig :=
    { dir := dirOut, srcDir := srcDir, lakeArgs := lakeArgs,
      toolPrefixes := toolPrefixes, excludePrefixes := excludePrefixes }
  exact ⟨ws, ⟨obj, dirRaw, rfl, hkeys, hd, (healthy_validRelDir_iff _ _).mp hnd,
    hsrcOk, hlaOk, htpOk, hepOk⟩, rfl⟩

theorem validExclude_iff_healthy (j : Json) :
    (∃ r, ValidExcludeJson j r) ↔ Healthy.ValidExcludeJson j := by
  constructor
  · rintro ⟨r, obj, pfxRaw, reasonRaw, rfl, hkeys, hp, hnp, hr, htrim, hne⟩
    refine ⟨obj, rfl, hkeys, ⟨pfxRaw, r.prefix_, hp, (healthy_validPrefix_iff _ _).mpr hnp⟩,
      ⟨reasonRaw, hr, htrim ▸ hne⟩⟩
  · rintro ⟨obj, rfl, hkeys, ⟨pfxRaw, pfxOut, hp, hnp⟩, ⟨reasonRaw, hr, hne⟩⟩
    exact ⟨{ prefix_ := pfxOut, reason := reasonRaw.trimAscii.toString },
      obj, pfxRaw, reasonRaw, rfl, hkeys, hp, (healthy_validPrefix_iff _ _).mp hnp, hr, rfl, hne⟩

theorem validConfigJson_iff_healthy {json : Json} :
    (∃ cfg, ValidConfigJson json cfg) ↔ Healthy.ConfigJson json := by
  constructor
  · rintro ⟨cfg, obj, wsArr, rRaw, hp, hkeys, hws, hwsPos, hsz, helts, hnd, hexcl, hr, hnr⟩
    refine ⟨obj, wsArr, cfg.workspaces.toList.map (·.dir), rRaw, cfg.ratchet, hp, hkeys, hws,
      hwsPos, by simpa using hsz, hnd, fun i hi => ⟨by simpa [hsz] using hi, ?_⟩, ?_, hr,
      (healthy_validRelFile_iff _ _).mpr hnr⟩
    · obtain ⟨hc, hvw⟩ := helts i hi
      simpa [List.getElem_map] using healthy_workspace_of_valid hvw
    · cases he : obj.get? "exclude" with
      | none => trivial
      | some ev =>
        rw [he] at hexcl
        cases ev with
        | arr exclArr =>
          intro item hmem
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
          obtain ⟨hc, hve⟩ := hexcl.2 i (by simpa using hi)
          exact (validExclude_iff_healthy _).mp ⟨cfg.exclude[i], by simpa using hve⟩
        | _ => exact hexcl.elim
  · rintro ⟨obj, wsArr, dirs, rRaw, rOut, hp, hkeys, hws, hwsPos, hlen, hnd, helts, hexcl, hr, hnr⟩
    have hws' : ∀ (i : Nat) (_ : i < wsArr.size),
        ∃ (hi : i < dirs.length), ∃ ws, ValidWorkspaceJson wsArr[i] ws ∧ ws.dir = dirs[i] := by
      intro i hi
      obtain ⟨hd, hvw⟩ := helts i hi
      exact ⟨hd, validWorkspace_of_healthy hvw⟩
    let wss : Array Config.WorkspaceConfig :=
      Array.ofFn fun idx : Fin wsArr.size =>
        Classical.choose (hws' idx.1 idx.2).2
    have hwssValid : ∀ (i : Nat) (h : i < wsArr.size),
        ∃ (hc : i < wss.size), ValidWorkspaceJson wsArr[i] wss[i] := fun i hi =>
      ⟨by simp [wss]; exact hi, by simpa [wss] using (Classical.choose_spec (hws' i hi).2).1⟩
    have hwssDirs : wss.toList.map (·.dir) = dirs := by
      apply List.ext_getElem
      · simp [wss, hlen]
      · intro i h1 h2
        have hi : i < wsArr.size := by simpa [wss] using h1
        have hs := (Classical.choose_spec (hws' i hi).2).2
        simpa [wss] using hs
    have hex' : ∃ excl : Array Config.ExcludeRule,
        match obj.get? "exclude" with
        | some (Json.arr exclArr) =>
          excl.size = exclArr.size ∧
            ∀ (i : Nat) (_h : i < exclArr.size),
              ∃ (_hc : i < excl.size), ValidExcludeJson exclArr[i] excl[i]
        | some _ => False
        | none => excl = #[] := by
      cases he : obj.get? "exclude" with
      | none => exact ⟨#[], rfl⟩
      | some ev =>
        rw [he] at hexcl
        cases ev with
        | arr exclArr =>
          have helts' : ∀ (i : Nat) (_ : i < exclArr.size), ∃ r, ValidExcludeJson exclArr[i] r := by
            intro i hi
            exact (validExclude_iff_healthy _).mpr (hexcl exclArr[i] (Array.getElem_mem_toList hi))
          let excl : Array Config.ExcludeRule :=
            Array.ofFn fun idx : Fin exclArr.size => Classical.choose (helts' idx.1 idx.2)
          refine ⟨excl, Array.size_ofFn, fun i hi => ⟨by simp [excl]; exact hi, ?_⟩⟩
          simpa [excl] using Classical.choose_spec (helts' i hi)
        | _ => exact hexcl.elim
    obtain ⟨excl, hexOk⟩ := hex'
    refine ⟨{ workspaces := wss, exclude := excl, ratchet := rOut },
      obj, wsArr, rRaw, hp, hkeys, hws, hwsPos, Array.size_ofFn, hwssValid,
      hwssDirs ▸ hnd, hexOk, hr, (healthy_validRelFile_iff _ _).mp hnr⟩

noncomputable def parseConfigModelWith (errMsg : String) : ParseConfigFn :=
  open Classical in
  fun json =>
    if h : ∃ cfg, ValidConfigJson json cfg then .ok (Classical.choose h)
    else .error errMsg

noncomputable def parseConfigModel : ParseConfigFn :=
  parseConfigModelWith "invalid config"

theorem parseConfigModelWith_meets (errMsg : String) :
    parseConfigRecord.Meets (parseConfigModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro json cfg hok
    dsimp [parseConfigModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact Classical.choose_spec h
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro json msg herr
    dsimp [parseConfigModelWith] at herr
    split at herr
    · contradiction
    · rename_i hnv
      rcases validConfigJson_total json with hv | href
      · exact absurd hv hnv
      · exact href
  exact nomatch hp

theorem parseConfigModel_meets : parseConfigRecord.Meets parseConfigModel :=
  parseConfigModelWith_meets "invalid config"

def sampleWorkspaceObj : Std.TreeMap.Raw String Json compare :=
  (Std.TreeMap.Raw.empty : Std.TreeMap.Raw String Json compare).insert "dir" (Json.str ".")

def sampleWorkspaceJson : Json := Json.obj sampleWorkspaceObj

def sampleConfigObj : Std.TreeMap.Raw String Json compare :=
  ((Std.TreeMap.Raw.empty : Std.TreeMap.Raw String Json compare).insert "workspaces"
    (Json.arr #[sampleWorkspaceJson])).insert "ratchet" (Json.str "a")

def sampleConfigJson : Json := Json.obj sampleConfigObj

def sampleParsedWorkspace : Config.WorkspaceConfig where
  dir := "."
  srcDir := "."
  lakeArgs := #[]
  toolPrefixes := #[]
  excludePrefixes := #[]

def sampleParsedConfig : Config.RepoConfig where
  workspaces := #[sampleParsedWorkspace]
  exclude := #[]
  ratchet := "a"

theorem stripDotSlash_eq_self {s : String} (h : stripDotSlashChars s.toList = s.toList) :
    stripDotSlash s = s := by
  unfold stripDotSlash
  rw [h]
  exact String.ofList_toList

theorem stripTrailingSlashes_eq_self {s : String}
    (h : (stripTrailingSlashRev s.toList.reverse).reverse = s.toList) :
    stripTrailingSlashes s = s := by
  unfold stripTrailingSlashes
  rw [h]
  exact String.ofList_toList

theorem splitOn_slash_single_byte (s : String)
    (h0 : String.Pos.Raw.atEnd s 0 = false)
    (hget : (String.Pos.Raw.get s 0 == String.Pos.Raw.get "/" 0) = false)
    (hnext : String.Pos.Raw.next s 0 = ⟨1⟩)
    (h1 : String.Pos.Raw.atEnd s ⟨1⟩ = true)
    (hext : String.Pos.Raw.extract s 0 ⟨1⟩ = s) :
    s.splitOn "/" = [s] := by
  unfold String.splitOn
  have hsep : ("/" == "") = false := by decide
  rw [hsep]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [String.splitOnAux, h0]
  simp only [Bool.false_eq_true, ↓reduceIte, hget]
  have hu : String.Pos.Raw.unoffsetBy 0 0 = 0 := rfl
  rw [hu, hnext, String.splitOnAux, h1]
  simp [hext]

theorem sampleWorkspaceJson_valid :
    ValidWorkspaceJson sampleWorkspaceJson sampleParsedWorkspace := by
  refine ⟨sampleWorkspaceObj, ".", rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · intro kv hmem
    have hkv : kv ∈ [("dir", Json.str ".")] := hmem
    rcases List.mem_singleton.mp hkv with rfl
    decide
  · have h1 : stripDotSlash "." = "." := stripDotSlash_eq_self (by simp only [String.reduceToList]; decide)
    have h2 : stripTrailingSlashes "." = "." := stripTrailingSlashes_eq_self (by
      simp only [String.reduceToList, List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [stripTrailingSlashRev]
      · rfl
      · intro _ _ h; cases h)
    refine ⟨by decide, by decide, by decide, .inl ⟨?_, rfl⟩⟩
    rw [h1, h2]
    decide

theorem sampleConfigJson_valid :
    ValidConfigJson sampleConfigJson sampleParsedConfig := by
  refine ⟨sampleConfigObj, #[sampleWorkspaceJson], "a", rfl, ?_, rfl,
    by decide, rfl, ?_, by decide, rfl, rfl, ?_⟩
  · intro kv hmem
    have hkv : kv ∈ [("ratchet", Json.str "a"),
        ("workspaces", Json.arr #[sampleWorkspaceJson])] := hmem
    rcases List.mem_cons.mp hkv with rfl | hkv
    · decide
    · rcases List.mem_singleton.mp hkv with rfl
      decide
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    exact ⟨by decide, sampleWorkspaceJson_valid⟩
  · have h1 : stripDotSlash "a" = "a" :=
      stripDotSlash_eq_self (by simp only [String.reduceToList]; decide)
    have hsp : "a".splitOn "/" = ["a"] :=
      splitOn_slash_single_byte "a" (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, h1⟩
    · rw [h1]; decide
    · rw [h1]; decide
    · rw [h1, validSegmentsBool, hsp]; decide

theorem null_config_refusal : ConfigRefusal Json.null :=
  .notObject fun _ h => by cases h

theorem parseConfig_o2 : O2 parseConfigRecord := by
  refine (o2_correct _).mpr ⟨⟨parseConfigModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(sampleConfigJson, sampleParsedConfig), sampleConfigJson_valid⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨Json.null, null_config_refusal⟩
  exact nomatch hp

theorem parseConfig_o2Run : O2Run parseConfigRecord :=
  o2Run_of_meets parseConfigModel_meets

theorem parseConfig_o3 : O3 parseConfigRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => .ok sampleParsedConfig, fun h => ?_⟩
    exact validConfigJson_and_refusal_disjoint (h Json.null sampleParsedConfig rfl) null_config_refusal
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ => .error "always", fun h => ?_⟩
    exact validConfigJson_and_refusal_disjoint sampleConfigJson_valid
      (h sampleConfigJson "always" rfl)
  exact nomatch hc

theorem parseConfig_o4 : O4 parseConfigRecord := o4_function _ rfl

def ParseConfigFreedom : Freedom ParseConfigFn :=
  .rel fun f g => ∀ json,
    ((f json).isOk = (g json).isOk) ∧
    (∀ cfg1 cfg2, f json = .ok cfg1 → g json = .ok cfg2 → ValidConfigJson json cfg1 ∧ ValidConfigJson json cfg2)

theorem parseConfig_healthy_owed :
    ∀ f json, parseConfigRecord.Meets f →
      Healthy.ConfigJson json → ∃ cfg, f json = .ok cfg := by
  intro f json hf hh
  cases hfv : f json with
  | ok cfg => exact ⟨cfg, rfl⟩
  | error msg =>
    exfalso
    have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) json msg hfv
    obtain ⟨cfg, hv⟩ := validConfigJson_iff_healthy.mpr hh
    exact validConfigJson_and_refusal_disjoint hv href

theorem parseConfig_o5 : O5 parseConfigRecord ParseConfigFreedom := by
  refine ⟨fun f g hf hg json => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self json
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) json
  have hgok := hg.2 _ List.mem_cons_self json
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) json
  refine ⟨?_, fun cfg1 cfg2 h1 h2 => ⟨hfok cfg1 h1, hgok cfg2 h2⟩⟩
  cases h1 : f json with
  | ok cfg1 =>
    cases h2 : g json with
    | ok _ => rfl
    | error msg =>
      exfalso
      exact validConfigJson_and_refusal_disjoint (hfok cfg1 h1) (hgerr msg h2)
  | error msg =>
    cases h2 : g json with
    | error _ => rfl
    | ok cfg2 =>
      exfalso
      exact validConfigJson_and_refusal_disjoint (hgok cfg2 h2) (hferr msg h1)

theorem parseConfig_not_o5_eq : ¬ O5 parseConfigRecord .eq := by
  refine not_o5_eq parseConfigModel_meets (parseConfigModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun heq Json.null
  have hna : ¬ ∃ cfg, ValidConfigJson Json.null cfg := by
    rintro ⟨cfg, hv⟩
    exact validConfigJson_and_refusal_disjoint hv null_config_refusal
  dsimp [parseConfigModel, parseConfigModelWith] at hdiff
  simp [hna] at hdiff

theorem parseConfig_oPair_whole :
    ∀ c ∈ parseConfigRecord.props, OPair (Pair.whole parseConfigRecord c) parseConfigRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨parseConfigModel, parseConfigModel_meets, fun _ => parseConfigModel_meets.2 c hc⟩

def parseConfigPerInputPair : Pair ParseConfigFn where
  Input := Json
  pre := fun _ => True
  post := fun i f => ∀ cfg, f i = .ok cfg → ValidConfigJson i cfg

theorem parseConfig_perInput_pairOf :
    ∀ c ∈ parseConfigRecord.props, c.name = "ok_valid_repo_config" →
      parseConfigRecord.PairOf c parseConfigPerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, parseConfigRecord, Pair.Met, parseConfigPerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem parseConfig_perInput_table_attack :
    ∀ i : parseConfigPerInputPair.Input, parseConfigPerInputPair.pre i →
      ∃ f : ParseConfigFn, (∀ j, f j = f Json.null) ∧ parseConfigPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ => .error "table", fun _ => rfl, ?_⟩
  intro _ h; contradiction

theorem parseConfig_interim_const_fails :
    ∀ c, ¬ parseConfigRecord.Meets (fun _ => c) := by
  intro c hm
  cases c with
  | ok cfg =>
    have hbad := hm.2 _ List.mem_cons_self Json.null cfg rfl
    exact validConfigJson_and_refusal_disjoint hbad null_config_refusal
  | error msg =>
    have href := hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) sampleConfigJson msg rfl
    exact validConfigJson_and_refusal_disjoint sampleConfigJson_valid href

theorem parseConfig_healthy_nonempty : ∃ json, Healthy.ConfigJson json :=
  ⟨sampleConfigJson, validConfigJson_iff_healthy.mp ⟨sampleParsedConfig, sampleConfigJson_valid⟩⟩

theorem parseConfig_negative_external_model :
    ∃ (f : ParseConfigFn), ∃ json,
      (∀ j cfg, f j = .ok cfg → ValidConfigJson j cfg) ∧
      Healthy.ConfigJson json ∧
      ¬ ∃ cfg, f json = .ok cfg :=
  ⟨fun _ => .error "denied", sampleConfigJson, (fun _ _ h => nomatch h),
    validConfigJson_iff_healthy.mp ⟨sampleParsedConfig, sampleConfigJson_valid⟩,
    fun ⟨_, h⟩ => nomatch h⟩

theorem parseConfig_reason_classified :
    ∀ f json msg, parseConfigRecord.Meets f → f json = .error msg →
      ConfigRefusal json ∧ ¬ Healthy.ConfigJson json := by
  intro f json msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) json msg herr
  exact ⟨href, fun hh =>
    let ⟨_, hv⟩ := validConfigJson_iff_healthy.mpr hh
    validConfigJson_and_refusal_disjoint hv href⟩

theorem filterMap_zipIdx_length {α β : Type} (xs : List α) (f : α → Option β) :
    (xs.zipIdx.filterMap fun p => (f p.1).map fun r => (p.1, p.2, r)).length =
      (xs.filterMap f).length := by
  suffices ∀ (n : Nat),
      (xs.zipIdx n |>.filterMap fun p => (f p.1).map fun r => (p.1, p.2, r)).length =
        (xs.filterMap f).length from this 0
  intro n
  induction xs generalizing n with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases hf : f x with
    | none => simp [ih (n + 1)]
    | some r => simp [ih (n + 1)]

theorem filterMap_zipIdx_nil_iff {α β : Type} (xs : List α) (f : α → Option β) :
    (xs.zipIdx.filterMap fun p => (f p.1).map fun r => (p.1, p.2, r)) = [] ↔
      xs.filterMap f = [] := by
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, filterMap_zipIdx_length]

theorem classifyOutcome_unique {cfg : Config.RepoConfig} {relPath : String} {o1 o2 : Config.ClassifiedFile}
    (h1 : ClassifyOutcome cfg relPath o1) (h2 : ClassifyOutcome cfg relPath o2) : o1 = o2 := by
  dsimp [ClassifyOutcome] at h1 h2
  rcases h1 with ⟨r1, he1, rfl⟩ | ⟨he1, ws1, idx1, wr1, hw1, rfl⟩ <;>
    rcases h2 with ⟨r2, he2, rfl⟩ | ⟨he2, ws2, idx2, wr2, hw2, rfl⟩
  · rw [he1] at he2; cases he2; rfl
  · rw [he2] at he1; cases he1
  · rw [he1] at he2; cases he2
  · rw [hw1] at hw2; cases hw2; rfl

theorem classifyOutcome_and_refusal_disjoint {cfg : Config.RepoConfig} {relPath : String}
    {out : Config.ClassifiedFile}
    (ho : ClassifyOutcome cfg relPath out) (hr : ClassifyRefusal cfg relPath) : False := by
  dsimp [ClassifyOutcome] at ho
  cases hr with
  | ambiguousExclude hlen =>
    rcases ho with ⟨r, he, _⟩ | ⟨he, _⟩
    · rw [he] at hlen; simp at hlen
    · rw [he] at hlen; simp at hlen
  | unmatched he hws =>
    rcases ho with ⟨r, he1, _⟩ | ⟨_, ws, idx, wr, hw, _⟩
    · rw [he] at he1; cases he1
    · have hlen := filterMap_zipIdx_length cfg.workspaces.toList (MatchWorkspace · relPath)
      rw [hws, hw] at hlen
      simp at hlen
  | ambiguousWorkspace he hlen =>
    rcases ho with ⟨r, he1, _⟩ | ⟨_, ws, idx, wr, hw, _⟩
    · rw [he] at he1; cases he1
    · have hlen' := filterMap_zipIdx_length cfg.workspaces.toList (MatchWorkspace · relPath)
      rw [hw] at hlen'
      simp at hlen'
      omega

theorem classifyOutcome_total (cfg : Config.RepoConfig) (relPath : String) :
    (∃ out, ClassifyOutcome cfg relPath out) ∨ ClassifyRefusal cfg relPath := by
  cases hex : cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_ with
  | cons r1 rest =>
    cases rest with
    | nil =>
      exact .inl ⟨.excluded relPath r1, .inl ⟨r1, hex, rfl⟩⟩
    | cons r2 tail =>
      exact .inr (.ambiguousExclude (by rw [hex]; simp))
  | nil =>
    cases hws : cfg.workspaces.toList.zipIdx.filterMap fun p =>
        (MatchWorkspace p.1 relPath).map fun r => (p.1, p.2, r) with
    | nil =>
      have hfm := (filterMap_zipIdx_nil_iff cfg.workspaces.toList (MatchWorkspace · relPath)).mp hws
      exact .inr (.unmatched hex hfm)
    | cons h tail =>
      cases tail with
      | nil =>
        rcases h with ⟨ws, idx, wsRel⟩
        exact .inl ⟨.checked relPath idx wsRel (ws.toolPrefixes.any (PrefixMatches wsRel ·)),
          .inr ⟨hex, ws, idx, wsRel, hws, rfl⟩⟩
      | cons h2 tail2 =>
        have hlen := filterMap_zipIdx_length cfg.workspaces.toList (MatchWorkspace · relPath)
        rw [hws] at hlen
        exact .inr (.ambiguousWorkspace hex (by rw [← hlen]; simp))

theorem healthy_classifyInput_iff (cfg : Config.RepoConfig) (relPath : String) :
    Healthy.ClassifyInput cfg relPath ↔ ∃ out, ClassifyOutcome cfg relPath out := by
  simp only [Healthy.ClassifyInput, ClassifyOutcome, healthy_prefixMatches_eq, healthy_matchWsRel_eq]
  cases hex : cfg.exclude.toList.filter fun r => PrefixMatches relPath r.prefix_ with
  | cons r rest =>
    cases rest with
    | nil =>
      simp only [true_iff]
      exact ⟨.excluded relPath r, .inl ⟨r, rfl, rfl⟩⟩
    | cons _ _ =>
      simp only [false_iff, not_exists]
      intro out h
      rcases h with ⟨_, h1, _⟩ | ⟨h1, _⟩ <;> cases h1
  | nil =>
    have hlen := filterMap_zipIdx_length cfg.workspaces.toList (MatchWorkspace · relPath)
    constructor
    · intro h1
      rw [← hlen, List.length_eq_one_iff] at h1
      obtain ⟨⟨ws, idx, wsRel⟩, hEq⟩ := h1
      exact ⟨.checked relPath idx wsRel (ws.toolPrefixes.any (PrefixMatches wsRel ·)),
        .inr ⟨rfl, ws, idx, wsRel, hEq, rfl⟩⟩
    · rintro ⟨out, ⟨_, h1, _⟩ | ⟨_, ws, idx, wsRel, hEq, _⟩⟩
      · cases h1
      · rw [← hlen, hEq]; rfl

noncomputable def classifyFileModelWith (errMsg : String) : ClassifyFileFn :=
  open Classical in
  fun cfg relPath =>
    if h : ∃ out, ClassifyOutcome cfg relPath out then .ok (Classical.choose h)
    else .error errMsg

noncomputable def classifyFileModel : ClassifyFileFn :=
  classifyFileModelWith "classify failed"

theorem classifyFileModelWith_meets (errMsg : String) :
    classifyFileRecord.Meets (classifyFileModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro cfg relPath out hok
    dsimp [classifyFileModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact Classical.choose_spec h
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro cfg relPath msg herr
    dsimp [classifyFileModelWith] at herr
    split at herr
    · contradiction
    · rename_i hno
      rcases classifyOutcome_total cfg relPath with hok | href
      · exact absurd hok hno
      · exact href
  exact nomatch hp

theorem classifyFileModel_meets : classifyFileRecord.Meets classifyFileModel :=
  classifyFileModelWith_meets "classify failed"

def sampleRepoCfg : Config.RepoConfig where
  workspaces := #[{ dir := ".", srcDir := ".", lakeArgs := #[], toolPrefixes := #[], excludePrefixes := #[] }]
  exclude := #[]
  ratchet := "comment-ratchet.json"

def emptyRepoCfg : Config.RepoConfig where
  workspaces := #[]
  exclude := #[]
  ratchet := "comment-ratchet.json"

theorem sampleRepoCfg_foo_outcome :
    ClassifyOutcome sampleRepoCfg "Foo.lean" (.checked "Foo.lean" 0 "Foo.lean" false) := by
  dsimp [ClassifyOutcome, sampleRepoCfg, MatchWorkspace]
  exact .inr ⟨rfl, sampleRepoCfg.workspaces[0], 0, "Foo.lean", by simp [sampleRepoCfg], by simp [sampleRepoCfg]⟩

theorem emptyRepoCfg_foo_refusal : ClassifyRefusal emptyRepoCfg "Foo.lean" :=
  .unmatched rfl rfl

theorem classifyFile_o2 : O2 classifyFileRecord := by
  refine (o2_correct _).mpr ⟨⟨classifyFileModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(sampleRepoCfg, "Foo.lean", .checked "Foo.lean" 0 "Foo.lean" false),
      sampleRepoCfg_foo_outcome⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(emptyRepoCfg, "Foo.lean"), emptyRepoCfg_foo_refusal⟩
  exact nomatch hp

theorem classifyFile_o2Run : O2Run classifyFileRecord :=
  o2Run_of_meets classifyFileModel_meets

theorem classifyFile_o3 : O3 classifyFileRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ relPath => .ok (.checked relPath 0 relPath false), fun h => ?_⟩
    exact classifyOutcome_and_refusal_disjoint (h emptyRepoCfg "Foo.lean" _ rfl) emptyRepoCfg_foo_refusal
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .error "always", fun h => ?_⟩
    exact classifyOutcome_and_refusal_disjoint sampleRepoCfg_foo_outcome (h sampleRepoCfg "Foo.lean" "always" rfl)
  exact nomatch hc

theorem classifyFile_o4 : O4 classifyFileRecord := o4_function _ rfl

def ClassifyFileFreedom : Freedom ClassifyFileFn :=
  .rel fun f g => ∀ cfg relPath, (f cfg relPath).toOption = (g cfg relPath).toOption

theorem classifyFile_o5 : O5 classifyFileRecord ClassifyFileFreedom := by
  refine ⟨fun f g hf hg cfg relPath => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self cfg relPath
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg relPath
  have hgok := hg.2 _ List.mem_cons_self cfg relPath
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg relPath
  cases h1 : f cfg relPath with
  | ok o1 =>
    cases h2 : g cfg relPath with
    | ok o2 =>
      simp only [Except.toOption]
      rw [classifyOutcome_unique (hfok o1 h1) (hgok o2 h2)]
    | error msg =>
      exfalso
      exact classifyOutcome_and_refusal_disjoint (hfok o1 h1) (hgerr msg h2)
  | error msg =>
    cases h2 : g cfg relPath with
    | error _ => rfl
    | ok o2 =>
      exfalso
      exact classifyOutcome_and_refusal_disjoint (hgok o2 h2) (hferr msg h1)

theorem classifyFile_not_o5_eq : ¬ O5 classifyFileRecord .eq := by
  refine not_o5_eq classifyFileModel_meets (classifyFileModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun heq emptyRepoCfg) "Foo.lean"
  have hna : ¬ ∃ out, ClassifyOutcome emptyRepoCfg "Foo.lean" out := by
    rintro ⟨out, h⟩
    exact classifyOutcome_and_refusal_disjoint h emptyRepoCfg_foo_refusal
  dsimp [classifyFileModel, classifyFileModelWith] at hdiff
  simp [hna] at hdiff

theorem classifyFile_oPair_whole :
    ∀ c ∈ classifyFileRecord.props, OPair (Pair.whole classifyFileRecord c) classifyFileRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨classifyFileModel, classifyFileModel_meets, fun _ => classifyFileModel_meets.2 c hc⟩

def classifyFilePerInputPair : Pair ClassifyFileFn where
  Input := Config.RepoConfig × String
  pre := fun _ => True
  post := fun i f => ∀ out, f i.1 i.2 = .ok out → ClassifyOutcome i.1 i.2 out

theorem classifyFile_perInput_pairOf :
    ∀ c ∈ classifyFileRecord.props, c.name = "ok_unique_classification" →
      classifyFileRecord.PairOf c classifyFilePerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, classifyFileRecord, Pair.Met, classifyFilePerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem classifyFile_perInput_table_attack :
    ∀ i : classifyFilePerInputPair.Input, classifyFilePerInputPair.pre i →
      ∃ f : ClassifyFileFn, (∀ cfg p, f cfg p = f emptyRepoCfg "") ∧
        classifyFilePerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ _ => .error "table", fun _ _ => rfl, ?_⟩
  intro _ h; contradiction

theorem classifyFile_interim_const_fails :
    ∀ c, ¬ classifyFileRecord.Meets (fun _ _ => c) := by
  intro c hm
  cases c with
  | ok out =>
    exact classifyOutcome_and_refusal_disjoint (hm.2 _ List.mem_cons_self emptyRepoCfg "Foo.lean" out rfl)
      emptyRepoCfg_foo_refusal
  | error msg =>
    exact classifyOutcome_and_refusal_disjoint sampleRepoCfg_foo_outcome
      (hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) sampleRepoCfg "Foo.lean" msg rfl)

theorem classifyFile_healthy_nonempty :
    ∃ cfg relPath, Healthy.ClassifyInput cfg relPath :=
  ⟨sampleRepoCfg, "Foo.lean", (healthy_classifyInput_iff sampleRepoCfg "Foo.lean").mpr
    ⟨_, sampleRepoCfg_foo_outcome⟩⟩

theorem classifyFile_healthy_owed :
    ∀ f cfg relPath, classifyFileRecord.Meets f →
      Healthy.ClassifyInput cfg relPath → ∃ out, f cfg relPath = .ok out := by
  intro f cfg relPath hf hh
  cases hfv : f cfg relPath with
  | ok out => exact ⟨out, rfl⟩
  | error msg =>
    exfalso
    obtain ⟨_, ho⟩ := (healthy_classifyInput_iff cfg relPath).mp hh
    exact classifyOutcome_and_refusal_disjoint ho
      (hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg relPath msg hfv)

theorem classifyFile_negative_external_model :
    ∃ (f : ClassifyFileFn), ∃ cfg relPath,
      (∀ c r o, f c r = .ok o → ClassifyOutcome c r o) ∧
      Healthy.ClassifyInput cfg relPath ∧
      ¬ ∃ out, f cfg relPath = .ok out := by
  refine ⟨fun _ _ => .error "denied", sampleRepoCfg, "Foo.lean", (fun _ _ _ h => nomatch h),
    (healthy_classifyInput_iff sampleRepoCfg "Foo.lean").mpr ⟨_, sampleRepoCfg_foo_outcome⟩,
    fun ⟨_, h⟩ => nomatch h⟩

theorem classifyFile_reason_classified :
    ∀ f cfg relPath msg, classifyFileRecord.Meets f → f cfg relPath = .error msg →
      ClassifyRefusal cfg relPath ∧ ¬ Healthy.ClassifyInput cfg relPath := by
  intro f cfg relPath msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg relPath msg herr
  refine ⟨href, fun hh => ?_⟩
  obtain ⟨_, ho⟩ := (healthy_classifyInput_iff cfg relPath).mp hh
  exact classifyOutcome_and_refusal_disjoint ho href

theorem classifyTrackedOutcome_unique {cfg : Config.RepoConfig} {tracked : Array String}
    {o1 o2 : Array Config.ClassifiedFile}
    (h1 : ClassifyTrackedOutcome cfg tracked o1)
    (h2 : ClassifyTrackedOutcome cfg tracked o2) : o1 = o2 := by
  rcases h1 with ⟨hs1, he1⟩
  rcases h2 with ⟨hs2, he2⟩
  apply Array.ext
  · rw [hs1, hs2]
  · intro i hi1 hi2
    have hit : i < tracked.size := by omega
    obtain ⟨_, hc1⟩ := he1 i hit
    obtain ⟨_, hc2⟩ := he2 i hit
    exact classifyOutcome_unique hc1 hc2

theorem classifyTrackedOutcome_and_refusal_disjoint {cfg : Config.RepoConfig} {tracked : Array String}
    {out : Array Config.ClassifiedFile}
    (ho : ClassifyTrackedOutcome cfg tracked out) (hr : ClassifyTrackedRefusal cfg tracked) : False := by
  rcases ho with ⟨_, helts⟩
  rcases hr with ⟨relPath, hmem, href⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨_, hc⟩ := helts i (by simpa using hi)
  exact classifyOutcome_and_refusal_disjoint hc href

theorem classifyTrackedOutcome_total (cfg : Config.RepoConfig) (tracked : Array String) :
    (∃ out, ClassifyTrackedOutcome cfg tracked out) ∨ ClassifyTrackedRefusal cfg tracked := by
  by_cases hall : ∀ relPath ∈ tracked.toList, ∃ out, ClassifyOutcome cfg relPath out
  · let out : Array Config.ClassifiedFile := Array.ofFn fun idx : Fin tracked.size =>
      Classical.choose (hall tracked[idx.1] (Array.getElem_mem_toList idx.2))
    refine .inl ⟨out, Array.size_ofFn, fun i hi => ⟨by simp [out]; exact hi, ?_⟩⟩
    simpa [out] using Classical.choose_spec (hall tracked[i] (Array.getElem_mem_toList hi))
  · obtain ⟨relPath, hnr⟩ := Classical.not_forall.mp hall
    obtain ⟨hmem, hno⟩ := Classical.not_imp.mp hnr
    rcases classifyOutcome_total cfg relPath with hok | href
    · exact absurd hok hno
    · exact .inr ⟨relPath, hmem, href⟩

theorem healthy_classifyTrackedInput_iff (cfg : Config.RepoConfig) (tracked : Array String) :
    Healthy.ClassifyTrackedInput cfg tracked ↔ ∃ out, ClassifyTrackedOutcome cfg tracked out := by
  constructor
  · intro hh
    let out : Array Config.ClassifiedFile := Array.ofFn fun idx : Fin tracked.size =>
      Classical.choose ((healthy_classifyInput_iff cfg tracked[idx.1]).mp
        (hh tracked[idx.1] (Array.getElem_mem_toList idx.2)))
    refine ⟨out, Array.size_ofFn, fun i hi => ⟨by simp [out]; exact hi, ?_⟩⟩
    simpa [out] using Classical.choose_spec ((healthy_classifyInput_iff cfg tracked[i]).mp
      (hh tracked[i] (Array.getElem_mem_toList hi)))
  · rintro ⟨out, _, helts⟩ relPath hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨_, hc⟩ := helts i (by simpa using hi)
    exact (healthy_classifyInput_iff _ _).mpr ⟨_, hc⟩

noncomputable def classifyTrackedModelWith (errMsg : String) : ClassifyTrackedFn :=
  open Classical in
  fun cfg tracked =>
    if h : ∃ out, ClassifyTrackedOutcome cfg tracked out then .ok (Classical.choose h)
    else .error errMsg

noncomputable def classifyTrackedModel : ClassifyTrackedFn :=
  classifyTrackedModelWith "classify tracked failed"

theorem classifyTrackedModelWith_meets (errMsg : String) :
    classifyTrackedRecord.Meets (classifyTrackedModelWith errMsg) := by
  refine ⟨(fun _ h => nomatch h), fun p hp => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · intro cfg tracked out hok
    dsimp [classifyTrackedModelWith] at hok
    split at hok
    · rename_i h
      cases hok
      exact Classical.choose_spec h
    · contradiction
  rcases List.mem_cons.mp hp with rfl | hp
  · intro cfg tracked msg herr
    dsimp [classifyTrackedModelWith] at herr
    split at herr
    · contradiction
    · rename_i hno
      rcases classifyTrackedOutcome_total cfg tracked with hok | href
      · exact absurd hok hno
      · exact href
  exact nomatch hp

theorem classifyTrackedModel_meets : classifyTrackedRecord.Meets classifyTrackedModel :=
  classifyTrackedModelWith_meets "classify tracked failed"

theorem sampleTracked_outcome :
    ClassifyTrackedOutcome sampleRepoCfg #["Foo.lean"] #[.checked "Foo.lean" 0 "Foo.lean" false] := by
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 := by simp at hi; omega
  subst this
  exact ⟨by decide, sampleRepoCfg_foo_outcome⟩

theorem emptyTracked_refusal : ClassifyTrackedRefusal emptyRepoCfg #["Foo.lean"] :=
  ⟨"Foo.lean", by simp, emptyRepoCfg_foo_refusal⟩

theorem classifyTracked_o2 : O2 classifyTrackedRecord := by
  refine (o2_correct _).mpr ⟨⟨classifyTrackedModel, (fun _ h => nomatch h)⟩, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(sampleRepoCfg, #["Foo.lean"], #[.checked "Foo.lean" 0 "Foo.lean" false]),
      sampleTracked_outcome⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨(emptyRepoCfg, #["Foo.lean"]), emptyTracked_refusal⟩
  exact nomatch hp

theorem classifyTracked_o2Run : O2Run classifyTrackedRecord :=
  o2Run_of_meets classifyTrackedModel_meets

theorem classifyTracked_o3 : O3 classifyTrackedRecord := by
  refine (o3_correct _).mpr fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .ok #[], fun h => ?_⟩
    obtain ⟨hsz, _⟩ := h sampleRepoCfg #["Foo.lean"] #[] rfl
    have h0 : (#[] : Array Config.ClassifiedFile).size = 0 := rfl
    have h1 : (#["Foo.lean"] : Array String).size = 1 := rfl
    omega
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨fun _ _ => .error "always", fun h => ?_⟩
    exact classifyTrackedOutcome_and_refusal_disjoint sampleTracked_outcome
      (h sampleRepoCfg #["Foo.lean"] "always" rfl)
  exact nomatch hc

theorem classifyTracked_o4 : O4 classifyTrackedRecord := o4_function _ rfl

def ClassifyTrackedFreedom : Freedom ClassifyTrackedFn :=
  .rel fun f g => ∀ cfg tracked, (f cfg tracked).toOption = (g cfg tracked).toOption

theorem classifyTracked_o5 : O5 classifyTrackedRecord ClassifyTrackedFreedom := by
  refine ⟨fun f g hf hg cfg tracked => ?_, trivial⟩
  have hfok := hf.2 _ List.mem_cons_self cfg tracked
  have hferr := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg tracked
  have hgok := hg.2 _ List.mem_cons_self cfg tracked
  have hgerr := hg.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg tracked
  cases h1 : f cfg tracked with
  | ok o1 =>
    cases h2 : g cfg tracked with
    | ok o2 =>
      simp only [Except.toOption]
      rw [classifyTrackedOutcome_unique (hfok o1 h1) (hgok o2 h2)]
    | error msg =>
      exfalso
      exact classifyTrackedOutcome_and_refusal_disjoint (hfok o1 h1) (hgerr msg h2)
  | error msg =>
    cases h2 : g cfg tracked with
    | error _ => rfl
    | ok o2 =>
      exfalso
      exact classifyTrackedOutcome_and_refusal_disjoint (hgok o2 h2) (hferr msg h1)

theorem classifyTracked_not_o5_eq : ¬ O5 classifyTrackedRecord .eq := by
  refine not_o5_eq classifyTrackedModel_meets (classifyTrackedModelWith_meets "denied") fun heq => ?_
  have hdiff := congrFun (congrFun heq emptyRepoCfg) #["Foo.lean"]
  have hna : ¬ ∃ out, ClassifyTrackedOutcome emptyRepoCfg #["Foo.lean"] out := by
    rintro ⟨out, h⟩
    exact classifyTrackedOutcome_and_refusal_disjoint h emptyTracked_refusal
  dsimp [classifyTrackedModel, classifyTrackedModelWith] at hdiff
  simp [hna] at hdiff

theorem classifyTracked_oPair_whole :
    ∀ c ∈ classifyTrackedRecord.props, OPair (Pair.whole classifyTrackedRecord c) classifyTrackedRecord.Meets :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨classifyTrackedModel, classifyTrackedModel_meets, fun _ => classifyTrackedModel_meets.2 c hc⟩

def classifyTrackedPerInputPair : Pair ClassifyTrackedFn where
  Input := Config.RepoConfig × Array String
  pre := fun _ => True
  post := fun i f => ∀ out, f i.1 i.2 = .ok out → ClassifyTrackedOutcome i.1 i.2 out

theorem classifyTracked_perInput_pairOf :
    ∀ c ∈ classifyTrackedRecord.props, c.name = "ok_all_classified_in_order" →
      classifyTrackedRecord.PairOf c classifyTrackedPerInputPair := by
  intro c hc hnm
  rcases List.mem_cons.mp hc with rfl | hc
  · refine ⟨List.mem_cons_self, fun f => ?_⟩
    simp [IntentRecord.Dom, classifyTrackedRecord, Pair.Met, classifyTrackedPerInputPair]
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp at hnm
    exact nomatch hc

theorem classifyTracked_perInput_table_attack :
    ∀ i : classifyTrackedPerInputPair.Input, classifyTrackedPerInputPair.pre i →
      ∃ f : ClassifyTrackedFn, (∀ cfg t, f cfg t = f emptyRepoCfg #[]) ∧
        classifyTrackedPerInputPair.post i f := by
  intro _ _
  refine ⟨fun _ _ => .error "table", fun _ _ => rfl, ?_⟩
  intro _ h; contradiction

theorem classifyTracked_interim_const_fails :
    ∀ c, ¬ classifyTrackedRecord.Meets (fun _ _ => c) := by
  intro c hm
  cases c with
  | ok out =>
    rcases hm.2 _ List.mem_cons_self sampleRepoCfg #["Foo.lean"] out rfl with ⟨hsz, _⟩
    rcases hm.2 _ List.mem_cons_self emptyRepoCfg #[] out rfl with ⟨hsz0, _⟩
    have h0 : (#[] : Array String).size = 0 := rfl
    have h1 : (#["Foo.lean"] : Array String).size = 1 := rfl
    omega
  | error msg =>
    exact classifyTrackedOutcome_and_refusal_disjoint sampleTracked_outcome
      (hm.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) sampleRepoCfg #["Foo.lean"] msg rfl)

theorem classifyTracked_healthy_nonempty :
    ∃ cfg tracked, Healthy.ClassifyTrackedInput cfg tracked :=
  ⟨sampleRepoCfg, #["Foo.lean"], (healthy_classifyTrackedInput_iff sampleRepoCfg #["Foo.lean"]).mpr
    ⟨_, sampleTracked_outcome⟩⟩

theorem classifyTracked_healthy_owed :
    ∀ f cfg tracked, classifyTrackedRecord.Meets f →
      Healthy.ClassifyTrackedInput cfg tracked → ∃ out, f cfg tracked = .ok out := by
  intro f cfg tracked hf hh
  cases hfv : f cfg tracked with
  | ok out => exact ⟨out, rfl⟩
  | error msg =>
    exfalso
    obtain ⟨_, ho⟩ := (healthy_classifyTrackedInput_iff cfg tracked).mp hh
    exact classifyTrackedOutcome_and_refusal_disjoint ho
      (hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg tracked msg hfv)

theorem classifyTracked_negative_external_model :
    ∃ (f : ClassifyTrackedFn), ∃ cfg tracked,
      (∀ c t o, f c t = .ok o → ClassifyTrackedOutcome c t o) ∧
      Healthy.ClassifyTrackedInput cfg tracked ∧
      ¬ ∃ out, f cfg tracked = .ok out := by
  refine ⟨fun _ _ => .error "denied", sampleRepoCfg, #["Foo.lean"], (fun _ _ _ h => nomatch h),
    (healthy_classifyTrackedInput_iff sampleRepoCfg #["Foo.lean"]).mpr ⟨_, sampleTracked_outcome⟩,
    fun ⟨_, h⟩ => nomatch h⟩

theorem classifyTracked_reason_classified :
    ∀ f cfg tracked msg, classifyTrackedRecord.Meets f → f cfg tracked = .error msg →
      ClassifyTrackedRefusal cfg tracked ∧ ¬ Healthy.ClassifyTrackedInput cfg tracked := by
  intro f cfg tracked msg hf herr
  have href := hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self) cfg tracked msg herr
  refine ⟨href, fun hh => ?_⟩
  obtain ⟨_, ho⟩ := (healthy_classifyTrackedInput_iff cfg tracked).mp hh
  exact classifyTrackedOutcome_and_refusal_disjoint ho href

end NoCommentsSpecification.AdequacyConfig
