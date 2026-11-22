module

public import Lean
import Lake.CLI.Error
import Lake.Load.Package
import Lake.Util.IO
meta import Lake.CLI.Error
meta import Lake.Load.Package
meta import Lake.Util.IO

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean

namespace NoComments.TestListing

public section

inductive Mode where
  | list
  | check
  deriving @[expose] Repr, @[expose] BEq, @[expose] DecidableEq

structure CheckOutcome where
  exitCode : UInt32
  errorMessage? : Option String
  deriving @[expose] Repr, @[expose] BEq, @[expose] DecidableEq

structure ParsedFile where
  path : String
  ictx : Parser.InputContext
  commands : Array Syntax

structure RepoSnapshot where
  lakeTestDriver : String
  files : Array ParsedFile

structure CheckResult where
  findings : Array String
  outcome : CheckOutcome
  deriving @[expose] Repr, @[expose] BEq, @[expose] DecidableEq

@[expose] def parseMode : List String → Except String Mode
  | [] => .ok .list
  | ["--check"] => .ok .check
  | _ => .error "usage: test-listing [--check]"

@[expose] def decideOutcome (mode : Mode) (findings : Array String) : CheckOutcome :=
  match mode with
  | .check =>
    if findings.isEmpty then
      { exitCode := 0, errorMessage? := none }
    else
      { exitCode := 1, errorMessage? := some s!"error: found {findings.size} forbidden test item(s)" }
  | .list =>
    { exitCode := 0, errorMessage? := none }

@[expose] def lakeTestDriverFindings (lakeTestDriver : String) : Array String :=
  if lakeTestDriver == "" then #[]
  else #[s!"lake-test-driver:{lakeTestDriver}"]

@[expose] def forbiddenCommandKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.eval,
   ``Lean.Parser.Command.evalBang,
   ``Lean.Parser.Command.guardCmd,
   ``Lean.guardMsgsCmd,
   ``Lean.guardPanicCmd,
   ``Lean.Parser.Command.guardExprCmd,
   ``Lean.Parser.Command.check,
   ``Lean.Parser.Command.check_failure,
   ``Lean.Parser.checkSimp,
   ``Lean.Parser.checkSimpFailure,
   ``Lean.Parser.checkTactic,
   ``Lean.Parser.checkTacticFailure,
   ``Lean.Parser.Command.print,
   ``Lean.Parser.Command.printAxioms,
   ``Lean.Parser.Command.printSig,
   ``Lean.Parser.Command.printEqns,
   ``Lean.Parser.Command.printTacTags,
   ``Lean.Parser.Command.example]

@[expose] def forbiddenAttrs : List Name :=
  [`test_driver, `Lake.test_driver]

@[expose] def lineOfPos (ictx : Parser.InputContext) (stx : Syntax) : Nat :=
  match stx.getPos? with
  | some pos => (ictx.fileMap.toPosition pos).line
  | none => 1

@[expose] def nodeFindings (ictx : Parser.InputContext) (file : String) (stx : Syntax) :
    Array String :=
  match stx with
  | .node _ k args =>
    if forbiddenCommandKinds.contains k then
      #[s!"{file}:{lineOfPos ictx stx}:cmd:{k}"]
    else if k == ``Lean.Parser.Attr.simple then
      match args with
      | .mk (idStx@(.ident _ _ n _) :: _) =>
        if forbiddenAttrs.contains n then
          #[s!"{file}:{lineOfPos ictx idStx}:attr:{n}"]
        else
          #[]
      | _ => #[]
    else
      #[]
  | _ => #[]

mutual

@[expose] def scanSyntax (ictx : Parser.InputContext) (file : String) (stx : Syntax)
    (acc : Array String) : Array String :=
  match stx with
  | .node info k (.mk args) =>
    let acc' := acc ++ nodeFindings ictx file (.node info k (.mk args))
    scanSyntaxList ictx file args acc'
  | _ => acc
termination_by sizeOf stx

@[expose] def scanSyntaxList (ictx : Parser.InputContext) (file : String)
    (args : List Syntax) (acc : Array String) : Array String :=
  match args with
  | [] => acc
  | c :: cs => scanSyntaxList ictx file cs (scanSyntax ictx file c acc)
termination_by sizeOf args

end

@[expose] def splitSlashChars (acc : List Char) : List Char → List String
  | [] => [String.ofList acc.reverse]
  | '/' :: rest => String.ofList acc.reverse :: splitSlashChars [] rest
  | c :: rest => splitSlashChars (c :: acc) rest

@[expose] def pathDirectories (file : String) : List String :=
  (splitSlashChars [] file.toList).dropLast

@[expose] def hasTestDirectory (file : String) : Bool :=
  let dirs := pathDirectories file
  dirs.contains "test" || dirs.contains "tests"

@[expose] def fileDirectoryFindings (file : String) : Array String :=
  if hasTestDirectory file then #[s!"file:{file}"]
  else #[]

@[expose] def collectFileFindings (file : ParsedFile) : Array String :=
  file.commands.foldl (fun acc cmd => scanSyntax file.ictx file.path cmd acc)
    (fileDirectoryFindings file.path)

@[expose] def collectFindings (snapshot : RepoSnapshot) : Array String :=
  snapshot.files.foldl (fun acc file => acc ++ collectFileFindings file)
    (lakeTestDriverFindings snapshot.lakeTestDriver)

@[expose] def evaluateSnapshot (mode : Mode) (snapshot : RepoSnapshot) : CheckResult :=
  let findings := collectFindings snapshot
  { findings, outcome := decideOutcome mode findings }

@[expose] def IsForbiddenCommandKind (k : SyntaxNodeKind) : Prop :=
  k = ``Lean.Parser.Command.eval ∨
  k = ``Lean.Parser.Command.evalBang ∨
  k = ``Lean.Parser.Command.guardCmd ∨
  k = ``Lean.guardMsgsCmd ∨
  k = ``Lean.guardPanicCmd ∨
  k = ``Lean.Parser.Command.guardExprCmd ∨
  k = ``Lean.Parser.Command.check ∨
  k = ``Lean.Parser.Command.check_failure ∨
  k = ``Lean.Parser.checkSimp ∨
  k = ``Lean.Parser.checkSimpFailure ∨
  k = ``Lean.Parser.checkTactic ∨
  k = ``Lean.Parser.checkTacticFailure ∨
  k = ``Lean.Parser.Command.print ∨
  k = ``Lean.Parser.Command.printAxioms ∨
  k = ``Lean.Parser.Command.printSig ∨
  k = ``Lean.Parser.Command.printEqns ∨
  k = ``Lean.Parser.Command.printTacTags ∨
  k = ``Lean.Parser.Command.example

@[expose] def IsForbiddenAttr (n : Name) : Prop :=
  n = `test_driver ∨ n = `Lake.test_driver

inductive SubSyntax : Syntax → Syntax → Prop where
  | self (s : Syntax) : SubSyntax s s
  | child {sub child : Syntax} {info : SourceInfo} {k : SyntaxNodeKind} {args : Array Syntax} :
      child ∈ args.toList → SubSyntax sub child → SubSyntax sub (.node info k args)

inductive ForbiddenNodeFinding (ictx : Parser.InputContext) (file : String) :
    Syntax → String → Prop where
  | cmd {info : SourceInfo} {k : SyntaxNodeKind} {args : Array Syntax} :
      IsForbiddenCommandKind k →
      ForbiddenNodeFinding ictx file (.node info k args)
        s!"{file}:{lineOfPos ictx (.node info k args)}:cmd:{k}"
  | attr {info idInfo : SourceInfo} {args : Array Syntax}
      {rawVal : Substring.Raw} {n : Name} {preresolved : List Syntax.Preresolved}
      (h : 0 < args.size) :
      args[0] = .ident idInfo rawVal n preresolved →
      IsForbiddenAttr n →
      ForbiddenNodeFinding ictx file (.node info ``Lean.Parser.Attr.simple args)
        s!"{file}:{lineOfPos ictx args[0]}:attr:{n}"

inductive SnapshotFinding (snapshot : RepoSnapshot) : String → Prop where
  | lakeTestDriver :
      snapshot.lakeTestDriver ≠ "" →
      SnapshotFinding snapshot s!"lake-test-driver:{snapshot.lakeTestDriver}"
  | testDirectory {file : ParsedFile} :
      file ∈ snapshot.files.toList →
      ("test" ∈ pathDirectories file.path ∨ "tests" ∈ pathDirectories file.path) →
      SnapshotFinding snapshot s!"file:{file.path}"
  | syntaxNode {file : ParsedFile} {cmd sub : Syntax} {msg : String} :
      file ∈ snapshot.files.toList →
      cmd ∈ file.commands.toList →
      SubSyntax sub cmd →
      ForbiddenNodeFinding file.ictx file.path sub msg →
      SnapshotFinding snapshot msg

theorem mem_forbiddenCommandKinds_iff (k : SyntaxNodeKind) :
    k ∈ forbiddenCommandKinds ↔ IsForbiddenCommandKind k := by
  simp [forbiddenCommandKinds, IsForbiddenCommandKind]

theorem mem_forbiddenAttrs_iff (n : Name) :
    n ∈ forbiddenAttrs ↔ IsForbiddenAttr n := by
  simp [forbiddenAttrs, IsForbiddenAttr]

theorem attrSimple_not_mem_forbiddenCommandKinds :
    ``Lean.Parser.Attr.simple ∉ forbiddenCommandKinds := by
  simp [forbiddenCommandKinds]

theorem mem_nodeFindings_iff (ictx : Parser.InputContext) (file : String)
    (stx : Syntax) (msg : String) :
    msg ∈ (nodeFindings ictx file stx).toList ↔ ForbiddenNodeFinding ictx file stx msg := by
  cases stx with
  | missing =>
    simp only [nodeFindings, List.not_mem_nil, false_iff]
    intro h
    cases h
  | atom info val =>
    simp only [nodeFindings, List.not_mem_nil, false_iff]
    intro h
    cases h
  | ident info rawVal val preresolved =>
    simp only [nodeFindings, List.not_mem_nil, false_iff]
    intro h
    cases h
  | node info k args =>
    unfold nodeFindings
    by_cases hcmd : forbiddenCommandKinds.contains k = true
    · simp only [hcmd, ↓reduceIte, List.mem_singleton]
      have hk : IsForbiddenCommandKind k :=
        (mem_forbiddenCommandKinds_iff k).mp (List.contains_iff_mem.mp hcmd)
      constructor
      · intro hmsg
        subst hmsg
        exact .cmd hk
      · intro hfind
        cases hfind with
        | cmd _ => rfl
        | attr _ _ _ =>
          exact False.elim (attrSimple_not_mem_forbiddenCommandKinds (List.contains_iff_mem.mp hcmd))
    · have hcmdFalse : forbiddenCommandKinds.contains k = false :=
        Bool.eq_false_iff.mpr hcmd
      have hnotCmd : ¬ IsForbiddenCommandKind k := by
        intro hk
        exact hcmd (List.contains_iff_mem.mpr ((mem_forbiddenCommandKinds_iff k).mpr hk))
      simp only [hcmdFalse, Bool.false_eq_true, ↓reduceIte]
      by_cases hsimple : (k == ``Lean.Parser.Attr.simple) = true
      · have hkeq : k = ``Lean.Parser.Attr.simple := eq_of_beq hsimple
        subst hkeq
        simp only [beq_self_eq_true, ↓reduceIte]
        cases args with
        | mk xs =>
          cases xs with
          | nil =>
            simp only [List.not_mem_nil, false_iff]
            intro hfind
            cases hfind with
            | cmd hk => exact hnotCmd hk
            | attr h0 _ _ => simp at h0
          | cons hd tl =>
            cases hd with
            | ident idInfo rawVal n preresolved =>
              by_cases hattr : forbiddenAttrs.contains n = true
              · simp only [hattr, ↓reduceIte, List.mem_singleton]
                have hn : IsForbiddenAttr n :=
                  (mem_forbiddenAttrs_iff n).mp (List.contains_iff_mem.mp hattr)
                constructor
                · intro hmsg
                  subst hmsg
                  exact .attr (by simp) rfl hn
                · intro hfind
                  cases hfind with
                  | cmd hk => exact False.elim (hnotCmd hk)
                  | attr _ hident _ =>
                    change Syntax.ident idInfo rawVal n preresolved = Syntax.ident _ _ _ _ at hident
                    cases hident
                    rfl
              · have hattrFalse : forbiddenAttrs.contains n = false :=
                  Bool.eq_false_iff.mpr hattr
                simp only [hattrFalse, Bool.false_eq_true, ↓reduceIte,
                  List.not_mem_nil, false_iff]
                intro hfind
                cases hfind with
                | cmd hk => exact hnotCmd hk
                | attr _ hident hn =>
                  change Syntax.ident idInfo rawVal n preresolved = Syntax.ident _ _ _ _ at hident
                  cases hident
                  exact hattr (List.contains_iff_mem.mpr ((mem_forbiddenAttrs_iff n).mpr hn))
            | missing =>
              simp only [List.not_mem_nil, false_iff]
              intro hfind
              cases hfind with
              | cmd hk => exact hnotCmd hk
              | attr _ hident _ =>
                change Syntax.missing = Syntax.ident _ _ _ _ at hident
                cases hident
            | node _ _ _ =>
              simp only [List.not_mem_nil, false_iff]
              intro hfind
              cases hfind with
              | cmd hk => exact hnotCmd hk
              | attr _ hident _ =>
                change Syntax.node _ _ _ = Syntax.ident _ _ _ _ at hident
                cases hident
            | atom _ _ =>
              simp only [List.not_mem_nil, false_iff]
              intro hfind
              cases hfind with
              | cmd hk => exact hnotCmd hk
              | attr _ hident _ =>
                change Syntax.atom _ _ = Syntax.ident _ _ _ _ at hident
                cases hident
      · have hsimpleFalse : (k == ``Lean.Parser.Attr.simple) = false :=
          Bool.eq_false_iff.mpr hsimple
        simp only [hsimpleFalse, Bool.false_eq_true, ↓reduceIte,
          List.not_mem_nil, false_iff]
        intro hfind
        cases hfind with
        | cmd hk => exact hnotCmd hk
        | attr _ _ _ => exact hsimple (beq_self_eq_true _)

mutual

theorem mem_scanSyntax_iff (ictx : Parser.InputContext) (file : String)
    (stx : Syntax) (acc : Array String) (msg : String) :
    msg ∈ (scanSyntax ictx file stx acc).toList ↔
      msg ∈ acc.toList ∨ ∃ sub, SubSyntax sub stx ∧ ForbiddenNodeFinding ictx file sub msg := by
  match stx with
  | .node info k (.mk args) =>
    rw [scanSyntax, mem_scanSyntaxList_iff]
    simp only [Array.toList_append, List.mem_append, mem_nodeFindings_iff]
    constructor
    · rintro ((hacc | hnode) | ⟨c, hc, sub, hsub, hfind⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨.node info k (.mk args), .self _, hnode⟩
      · exact Or.inr ⟨sub, .child hc hsub, hfind⟩
    · rintro (hacc | ⟨sub, hsub, hfind⟩)
      · exact Or.inl (Or.inl hacc)
      · cases hsub with
        | self => exact Or.inl (Or.inr hfind)
        | child hc hsub' => exact Or.inr ⟨_, hc, sub, hsub', hfind⟩
  | .missing =>
    simp only [scanSyntax]
    constructor
    · exact Or.inl
    · rintro (hacc | ⟨sub, hsub, hfind⟩)
      · exact hacc
      · cases hsub
        cases hfind
  | .atom _ _ =>
    simp only [scanSyntax]
    constructor
    · exact Or.inl
    · rintro (hacc | ⟨sub, hsub, hfind⟩)
      · exact hacc
      · cases hsub
        cases hfind
  | .ident _ _ _ _ =>
    simp only [scanSyntax]
    constructor
    · exact Or.inl
    · rintro (hacc | ⟨sub, hsub, hfind⟩)
      · exact hacc
      · cases hsub
        cases hfind
termination_by sizeOf stx

theorem mem_scanSyntaxList_iff (ictx : Parser.InputContext) (file : String)
    (args : List Syntax) (acc : Array String) (msg : String) :
    msg ∈ (scanSyntaxList ictx file args acc).toList ↔
      msg ∈ acc.toList ∨
        ∃ c ∈ args, ∃ sub, SubSyntax sub c ∧ ForbiddenNodeFinding ictx file sub msg := by
  match args with
  | [] =>
    simp [scanSyntaxList]
  | c :: cs =>
    rw [scanSyntaxList, mem_scanSyntaxList_iff, mem_scanSyntax_iff]
    constructor
    · rintro ((hacc | ⟨sub, hsub, hfind⟩) | ⟨c', hc', sub, hsub, hfind⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨c, List.mem_cons_self, sub, hsub, hfind⟩
      · exact Or.inr ⟨c', List.mem_cons_of_mem c hc', sub, hsub, hfind⟩
    · rintro (hacc | ⟨c', hc', sub, hsub, hfind⟩)
      · exact Or.inl (Or.inl hacc)
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inl (Or.inr ⟨sub, hsub, hfind⟩)
        · exact Or.inr ⟨c', hc', sub, hsub, hfind⟩
termination_by sizeOf args

end

theorem hasTestDirectory_iff (file : String) :
    hasTestDirectory file = true ↔
      "test" ∈ pathDirectories file ∨ "tests" ∈ pathDirectories file := by
  simp [hasTestDirectory]

theorem mem_lakeTestDriverFindings_iff (lakeTestDriver msg : String) :
    msg ∈ (lakeTestDriverFindings lakeTestDriver).toList ↔
      lakeTestDriver ≠ "" ∧ msg = s!"lake-test-driver:{lakeTestDriver}" := by
  unfold lakeTestDriverFindings
  by_cases h : lakeTestDriver = ""
  · subst h
    simp
  · have hbeq : (lakeTestDriver == "") = false := beq_false_of_ne h
    simp [h, hbeq]

theorem mem_fileDirectoryFindings_iff (file msg : String) :
    msg ∈ (fileDirectoryFindings file).toList ↔
      ("test" ∈ pathDirectories file ∨ "tests" ∈ pathDirectories file) ∧
        msg = s!"file:{file}" := by
  unfold fileDirectoryFindings
  by_cases h : hasTestDirectory file = true
  · simp [h, (hasTestDirectory_iff file).mp h]
  · have hfalse : hasTestDirectory file = false := Bool.eq_false_iff.mpr h
    have hnot : ¬ ("test" ∈ pathDirectories file ∨ "tests" ∈ pathDirectories file) := by
      intro hd
      exact h ((hasTestDirectory_iff file).mpr hd)
    simp [hfalse, hnot]

private theorem mem_foldl_scanSyntax_iff (ictx : Parser.InputContext) (file : String)
    (cmds : List Syntax) (acc : Array String) (msg : String) :
    msg ∈ (cmds.foldl (fun a cmd => scanSyntax ictx file cmd a) acc).toList ↔
      msg ∈ acc.toList ∨
        ∃ cmd ∈ cmds, ∃ sub, SubSyntax sub cmd ∧ ForbiddenNodeFinding ictx file sub msg := by
  induction cmds generalizing acc with
  | nil =>
    simp
  | cons cmd rest ih =>
    simp only [List.foldl_cons, ih, mem_scanSyntax_iff]
    constructor
    · rintro ((hacc | ⟨sub, hsub, hfind⟩) | ⟨c', hc', sub, hsub, hfind⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨cmd, List.mem_cons_self, sub, hsub, hfind⟩
      · exact Or.inr ⟨c', List.mem_cons_of_mem cmd hc', sub, hsub, hfind⟩
    · rintro (hacc | ⟨c', hc', sub, hsub, hfind⟩)
      · exact Or.inl (Or.inl hacc)
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inl (Or.inr ⟨sub, hsub, hfind⟩)
        · exact Or.inr ⟨c', hc', sub, hsub, hfind⟩

theorem mem_collectFileFindings_iff (file : ParsedFile) (msg : String) :
    msg ∈ (collectFileFindings file).toList ↔
      (("test" ∈ pathDirectories file.path ∨ "tests" ∈ pathDirectories file.path) ∧
          msg = s!"file:{file.path}") ∨
        ∃ cmd ∈ file.commands.toList, ∃ sub,
          SubSyntax sub cmd ∧ ForbiddenNodeFinding file.ictx file.path sub msg := by
  unfold collectFileFindings
  rw [← Array.foldl_toList, mem_foldl_scanSyntax_iff, mem_fileDirectoryFindings_iff]

private theorem mem_foldl_collectFileFindings_iff (files : List ParsedFile)
    (acc : Array String) (msg : String) :
    msg ∈ (files.foldl (fun a f => a ++ collectFileFindings f) acc).toList ↔
      msg ∈ acc.toList ∨ ∃ f ∈ files, msg ∈ (collectFileFindings f).toList := by
  induction files generalizing acc with
  | nil =>
    simp
  | cons f rest ih =>
    simp only [List.foldl_cons, ih, Array.toList_append, List.mem_append]
    constructor
    · rintro ((hacc | hf) | ⟨f', hf', hmsg⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨f, List.mem_cons_self, hf⟩
      · exact Or.inr ⟨f', List.mem_cons_of_mem f hf', hmsg⟩
    · rintro (hacc | ⟨f', hf', hmsg⟩)
      · exact Or.inl (Or.inl hacc)
      · rcases List.mem_cons.mp hf' with rfl | hf'
        · exact Or.inl (Or.inr hmsg)
        · exact Or.inr ⟨f', hf', hmsg⟩

theorem mem_collectFindings_iff (snapshot : RepoSnapshot) (msg : String) :
    msg ∈ (collectFindings snapshot).toList ↔ SnapshotFinding snapshot msg := by
  unfold collectFindings
  rw [← Array.foldl_toList, mem_foldl_collectFileFindings_iff, mem_lakeTestDriverFindings_iff]
  constructor
  · rintro (⟨hd, rfl⟩ | ⟨file, hfile, hmsg⟩)
    · exact .lakeTestDriver hd
    · rcases (mem_collectFileFindings_iff file msg).mp hmsg with ⟨hdir, rfl⟩ | ⟨cmd, hcmd, sub, hsub, hfind⟩
      · exact .testDirectory hfile hdir
      · exact .syntaxNode hfile hcmd hsub hfind
  · intro h
    cases h with
    | lakeTestDriver hd =>
      exact Or.inl ⟨hd, rfl⟩
    | testDirectory hfile hdir =>
      exact Or.inr ⟨_, hfile, (mem_collectFileFindings_iff _ _).mpr (Or.inl ⟨hdir, rfl⟩)⟩
    | syntaxNode hfile hcmd hsub hfind =>
      exact Or.inr ⟨_, hfile, (mem_collectFileFindings_iff _ _).mpr (Or.inr ⟨_, hcmd, _, hsub, hfind⟩)⟩

theorem parseMode_iff (args : List String) (mode : Mode) :
    parseMode args = .ok mode ↔
      (args = [] ∧ mode = .list) ∨ (args = ["--check"] ∧ mode = .check) := by
  cases args with
  | nil =>
    simp [parseMode, eq_comm]
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases h : a = "--check"
      · subst h
        simp [parseMode, eq_comm]
      · simp [parseMode, h]
    | cons b tail =>
      simp [parseMode]

theorem parseMode_invalid (args : List String) (h0 : args ≠ []) (h1 : args ≠ ["--check"]) :
    parseMode args = .error "usage: test-listing [--check]" := by
  cases args with
  | nil => exact False.elim (h0 rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases h : a = "--check"
      · subst h
        exact False.elim (h1 rfl)
      · simp [parseMode]
    | cons b tail =>
      simp [parseMode]

private theorem array_isEmpty_eq_false_of_mem {α : Type} {arr : Array α} {x : α}
    (hx : x ∈ arr.toList) : arr.isEmpty = false := by
  cases arr with
  | mk xs =>
    cases xs with
    | nil => cases hx
    | cons _ _ => rfl

theorem decideOutcome_check_of_mem (findings : Array String) (msg : String)
    (hmsg : msg ∈ findings.toList) :
    decideOutcome .check findings =
      { exitCode := 1
        errorMessage? := some s!"error: found {findings.size} forbidden test item(s)" } := by
  simp [decideOutcome, array_isEmpty_eq_false_of_mem hmsg]

theorem evaluateSnapshot_check_passes_iff (snapshot : RepoSnapshot) :
    (evaluateSnapshot .check snapshot).outcome = { exitCode := 0, errorMessage? := none } ↔
      ∀ msg, ¬ SnapshotFinding snapshot msg := by
  unfold evaluateSnapshot decideOutcome
  cases h : collectFindings snapshot with
  | mk xs =>
    cases xs with
    | nil =>
      have hemp : ({ toList := [] } : Array String).isEmpty = true := rfl
      simp only [hemp, ↓reduceIte, true_iff]
      intro msg hfind
      have hmem : msg ∈ (collectFindings snapshot).toList := (mem_collectFindings_iff snapshot msg).mpr hfind
      rw [h] at hmem
      cases hmem
    | cons x rest =>
      have hne : ({ toList := x :: rest } : Array String).isEmpty = false := rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte, CheckOutcome.mk.injEq, reduceCtorEq,
        and_false, false_iff, Classical.not_forall, Classical.not_not]
      refine ⟨x, (mem_collectFindings_iff snapshot x).mp ?_⟩
      rw [h]
      exact List.mem_cons_self

theorem evaluateSnapshot_check_fails_iff (snapshot : RepoSnapshot) :
    (evaluateSnapshot .check snapshot).outcome.exitCode = 1 ↔
      ∃ msg, SnapshotFinding snapshot msg := by
  unfold evaluateSnapshot decideOutcome
  cases h : collectFindings snapshot with
  | mk xs =>
    cases xs with
    | nil =>
      have hemp : ({ toList := [] } : Array String).isEmpty = true := rfl
      simp only [hemp, ↓reduceIte]
      constructor
      · intro h0
        cases h0
      · rintro ⟨msg, hfind⟩
        have hmem : msg ∈ (collectFindings snapshot).toList := (mem_collectFindings_iff snapshot msg).mpr hfind
        rw [h] at hmem
        cases hmem
    | cons x rest =>
      have hne : ({ toList := x :: rest } : Array String).isEmpty = false := rfl
      simp only [hne, Bool.false_eq_true, ↓reduceIte, true_iff]
      refine ⟨x, (mem_collectFindings_iff snapshot x).mp ?_⟩
      rw [h]
      exact List.mem_cons_self

theorem evaluateSnapshot_list_spec (snapshot : RepoSnapshot) :
    (evaluateSnapshot .list snapshot).outcome = { exitCode := 0, errorMessage? := none } ∧
      ∀ msg, msg ∈ (evaluateSnapshot .list snapshot).findings.toList ↔ SnapshotFinding snapshot msg := by
  refine ⟨rfl, fun msg => mem_collectFindings_iff snapshot msg⟩

theorem evaluateSnapshot_check_rejects_lakeTestDriver (snapshot : RepoSnapshot)
    (h : snapshot.lakeTestDriver ≠ "") :
    s!"lake-test-driver:{snapshot.lakeTestDriver}" ∈ (evaluateSnapshot .check snapshot).findings.toList ∧
      (evaluateSnapshot .check snapshot).outcome =
        { exitCode := 1
          errorMessage? := some s!"error: found {(evaluateSnapshot .check snapshot).findings.size} forbidden test item(s)" } := by
  have hmem : s!"lake-test-driver:{snapshot.lakeTestDriver}" ∈
      (evaluateSnapshot .check snapshot).findings.toList :=
    (mem_collectFindings_iff snapshot _).mpr (.lakeTestDriver h)
  exact ⟨hmem, decideOutcome_check_of_mem _ _ hmem⟩

theorem evaluateSnapshot_check_rejects_testDirectory (snapshot : RepoSnapshot)
    (file : ParsedFile) (hfile : file ∈ snapshot.files.toList)
    (hdir : "test" ∈ pathDirectories file.path ∨ "tests" ∈ pathDirectories file.path) :
    s!"file:{file.path}" ∈ (evaluateSnapshot .check snapshot).findings.toList ∧
      (evaluateSnapshot .check snapshot).outcome =
        { exitCode := 1
          errorMessage? := some s!"error: found {(evaluateSnapshot .check snapshot).findings.size} forbidden test item(s)" } := by
  have hmem : s!"file:{file.path}" ∈ (evaluateSnapshot .check snapshot).findings.toList :=
    (mem_collectFindings_iff snapshot _).mpr (.testDirectory hfile hdir)
  exact ⟨hmem, decideOutcome_check_of_mem _ _ hmem⟩

theorem evaluateSnapshot_check_rejects_forbiddenCommand (snapshot : RepoSnapshot)
    (file : ParsedFile) (cmd : Syntax) (info : SourceInfo) (k : SyntaxNodeKind) (args : Array Syntax)
    (hfile : file ∈ snapshot.files.toList) (hcmd : cmd ∈ file.commands.toList)
    (hsub : SubSyntax (.node info k args) cmd) (hk : IsForbiddenCommandKind k) :
    s!"{file.path}:{lineOfPos file.ictx (.node info k args)}:cmd:{k}" ∈
        (evaluateSnapshot .check snapshot).findings.toList ∧
      (evaluateSnapshot .check snapshot).outcome =
        { exitCode := 1
          errorMessage? := some s!"error: found {(evaluateSnapshot .check snapshot).findings.size} forbidden test item(s)" } := by
  have hmem : s!"{file.path}:{lineOfPos file.ictx (.node info k args)}:cmd:{k}" ∈
      (evaluateSnapshot .check snapshot).findings.toList :=
    (mem_collectFindings_iff snapshot _).mpr (.syntaxNode hfile hcmd hsub (.cmd hk))
  exact ⟨hmem, decideOutcome_check_of_mem _ _ hmem⟩

theorem evaluateSnapshot_check_rejects_forbiddenAttr (snapshot : RepoSnapshot)
    (file : ParsedFile) (cmd : Syntax) (info idInfo : SourceInfo) (args : Array Syntax)
    (rawVal : Substring.Raw) (n : Name) (preresolved : List Syntax.Preresolved)
    (hfile : file ∈ snapshot.files.toList) (hcmd : cmd ∈ file.commands.toList)
    (hsub : SubSyntax (.node info ``Lean.Parser.Attr.simple args) cmd)
    (h0 : 0 < args.size) (hident : args[0] = .ident idInfo rawVal n preresolved)
    (hn : IsForbiddenAttr n) :
    s!"{file.path}:{lineOfPos file.ictx args[0]}:attr:{n}" ∈
        (evaluateSnapshot .check snapshot).findings.toList ∧
      (evaluateSnapshot .check snapshot).outcome =
        { exitCode := 1
          errorMessage? := some s!"error: found {(evaluateSnapshot .check snapshot).findings.size} forbidden test item(s)" } := by
  have hmem : s!"{file.path}:{lineOfPos file.ictx args[0]}:attr:{n}" ∈
      (evaluateSnapshot .check snapshot).findings.toList :=
    (mem_collectFindings_iff snapshot _).mpr (.syntaxNode hfile hcmd hsub (.attr h0 hident hn))
  exact ⟨hmem, decideOutcome_check_of_mem _ _ hmem⟩

theorem evaluateSnapshot_check_empty_passes :
    evaluateSnapshot .check { lakeTestDriver := "", files := #[] } =
      { findings := #[], outcome := { exitCode := 0, errorMessage? := none } } := by
  rfl

theorem evaluateSnapshot_check_onlyLakeTestDriver (driver : String) (h : driver ≠ "") :
    evaluateSnapshot .check { lakeTestDriver := driver, files := #[] } =
      { findings := #[s!"lake-test-driver:{driver}"]
        outcome :=
          { exitCode := 1
            errorMessage? := some s!"error: found {(1 : Nat)} forbidden test item(s)" } } := by
  have hbeq : (driver == "") = false := beq_false_of_ne h
  have hne : (#[s!"lake-test-driver:{driver}"] : Array String).isEmpty = false := rfl
  have hsz : (#[s!"lake-test-driver:{driver}"] : Array String).size = 1 := rfl
  simp only [evaluateSnapshot, collectFindings, lakeTestDriverFindings, decideOutcome, hbeq,
    Bool.false_eq_true, ↓reduceIte, Array.foldl_empty, hne, hsz]

private theorem splitSlashChars_nonempty (acc cs : List Char) :
    splitSlashChars acc cs ≠ [] := by
  induction cs generalizing acc with
  | nil => simp [splitSlashChars]
  | cons c rest ih =>
    by_cases hc : c = '/'
    · subst hc
      simp [splitSlashChars]
    · cases c with
      | mk v hv =>
        simp [splitSlashChars, ih]

private theorem mem_dropLast_cons_of_nonempty {α : Type} {x : α} {xs : List α}
    (h : xs ≠ []) : x ∈ (x :: xs).dropLast := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons y ys => simp [List.dropLast]

theorem pathDirectories_mem_test_prefix (rest : String) :
    "test" ∈ pathDirectories ("test/" ++ rest) := by
  unfold pathDirectories
  rw [String.toList_append]
  change "test" ∈ ("test" :: splitSlashChars [] rest.toList).dropLast
  exact mem_dropLast_cons_of_nonempty (splitSlashChars_nonempty [] rest.toList)

theorem pathDirectories_mem_tests_prefix (rest : String) :
    "tests" ∈ pathDirectories ("tests/" ++ rest) := by
  unfold pathDirectories
  rw [String.toList_append]
  change "tests" ∈ ("tests" :: splitSlashChars [] rest.toList).dropLast
  exact mem_dropLast_cons_of_nonempty (splitSlashChars_nonempty [] rest.toList)

private theorem splitSlashChars_append_slash_eq (acc pre post : List Char) :
    ∃ pref, splitSlashChars acc (pre ++ '/' :: post) = pref ++ splitSlashChars [] post := by
  induction pre generalizing acc with
  | nil =>
    exact ⟨[String.ofList acc.reverse], rfl⟩
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc
      rcases ih [] with ⟨pref, hpref⟩
      exact ⟨String.ofList acc.reverse :: pref, by simp [splitSlashChars, hpref]⟩
    · rcases ih (c :: acc) with ⟨pref, hpref⟩
      cases c with
      | mk v hv =>
        exact ⟨pref, by simp [splitSlashChars, hpref]⟩

private theorem dropLast_append_of_nonempty {α : Type} (xs ys : List α) (hys : ys ≠ []) :
    (xs ++ ys).dropLast = xs ++ ys.dropLast := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hne : rest ++ ys ≠ [] := by
      intro hemp
      exact hys (List.append_eq_nil_iff.mp hemp).2
    cases h : rest ++ ys with
    | nil => exact False.elim (hne h)
    | cons y ys' =>
      simp only [List.cons_append, List.dropLast, h]
      rw [← h, ih]

theorem pathDirectories_mem_nested_test (pre rest : String) :
    "test" ∈ pathDirectories (pre ++ "/test/" ++ rest) := by
  unfold pathDirectories
  rw [String.toList_append, String.toList_append]
  have hmid : "/test/".toList = '/' :: ['t', 'e', 's', 't', '/'] := rfl
  rw [hmid, List.append_assoc, List.cons_append]
  rcases splitSlashChars_append_slash_eq [] pre.toList (['t', 'e', 's', 't', '/'] ++ rest.toList) with
    ⟨pref, hpref⟩
  rw [hpref, dropLast_append_of_nonempty pref _ (splitSlashChars_nonempty [] _), List.mem_append]
  refine Or.inr ?_
  change "test" ∈ ("test" :: splitSlashChars [] rest.toList).dropLast
  exact mem_dropLast_cons_of_nonempty (splitSlashChars_nonempty [] rest.toList)

theorem pathDirectories_mem_nested_tests (pre rest : String) :
    "tests" ∈ pathDirectories (pre ++ "/tests/" ++ rest) := by
  unfold pathDirectories
  rw [String.toList_append, String.toList_append]
  have hmid : "/tests/".toList = '/' :: ['t', 'e', 's', 't', 's', '/'] := rfl
  rw [hmid, List.append_assoc, List.cons_append]
  rcases splitSlashChars_append_slash_eq [] pre.toList (['t', 'e', 's', 't', 's', '/'] ++ rest.toList) with
    ⟨pref, hpref⟩
  rw [hpref, dropLast_append_of_nonempty pref _ (splitSlashChars_nonempty [] _), List.mem_append]
  refine Or.inr ?_
  change "tests" ∈ ("tests" :: splitSlashChars [] rest.toList).dropLast
  exact mem_dropLast_cons_of_nonempty (splitSlashChars_nonempty [] rest.toList)

end

private unsafe def enableInitializersImpl : IO Unit :=
  Lean.enableInitializersExecution

@[implemented_by enableInitializersImpl]
private def enableInitializers : IO Unit := pure ()

private def loadPackageConfig (elanInstall? : Option Lake.ElanInstall)
    (leanInstall? : Option Lake.LeanInstall) (lakeInstall? : Option Lake.LakeInstall) :
    EIO Lake.CliError Lake.LoadConfig := do
  let some wsDir ← Lake.resolvePath? "."
    | throw <| .missingRootDir "."
  let lake ← match lakeInstall? with
    | none => throw .unknownLakeInstall
    | some lake => pure lake
  let lean ← match leanInstall? with
    | none => throw .unknownLeanInstall
    | some lean => pure lean
  let lakeEnv ← Lake.Env.compute lake lean elanInstall? none |>.adapt fun msg => .invalidEnv msg
  return {
    lakeArgs? := some #[]
    lakeEnv
    wsDir
    relConfigFile := Lake.defaultConfigFile
    packageOverrides := #[]
    lakeOpts := {}
    leanOpts := Lean.Options.empty
    reconfigure := false
    updateDeps := false
    updateToolchain := true
  }

private def readLakeTestDriver : IO String := do
  let installs ← Lake.findInstall?
  let loaded ← (((loadPackageConfig installs.1 installs.2.1 installs.2.2).adapt toString >>= fun config =>
    liftM (m := EIO String) ((Lake.loadPackage config).toBaseIO : BaseIO _)) :
      EIO String (Option Lake.Package)).toBaseIO
  match loaded with
  | .error why => throw <| IO.userError why
  | .ok none => throw <| IO.userError "Lake failed to load package configuration"
  | .ok (some pkg) => return pkg.testDriver

private def listTrackedLeanFiles : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["ls-files", "--full-name", "-z", "--", "*.lean"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"git ls-files failed: {out.stderr.trimAscii.toString}"
  let files := ((out.stdout.splitOn "\x00").filter (· != "")).toArray.qsort (· < ·)
  if files.isEmpty then
    throw <| IO.userError "git ls-files returned no Lean files"
  return files

private def parseLeanEnv : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializers
  let ictx := Parser.mkInputContext "import Lean\nimport Lake\n" "<init>"
  let (hdr, ps, msgs) ← Parser.parseHeader ictx
  let hstx : Elab.HeaderSyntax := ⟨hdr⟩
  let (env, hdrMsgs) ← Elab.processHeaderCore ps.pos (hstx.imports true) false {} msgs ictx
  if hdrMsgs.hasErrors then
    let shown ← hdrMsgs.toList.mapM (·.toString)
    throw <| IO.userError s!"failed to initialize Lean parser environment:\n{String.join shown}"
  return env

private def parseCommands (ictx : Parser.InputContext) (pmctx : Parser.ParserModuleContext)
    (file : String) (ps : Parser.ModuleParserState) (msgs : MessageLog)
    (acc : Array Syntax) : Except String (Array Syntax) :=
  let (cmd, ps', msgs') := Parser.parseCommand ictx pmctx ps msgs
  let acc' := acc.push cmd
  if Parser.isTerminalCommand cmd || ictx.atEnd ps'.pos then
    if msgs'.hasErrors then
      .error s!"{file}: Lean parser reported errors while scanning for tests"
    else
      .ok acc'
  else if _h : ps.pos.byteIdx < ps'.pos.byteIdx ∧ ps.pos.byteIdx < ictx.endPos.byteIdx then
    parseCommands ictx pmctx file ps' msgs' acc'
  else
    .error s!"{file}: Lean parser failed to advance while scanning for tests"
termination_by ictx.endPos.byteIdx - ps.pos.byteIdx
decreasing_by omega

public def loadRepoSnapshot : IO RepoSnapshot := do
  let lakeTestDriver ← readLakeTestDriver
  let env ← parseLeanEnv
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let files ← listTrackedLeanFiles
  let mut parsed : Array ParsedFile := #[]
  for path in files do
    let text ← IO.FS.readFile path
    let ictx := Parser.mkInputContext text path
    let (_, ps, msgs) ← Parser.parseHeader ictx
    if msgs.hasErrors then
      throw <| IO.userError s!"{path}: parse error in header while scanning for tests"
    match parseCommands ictx pmctx path ps msgs #[] with
    | .ok commands => parsed := parsed.push { path, ictx, commands }
    | .error err => throw <| IO.userError err
  return { lakeTestDriver, files := parsed }

public def collectTestFindings : IO (Array String) := do
  return collectFindings (← loadRepoSnapshot)

end NoComments.TestListing

public def main (args : List String) : IO UInt32 := do
  match NoComments.TestListing.parseMode args with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok mode =>
    let snapshot ← NoComments.TestListing.loadRepoSnapshot
    let result := NoComments.TestListing.evaluateSnapshot mode snapshot
    for f in result.findings do
      IO.println f
    if let some err := result.outcome.errorMessage? then
      IO.eprintln err
    return result.outcome.exitCode
