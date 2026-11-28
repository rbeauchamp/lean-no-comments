module

@[expose] public section

namespace NoCommentsSpecification.OwnersLogEntriesConfig

def restatement_parseConfig : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-parseConfig
date 2026-11-28
words 1
| Owner @rbeauchamp confirmed Option A on rbeauchamp/lean-no-comments#12: parseConfigRecord is a pure total function Lean.Json -> Except String Config.RepoConfig with ValidConfigJson/ConfigRefusal and ParseConfigFreedom preserved, JsonConfigOracle removed, and Lean.Json.parse plus .badJson moved to NoCommentsCLI (ConfigIO.loadConfig) with zero net TCB expansion.
by rbeauchamp
as owner
record NoCommentsSpecification.ConfigRecords.parseConfigRecord
revision 1161
| # The intent record NoCommentsSpecification.ConfigRecords.parseConfigRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} Lean.Json (fun (a : Lean.Json) => Except.{0, 0} String NoComments.Config.RepoConfig)
| ```
| 
| - **Requires:** parseConfigJson is a total pure function from Json to Except String RepoConfig.
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of type Json -> Except String RepoConfig until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_valid_repo_config
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), ∀ (cfg : NoComments.Config.RepoConfig), @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.ok.{0, 0} String NoComments.Config.RepoConfig cfg) → NoCommentsSpecification.ConfigSpec.ValidConfigJson json cfg
| ```
| 
| - **Requires:** Returns .ok cfg only when ValidConfigJson holds with normalized paths, allowed keys, and unique dirs.
| - **Rules out:** Unknown keys, empty workspace list, duplicate workspace dirs, '..'/backslash/NUL/newline/CR/tab paths, or blank reasons.
| - **Still allows:** Valid normalized RepoConfig values.
| - **Freedom O5 leaves:** Valid normalized field order/hash specifics.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.error.{0, 0} String NoComments.Config.RepoConfig msg) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| - **Requires:** Returns .error only when ConfigRefusal holds.
| - **Rules out:** Rejecting healthy configurations.
| - **Still allows:** Refusing invalid config inputs with arbitrary error strings.
| - **Freedom O5 leaves:** Error message wording is left free.
| 
| ## Vocabulary
| 
| ### ValidConfigJson, a predicate over `Prod.{0, 0} Lean.Json NoComments.Config.RepoConfig`
| 
| ```lean
| fun (p : Prod.{0, 0} Lean.Json NoComments.Config.RepoConfig) => NoCommentsSpecification.ConfigSpec.ValidConfigJson (@Prod.fst.{0, 0} Lean.Json NoComments.Config.RepoConfig p) (@Prod.snd.{0, 0} Lean.Json NoComments.Config.RepoConfig p)
| ```
| 
| - **Requires:** ValidConfigJson characterizes schema, allowed keys, normalized paths, and non-duplicate dirs.
| - **Rules out:** Malformed or unsafe configs.
| - **Still allows:** Normalized valid configs.
| - **Freedom O5 leaves:** Exact schema validation.
| 
| ### ConfigRefusal, a predicate over `Lean.Json`
| 
| ```lean
| NoCommentsSpecification.ConfigSpec.ConfigRefusal
| ```
| 
| - **Requires:** ConfigRefusal enumerates every config error cause.
| - **Rules out:** Healthy JSON configs.
| - **Still allows:** All malformed config inputs.
| - **Freedom O5 leaves:** Disjoint complement of ValidConfigJson.
| 
| ## Consequences
| 
| ### succeeds on every healthy configuration JSON value, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), NoCommentsSpecification.Healthy.ConfigJson json → @Exists.{1} NoComments.Config.RepoConfig (fun (cfg : NoComments.Config.RepoConfig) => @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.ok.{0, 0} String NoComments.Config.RepoConfig cfg))
| ```
| 
| - **Requires:** Any valid healthy config JSON value decodes to .ok cfg.
| - **Rules out:** False config rejections.
| - **Still allows:** Any schema-compliant decoder.
| - **Freedom O5 leaves:** Success guaranteed on healthy config JSON.
| 
| ### leaves refusal error wording free on invalid config JSON, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f Lean.Json.null) (@Except.error.{0, 0} String NoComments.Config.RepoConfig "denied")
| ```
| 
| - **Requires:** Some conforming config decoder returns "denied" on non-object JSON null.
| - **Rules out:** Nothing; establishes refusal-message freedom.
| - **Still allows:** Different human-readable error strings.
| - **Freedom O5 leaves:** Error formatting decided below owner level (O5 ParseConfigFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ParseConfigFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| Lean.Json → Except.{0, 0} String NoComments.Config.RepoConfig
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), ∀ (cfg : NoComments.Config.RepoConfig), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (json : Lean.Json) => fun (cfg : NoComments.Config.RepoConfig) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} (Array.{0} Lean.Json) (fun (wsArr : Array.{0} Lean.Json) => @Exists.{1} String (fun (ratchetRaw : String) => And (@Eq.{1} Lean.Json json (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr))) (And (@GT.gt.{0} Nat instLTNat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@Array.size.{0} Lean.Json wsArr)) (And (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (fun (_hc : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) => NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i _h) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.WorkspaceConfig) Nat NoComments.Config.WorkspaceConfig (fun (xs : Array.{0} NoComments.Config.WorkspaceConfig) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.WorkspaceConfig xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.WorkspaceConfig) (NoComments.Config.RepoConfig.workspaces cfg) i _hc))) (And (@List.Nodup.{0} String (@List.map.{0, 0} NoComments.Config.WorkspaceConfig String (fun (x : NoComments.Config.WorkspaceConfig) => NoComments.Config.WorkspaceConfig.dir x) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (And (NoCommentsSpecification.ConfigSpec.ValidConfigJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (fun (exclArr : Array.{0} Lean.Json) => And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)) (@Array.size.{0} Lean.Json exclArr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json exclArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (fun (_hc : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) => NoCommentsSpecification.ConfigSpec.ValidExcludeJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) exclArr i _h) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.ExcludeRule) Nat NoComments.Config.ExcludeRule (fun (xs : Array.{0} NoComments.Config.ExcludeRule) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.ExcludeRule xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.ExcludeRule) (NoComments.Config.RepoConfig.exclude cfg) i _hc)))) (fun (val : Lean.Json) => False) (fun («_» : Unit) => @Eq.{1} (Array.{0} NoComments.Config.ExcludeRule) (NoComments.Config.RepoConfig.exclude cfg) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str ratchetRaw))) (NoCommentsSpecification.ConfigSpec.NormRelFile ratchetRaw (NoComments.Config.RepoConfig.ratchet cfg)))))))))))))
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (ws : NoComments.Config.WorkspaceConfig), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (dirRaw : String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "dir" (@List.cons.{0} String "srcDir" (@List.cons.{0} String "lakeArgs" (@List.cons.{0} String "toolPrefixes" (@List.cons.{0} String "excludePrefixes" (@List.nil.{0} String)))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "dir") (@Option.some.{0} Lean.Json (Lean.Json.str dirRaw))) (And (NoCommentsSpecification.ConfigSpec.NormRelDir dirRaw (NoComments.Config.WorkspaceConfig.dir ws)) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "srcDir") (fun (v : Lean.Json) => @Exists.{1} String (fun (srcRaw : String) => And (@Eq.{1} Lean.Json v (Lean.Json.str srcRaw)) (NoCommentsSpecification.ConfigSpec.NormRelDir srcRaw (NoComments.Config.WorkspaceConfig.srcDir ws)))) (fun («_» : Unit) => @Eq.{1} String (NoComments.Config.WorkspaceConfig.srcDir ws) ".")) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lakeArgs") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidCleanStringArray v (NoComments.Config.WorkspaceConfig.lakeArgs ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.lakeArgs ws) (@List.toArray.{0} String (@List.nil.{0} String)))) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "toolPrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidPrefixArray v (NoComments.Config.WorkspaceConfig.toolPrefixes ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (@List.toArray.{0} String (@List.nil.{0} String)))) (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "excludePrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidPrefixArray v (NoComments.Config.WorkspaceConfig.excludePrefixes ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.excludePrefixes ws) (@List.toArray.{0} String (@List.nil.{0} String))))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormRelDir
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripTrailingSlashes (NoCommentsSpecification.ConfigSpec.stripDotSlash raw); Or (And (@Eq.{1} Bool (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned ".") (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned "")) Bool.true) (@Eq.{1} String out ".")) (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.cleanStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => Bool.not (@List.any.{0} Char (String.toList s) (fun (c : Char) => Bool.or (Bool.or (Bool.or (Bool.or (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 10))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 13)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 9)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 0)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 92)))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashes
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (@List.reverse.{0} Char (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev (@List.reverse.{0} Char (String.toList s))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev
| 
| A definition by well-founded recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev x) (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => fun (head : Char) => fun (tail : List.{0} Char) => fun (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)) => NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev: Lean accepts a definition by well-founded recursion only when its termination proof shows that the right of the equation uses the values of NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev, and of any function defined together with it, only at arguments below those on the left by a well-founded relation, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 47))) (instDecidableEqChar head (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => h_1 (@List.cons.{0} Char x_1 x_2) x_1 x_2 (@Eq.refl.{1} (List.{0} Char) (@List.cons.{0} Char x_1 x_2))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1
| 
| A definition. It has the universe parameters u_1, u, in that order. Its type:
| 
| ```lean
| ∀ {α : Type u}, ∀ {motive : ∀ (t : List.{u} α), Sort u_1}, ∀ (t : List.{u} α), ∀ (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)), (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α t)), motive t) → motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Type u} => fun {motive : ∀ (t : List.{u} α), Sort u_1} => fun (t : List.{u} α) => fun (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)) => @List.rec.{u_1, u} α (fun (x : List.{u} α) => (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α x)), motive x) → motive x) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.nil.{u} α))), motive (@List.nil.{u} α)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 2) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (head : α) => fun (tail : List.{u} α) => fun (tail_ih : (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α tail)), motive tail) → motive tail) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.cons.{u} α head tail))), motive (@List.cons.{u} α head tail)) => cons head tail) t
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlash
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (NoCommentsSpecification.ConfigSpec.stripDotSlashChars (String.toList s))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars
| 
| A definition by structural recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.ConfigSpec.stripDotSlashChars.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.ConfigSpec.stripDotSlashChars x) (NoCommentsSpecification.ConfigSpec.stripDotSlashChars.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => NoCommentsSpecification.ConfigSpec.stripDotSlashChars rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.ConfigSpec.stripDotSlashChars: Lean accepts a definition by structural recursion only when the right of the equation uses the values of NoCommentsSpecification.ConfigSpec.stripDotSlashChars, and of any function defined together with it, only at structural subterms of the arguments it recurses on, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.ConfigSpec.stripDotSlashChars and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 46))) (instDecidableEqChar head (Char.ofNat (nat_lit 46))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 46)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2))) (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47))) (instDecidableEqChar x_1 (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_3 : Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_3 x_2))) (h_1 x_2) x_1) (fun (x_3 : Not (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2)))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 46)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.validSegmentsBool
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => @List.all.{0} String (String.splitOn s "/") (fun (seg : String) => Bool.and (Bool.and (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg "") (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".")) (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".."))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_2 Unit.unit) (fun (val : Lean.Json) => h_1 val)
| ```
| 
| ### NoComments.Config.WorkspaceConfig.srcDir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidCleanStringArray
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (out : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (out : Array.{0} String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (And (@Eq.{1} Nat (@Array.size.{0} String out) (@Array.size.{0} Lean.Json arr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) => And (@Eq.{1} Lean.Json (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (Lean.Json.str (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho))) (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho)) Bool.true)))))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.lakeArgs
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidPrefixArray
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (out : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (out : Array.{0} String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (And (@Eq.{1} Nat (@Array.size.{0} String out) (@Array.size.{0} Lean.Json arr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) => @Exists.{1} String (fun (raw : String) => And (@Eq.{1} Lean.Json (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (Lean.Json.str raw)) (NoCommentsSpecification.ConfigSpec.NormPrefix raw (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho)))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormPrefix
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "./") (have trailing : Bool := @BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList cleaned)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47))); have body : String := @ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (String.ofList (@List.dropLast.{0} Char (String.toList cleaned))) cleaned; And (@Ne.{1} String body "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool body) Bool.true) (@Eq.{1} String out (@ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (@HAppend.hAppend.{0, 0, 0} String String String (@instHAppendOfAppend.{0} String instAppendString) body "/") body)))))))))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))), ∀ (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)), ∀ (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))) => fun (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)) => fun (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_3 Unit.unit) (fun (val : Lean.Json) => @NoCommentsSpecification.ConfigSpec.ValidConfigJson._sparseCasesOn_1.{u_1} (fun (x_1 : Lean.Json) => motive (@Option.some.{0} Lean.Json x_1)) val (fun (elems : Array.{0} Lean.Json) => h_1 elems) (fun (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx val)) => h_2 val))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson._sparseCasesOn_1
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive_1 : ∀ (t : Lean.Json), Sort u}, ∀ (t : Lean.Json), ∀ (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)), (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx t)), motive_1 t) → motive_1 t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive_1 : ∀ (t : Lean.Json), Sort u} => fun (t : Lean.Json) => fun (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)) => @Lean.Json.rec.{u} (fun (x : Lean.Json) => (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx x)), motive_1 x) → motive_1 x) (fun (x : Array.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : List.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => PUnit.{u}) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx Lean.Json.null)), motive_1 Lean.Json.null) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (b : Bool) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.bool b))), motive_1 (Lean.Json.bool b)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (n : Lean.JsonNumber) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.num n))), motive_1 (Lean.Json.num n)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (s : String) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.str s))), motive_1 (Lean.Json.str s)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 3))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (elems : Array.{0} Lean.Json) => fun (elems_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.arr elems))), motive_1 (Lean.Json.arr elems)) => arr elems) (fun (kvPairs : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => fun (kvPairs_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.obj kvPairs))), motive_1 (Lean.Json.obj kvPairs)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 5))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (toList : List.{0} Lean.Json) => fun (toList_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} (fun (head : Lean.Json) => fun (tail : List.{0} Lean.Json) => fun (head_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx head)), motive_1 head) → motive_1 head) => fun (tail_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (size : Nat) => fun (k : String) => fun (v : Lean.Json) => fun (l : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (r : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (v_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx v)), motive_1 v) → motive_1 v) => fun (l_ih : PUnit.{u}) => fun (r_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} t
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidExcludeJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (r : NoComments.Config.ExcludeRule), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (r : NoComments.Config.ExcludeRule) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (pfxRaw : String) => @Exists.{1} String (fun (reasonRaw : String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "prefix" (@List.cons.{0} String "reason" (@List.nil.{0} String))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "prefix") (@Option.some.{0} Lean.Json (Lean.Json.str pfxRaw))) (And (NoCommentsSpecification.ConfigSpec.NormPrefix pfxRaw (NoComments.Config.ExcludeRule.prefix_ r)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "reason") (@Option.some.{0} Lean.Json (Lean.Json.str reasonRaw))) (And (@Eq.{1} String (String.Slice.toString (String.trimAscii reasonRaw)) (NoComments.Config.ExcludeRule.reason r)) (@Ne.{1} String (NoComments.Config.ExcludeRule.reason r) "")))))))))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.ExcludeRule.reason
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormRelFile
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoComments.Config.RepoConfig.ratchet
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ConfigRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), Prop
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.notObject
| 
| ```lean
| ∀ {json : Lean.Json}, (∀ (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)), @Ne.{1} Lean.Json json (Lean.Json.obj obj)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.unknownRootKey
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {k : String}, ∀ {v : Lean.Json}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) (@Prod.mk.{0, 0} String Lean.Json k v) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) k) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badWorkspacesField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → (∀ (wsArr : Array.{0} Lean.Json), @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → @Eq.{1} Nat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.invalidWorkspace
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {wsArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → (∀ (ws : NoComments.Config.WorkspaceConfig), Not (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i hi) ws)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.duplicateWorkspaceDir
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {wsArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ {j : Nat}, ∀ {ws1 : NoComments.Config.WorkspaceConfig}, ∀ {ws2 : NoComments.Config.WorkspaceConfig}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), ∀ (hj : @LT.lt.{0} Nat instLTNat j (@Array.size.{0} Lean.Json wsArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → @Ne.{1} Nat i j → NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i hi) ws1 → NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr j hj) ws2 → @Eq.{1} String (NoComments.Config.WorkspaceConfig.dir ws1) (NoComments.Config.WorkspaceConfig.dir ws2) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badExcludeField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {v : Lean.Json}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (@Option.some.{0} Lean.Json v) → (∀ (exclArr : Array.{0} Lean.Json), @Ne.{1} Lean.Json v (Lean.Json.arr exclArr)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.invalidExcludeRule
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {exclArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json exclArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr)) → (∀ (r : NoComments.Config.ExcludeRule), Not (NoCommentsSpecification.ConfigSpec.ValidExcludeJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) exclArr i hi) r)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badRatchetField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → (∀ (raw : String), ∀ (out : String), @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str raw)) → Not (NoCommentsSpecification.ConfigSpec.NormRelFile raw out)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (json : Lean.Json) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} (Array.{0} Lean.Json) (fun (wsArr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (dirs : List.{0} String) => @Exists.{1} String (fun (ratchetRaw : String) => @Exists.{1} String (fun (ratchetOut : String) => And (@Eq.{1} Lean.Json json (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr))) (And (@GT.gt.{0} Nat instLTNat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} Nat (@List.length.{0} String dirs) (@Array.size.{0} Lean.Json wsArr)) (And (@List.Nodup.{0} String dirs) (And (∀ (i : Nat), ∀ (h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} String dirs)) (fun (hd : @LT.lt.{0} Nat instLTNat i (@List.length.{0} String dirs)) => NoCommentsSpecification.Healthy.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i h) (@GetElem.getElem.{0, 0, 0} (List.{0} String) Nat String (fun (as : List.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} String as)) (@List.instGetElemNatLtLength.{0} String) dirs i hd))) (And (NoCommentsSpecification.Healthy.ConfigJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (fun (exclArr : Array.{0} Lean.Json) => ∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json exclArr) item → NoCommentsSpecification.Healthy.ValidExcludeJson item) (fun (val : Lean.Json) => False) (fun («_» : Unit) => True)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str ratchetRaw))) (NoCommentsSpecification.Healthy.ValidRelFile ratchetRaw ratchetOut))))))))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidWorkspaceJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (dirOut : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (dirOut : String) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "dir" (@List.cons.{0} String "srcDir" (@List.cons.{0} String "lakeArgs" (@List.cons.{0} String "toolPrefixes" (@List.cons.{0} String "excludePrefixes" (@List.nil.{0} String)))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Exists.{1} String (fun (dirRaw : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "dir") (@Option.some.{0} Lean.Json (Lean.Json.str dirRaw))) (NoCommentsSpecification.Healthy.ValidRelDir dirRaw dirOut))) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "srcDir") (fun (v : Lean.Json) => @Exists.{1} String (fun (s : String) => @Exists.{1} String (fun (out : String) => And (@Eq.{1} Lean.Json v (Lean.Json.str s)) (NoCommentsSpecification.Healthy.ValidRelDir s out)))) (fun («_» : Unit) => True)) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lakeArgs") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.cleanStringList v) (fun («_» : Unit) => True)) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "toolPrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.validPrefixList v) (fun («_» : Unit) => True)) (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "excludePrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.validPrefixList v) (fun («_» : Unit) => True))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRelDir
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripTrailingSlashes (NoCommentsSpecification.Healthy.stripDotSlash raw); Or (And (@Eq.{1} Bool (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned ".") (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned "")) Bool.true) (@Eq.{1} String out ".")) (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.cleanStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => Bool.not (@List.any.{0} Char (String.toList s) (fun (c : Char) => Bool.or (Bool.or (Bool.or (Bool.or (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 10))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 13)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 9)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 0)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 92)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashes
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (@List.reverse.{0} Char (NoCommentsSpecification.Healthy.stripTrailingSlashRev (@List.reverse.{0} Char (String.toList s))))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashRev
| 
| A definition by well-founded recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.Healthy.stripTrailingSlashRev.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.Healthy.stripTrailingSlashRev x) (NoCommentsSpecification.Healthy.stripTrailingSlashRev.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => fun (head : Char) => fun (tail : List.{0} Char) => fun (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)) => NoCommentsSpecification.Healthy.stripTrailingSlashRev rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.Healthy.stripTrailingSlashRev: Lean accepts a definition by well-founded recursion only when its termination proof shows that the right of the equation uses the values of NoCommentsSpecification.Healthy.stripTrailingSlashRev, and of any function defined together with it, only at arguments below those on the left by a well-founded relation, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.Healthy.stripTrailingSlashRev and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashRev.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 47))) (instDecidableEqChar head (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => h_1 (@List.cons.{0} Char x_1 x_2) x_1 x_2 (@Eq.refl.{1} (List.{0} Char) (@List.cons.{0} Char x_1 x_2))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1
| 
| A definition. It has the universe parameters u_1, u, in that order. Its type:
| 
| ```lean
| ∀ {α : Type u}, ∀ {motive : ∀ (t : List.{u} α), Sort u_1}, ∀ (t : List.{u} α), ∀ (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)), (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α t)), motive t) → motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Type u} => fun {motive : ∀ (t : List.{u} α), Sort u_1} => fun (t : List.{u} α) => fun (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)) => @List.rec.{u_1, u} α (fun (x : List.{u} α) => (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α x)), motive x) → motive x) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.nil.{u} α))), motive (@List.nil.{u} α)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 2) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (head : α) => fun (tail : List.{u} α) => fun (tail_ih : (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α tail)), motive tail) → motive tail) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.cons.{u} α head tail))), motive (@List.cons.{u} α head tail)) => cons head tail) t
| ```
| 
| ### NoCommentsSpecification.Healthy.stripDotSlash
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (NoCommentsSpecification.Healthy.stripDotSlashChars (String.toList s))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripDotSlashChars
| 
| A definition by structural recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.Healthy.stripDotSlashChars.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.Healthy.stripDotSlashChars x) (NoCommentsSpecification.Healthy.stripDotSlashChars.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => NoCommentsSpecification.Healthy.stripDotSlashChars rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.Healthy.stripDotSlashChars: Lean accepts a definition by structural recursion only when the right of the equation uses the values of NoCommentsSpecification.Healthy.stripDotSlashChars, and of any function defined together with it, only at structural subterms of the arguments it recurses on, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.Healthy.stripDotSlashChars and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.Healthy.stripDotSlashChars.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 46))) (instDecidableEqChar head (Char.ofNat (nat_lit 46))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 46)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2))) (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47))) (instDecidableEqChar x_1 (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_3 : Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_3 x_2))) (h_1 x_2) x_1) (fun (x_3 : Not (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2)))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 46)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.Healthy.validSegmentsBool
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => @List.all.{0} String (String.splitOn s "/") (fun (seg : String) => Bool.and (Bool.and (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg "") (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".")) (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".."))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_2 Unit.unit) (fun (val : Lean.Json) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.cleanStringList
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json arr) item → @Exists.{1} String (fun (s : String) => And (@Eq.{1} Lean.Json item (Lean.Json.str s)) (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr s) Bool.true))))
| ```
| 
| ### NoCommentsSpecification.Healthy.validPrefixList
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json arr) item → @Exists.{1} String (fun (s : String) => @Exists.{1} String (fun (pfx : String) => And (@Eq.{1} Lean.Json item (Lean.Json.str s)) (NoCommentsSpecification.Healthy.ValidPrefix s pfx)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidPrefix
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "./") (have trailing : Bool := @BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList cleaned)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47))); have body : String := @ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (String.ofList (@List.dropLast.{0} Char (String.toList cleaned))) cleaned; And (@Ne.{1} String body "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool body) Bool.true) (@Eq.{1} String out (@ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (@HAppend.hAppend.{0, 0, 0} String String String (@instHAppendOfAppend.{0} String instAppendString) body "/") body)))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))), ∀ (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)), ∀ (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))) => fun (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)) => fun (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_3 Unit.unit) (fun (val : Lean.Json) => @NoCommentsSpecification.Healthy.ConfigJson._sparseCasesOn_1.{u_1} (fun (x_1 : Lean.Json) => motive (@Option.some.{0} Lean.Json x_1)) val (fun (elems : Array.{0} Lean.Json) => h_1 elems) (fun (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx val)) => h_2 val))
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson._sparseCasesOn_1
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive_1 : ∀ (t : Lean.Json), Sort u}, ∀ (t : Lean.Json), ∀ (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)), (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx t)), motive_1 t) → motive_1 t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive_1 : ∀ (t : Lean.Json), Sort u} => fun (t : Lean.Json) => fun (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)) => @Lean.Json.rec.{u} (fun (x : Lean.Json) => (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx x)), motive_1 x) → motive_1 x) (fun (x : Array.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : List.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => PUnit.{u}) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx Lean.Json.null)), motive_1 Lean.Json.null) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (b : Bool) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.bool b))), motive_1 (Lean.Json.bool b)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (n : Lean.JsonNumber) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.num n))), motive_1 (Lean.Json.num n)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (s : String) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.str s))), motive_1 (Lean.Json.str s)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 3))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (elems : Array.{0} Lean.Json) => fun (elems_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.arr elems))), motive_1 (Lean.Json.arr elems)) => arr elems) (fun (kvPairs : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => fun (kvPairs_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.obj kvPairs))), motive_1 (Lean.Json.obj kvPairs)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 5))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (toList : List.{0} Lean.Json) => fun (toList_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} (fun (head : Lean.Json) => fun (tail : List.{0} Lean.Json) => fun (head_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx head)), motive_1 head) → motive_1 head) => fun (tail_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (size : Nat) => fun (k : String) => fun (v : Lean.Json) => fun (l : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (r : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (v_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx v)), motive_1 v) → motive_1 v) => fun (l_ih : PUnit.{u}) => fun (r_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} t
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidExcludeJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "prefix" (@List.cons.{0} String "reason" (@List.nil.{0} String))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Exists.{1} String (fun (pfxRaw : String) => @Exists.{1} String (fun (pfxOut : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "prefix") (@Option.some.{0} Lean.Json (Lean.Json.str pfxRaw))) (NoCommentsSpecification.Healthy.ValidPrefix pfxRaw pfxOut)))) (@Exists.{1} String (fun (reasonRaw : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "reason") (@Option.some.{0} Lean.Json (Lean.Json.str reasonRaw))) (@Ne.{1} String (String.Slice.toString (String.trimAscii reasonRaw)) ""))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRelFile
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence the record's plain restatement
shown as entailment
predicate 1
| the record, as its revision prints it
verdict confirmed
"###

def delegated_parseConfig : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-parseConfig
date 2026-11-28
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.ConfigRecords.parseConfigRecord
revision 1161
| # The intent record NoCommentsSpecification.ConfigRecords.parseConfigRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} Lean.Json (fun (a : Lean.Json) => Except.{0, 0} String NoComments.Config.RepoConfig)
| ```
| 
| - **Requires:** parseConfigJson is a total pure function from Json to Except String RepoConfig.
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of type Json -> Except String RepoConfig until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_valid_repo_config
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), ∀ (cfg : NoComments.Config.RepoConfig), @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.ok.{0, 0} String NoComments.Config.RepoConfig cfg) → NoCommentsSpecification.ConfigSpec.ValidConfigJson json cfg
| ```
| 
| - **Requires:** Returns .ok cfg only when ValidConfigJson holds with normalized paths, allowed keys, and unique dirs.
| - **Rules out:** Unknown keys, empty workspace list, duplicate workspace dirs, '..'/backslash/NUL/newline/CR/tab paths, or blank reasons.
| - **Still allows:** Valid normalized RepoConfig values.
| - **Freedom O5 leaves:** Valid normalized field order/hash specifics.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.error.{0, 0} String NoComments.Config.RepoConfig msg) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| - **Requires:** Returns .error only when ConfigRefusal holds.
| - **Rules out:** Rejecting healthy configurations.
| - **Still allows:** Refusing invalid config inputs with arbitrary error strings.
| - **Freedom O5 leaves:** Error message wording is left free.
| 
| ## Vocabulary
| 
| ### ValidConfigJson, a predicate over `Prod.{0, 0} Lean.Json NoComments.Config.RepoConfig`
| 
| ```lean
| fun (p : Prod.{0, 0} Lean.Json NoComments.Config.RepoConfig) => NoCommentsSpecification.ConfigSpec.ValidConfigJson (@Prod.fst.{0, 0} Lean.Json NoComments.Config.RepoConfig p) (@Prod.snd.{0, 0} Lean.Json NoComments.Config.RepoConfig p)
| ```
| 
| - **Requires:** ValidConfigJson characterizes schema, allowed keys, normalized paths, and non-duplicate dirs.
| - **Rules out:** Malformed or unsafe configs.
| - **Still allows:** Normalized valid configs.
| - **Freedom O5 leaves:** Exact schema validation.
| 
| ### ConfigRefusal, a predicate over `Lean.Json`
| 
| ```lean
| NoCommentsSpecification.ConfigSpec.ConfigRefusal
| ```
| 
| - **Requires:** ConfigRefusal enumerates every config error cause.
| - **Rules out:** Healthy JSON configs.
| - **Still allows:** All malformed config inputs.
| - **Freedom O5 leaves:** Disjoint complement of ValidConfigJson.
| 
| ## Consequences
| 
| ### succeeds on every healthy configuration JSON value, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => ∀ (json : Lean.Json), NoCommentsSpecification.Healthy.ConfigJson json → @Exists.{1} NoComments.Config.RepoConfig (fun (cfg : NoComments.Config.RepoConfig) => @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f json) (@Except.ok.{0, 0} String NoComments.Config.RepoConfig cfg))
| ```
| 
| - **Requires:** Any valid healthy config JSON value decodes to .ok cfg.
| - **Rules out:** False config rejections.
| - **Still allows:** Any schema-compliant decoder.
| - **Freedom O5 leaves:** Success guaranteed on healthy config JSON.
| 
| ### leaves refusal error wording free on invalid config JSON, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f Lean.Json.null) (@Except.error.{0, 0} String NoComments.Config.RepoConfig "denied")
| ```
| 
| - **Requires:** Some conforming config decoder returns "denied" on non-object JSON null.
| - **Rules out:** Nothing; establishes refusal-message freedom.
| - **Still allows:** Different human-readable error strings.
| - **Freedom O5 leaves:** Error formatting decided below owner level (O5 ParseConfigFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ParseConfigFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| Lean.Json → Except.{0, 0} String NoComments.Config.RepoConfig
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), ∀ (cfg : NoComments.Config.RepoConfig), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (json : Lean.Json) => fun (cfg : NoComments.Config.RepoConfig) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} (Array.{0} Lean.Json) (fun (wsArr : Array.{0} Lean.Json) => @Exists.{1} String (fun (ratchetRaw : String) => And (@Eq.{1} Lean.Json json (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr))) (And (@GT.gt.{0} Nat instLTNat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@Array.size.{0} Lean.Json wsArr)) (And (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (fun (_hc : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) => NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i _h) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.WorkspaceConfig) Nat NoComments.Config.WorkspaceConfig (fun (xs : Array.{0} NoComments.Config.WorkspaceConfig) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.WorkspaceConfig xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.WorkspaceConfig) (NoComments.Config.RepoConfig.workspaces cfg) i _hc))) (And (@List.Nodup.{0} String (@List.map.{0, 0} NoComments.Config.WorkspaceConfig String (fun (x : NoComments.Config.WorkspaceConfig) => NoComments.Config.WorkspaceConfig.dir x) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (And (NoCommentsSpecification.ConfigSpec.ValidConfigJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (fun (exclArr : Array.{0} Lean.Json) => And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)) (@Array.size.{0} Lean.Json exclArr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json exclArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (fun (_hc : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) => NoCommentsSpecification.ConfigSpec.ValidExcludeJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) exclArr i _h) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.ExcludeRule) Nat NoComments.Config.ExcludeRule (fun (xs : Array.{0} NoComments.Config.ExcludeRule) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.ExcludeRule xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.ExcludeRule) (NoComments.Config.RepoConfig.exclude cfg) i _hc)))) (fun (val : Lean.Json) => False) (fun («_» : Unit) => @Eq.{1} (Array.{0} NoComments.Config.ExcludeRule) (NoComments.Config.RepoConfig.exclude cfg) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str ratchetRaw))) (NoCommentsSpecification.ConfigSpec.NormRelFile ratchetRaw (NoComments.Config.RepoConfig.ratchet cfg)))))))))))))
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (ws : NoComments.Config.WorkspaceConfig), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (dirRaw : String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "dir" (@List.cons.{0} String "srcDir" (@List.cons.{0} String "lakeArgs" (@List.cons.{0} String "toolPrefixes" (@List.cons.{0} String "excludePrefixes" (@List.nil.{0} String)))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "dir") (@Option.some.{0} Lean.Json (Lean.Json.str dirRaw))) (And (NoCommentsSpecification.ConfigSpec.NormRelDir dirRaw (NoComments.Config.WorkspaceConfig.dir ws)) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "srcDir") (fun (v : Lean.Json) => @Exists.{1} String (fun (srcRaw : String) => And (@Eq.{1} Lean.Json v (Lean.Json.str srcRaw)) (NoCommentsSpecification.ConfigSpec.NormRelDir srcRaw (NoComments.Config.WorkspaceConfig.srcDir ws)))) (fun («_» : Unit) => @Eq.{1} String (NoComments.Config.WorkspaceConfig.srcDir ws) ".")) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lakeArgs") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidCleanStringArray v (NoComments.Config.WorkspaceConfig.lakeArgs ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.lakeArgs ws) (@List.toArray.{0} String (@List.nil.{0} String)))) (And (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "toolPrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidPrefixArray v (NoComments.Config.WorkspaceConfig.toolPrefixes ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (@List.toArray.{0} String (@List.nil.{0} String)))) (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "excludePrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.ConfigSpec.ValidPrefixArray v (NoComments.Config.WorkspaceConfig.excludePrefixes ws)) (fun («_» : Unit) => @Eq.{1} (Array.{0} String) (NoComments.Config.WorkspaceConfig.excludePrefixes ws) (@List.toArray.{0} String (@List.nil.{0} String))))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormRelDir
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripTrailingSlashes (NoCommentsSpecification.ConfigSpec.stripDotSlash raw); Or (And (@Eq.{1} Bool (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned ".") (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned "")) Bool.true) (@Eq.{1} String out ".")) (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.cleanStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => Bool.not (@List.any.{0} Char (String.toList s) (fun (c : Char) => Bool.or (Bool.or (Bool.or (Bool.or (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 10))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 13)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 9)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 0)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 92)))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashes
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (@List.reverse.{0} Char (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev (@List.reverse.{0} Char (String.toList s))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev
| 
| A definition by well-founded recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev x) (NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => fun (head : Char) => fun (tail : List.{0} Char) => fun (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)) => NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev: Lean accepts a definition by well-founded recursion only when its termination proof shows that the right of the equation uses the values of NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev, and of any function defined together with it, only at arguments below those on the left by a well-founded relation, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.ConfigSpec.stripTrailingSlashRev.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 47))) (instDecidableEqChar head (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => h_1 (@List.cons.{0} Char x_1 x_2) x_1 x_2 (@Eq.refl.{1} (List.{0} Char) (@List.cons.{0} Char x_1 x_2))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1
| 
| A definition. It has the universe parameters u_1, u, in that order. Its type:
| 
| ```lean
| ∀ {α : Type u}, ∀ {motive : ∀ (t : List.{u} α), Sort u_1}, ∀ (t : List.{u} α), ∀ (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)), (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α t)), motive t) → motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Type u} => fun {motive : ∀ (t : List.{u} α), Sort u_1} => fun (t : List.{u} α) => fun (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)) => @List.rec.{u_1, u} α (fun (x : List.{u} α) => (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α x)), motive x) → motive x) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.nil.{u} α))), motive (@List.nil.{u} α)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 2) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (head : α) => fun (tail : List.{u} α) => fun (tail_ih : (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α tail)), motive tail) → motive tail) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.cons.{u} α head tail))), motive (@List.cons.{u} α head tail)) => cons head tail) t
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlash
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (NoCommentsSpecification.ConfigSpec.stripDotSlashChars (String.toList s))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars
| 
| A definition by structural recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.ConfigSpec.stripDotSlashChars.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.ConfigSpec.stripDotSlashChars x) (NoCommentsSpecification.ConfigSpec.stripDotSlashChars.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => NoCommentsSpecification.ConfigSpec.stripDotSlashChars rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.ConfigSpec.stripDotSlashChars: Lean accepts a definition by structural recursion only when the right of the equation uses the values of NoCommentsSpecification.ConfigSpec.stripDotSlashChars, and of any function defined together with it, only at structural subterms of the arguments it recurses on, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.ConfigSpec.stripDotSlashChars and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.ConfigSpec.stripDotSlashChars.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 46))) (instDecidableEqChar head (Char.ofNat (nat_lit 46))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 46)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.ConfigSpec.stripDotSlashChars._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2))) (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47))) (instDecidableEqChar x_1 (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_3 : Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_3 x_2))) (h_1 x_2) x_1) (fun (x_3 : Not (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2)))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 46)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.validSegmentsBool
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => @List.all.{0} String (String.splitOn s "/") (fun (seg : String) => Bool.and (Bool.and (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg "") (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".")) (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".."))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_2 Unit.unit) (fun (val : Lean.Json) => h_1 val)
| ```
| 
| ### NoComments.Config.WorkspaceConfig.srcDir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidCleanStringArray
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (out : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (out : Array.{0} String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (And (@Eq.{1} Nat (@Array.size.{0} String out) (@Array.size.{0} Lean.Json arr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) => And (@Eq.{1} Lean.Json (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (Lean.Json.str (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho))) (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho)) Bool.true)))))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.lakeArgs
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidPrefixArray
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (out : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (out : Array.{0} String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (And (@Eq.{1} Nat (@Array.size.{0} String out) (@Array.size.{0} Lean.Json arr)) (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String out)) => @Exists.{1} String (fun (raw : String) => And (@Eq.{1} Lean.Json (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (Lean.Json.str raw)) (NoCommentsSpecification.ConfigSpec.NormPrefix raw (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) out i _ho)))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormPrefix
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "./") (have trailing : Bool := @BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList cleaned)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47))); have body : String := @ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (String.ofList (@List.dropLast.{0} Char (String.toList cleaned))) cleaned; And (@Ne.{1} String body "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool body) Bool.true) (@Eq.{1} String out (@ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (@HAppend.hAppend.{0, 0, 0} String String String (@instHAppendOfAppend.{0} String instAppendString) body "/") body)))))))))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))), ∀ (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)), ∀ (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))) => fun (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)) => fun (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_3 Unit.unit) (fun (val : Lean.Json) => @NoCommentsSpecification.ConfigSpec.ValidConfigJson._sparseCasesOn_1.{u_1} (fun (x_1 : Lean.Json) => motive (@Option.some.{0} Lean.Json x_1)) val (fun (elems : Array.{0} Lean.Json) => h_1 elems) (fun (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx val)) => h_2 val))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidConfigJson._sparseCasesOn_1
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive_1 : ∀ (t : Lean.Json), Sort u}, ∀ (t : Lean.Json), ∀ (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)), (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx t)), motive_1 t) → motive_1 t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive_1 : ∀ (t : Lean.Json), Sort u} => fun (t : Lean.Json) => fun (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)) => @Lean.Json.rec.{u} (fun (x : Lean.Json) => (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx x)), motive_1 x) → motive_1 x) (fun (x : Array.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : List.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => PUnit.{u}) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx Lean.Json.null)), motive_1 Lean.Json.null) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (b : Bool) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.bool b))), motive_1 (Lean.Json.bool b)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (n : Lean.JsonNumber) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.num n))), motive_1 (Lean.Json.num n)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (s : String) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.str s))), motive_1 (Lean.Json.str s)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 3))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (elems : Array.{0} Lean.Json) => fun (elems_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.arr elems))), motive_1 (Lean.Json.arr elems)) => arr elems) (fun (kvPairs : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => fun (kvPairs_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.obj kvPairs))), motive_1 (Lean.Json.obj kvPairs)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 5))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (toList : List.{0} Lean.Json) => fun (toList_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} (fun (head : Lean.Json) => fun (tail : List.{0} Lean.Json) => fun (head_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx head)), motive_1 head) → motive_1 head) => fun (tail_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (size : Nat) => fun (k : String) => fun (v : Lean.Json) => fun (l : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (r : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (v_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx v)), motive_1 v) → motive_1 v) => fun (l_ih : PUnit.{u}) => fun (r_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} t
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ValidExcludeJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (r : NoComments.Config.ExcludeRule), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (r : NoComments.Config.ExcludeRule) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (pfxRaw : String) => @Exists.{1} String (fun (reasonRaw : String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "prefix" (@List.cons.{0} String "reason" (@List.nil.{0} String))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "prefix") (@Option.some.{0} Lean.Json (Lean.Json.str pfxRaw))) (And (NoCommentsSpecification.ConfigSpec.NormPrefix pfxRaw (NoComments.Config.ExcludeRule.prefix_ r)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "reason") (@Option.some.{0} Lean.Json (Lean.Json.str reasonRaw))) (And (@Eq.{1} String (String.Slice.toString (String.trimAscii reasonRaw)) (NoComments.Config.ExcludeRule.reason r)) (@Ne.{1} String (NoComments.Config.ExcludeRule.reason r) "")))))))))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.ExcludeRule.reason
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.NormRelFile
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.ConfigSpec.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Eq.{1} Bool (NoCommentsSpecification.ConfigSpec.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoComments.Config.RepoConfig.ratchet
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ConfigRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), Prop
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.notObject
| 
| ```lean
| ∀ {json : Lean.Json}, (∀ (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)), @Ne.{1} Lean.Json json (Lean.Json.obj obj)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.unknownRootKey
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {k : String}, ∀ {v : Lean.Json}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) (@Prod.mk.{0, 0} String Lean.Json k v) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) k) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badWorkspacesField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → (∀ (wsArr : Array.{0} Lean.Json), @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → @Eq.{1} Nat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.invalidWorkspace
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {wsArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → (∀ (ws : NoComments.Config.WorkspaceConfig), Not (NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i hi) ws)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.duplicateWorkspaceDir
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {wsArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ {j : Nat}, ∀ {ws1 : NoComments.Config.WorkspaceConfig}, ∀ {ws2 : NoComments.Config.WorkspaceConfig}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), ∀ (hj : @LT.lt.{0} Nat instLTNat j (@Array.size.{0} Lean.Json wsArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr)) → @Ne.{1} Nat i j → NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i hi) ws1 → NoCommentsSpecification.ConfigSpec.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr j hj) ws2 → @Eq.{1} String (NoComments.Config.WorkspaceConfig.dir ws1) (NoComments.Config.WorkspaceConfig.dir ws2) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badExcludeField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {v : Lean.Json}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (@Option.some.{0} Lean.Json v) → (∀ (exclArr : Array.{0} Lean.Json), @Ne.{1} Lean.Json v (Lean.Json.arr exclArr)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.invalidExcludeRule
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, ∀ {exclArr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json exclArr)), @Eq.{1} Lean.Json json (Lean.Json.obj obj) → @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr)) → (∀ (r : NoComments.Config.ExcludeRule), Not (NoCommentsSpecification.ConfigSpec.ValidExcludeJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) exclArr i hi) r)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ConfigRefusal.badRatchetField
| 
| ```lean
| ∀ {json : Lean.Json}, ∀ {obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)}, @Eq.{1} Lean.Json json (Lean.Json.obj obj) → (∀ (raw : String), ∀ (out : String), @Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str raw)) → Not (NoCommentsSpecification.ConfigSpec.NormRelFile raw out)) → NoCommentsSpecification.ConfigSpec.ConfigRefusal json
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (json : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (json : Lean.Json) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} (Array.{0} Lean.Json) (fun (wsArr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (dirs : List.{0} String) => @Exists.{1} String (fun (ratchetRaw : String) => @Exists.{1} String (fun (ratchetOut : String) => And (@Eq.{1} Lean.Json json (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "workspaces" (@List.cons.{0} String "exclude" (@List.cons.{0} String "ratchet" (@List.nil.{0} String)))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "workspaces") (@Option.some.{0} Lean.Json (Lean.Json.arr wsArr))) (And (@GT.gt.{0} Nat instLTNat (@Array.size.{0} Lean.Json wsArr) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} Nat (@List.length.{0} String dirs) (@Array.size.{0} Lean.Json wsArr)) (And (@List.Nodup.{0} String dirs) (And (∀ (i : Nat), ∀ (h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json wsArr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} String dirs)) (fun (hd : @LT.lt.{0} Nat instLTNat i (@List.length.{0} String dirs)) => NoCommentsSpecification.Healthy.ValidWorkspaceJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) wsArr i h) (@GetElem.getElem.{0, 0, 0} (List.{0} String) Nat String (fun (as : List.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} String as)) (@List.instGetElemNatLtLength.{0} String) dirs i hd))) (And (NoCommentsSpecification.Healthy.ConfigJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "exclude") (fun (exclArr : Array.{0} Lean.Json) => ∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json exclArr) item → NoCommentsSpecification.Healthy.ValidExcludeJson item) (fun (val : Lean.Json) => False) (fun («_» : Unit) => True)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "ratchet") (@Option.some.{0} Lean.Json (Lean.Json.str ratchetRaw))) (NoCommentsSpecification.Healthy.ValidRelFile ratchetRaw ratchetOut))))))))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidWorkspaceJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (dirOut : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (dirOut : String) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "dir" (@List.cons.{0} String "srcDir" (@List.cons.{0} String "lakeArgs" (@List.cons.{0} String "toolPrefixes" (@List.cons.{0} String "excludePrefixes" (@List.nil.{0} String)))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Exists.{1} String (fun (dirRaw : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "dir") (@Option.some.{0} Lean.Json (Lean.Json.str dirRaw))) (NoCommentsSpecification.Healthy.ValidRelDir dirRaw dirOut))) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "srcDir") (fun (v : Lean.Json) => @Exists.{1} String (fun (s : String) => @Exists.{1} String (fun (out : String) => And (@Eq.{1} Lean.Json v (Lean.Json.str s)) (NoCommentsSpecification.Healthy.ValidRelDir s out)))) (fun («_» : Unit) => True)) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lakeArgs") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.cleanStringList v) (fun («_» : Unit) => True)) (And (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "toolPrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.validPrefixList v) (fun («_» : Unit) => True)) (NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1.{1} (fun (x : Option.{0} Lean.Json) => Prop) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "excludePrefixes") (fun (v : Lean.Json) => NoCommentsSpecification.Healthy.validPrefixList v) (fun («_» : Unit) => True))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRelDir
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripTrailingSlashes (NoCommentsSpecification.Healthy.stripDotSlash raw); Or (And (@Eq.{1} Bool (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned ".") (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) cleaned "")) Bool.true) (@Eq.{1} String out ".")) (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.cleanStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => Bool.not (@List.any.{0} Char (String.toList s) (fun (c : Char) => Bool.or (Bool.or (Bool.or (Bool.or (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 10))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 13)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 9)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 0)))) (@BEq.beq.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) c (Char.ofNat (nat_lit 92)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashes
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (@List.reverse.{0} Char (NoCommentsSpecification.Healthy.stripTrailingSlashRev (@List.reverse.{0} Char (String.toList s))))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashRev
| 
| A definition by well-founded recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.Healthy.stripTrailingSlashRev.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.Healthy.stripTrailingSlashRev x) (NoCommentsSpecification.Healthy.stripTrailingSlashRev.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => fun (head : Char) => fun (tail : List.{0} Char) => fun (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)) => NoCommentsSpecification.Healthy.stripTrailingSlashRev rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.Healthy.stripTrailingSlashRev: Lean accepts a definition by well-founded recursion only when its termination proof shows that the right of the equation uses the values of NoCommentsSpecification.Healthy.stripTrailingSlashRev, and of any function defined together with it, only at arguments below those on the left by a well-founded relation, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.Healthy.stripTrailingSlashRev and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.Healthy.stripTrailingSlashRev.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), ∀ (head : Char), ∀ (tail : List.{0} Char), ∀ (h : @Eq.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail)), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@namedPattern.{1} (List.{0} Char) rest (@List.cons.{0} Char head tail) h))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 47))) (instDecidableEqChar head (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => h_1 (@List.cons.{0} Char x_1 x_2) x_1 x_2 (@Eq.refl.{1} (List.{0} Char) (@List.cons.{0} Char x_1 x_2))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1
| 
| A definition. It has the universe parameters u_1, u, in that order. Its type:
| 
| ```lean
| ∀ {α : Type u}, ∀ {motive : ∀ (t : List.{u} α), Sort u_1}, ∀ (t : List.{u} α), ∀ (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)), (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α t)), motive t) → motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Type u} => fun {motive : ∀ (t : List.{u} α), Sort u_1} => fun (t : List.{u} α) => fun (cons : ∀ (head : α), ∀ (tail : List.{u} α), motive (@List.cons.{u} α head tail)) => @List.rec.{u_1, u} α (fun (x : List.{u} α) => (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α x)), motive x) → motive x) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.nil.{u} α))), motive (@List.nil.{u} α)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 2) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (head : α) => fun (tail : List.{u} α) => fun (tail_ih : (∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α tail)), motive tail) → motive tail) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{u} α (@List.cons.{u} α head tail))), motive (@List.cons.{u} α head tail)) => cons head tail) t
| ```
| 
| ### NoCommentsSpecification.Healthy.stripDotSlash
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), String
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => String.ofList (NoCommentsSpecification.Healthy.stripDotSlashChars (String.toList s))
| ```
| 
| ### NoCommentsSpecification.Healthy.stripDotSlashChars
| 
| A definition by structural recursion. It has no universe parameter. Its type:
| 
| ```lean
| List.{0} Char → List.{0} Char
| ```
| 
| Its value is not printed: Lean compiles a definition by recursion into a term its syntax cannot write. In its place is the equation Lean proves for it, `NoCommentsSpecification.Healthy.stripDotSlashChars.eq_def`, which Lean's kernel checked, stating its value at every argument:
| 
| ```lean
| ∀ (x : List.{0} Char), @Eq.{1} (List.{0} Char) (NoCommentsSpecification.Healthy.stripDotSlashChars x) (NoCommentsSpecification.Healthy.stripDotSlashChars.match_1.{1} (fun (x_1 : List.{0} Char) => List.{0} Char) x (fun (rest : List.{0} Char) => NoCommentsSpecification.Healthy.stripDotSlashChars rest) (fun (cs : List.{0} Char) => cs))
| ```
| 
| The equation determines NoCommentsSpecification.Healthy.stripDotSlashChars: Lean accepts a definition by structural recursion only when the right of the equation uses the values of NoCommentsSpecification.Healthy.stripDotSlashChars, and of any function defined together with it, only at structural subterms of the arguments it recurses on, so only one function, or family of functions defined together, satisfies their equations. NoCommentsSpecification.Healthy.stripDotSlashChars and its equation rest on no axiom but Lean's own.
| 
| ### NoCommentsSpecification.Healthy.stripDotSlashChars.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} Char → Sort u_1), ∀ (x : List.{0} Char), ∀ (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))), ∀ (h_2 : ∀ (cs : List.{0} Char), motive cs), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} Char → Sort u_1) => fun (x : List.{0} Char) => fun (h_1 : ∀ (rest : List.{0} Char), motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) rest))) => fun (h_2 : ∀ (cs : List.{0} Char), motive cs) => @NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive x_1) x (fun (head : Char) => fun (tail : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char head tail)) (@Eq.{1} Char head (Char.ofNat (nat_lit 46))) (instDecidableEqChar head (Char.ofNat (nat_lit 46))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 46)) (fun (x_1 : Char) => motive (@List.cons.{0} Char x_1 tail)) (@NoCommentsSpecification.Healthy.hasCharPair._sparseCasesOn_1.{u_1, 0} Char (fun (x_1 : List.{0} Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) x_1)) tail (fun (x_1 : Char) => fun (x_2 : List.{0} Char) => @dite.{u_1} (motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2))) (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47))) (instDecidableEqChar x_1 (Char.ofNat (nat_lit 47))) (@Eq.ndrec_symm.{u_1, 1} Char (Char.ofNat (nat_lit 47)) (fun (x_3 : Char) => motive (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_3 x_2))) (h_1 x_2) x_1) (fun (x_3 : Not (@Eq.{1} Char x_1 (Char.ofNat (nat_lit 47)))) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) (@List.cons.{0} Char x_1 x_2)))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char tail)) => h_2 (@List.cons.{0} Char (Char.ofNat (nat_lit 46)) tail))) head) (fun (x_1 : Not (@Eq.{1} Char head (Char.ofNat (nat_lit 46)))) => h_2 (@List.cons.{0} Char head tail))) (fun (h : Nat.hasNotBit (nat_lit 2) (@List.ctorIdx.{0} Char x)) => h_2 x)
| ```
| 
| ### NoCommentsSpecification.Healthy.validSegmentsBool
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => @List.all.{0} String (String.splitOn s "/") (fun (seg : String) => Bool.and (Bool.and (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg "") (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".")) (@bne.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) seg ".."))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidWorkspaceJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (v : Lean.Json), motive (@Option.some.{0} Lean.Json v)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_2 Unit.unit) (fun (val : Lean.Json) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.cleanStringList
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json arr) item → @Exists.{1} String (fun (s : String) => And (@Eq.{1} Lean.Json item (Lean.Json.str s)) (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr s) Bool.true))))
| ```
| 
| ### NoCommentsSpecification.Healthy.validPrefixList
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.arr arr)) (∀ (item : Lean.Json), @Membership.mem.{0, 0} Lean.Json (List.{0} Lean.Json) (@List.instMembership.{0} Lean.Json) (@Array.toList.{0} Lean.Json arr) item → @Exists.{1} String (fun (s : String) => @Exists.{1} String (fun (pfx : String) => And (@Eq.{1} Lean.Json item (Lean.Json.str s)) (NoCommentsSpecification.Healthy.ValidPrefix s pfx)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidPrefix
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Ne.{1} String cleaned "./") (have trailing : Bool := @BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList cleaned)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47))); have body : String := @ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (String.ofList (@List.dropLast.{0} Char (String.toList cleaned))) cleaned; And (@Ne.{1} String body "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool body) Bool.true) (@Eq.{1} String out (@ite.{1} String (@Eq.{1} Bool trailing Bool.true) (instDecidableEqBool trailing Bool.true) (@HAppend.hAppend.{0, 0, 0} String String String (@instHAppendOfAppend.{0} String instAppendString) body "/") body)))))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} Lean.Json → Sort u_1), ∀ (x : Option.{0} Lean.Json), ∀ (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))), ∀ (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)), ∀ (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} Lean.Json → Sort u_1) => fun (x : Option.{0} Lean.Json) => fun (h_1 : ∀ (exclArr : Array.{0} Lean.Json), motive (@Option.some.{0} Lean.Json (Lean.Json.arr exclArr))) => fun (h_2 : ∀ (val : Lean.Json), motive (@Option.some.{0} Lean.Json val)) => fun (h_3 : ∀ («_» : Unit), motive (@Option.none.{0} Lean.Json)) => @Option.casesOn.{u_1, 0} Lean.Json (fun (x_1 : Option.{0} Lean.Json) => motive x_1) x (h_3 Unit.unit) (fun (val : Lean.Json) => @NoCommentsSpecification.Healthy.ConfigJson._sparseCasesOn_1.{u_1} (fun (x_1 : Lean.Json) => motive (@Option.some.{0} Lean.Json x_1)) val (fun (elems : Array.{0} Lean.Json) => h_1 elems) (fun (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx val)) => h_2 val))
| ```
| 
| ### NoCommentsSpecification.Healthy.ConfigJson._sparseCasesOn_1
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive_1 : ∀ (t : Lean.Json), Sort u}, ∀ (t : Lean.Json), ∀ (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)), (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx t)), motive_1 t) → motive_1 t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive_1 : ∀ (t : Lean.Json), Sort u} => fun (t : Lean.Json) => fun (arr : ∀ (elems : Array.{0} Lean.Json), motive_1 (Lean.Json.arr elems)) => @Lean.Json.rec.{u} (fun (x : Lean.Json) => (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx x)), motive_1 x) → motive_1 x) (fun (x : Array.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : List.{0} Lean.Json) => PUnit.{u}) (fun (x : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => PUnit.{u}) (fun (x : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => PUnit.{u}) (fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx Lean.Json.null)), motive_1 Lean.Json.null) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (b : Bool) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.bool b))), motive_1 (Lean.Json.bool b)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (n : Lean.JsonNumber) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.num n))), motive_1 (Lean.Json.num n)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 2))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (s : String) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.str s))), motive_1 (Lean.Json.str s)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 3))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (elems : Array.{0} Lean.Json) => fun (elems_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.arr elems))), motive_1 (Lean.Json.arr elems)) => arr elems) (fun (kvPairs : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => fun (kvPairs_ih : PUnit.{u}) => fun («else» : ∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx (Lean.Json.obj kvPairs))), motive_1 (Lean.Json.obj kvPairs)) => «else» (@Nat.ne_of_beq_eq_false (Nat.land (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Nat.shiftRight (nat_lit 16) (nat_lit 5))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Eq.refl.{1} Bool Bool.false))) (fun (toList : List.{0} Lean.Json) => fun (toList_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Raw.{0, 0} String (fun (x : String) => Lean.Json) (@Ord.compare.{0} String String.instOrd)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} (fun (head : Lean.Json) => fun (tail : List.{0} Lean.Json) => fun (head_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx head)), motive_1 head) → motive_1 head) => fun (tail_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (inner : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (inner_ih : PUnit.{u}) => PUnit.unit.{u}) (fun (size : Nat) => fun (k : String) => fun (v : Lean.Json) => fun (l : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (r : Std.DTreeMap.Internal.Impl.{0, 0} String (fun (x : String) => Lean.Json)) => fun (v_ih : (∀ (h : Nat.hasNotBit (nat_lit 16) (Lean.Json.ctorIdx v)), motive_1 v) → motive_1 v) => fun (l_ih : PUnit.{u}) => fun (r_ih : PUnit.{u}) => PUnit.unit.{u}) PUnit.unit.{u} t
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidExcludeJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "prefix" (@List.cons.{0} String "reason" (@List.nil.{0} String))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Exists.{1} String (fun (pfxRaw : String) => @Exists.{1} String (fun (pfxOut : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "prefix") (@Option.some.{0} Lean.Json (Lean.Json.str pfxRaw))) (NoCommentsSpecification.Healthy.ValidPrefix pfxRaw pfxOut)))) (@Exists.{1} String (fun (reasonRaw : String) => And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "reason") (@Option.some.{0} Lean.Json (Lean.Json.str reasonRaw))) (@Ne.{1} String (String.Slice.toString (String.trimAscii reasonRaw)) ""))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRelFile
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (raw : String), ∀ (out : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (raw : String) => fun (out : String) => And (@Ne.{1} String raw "") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.cleanStr raw) Bool.true) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.head?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (And (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList raw)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.false) (have cleaned : String := NoCommentsSpecification.Healthy.stripDotSlash raw; And (@Ne.{1} String cleaned "") (And (@Ne.{1} String cleaned ".") (And (@Eq.{1} Bool (NoCommentsSpecification.Healthy.validSegmentsBool cleaned) Bool.true) (@Eq.{1} String out cleaned)))))))
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence leaves refusal error wording free on invalid config JSON
shown as possibility
predicate 438
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseConfigFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.RepoConfig) (f Lean.Json.null) (@Except.error.{0, 0} String NoComments.Config.RepoConfig "denied")
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.ParseConfigFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| Lean.Json → Except.{0, 0} String NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### LeanIntent.Answer.KeptBy
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanIntent.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))
| ```
| 
| ### LeanIntent.Answer
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Answer.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.Verdict), LeanIntent.Answer.{u} W
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Verdict
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Verdict.confirmed
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| #### LeanIntent.Verdict.declined
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.Answer.KeptBy.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀ (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined), motive x x_1
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 Unit.unit))
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Verdict.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirmed : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun (confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent.Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Answer.consequence
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 1, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Answer.verdict
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
verdict confirmed
"###

def restatement_classifyFile : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-classifyFile
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.ConfigRecords.classifyFileRecord
revision 679
| # The intent record NoCommentsSpecification.ConfigRecords.classifyFileRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.Config.RepoConfig (fun (a : NoComments.Config.RepoConfig) => String → Except.{0, 0} String NoComments.Config.ClassifiedFile)
| ```
| 
| - **Requires:** classifyFile is a total pure function from RepoConfig and String to Except String ClassifiedFile.
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of that signature until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_unique_classification
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg relPath) (@Except.ok.{0, 0} String NoComments.Config.ClassifiedFile out) → NoCommentsSpecification.ConfigSpec.ClassifyOutcome cfg relPath out
| ```
| 
| - **Requires:** Returns .ok out only when at most 1 exclude rule and (if unexcluded) exactly 1 workspace matches on segment boundaries.
| - **Rules out:** Unowned files, overlapping workspaces, overlapping excludes, or raw non-segment prefix matches.
| - **Still allows:** Unique excluded or checked classification with isTool status.
| - **Freedom O5 leaves:** None on outcome value when valid.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg relPath) (@Except.error.{0, 0} String NoComments.Config.ClassifiedFile msg) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| - **Requires:** Returns .error only when ClassifyRefusal holds.
| - **Rules out:** Rejecting unambiguously owned files.
| - **Still allows:** Refusing ambiguous or unmatched files with arbitrary error message.
| - **Freedom O5 leaves:** Error message wording left free.
| 
| ## Vocabulary
| 
| ### ClassifyOutcome, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile)) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p) (@Prod.fst.{0, 0} String NoComments.Config.ClassifiedFile (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p)) (@Prod.snd.{0, 0} String NoComments.Config.ClassifiedFile (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p))
| ```
| 
| - **Requires:** ClassifyOutcome specifies unique exclude vs unique workspace ownership using segment PrefixMatches.
| - **Rules out:** Ambiguous or unowned paths.
| - **Still allows:** Unambiguous ownership.
| - **Freedom O5 leaves:** Unique outcome per file.
| 
| ### ClassifyRefusal, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig String`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig String) => NoCommentsSpecification.ConfigSpec.ClassifyRefusal (@Prod.fst.{0, 0} NoComments.Config.RepoConfig String p) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig String p)
| ```
| 
| - **Requires:** ClassifyRefusal captures ambiguousExclude, unmatched, and ambiguousWorkspace.
| - **Rules out:** Unambiguously owned paths.
| - **Still allows:** Ownership failures.
| - **Freedom O5 leaves:** Disjoint from ClassifyOutcome.
| 
| ## Consequences
| 
| ### classifies every unambiguous healthy file, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (p : String), NoCommentsSpecification.Healthy.ClassifyInput cfg p → @Exists.{1} NoComments.Config.ClassifiedFile (fun (out : NoComments.Config.ClassifiedFile) => @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg p) (@Except.ok.{0, 0} String NoComments.Config.ClassifiedFile out))
| ```
| 
| - **Requires:** Any unambiguously owned file succeeds.
| - **Rules out:** False failures on valid file layouts.
| - **Still allows:** Any compliant classifier.
| - **Freedom O5 leaves:** Success guaranteed on healthy classification inputs.
| 
| ### leaves refusal message string unconstrained on unmatched file, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg "Foo.lean") (@Except.error.{0, 0} String NoComments.Config.ClassifiedFile "denied")
| ```
| 
| - **Requires:** Some conforming classifier returns "denied" on an unmatched file.
| - **Rules out:** Nothing; establishes error-text freedom.
| - **Still allows:** Custom error wording.
| - **Freedom O5 leaves:** Error formatting decided below owner level (O5 ClassifyFileFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ClassifyFileFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → String → Except.{0, 0} String NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => fun (out : NoComments.Config.ClassifiedFile) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); Or (@Exists.{1} NoComments.Config.ExcludeRule (fun (rule : NoComments.Config.ExcludeRule) => And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.cons.{0} NoComments.Config.ExcludeRule rule (@List.nil.{0} NoComments.Config.ExcludeRule))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.excluded relPath rule)))) (And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.nil.{0} NoComments.Config.ExcludeRule)) (@Exists.{1} NoComments.Config.WorkspaceConfig (fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} Nat (fun (wsIdx : Nat) => @Exists.{1} String (fun (wsRel : String) => And (@Eq.{1} (List.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) (@List.filterMap.{0, 0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1.{1} (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => Option.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) x (fun (w : NoComments.Config.WorkspaceConfig) => fun (idx : Nat) => @Option.map.{0, 0} String (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (r : String) => @Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) w (@Prod.mk.{0, 0} Nat String idx r)) (NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath))) (@List.zipIdx.{0} NoComments.Config.WorkspaceConfig (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.cons.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) ws (@Prod.mk.{0, 0} Nat String wsIdx wsRel)) (@List.nil.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.checked relPath wsIdx wsRel (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.PrefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1), ∀ (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat), ∀ (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1) => fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => fun (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)) => @Prod.casesOn.{u_1, 0, 0} NoComments.Config.WorkspaceConfig Nat (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => motive x_1) x (fun (fst : NoComments.Config.WorkspaceConfig) => fun (snd : Nat) => h_1 fst snd)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.MatchWorkspace
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Of the arguments its type takes, the first 2 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousExclude
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @GE.ge.{0} Nat instLENat (@List.length.{0} NoComments.Config.ExcludeRule (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.unmatched
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @Eq.{1} (List.{0} String) (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (@List.nil.{0} String) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousWorkspace
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @GE.ge.{0} Nat instLENat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.Healthy.prefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); NoCommentsSpecification.Healthy.ClassifyInput.match_1.{1} (fun (x : List.{0} NoComments.Config.ExcludeRule) => Prop) exclHits (fun (head : NoComments.Config.ExcludeRule) => True) (fun («_» : Unit) => @Eq.{1} Nat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (ws : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.Healthy.matchWsRel ws relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (head : NoComments.Config.ExcludeRule) => fun (x : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => False)
| ```
| 
| ### NoCommentsSpecification.Healthy.prefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1), ∀ (exclHits : List.{0} NoComments.Config.ExcludeRule), ∀ (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))), ∀ (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)), ∀ (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))), motive exclHits
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1) => fun (exclHits : List.{0} NoComments.Config.ExcludeRule) => fun (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))) => fun (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)) => fun (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive x) exclHits (h_2 Unit.unit) (fun (head : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive (@List.cons.{0} NoComments.Config.ExcludeRule head x)) tail (h_1 head) (fun (x : NoComments.Config.ExcludeRule) => fun (x_1 : List.{0} NoComments.Config.ExcludeRule) => h_3 head x x_1))
| ```
| 
| ### NoCommentsSpecification.Healthy.matchWsRel
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence the record's plain restatement
shown as entailment
predicate 1
| the record, as its revision prints it
verdict confirmed
"###

def delegated_classifyFile : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-classifyFile
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.ConfigRecords.classifyFileRecord
revision 679
| # The intent record NoCommentsSpecification.ConfigRecords.classifyFileRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.Config.RepoConfig (fun (a : NoComments.Config.RepoConfig) => String → Except.{0, 0} String NoComments.Config.ClassifiedFile)
| ```
| 
| - **Requires:** classifyFile is a total pure function from RepoConfig and String to Except String ClassifiedFile.
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of that signature until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_unique_classification
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg relPath) (@Except.ok.{0, 0} String NoComments.Config.ClassifiedFile out) → NoCommentsSpecification.ConfigSpec.ClassifyOutcome cfg relPath out
| ```
| 
| - **Requires:** Returns .ok out only when at most 1 exclude rule and (if unexcluded) exactly 1 workspace matches on segment boundaries.
| - **Rules out:** Unowned files, overlapping workspaces, overlapping excludes, or raw non-segment prefix matches.
| - **Still allows:** Unique excluded or checked classification with isTool status.
| - **Freedom O5 leaves:** None on outcome value when valid.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg relPath) (@Except.error.{0, 0} String NoComments.Config.ClassifiedFile msg) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| - **Requires:** Returns .error only when ClassifyRefusal holds.
| - **Rules out:** Rejecting unambiguously owned files.
| - **Still allows:** Refusing ambiguous or unmatched files with arbitrary error message.
| - **Freedom O5 leaves:** Error message wording left free.
| 
| ## Vocabulary
| 
| ### ClassifyOutcome, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile)) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p) (@Prod.fst.{0, 0} String NoComments.Config.ClassifiedFile (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p)) (@Prod.snd.{0, 0} String NoComments.Config.ClassifiedFile (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} String NoComments.Config.ClassifiedFile) p))
| ```
| 
| - **Requires:** ClassifyOutcome specifies unique exclude vs unique workspace ownership using segment PrefixMatches.
| - **Rules out:** Ambiguous or unowned paths.
| - **Still allows:** Unambiguous ownership.
| - **Freedom O5 leaves:** Unique outcome per file.
| 
| ### ClassifyRefusal, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig String`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig String) => NoCommentsSpecification.ConfigSpec.ClassifyRefusal (@Prod.fst.{0, 0} NoComments.Config.RepoConfig String p) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig String p)
| ```
| 
| - **Requires:** ClassifyRefusal captures ambiguousExclude, unmatched, and ambiguousWorkspace.
| - **Rules out:** Unambiguously owned paths.
| - **Still allows:** Ownership failures.
| - **Freedom O5 leaves:** Disjoint from ClassifyOutcome.
| 
| ## Consequences
| 
| ### classifies every unambiguous healthy file, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (p : String), NoCommentsSpecification.Healthy.ClassifyInput cfg p → @Exists.{1} NoComments.Config.ClassifiedFile (fun (out : NoComments.Config.ClassifiedFile) => @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f cfg p) (@Except.ok.{0, 0} String NoComments.Config.ClassifiedFile out))
| ```
| 
| - **Requires:** Any unambiguously owned file succeeds.
| - **Rules out:** False failures on valid file layouts.
| - **Still allows:** Any compliant classifier.
| - **Freedom O5 leaves:** Success guaranteed on healthy classification inputs.
| 
| ### leaves refusal message string unconstrained on unmatched file, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg "Foo.lean") (@Except.error.{0, 0} String NoComments.Config.ClassifiedFile "denied")
| ```
| 
| - **Requires:** Some conforming classifier returns "denied" on an unmatched file.
| - **Rules out:** Nothing; establishes error-text freedom.
| - **Still allows:** Custom error wording.
| - **Freedom O5 leaves:** Error formatting decided below owner level (O5 ClassifyFileFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ClassifyFileFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → String → Except.{0, 0} String NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => fun (out : NoComments.Config.ClassifiedFile) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); Or (@Exists.{1} NoComments.Config.ExcludeRule (fun (rule : NoComments.Config.ExcludeRule) => And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.cons.{0} NoComments.Config.ExcludeRule rule (@List.nil.{0} NoComments.Config.ExcludeRule))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.excluded relPath rule)))) (And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.nil.{0} NoComments.Config.ExcludeRule)) (@Exists.{1} NoComments.Config.WorkspaceConfig (fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} Nat (fun (wsIdx : Nat) => @Exists.{1} String (fun (wsRel : String) => And (@Eq.{1} (List.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) (@List.filterMap.{0, 0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1.{1} (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => Option.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) x (fun (w : NoComments.Config.WorkspaceConfig) => fun (idx : Nat) => @Option.map.{0, 0} String (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (r : String) => @Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) w (@Prod.mk.{0, 0} Nat String idx r)) (NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath))) (@List.zipIdx.{0} NoComments.Config.WorkspaceConfig (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.cons.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) ws (@Prod.mk.{0, 0} Nat String wsIdx wsRel)) (@List.nil.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.checked relPath wsIdx wsRel (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.PrefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1), ∀ (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat), ∀ (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1) => fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => fun (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)) => @Prod.casesOn.{u_1, 0, 0} NoComments.Config.WorkspaceConfig Nat (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => motive x_1) x (fun (fst : NoComments.Config.WorkspaceConfig) => fun (snd : Nat) => h_1 fst snd)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.MatchWorkspace
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Of the arguments its type takes, the first 2 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousExclude
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @GE.ge.{0} Nat instLENat (@List.length.{0} NoComments.Config.ExcludeRule (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.unmatched
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @Eq.{1} (List.{0} String) (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (@List.nil.{0} String) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousWorkspace
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @GE.ge.{0} Nat instLENat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.Healthy.prefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); NoCommentsSpecification.Healthy.ClassifyInput.match_1.{1} (fun (x : List.{0} NoComments.Config.ExcludeRule) => Prop) exclHits (fun (head : NoComments.Config.ExcludeRule) => True) (fun («_» : Unit) => @Eq.{1} Nat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (ws : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.Healthy.matchWsRel ws relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (head : NoComments.Config.ExcludeRule) => fun (x : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => False)
| ```
| 
| ### NoCommentsSpecification.Healthy.prefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1), ∀ (exclHits : List.{0} NoComments.Config.ExcludeRule), ∀ (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))), ∀ (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)), ∀ (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))), motive exclHits
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1) => fun (exclHits : List.{0} NoComments.Config.ExcludeRule) => fun (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))) => fun (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)) => fun (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive x) exclHits (h_2 Unit.unit) (fun (head : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive (@List.cons.{0} NoComments.Config.ExcludeRule head x)) tail (h_1 head) (fun (x : NoComments.Config.ExcludeRule) => fun (x_1 : List.{0} NoComments.Config.ExcludeRule) => h_3 head x x_1))
| ```
| 
| ### NoCommentsSpecification.Healthy.matchWsRel
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence leaves refusal message string unconstrained on unmatched file
shown as possibility
predicate 474
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyFileFn) => @Eq.{1} (Except.{0, 0} String NoComments.Config.ClassifiedFile) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg "Foo.lean") (@Except.error.{0, 0} String NoComments.Config.ClassifiedFile "denied")
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.ClassifyFileFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → String → Except.{0, 0} String NoComments.Config.ClassifiedFile
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.Answer.KeptBy
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanIntent.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))
| ```
| 
| ### LeanIntent.Answer
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Answer.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.Verdict), LeanIntent.Answer.{u} W
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Verdict
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Verdict.confirmed
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| #### LeanIntent.Verdict.declined
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.Answer.KeptBy.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀ (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined), motive x x_1
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 Unit.unit))
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Verdict.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirmed : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun (confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent.Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Answer.consequence
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 1, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Answer.verdict
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
verdict confirmed
"###

def restatement_classifyTracked : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-classifyTracked
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.ConfigRecords.classifyTrackedRecord
revision 721
| # The intent record NoCommentsSpecification.ConfigRecords.classifyTrackedRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.Config.RepoConfig (fun (a : NoComments.Config.RepoConfig) => Array.{0} String → Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile))
| ```
| 
| - **Requires:** classifyTrackedFiles is a total pure function from RepoConfig and Array String to Except String (Array ClassifiedFile).
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of that signature until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_all_classified_in_order
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (out : Array.{0} NoComments.Config.ClassifiedFile), @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg tracked) (@Except.ok.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) out) → NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome cfg tracked out
| ```
| 
| - **Requires:** Maps classifyFile across every tracked file preserving order and array length.
| - **Rules out:** Skipping tracked files or reordering classifications.
| - **Still allows:** Only the exact in-order array of file classifications.
| - **Freedom O5 leaves:** Choice of which failing file error message is reported first.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg tracked) (@Except.error.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) msg) → NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal cfg tracked
| ```
| 
| - **Requires:** Returns .error only when some tracked file fails ClassifyRefusal.
| - **Rules out:** Failing when all tracked files are cleanly owned.
| - **Still allows:** Refusal citing any unowned or ambiguous tracked file.
| - **Freedom O5 leaves:** Error wording left free.
| 
| ## Vocabulary
| 
| ### ClassifyTrackedOutcome, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile))`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile))) => NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p) (@Prod.fst.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p)) (@Prod.snd.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p))
| ```
| 
| - **Requires:** ClassifyTrackedOutcome specifies exact length preservation and per-index ClassifyOutcome.
| - **Rules out:** Mismatched lengths or misclassified entries.
| - **Still allows:** Exact array correspondence.
| - **Freedom O5 leaves:** Unique outcome array.
| 
| ### ClassifyTrackedRefusal, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Array.{0} String)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Array.{0} String)) => NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Array.{0} String) p) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Array.{0} String) p)
| ```
| 
| - **Requires:** ClassifyTrackedRefusal holds when at least one tracked file hits ClassifyRefusal.
| - **Rules out:** Repositories with full clean coverage.
| - **Still allows:** Partial or ambiguous coverage inputs.
| - **Freedom O5 leaves:** Disjoint from ClassifyTrackedOutcome.
| 
| ## Consequences
| 
| ### succeeds when all tracked files have unambiguous ownership, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (ps : Array.{0} String), NoCommentsSpecification.Healthy.ClassifyTrackedInput cfg ps → @Exists.{1} (Array.{0} NoComments.Config.ClassifiedFile) (fun (out : Array.{0} NoComments.Config.ClassifiedFile) => @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg ps) (@Except.ok.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) out))
| ```
| 
| - **Requires:** Healthy tracked file lists always succeed.
| - **Rules out:** False failures on fully covered repositories.
| - **Still allows:** Any compliant batch classifier.
| - **Freedom O5 leaves:** Success guaranteed on healthy file lists.
| 
| ### leaves refusal message string free on unmatched file array, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg (@List.toArray.{0} String (@List.cons.{0} String "Foo.lean" (@List.nil.{0} String)))) (@Except.error.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) "denied")
| ```
| 
| - **Requires:** Some conforming batch classifier returns "denied".
| - **Rules out:** Nothing; establishes error-message freedom.
| - **Still allows:** Any refusal diagnostic.
| - **Freedom O5 leaves:** Error wording decided below owner level (O5 ClassifyTrackedFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ClassifyTrackedFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → Array.{0} String → Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (out : Array.{0} NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => fun (out : Array.{0} NoComments.Config.ClassifiedFile) => And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.ClassifiedFile out) (@Array.size.{0} String tracked)) (∀ (i : Nat), ∀ (_ht : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String tracked)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ClassifiedFile out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ClassifiedFile out)) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome cfg (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) tracked i _ht) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.ClassifiedFile) Nat NoComments.Config.ClassifiedFile (fun (xs : Array.{0} NoComments.Config.ClassifiedFile) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.ClassifiedFile xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.ClassifiedFile) out i _ho)))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => fun (out : NoComments.Config.ClassifiedFile) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); Or (@Exists.{1} NoComments.Config.ExcludeRule (fun (rule : NoComments.Config.ExcludeRule) => And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.cons.{0} NoComments.Config.ExcludeRule rule (@List.nil.{0} NoComments.Config.ExcludeRule))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.excluded relPath rule)))) (And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.nil.{0} NoComments.Config.ExcludeRule)) (@Exists.{1} NoComments.Config.WorkspaceConfig (fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} Nat (fun (wsIdx : Nat) => @Exists.{1} String (fun (wsRel : String) => And (@Eq.{1} (List.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) (@List.filterMap.{0, 0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1.{1} (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => Option.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) x (fun (w : NoComments.Config.WorkspaceConfig) => fun (idx : Nat) => @Option.map.{0, 0} String (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (r : String) => @Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) w (@Prod.mk.{0, 0} Nat String idx r)) (NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath))) (@List.zipIdx.{0} NoComments.Config.WorkspaceConfig (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.cons.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) ws (@Prod.mk.{0, 0} Nat String wsIdx wsRel)) (@List.nil.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.checked relPath wsIdx wsRel (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.PrefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1), ∀ (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat), ∀ (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1) => fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => fun (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)) => @Prod.casesOn.{u_1, 0, 0} NoComments.Config.WorkspaceConfig Nat (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => motive x_1) x (fun (fst : NoComments.Config.WorkspaceConfig) => fun (snd : Nat) => h_1 fst snd)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.MatchWorkspace
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => @Exists.{1} String (fun (relPath : String) => And (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String tracked) relPath) (NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Of the arguments its type takes, the first 2 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousExclude
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @GE.ge.{0} Nat instLENat (@List.length.{0} NoComments.Config.ExcludeRule (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.unmatched
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @Eq.{1} (List.{0} String) (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (@List.nil.{0} String) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousWorkspace
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @GE.ge.{0} Nat instLENat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyTrackedInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => ∀ (relPath : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String tracked) relPath → NoCommentsSpecification.Healthy.ClassifyInput cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.Healthy.prefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); NoCommentsSpecification.Healthy.ClassifyInput.match_1.{1} (fun (x : List.{0} NoComments.Config.ExcludeRule) => Prop) exclHits (fun (head : NoComments.Config.ExcludeRule) => True) (fun («_» : Unit) => @Eq.{1} Nat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (ws : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.Healthy.matchWsRel ws relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (head : NoComments.Config.ExcludeRule) => fun (x : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => False)
| ```
| 
| ### NoCommentsSpecification.Healthy.prefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1), ∀ (exclHits : List.{0} NoComments.Config.ExcludeRule), ∀ (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))), ∀ (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)), ∀ (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))), motive exclHits
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1) => fun (exclHits : List.{0} NoComments.Config.ExcludeRule) => fun (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))) => fun (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)) => fun (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive x) exclHits (h_2 Unit.unit) (fun (head : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive (@List.cons.{0} NoComments.Config.ExcludeRule head x)) tail (h_1 head) (fun (x : NoComments.Config.ExcludeRule) => fun (x_1 : List.{0} NoComments.Config.ExcludeRule) => h_3 head x x_1))
| ```
| 
| ### NoCommentsSpecification.Healthy.matchWsRel
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence the record's plain restatement
shown as entailment
predicate 1
| the record, as its revision prints it
verdict confirmed
"###

def delegated_classifyTracked : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-classifyTracked
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.ConfigRecords.classifyTrackedRecord
revision 721
| # The intent record NoCommentsSpecification.ConfigRecords.classifyTrackedRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.Config.RepoConfig (fun (a : NoComments.Config.RepoConfig) => Array.{0} String → Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile))
| ```
| 
| - **Requires:** classifyTrackedFiles is a total pure function from RepoConfig and Array String to Except String (Array ClassifiedFile).
| - **Rules out:** Any subject with external side effects, partiality, or another signature.
| - **Still allows:** Every pure function of that signature until restricted by properties.
| - **Freedom O5 leaves:** Only fixes the pure function signature.
| 
| ## Domain hypotheses
| 
| None.
| 
| ## Properties
| 
| ### ok_all_classified_in_order
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (out : Array.{0} NoComments.Config.ClassifiedFile), @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg tracked) (@Except.ok.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) out) → NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome cfg tracked out
| ```
| 
| - **Requires:** Maps classifyFile across every tracked file preserving order and array length.
| - **Rules out:** Skipping tracked files or reordering classifications.
| - **Still allows:** Only the exact in-order array of file classifications.
| - **Freedom O5 leaves:** Choice of which failing file error message is reported first.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg tracked) (@Except.error.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) msg) → NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal cfg tracked
| ```
| 
| - **Requires:** Returns .error only when some tracked file fails ClassifyRefusal.
| - **Rules out:** Failing when all tracked files are cleanly owned.
| - **Still allows:** Refusal citing any unowned or ambiguous tracked file.
| - **Freedom O5 leaves:** Error wording left free.
| 
| ## Vocabulary
| 
| ### ClassifyTrackedOutcome, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile))`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile))) => NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p) (@Prod.fst.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p)) (@Prod.snd.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Prod.{0, 0} (Array.{0} String) (Array.{0} NoComments.Config.ClassifiedFile)) p))
| ```
| 
| - **Requires:** ClassifyTrackedOutcome specifies exact length preservation and per-index ClassifyOutcome.
| - **Rules out:** Mismatched lengths or misclassified entries.
| - **Still allows:** Exact array correspondence.
| - **Freedom O5 leaves:** Unique outcome array.
| 
| ### ClassifyTrackedRefusal, a predicate over `Prod.{0, 0} NoComments.Config.RepoConfig (Array.{0} String)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Config.RepoConfig (Array.{0} String)) => NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal (@Prod.fst.{0, 0} NoComments.Config.RepoConfig (Array.{0} String) p) (@Prod.snd.{0, 0} NoComments.Config.RepoConfig (Array.{0} String) p)
| ```
| 
| - **Requires:** ClassifyTrackedRefusal holds when at least one tracked file hits ClassifyRefusal.
| - **Rules out:** Repositories with full clean coverage.
| - **Still allows:** Partial or ambiguous coverage inputs.
| - **Freedom O5 leaves:** Disjoint from ClassifyTrackedOutcome.
| 
| ## Consequences
| 
| ### succeeds when all tracked files have unambiguous ownership, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => ∀ (cfg : NoComments.Config.RepoConfig), ∀ (ps : Array.{0} String), NoCommentsSpecification.Healthy.ClassifyTrackedInput cfg ps → @Exists.{1} (Array.{0} NoComments.Config.ClassifiedFile) (fun (out : Array.{0} NoComments.Config.ClassifiedFile) => @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f cfg ps) (@Except.ok.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) out))
| ```
| 
| - **Requires:** Healthy tracked file lists always succeed.
| - **Rules out:** False failures on fully covered repositories.
| - **Still allows:** Any compliant batch classifier.
| - **Freedom O5 leaves:** Success guaranteed on healthy file lists.
| 
| ### leaves refusal message string free on unmatched file array, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg (@List.toArray.{0} String (@List.cons.{0} String "Foo.lean" (@List.nil.{0} String)))) (@Except.error.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) "denied")
| ```
| 
| - **Requires:** Some conforming batch classifier returns "denied".
| - **Rules out:** Nothing; establishes error-message freedom.
| - **Still allows:** Any refusal diagnostic.
| - **Freedom O5 leaves:** Error wording decided below owner level (O5 ClassifyTrackedFreedom).
| 
| ## Definitions the record's meaning reaches
| 
| These are not statements of the record: each is a declaration that a statement above depends on, or that says what it is for a subject to meet the record and for a consequence to hold of it as shown, with everything those depend on in turn. Each is printed in full: its type, a definition's value, or for a definition by structural or well-founded recursion the equation that determines it, and an inductive type's constructors, which for a structure are its fields; a theorem's proof and an opaque constant's value are not, since no term that uses them depends on more than their types. Their plain words are those of the statements that use them.
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.ClassifyTrackedFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → Array.{0} String → Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyTrackedOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), ∀ (out : Array.{0} NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => fun (out : Array.{0} NoComments.Config.ClassifiedFile) => And (@Eq.{1} Nat (@Array.size.{0} NoComments.Config.ClassifiedFile out) (@Array.size.{0} String tracked)) (∀ (i : Nat), ∀ (_ht : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} String tracked)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ClassifiedFile out)) (fun (_ho : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} NoComments.Config.ClassifiedFile out)) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome cfg (@GetElem.getElem.{0, 0, 0} (Array.{0} String) Nat String (fun (xs : Array.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} String xs)) (@Array.instGetElemNatLtSize.{0} String) tracked i _ht) (@GetElem.getElem.{0, 0, 0} (Array.{0} NoComments.Config.ClassifiedFile) Nat NoComments.Config.ClassifiedFile (fun (xs : Array.{0} NoComments.Config.ClassifiedFile) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} NoComments.Config.ClassifiedFile xs)) (@Array.instGetElemNatLtSize.{0} NoComments.Config.ClassifiedFile) out i _ho)))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), ∀ (out : NoComments.Config.ClassifiedFile), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => fun (out : NoComments.Config.ClassifiedFile) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); Or (@Exists.{1} NoComments.Config.ExcludeRule (fun (rule : NoComments.Config.ExcludeRule) => And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.cons.{0} NoComments.Config.ExcludeRule rule (@List.nil.{0} NoComments.Config.ExcludeRule))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.excluded relPath rule)))) (And (@Eq.{1} (List.{0} NoComments.Config.ExcludeRule) exclHits (@List.nil.{0} NoComments.Config.ExcludeRule)) (@Exists.{1} NoComments.Config.WorkspaceConfig (fun (ws : NoComments.Config.WorkspaceConfig) => @Exists.{1} Nat (fun (wsIdx : Nat) => @Exists.{1} String (fun (wsRel : String) => And (@Eq.{1} (List.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) (@List.filterMap.{0, 0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1.{1} (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => Option.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))) x (fun (w : NoComments.Config.WorkspaceConfig) => fun (idx : Nat) => @Option.map.{0, 0} String (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (fun (r : String) => @Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) w (@Prod.mk.{0, 0} Nat String idx r)) (NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath))) (@List.zipIdx.{0} NoComments.Config.WorkspaceConfig (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.cons.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String)) (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String) ws (@Prod.mk.{0, 0} Nat String wsIdx wsRel)) (@List.nil.{0} (Prod.{0, 0} NoComments.Config.WorkspaceConfig (Prod.{0, 0} Nat String))))) (@Eq.{1} NoComments.Config.ClassifiedFile out (NoComments.Config.ClassifiedFile.checked relPath wsIdx wsRel (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.toolPrefixes ws))))))))))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.PrefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoComments.Config.ExcludeRule.prefix_
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.ExcludeRule's constructor, of its argument number 1, a value of NoComments.Config.ExcludeRule. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.ExcludeRule), String
| ```
| 
| ### NoComments.Config.RepoConfig.exclude
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.ExcludeRule
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyOutcome.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1), ∀ (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat), ∀ (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat → Sort u_1) => fun (x : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => fun (h_1 : ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (idx : Nat), motive (@Prod.mk.{0, 0} NoComments.Config.WorkspaceConfig Nat w idx)) => @Prod.casesOn.{u_1, 0, 0} NoComments.Config.WorkspaceConfig Nat (fun (x_1 : Prod.{0, 0} NoComments.Config.WorkspaceConfig Nat) => motive x_1) x (fun (fst : NoComments.Config.WorkspaceConfig) => fun (snd : Nat) => h_1 fst snd)
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.MatchWorkspace
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.ConfigSpec.PrefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoComments.Config.WorkspaceConfig.excludePrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 5, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoComments.Config.WorkspaceConfig.dir
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), String
| ```
| 
| ### NoComments.Config.RepoConfig.workspaces
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Config.RepoConfig's constructor, of its argument number 1, a value of NoComments.Config.RepoConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.RepoConfig), Array.{0} NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig.toolPrefixes
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Config.WorkspaceConfig's constructor, of its argument number 1, a value of NoComments.Config.WorkspaceConfig. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Config.WorkspaceConfig), Array.{0} String
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyTrackedRefusal
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => @Exists.{1} String (fun (relPath : String) => And (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String tracked) relPath) (NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath))
| ```
| 
| ### NoCommentsSpecification.ConfigSpec.ClassifyRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Of the arguments its type takes, the first 2 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousExclude
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @GE.ge.{0} Nat instLENat (@List.length.{0} NoComments.Config.ExcludeRule (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.unmatched
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @Eq.{1} (List.{0} String) (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg))) (@List.nil.{0} String) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| #### NoCommentsSpecification.ConfigSpec.ClassifyRefusal.ambiguousWorkspace
| 
| ```lean
| ∀ {cfg : NoComments.Config.RepoConfig}, ∀ {relPath : String}, @Eq.{1} (List.{0} NoComments.Config.ExcludeRule) (@List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.ConfigSpec.PrefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg))) (@List.nil.{0} NoComments.Config.ExcludeRule) → @GE.ge.{0} Nat instLENat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (w : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.ConfigSpec.MatchWorkspace w relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → NoCommentsSpecification.ConfigSpec.ClassifyRefusal cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyTrackedInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (tracked : Array.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (tracked : Array.{0} String) => ∀ (relPath : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String tracked) relPath → NoCommentsSpecification.Healthy.ClassifyInput cfg relPath
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (cfg : NoComments.Config.RepoConfig), ∀ (relPath : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (cfg : NoComments.Config.RepoConfig) => fun (relPath : String) => have exclHits : List.{0} NoComments.Config.ExcludeRule := @List.filter.{0} NoComments.Config.ExcludeRule (fun (r : NoComments.Config.ExcludeRule) => NoCommentsSpecification.Healthy.prefixMatches relPath (NoComments.Config.ExcludeRule.prefix_ r)) (@Array.toList.{0} NoComments.Config.ExcludeRule (NoComments.Config.RepoConfig.exclude cfg)); NoCommentsSpecification.Healthy.ClassifyInput.match_1.{1} (fun (x : List.{0} NoComments.Config.ExcludeRule) => Prop) exclHits (fun (head : NoComments.Config.ExcludeRule) => True) (fun («_» : Unit) => @Eq.{1} Nat (@List.length.{0} String (@List.filterMap.{0, 0} NoComments.Config.WorkspaceConfig String (fun (ws : NoComments.Config.WorkspaceConfig) => NoCommentsSpecification.Healthy.matchWsRel ws relPath) (@Array.toList.{0} NoComments.Config.WorkspaceConfig (NoComments.Config.RepoConfig.workspaces cfg)))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (fun (head : NoComments.Config.ExcludeRule) => fun (x : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => False)
| ```
| 
| ### NoCommentsSpecification.Healthy.prefixMatches
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (path : String), ∀ (pfx : String), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (path : String) => fun (pfx : String) => @ite.{1} Bool (@Eq.{1} Bool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (instDecidableEqBool (@BEq.beq.{0} (Option.{0} Char) (@instBEqOption.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar)) (@List.getLast?.{0} Char (String.toList pfx)) (@Option.some.{0} Char (Char.ofNat (nat_lit 47)))) Bool.true) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (String.toList pfx) (String.toList path)) (Bool.or (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) path pfx) (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) (@HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList pfx) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char))) (String.toList path)))
| ```
| 
| ### NoCommentsSpecification.Healthy.ClassifyInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1), ∀ (exclHits : List.{0} NoComments.Config.ExcludeRule), ∀ (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))), ∀ (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)), ∀ (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))), motive exclHits
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : List.{0} NoComments.Config.ExcludeRule → Sort u_1) => fun (exclHits : List.{0} NoComments.Config.ExcludeRule) => fun (h_1 : ∀ (head : NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.nil.{0} NoComments.Config.ExcludeRule))) => fun (h_2 : ∀ («_» : Unit), motive (@List.nil.{0} NoComments.Config.ExcludeRule)) => fun (h_3 : ∀ (head : NoComments.Config.ExcludeRule), ∀ (x : NoComments.Config.ExcludeRule), ∀ (tail : List.{0} NoComments.Config.ExcludeRule), motive (@List.cons.{0} NoComments.Config.ExcludeRule head (@List.cons.{0} NoComments.Config.ExcludeRule x tail))) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive x) exclHits (h_2 Unit.unit) (fun (head : NoComments.Config.ExcludeRule) => fun (tail : List.{0} NoComments.Config.ExcludeRule) => @List.casesOn.{u_1, 0} NoComments.Config.ExcludeRule (fun (x : List.{0} NoComments.Config.ExcludeRule) => motive (@List.cons.{0} NoComments.Config.ExcludeRule head x)) tail (h_1 head) (fun (x : NoComments.Config.ExcludeRule) => fun (x_1 : List.{0} NoComments.Config.ExcludeRule) => h_3 head x x_1))
| ```
| 
| ### NoCommentsSpecification.Healthy.matchWsRel
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (w : NoComments.Config.WorkspaceConfig), ∀ (relPath : String), Option.{0} String
| ```
| 
| Its value:
| 
| ```lean
| fun (w : NoComments.Config.WorkspaceConfig) => fun (relPath : String) => have __do_jp : String → Option.{0} String := fun (wsRel : String) => @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (instDecidableEqBool (@Array.any.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w) (fun (x : String) => NoCommentsSpecification.Healthy.prefixMatches wsRel x) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size.{0} String (NoComments.Config.WorkspaceConfig.excludePrefixes w))) Bool.true) (@Option.none.{0} String) (@Option.some.{0} String wsRel); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (instDecidableEqBool (@BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.Config.WorkspaceConfig.dir w) ".") Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String relPath) (fun (wsRel : String) => __do_jp wsRel)) (have prefixChars : List.{0} Char := @HAppend.hAppend.{0, 0, 0} (List.{0} Char) (List.{0} Char) (List.{0} Char) (@instHAppendOfAppend.{0} (List.{0} Char) (@List.instAppend.{0} Char)) (String.toList (NoComments.Config.WorkspaceConfig.dir w)) (@List.cons.{0} Char (Char.ofNat (nat_lit 47)) (@List.nil.{0} Char)); @ite.{1} (Option.{0} String) (@Eq.{1} Bool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (instDecidableEqBool (@List.isPrefixOf.{0} Char (@instBEqOfDecidableEq.{0} Char instDecidableEqChar) prefixChars (String.toList relPath)) Bool.true) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.some.{0} String (String.ofList (@List.drop.{0} Char (@List.length.{0} Char prefixChars) (String.toList relPath)))) (fun (wsRel : String) => __do_jp wsRel)) (@Bind.bind.{0, 0} Option.{0} (@Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) String String (@Option.none.{0} String) (fun (wsRel : String) => __do_jp wsRel)))
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.HoldsOf
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.HoldsOf.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility), motive x
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Unit.unit) (h_2 Unit.unit)
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
consequence leaves refusal message string free on unmatched file array
shown as possibility
predicate 474
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.ClassifyTrackedFn) => @Eq.{1} (Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)) (f NoCommentsSpecification.AdequacyConfig.emptyRepoCfg (@List.toArray.{0} String (@List.cons.{0} String "Foo.lean" (@List.nil.{0} String)))) (@Except.error.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile) "denied")
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.ClassifyTrackedFn
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig → Array.{0} String → Except.{0, 0} String (Array.{0} NoComments.Config.ClassifiedFile)
| ```
| 
| ### NoComments.Config.RepoConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.RepoConfig.mk
| 
| ```lean
| ∀ (workspaces : Array.{0} NoComments.Config.WorkspaceConfig), ∀ (exclude : Array.{0} NoComments.Config.ExcludeRule), ∀ (ratchet : String), NoComments.Config.RepoConfig
| ```
| 
| ### NoComments.Config.WorkspaceConfig
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.WorkspaceConfig.mk
| 
| ```lean
| ∀ (dir : String), ∀ (srcDir : String), ∀ (lakeArgs : Array.{0} String), ∀ (toolPrefixes : Array.{0} String), ∀ (excludePrefixes : Array.{0} String), NoComments.Config.WorkspaceConfig
| ```
| 
| ### NoComments.Config.ExcludeRule
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ExcludeRule.mk
| 
| ```lean
| ∀ (prefix_ : String), ∀ (reason : String), NoComments.Config.ExcludeRule
| ```
| 
| ### NoComments.Config.ClassifiedFile
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Config.ClassifiedFile.excluded
| 
| ```lean
| ∀ (relPath : String), ∀ (rule : NoComments.Config.ExcludeRule), NoComments.Config.ClassifiedFile
| ```
| 
| #### NoComments.Config.ClassifiedFile.checked
| 
| ```lean
| ∀ (relPath : String), ∀ (wsIdx : Nat), ∀ (wsRelPath : String), ∀ (isTool : Bool), NoComments.Config.ClassifiedFile
| ```
| 
| ### NoCommentsSpecification.AdequacyConfig.emptyRepoCfg
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Config.RepoConfig
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Config.RepoConfig.mk (@List.toArray.{0} NoComments.Config.WorkspaceConfig (@List.nil.{0} NoComments.Config.WorkspaceConfig)) (@List.toArray.{0} NoComments.Config.ExcludeRule (@List.nil.{0} NoComments.Config.ExcludeRule)) "comment-ratchet.json"
| ```
| 
| ### LeanIntent.Answer.KeptBy
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecord.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanIntent.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))
| ```
| 
| ### LeanIntent.Answer
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Answer.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.Verdict), LeanIntent.Answer.{u} W
| ```
| 
| ### LeanIntent.Consequence
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W → Prop), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Consequence.Kind
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Consequence.Kind.entailment
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| #### LeanIntent.Consequence.Kind.possibility
| 
| ```lean
| LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Verdict
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Verdict.confirmed
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| #### LeanIntent.Verdict.declined
| 
| ```lean
| LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.IntentRecord.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent.Pred.{u}), LeanIntent.IntentRecord.{u} W
| ```
| 
| ### LeanIntent.Shape
| 
| An inductive type. It has the universe parameter u. Its type:
| 
| ```lean
| Type u → Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Shape.value
| 
| ```lean
| ∀ (W : Type u), LeanIntent.Shape.{u} W
| ```
| 
| #### LeanIntent.Shape.function
| 
| ```lean
| ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)
| ```
| 
| #### LeanIntent.Shape.step
| 
| ```lean
| ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)
| ```
| 
| #### LeanIntent.Shape.stepOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)
| ```
| 
| #### LeanIntent.Shape.action
| 
| ```lean
| ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.actionOn
| 
| ```lean
| ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u} O S)
| ```
| 
| #### LeanIntent.Shape.bundle
| 
| ```lean
| ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W
| ```
| 
| ### LeanIntent.Member
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Member.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → Out), LeanIntent.Member.{u} W
| ```
| 
| ### LeanIntent.Clause
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ (W : Type u), Type u
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Clause.mk
| 
| ```lean
| ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W
| ```
| 
| ### LeanIntent.Pred
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has the universe parameter u. Its type:
| 
| ```lean
| Type (u + 1)
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### LeanIntent.Pred.mk
| 
| ```lean
| ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}
| ```
| 
| ### LeanIntent.Answer.KeptBy.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀ (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined), motive x x_1
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : LeanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 Unit.unit))
| ```
| 
| ### LeanIntent.Consequence.Kind.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : motive LeanIntent.Consequence.Kind.possibility), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (possibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.rec.{u} motive entailment possibility t
| ```
| 
| ### LeanIntent.Verdict.casesOn
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirmed : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined), motive t
| ```
| 
| Its value:
| 
| ```lean
| fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun (confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent.Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t
| ```
| 
| ### LeanIntent.Consequence.kind
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind
| ```
| 
| ### LeanIntent.Answer.consequence
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 1, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W
| ```
| 
| ### LeanIntent.Answer.verdict
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Answer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict
| ```
| 
| ### LeanIntent.IntentRecord.Meets
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanIntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)
| ```
| 
| ### LeanIntent.IntentRecord.Dom
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w
| ```
| 
| ### LeanIntent.IntentRecord.dom
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Clause.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 2, counted after the parameters in the type of LeanIntent.Clause's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop
| ```
| 
| ### LeanIntent.IntentRecord.Props
| 
| A definition. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : LeanIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanIntent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w
| ```
| 
| ### LeanIntent.IntentRecord.props
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.IntentRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u} W)
| ```
| 
| ### LeanIntent.Consequence.holds
| 
| A function that reads a field of a structure: its value is `fun` over its first 2 arguments and returns field number 3, counted after the parameters in the type of LeanIntent.Consequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has the universe parameter u. Its type:
| 
| ```lean
| ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop
| ```
| 
| ### LeanIntent.HasInstance
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)
| ```
| 
| ## Lean's own libraries
| 
| The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they are those of Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, which made this text. A declaration is counted as Lean's own when Lean found the module that declares it in that release's library directory.
| 
verdict confirmed
"###

end NoCommentsSpecification.OwnersLogEntriesConfig
