module

@[expose] public section

namespace NoCommentsSpecification.OwnersLogEntriesRatchet

def restatement_analyzeComments : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-analyzeComments
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.RatchetRecords.analyzeCommentsRecord
revision 528
| # The intent record NoCommentsSpecification.RatchetRecords.analyzeCommentsRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} String (fun (a : String) => Array.{0} NoComments.Core.Comment → NoComments.RatchetCore.FileAnalysis)
| ```
| 
| - **Requires:** analyzeComments is a total pure function from String and Array Comment to FileAnalysis.
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
| ### exact_file_comments_lines_fingerprints
| 
| ```lean
| fun (f : NoCommentsSpecification.AnalyzeCommentsFn) => ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), NoCommentsSpecification.RatchetSpec.AnalyzeCommentsSpec file comments (f file comments)
| ```
| 
| - **Requires:** Preserves file and comments, sets lines to DistinctLines, and sorts fingerprints preserving counts.
| - **Rules out:** Wrong file path, wrong distinct line count, or altered fingerprint multiset.
| - **Still allows:** Only the canonical sorted FileAnalysis record.
| - **Freedom O5 leaves:** None: uniquely determined (O5 .eq).
| 
| ## Vocabulary
| 
| ### AnalyzeCommentsSpec, a predicate over `Prod.{0, 0} String (Prod.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis)`
| 
| ```lean
| fun (p : Prod.{0, 0} String (Prod.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis)) => NoCommentsSpecification.RatchetSpec.AnalyzeCommentsSpec (@Prod.fst.{0, 0} String (Prod.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis) p) (@Prod.fst.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis (@Prod.snd.{0, 0} String (Prod.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis) p)) (@Prod.snd.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis (@Prod.snd.{0, 0} String (Prod.{0, 0} (Array.{0} NoComments.Core.Comment) NoComments.RatchetCore.FileAnalysis) p))
| ```
| 
| - **Requires:** AnalyzeCommentsSpec requires exact file, comments, DistinctLines, and MultisetEq sorted fingerprints.
| - **Rules out:** Misattributed file paths or inaccurate counts.
| - **Still allows:** Canonical FileAnalysis.
| - **Freedom O5 leaves:** Unique result.
| 
| ## Consequences
| 
| ### preserves analyzed file path, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.AnalyzeCommentsFn) => ∀ (file : String), ∀ (cs : Array.{0} NoComments.Core.Comment), @Eq.{1} String (NoComments.RatchetCore.FileAnalysis.file (f file cs)) file
| ```
| 
| - **Requires:** Result carries the exact file path argument.
| - **Rules out:** Dropping or mutating file names.
| - **Still allows:** Exact path preservation.
| - **Freedom O5 leaves:** Deterministically equal (O5 .eq).
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
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.AnalyzeCommentsFn
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
| String → Array.{0} NoComments.Core.Comment → NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.AnalyzeCommentsSpec
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (out : NoComments.RatchetCore.FileAnalysis), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (file : String) => fun (comments : Array.{0} NoComments.Core.Comment) => fun (out : NoComments.RatchetCore.FileAnalysis) => And (@Eq.{1} String (NoComments.RatchetCore.FileAnalysis.file out) file) (And (@Eq.{1} (Array.{0} NoComments.Core.Comment) (NoComments.RatchetCore.FileAnalysis.comments out) comments) (And (NoCommentsSpecification.CoreSpec.DistinctLines comments (NoComments.RatchetCore.FileAnalysis.lines out)) (NoCommentsSpecification.CoreSpec.MultisetEq (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints out))) (@List.map.{0, 0} NoComments.Core.Comment String (fun (x : NoComments.Core.Comment) => NoComments.Core.Comment.fingerprint x) (@Array.toList.{0} NoComments.Core.Comment comments)))))
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.file
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Array.{0} NoComments.Core.Comment
| ```
| 
| ### NoCommentsSpecification.CoreSpec.DistinctLines
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (n : Nat), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (comments : Array.{0} NoComments.Core.Comment) => fun (n : Nat) => @Exists.{1} (List.{0} Nat) (fun (ls : List.{0} Nat) => And (@List.Nodup.{0} Nat ls) (And (∀ (l : Nat), Iff (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) ls l) (@Exists.{1} NoComments.Core.Comment (fun (c : NoComments.Core.Comment) => And (@Membership.mem.{0, 0} NoComments.Core.Comment (List.{0} NoComments.Core.Comment) (@List.instMembership.{0} NoComments.Core.Comment) (@Array.toList.{0} NoComments.Core.Comment comments) c) (And (@LE.le.{0} Nat instLENat (NoComments.Core.Comment.startLine c) l) (@LE.le.{0} Nat instLENat l (NoComments.Core.Comment.endLine c)))))) (@Eq.{1} Nat n (@List.length.{0} Nat ls))))
| ```
| 
| ### NoComments.Core.Comment.startLine
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.Core.Comment's constructor, of its argument number 1, a value of NoComments.Core.Comment. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.Comment), Nat
| ```
| 
| ### NoComments.Core.Comment.endLine
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.Core.Comment's constructor, of its argument number 1, a value of NoComments.Core.Comment. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.Comment), Nat
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Nat
| ```
| 
| ### NoCommentsSpecification.CoreSpec.MultisetEq
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (xs : List.{0} String), ∀ (ys : List.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (xs : List.{0} String) => fun (ys : List.{0} String) => ∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a xs) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a ys)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.Core.Comment.fingerprint
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.Core.Comment's constructor, of its argument number 1, a value of NoComments.Core.Comment. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.Comment), String
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

def restatement_parseRatchet : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-parseRatchet
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.RatchetRecords.parseRatchetRecord
revision 825
| # The intent record NoCommentsSpecification.RatchetRecords.parseRatchetRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} String (fun (a : String) => Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))
| ```
| 
| - **Requires:** parseRatchetJson is a total pure function from String to Except String (HashMap String RatchetEntry).
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
| ### ok_valid_ratchet_map
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), ∀ (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.ok.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m) → NoCommentsSpecification.RatchetSpec.ValidRatchetJson text m
| ```
| 
| - **Requires:** Accepts only JSON arrays of distinct normalized file entries with positive counts and sorted valid fingerprints.
| - **Rules out:** Zero comment/line entries, unsorted fingerprints, duplicate files, unknown keys, or invalid paths/hashes.
| - **Still allows:** Canonical HashMap keyed by normalized file path.
| - **Freedom O5 leaves:** HashMap bucket layout.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.error.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) msg) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| - **Requires:** Returns .error only when RatchetRefusal holds.
| - **Rules out:** Rejecting valid canonical ratchet manifests.
| - **Still allows:** Refusing invalid manifests with arbitrary error strings.
| - **Freedom O5 leaves:** Error wording left free.
| 
| ## Vocabulary
| 
| ### ValidRatchetJson, a predicate over `Prod.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)`
| 
| ```lean
| fun (p : Prod.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => NoCommentsSpecification.RatchetSpec.ValidRatchetJson (@Prod.fst.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) p) (@Prod.snd.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) p)
| ```
| 
| - **Requires:** ValidRatchetJson enforces schema, normalized paths, positive counts, sorted valid hex digests, and unique files.
| - **Rules out:** Empty, unsorted, duplicate, or malformed ratchet entries.
| - **Still allows:** Valid ratchet maps.
| - **Freedom O5 leaves:** Exact map lookup equivalence.
| 
| ### RatchetRefusal, a predicate over `String`
| 
| ```lean
| NoCommentsSpecification.RatchetSpec.RatchetRefusal
| ```
| 
| - **Requires:** RatchetRefusal enumerates every invalid ratchet input cause.
| - **Rules out:** Healthy ratchet manifests.
| - **Still allows:** All malformed ratchet JSON inputs.
| - **Freedom O5 leaves:** Disjoint from ValidRatchetJson.
| 
| ## Consequences
| 
| ### succeeds on every healthy ratchet manifest, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), NoCommentsSpecification.Healthy.RatchetText text → @Exists.{1} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.ok.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m))
| ```
| 
| - **Requires:** Every healthy ratchet JSON text parses to .ok m.
| - **Rules out:** Spurious rejections on valid ratchets.
| - **Still allows:** Any compliant ratchet parser.
| - **Freedom O5 leaves:** Success guaranteed on healthy ratchet manifests.
| 
| ### leaves refusal message string free on unparseable JSON, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => (∀ (j : Lean.Json), @Ne.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse "") (@Except.ok.{0, 0} String Lean.Json j)) → @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f "") (@Except.error.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) "denied")
| ```
| 
| - **Requires:** Some conforming ratchet parser returns "denied" on empty text.
| - **Rules out:** Nothing; documents diagnostic message freedom.
| - **Still allows:** Custom error messages.
| - **Freedom O5 leaves:** Error text decided below owner level (O5 ParseRatchetFreedom).
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
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.ParseRatchetFn
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
| String → Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidRatchetJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), ∀ (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (text : String) => fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} NoComments.RatchetCore.RatchetEntry) (fun (entries : List.{0} NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr))) (And (@Eq.{1} Nat (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries) (@Array.size.{0} Lean.Json arr)) (And (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries)) (fun (_he : @LT.lt.{0} Nat instLTNat i (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries)) => NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (@GetElem.getElem.{0, 0, 0} (List.{0} NoComments.RatchetCore.RatchetEntry) Nat NoComments.RatchetCore.RatchetEntry (fun (as : List.{0} NoComments.RatchetCore.RatchetEntry) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} NoComments.RatchetCore.RatchetEntry as)) (@List.instGetElemNatLtLength.{0} NoComments.RatchetCore.RatchetEntry) entries i _he))) (And (@List.Nodup.{0} String (@List.map.{0, 0} NoComments.RatchetCore.RatchetEntry String (fun (x : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.file x) entries)) (∀ (k : String), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (x : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) x a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m k) (@List.find?.{0} NoComments.RatchetCore.RatchetEntry (fun (x : NoComments.RatchetCore.RatchetEntry) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.RatchetEntry.file x) k) entries)))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (e : NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (e : NoComments.RatchetCore.RatchetEntry) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (fileRaw : String) => @Exists.{1} (Array.{0} Lean.Json) (fun (fpsJson : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "file" (@List.cons.{0} String "comments" (@List.cons.{0} String "lines" (@List.cons.{0} String "fingerprints" (@List.nil.{0} String))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "file") (@Option.some.{0} Lean.Json (Lean.Json.str fileRaw))) (And (NoCommentsSpecification.ConfigSpec.NormRelFile fileRaw (NoComments.RatchetCore.RatchetEntry.file e)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "comments") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk (@Nat.cast.{0} Int instNatCastInt (NoComments.RatchetCore.RatchetEntry.comments e)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Nat instLTNat (NoComments.RatchetCore.RatchetEntry.comments e) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lines") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk (@Nat.cast.{0} Int instNatCastInt (NoComments.RatchetCore.RatchetEntry.lines e)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Nat instLTNat (NoComments.RatchetCore.RatchetEntry.lines e) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "fingerprints") (@Option.some.{0} Lean.Json (Lean.Json.arr fpsJson))) (And (@Eq.{1} (List.{0} Lean.Json) (@Array.toList.{0} Lean.Json fpsJson) (@List.map.{0, 0} String Lean.Json Lean.Json.str (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))))) (And (@Eq.{1} Nat (@Array.size.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (NoComments.RatchetCore.RatchetEntry.comments e)) (∀ (fp : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) fp → NoCommentsSpecification.CoreSpec.IsFingerprint fp))))))))))))))
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
| ### NoComments.RatchetCore.RatchetEntry.file
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.CoreSpec.IsFingerprint
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => And (@Eq.{1} Nat (String.length s) (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (∀ (c : Char), @Membership.mem.{0, 0} Char (List.{0} Char) (@List.instMembership.{0} Char) (String.toList s) c → @Eq.{1} Bool (NoCommentsSpecification.CoreSpec.isHexLowerChar c) Bool.true)
| ```
| 
| ### NoCommentsSpecification.CoreSpec.isHexLowerChar
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (c : Char), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (c : Char) => Bool.or (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 48)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 48)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 57))) (Char.instDecidableLe c (Char.ofNat (nat_lit 57))))) (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 97)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 97)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 102))) (Char.instDecidableLe c (Char.ofNat (nat_lit 102)))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.RatchetRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), Prop
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.badJson
| 
| ```lean
| ∀ {text : String}, (∀ (j : Lean.Json), @Ne.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json j)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.notArray
| 
| ```lean
| ∀ {text : String}, ∀ {j : Lean.Json}, @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json j) → (∀ (arr : Array.{0} Lean.Json), @Ne.{1} Lean.Json j (Lean.Json.arr arr)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.invalidEntry
| 
| ```lean
| ∀ {text : String}, ∀ {arr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr)) → (∀ (e : NoComments.RatchetCore.RatchetEntry), Not (NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i hi) e)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.duplicateFile
| 
| ```lean
| ∀ {text : String}, ∀ {arr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ {j : Nat}, ∀ {e1 : NoComments.RatchetCore.RatchetEntry}, ∀ {e2 : NoComments.RatchetCore.RatchetEntry}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), ∀ (hj : @LT.lt.{0} Nat instLTNat j (@Array.size.{0} Lean.Json arr)), @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr)) → @Ne.{1} Nat i j → NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i hi) e1 → NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr j hj) e2 → @Eq.{1} String (NoComments.RatchetCore.RatchetEntry.file e1) (NoComments.RatchetCore.RatchetEntry.file e2) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| ### NoCommentsSpecification.Healthy.RatchetText
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (text : String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (files : List.{0} String) => And (@Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr))) (And (@Eq.{1} Nat (@List.length.{0} String files) (@Array.size.{0} Lean.Json arr)) (And (@List.Nodup.{0} String files) (∀ (i : Nat), ∀ (h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} String files)) (fun (hf : @LT.lt.{0} Nat instLTNat i (@List.length.{0} String files)) => NoCommentsSpecification.Healthy.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i h) (@GetElem.getElem.{0, 0, 0} (List.{0} String) Nat String (fun (as : List.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} String as)) (@List.instGetElemNatLtLength.{0} String) files i hf)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRatchetEntryJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (fileOut : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (fileOut : String) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (fileRaw : String) => @Exists.{1} Int (fun (comments : Int) => @Exists.{1} Int (fun (lines : Int) => @Exists.{1} (Array.{0} Lean.Json) (fun (fpsJson : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (fpsStrs : List.{0} String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "file" (@List.cons.{0} String "comments" (@List.cons.{0} String "lines" (@List.cons.{0} String "fingerprints" (@List.nil.{0} String))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "file") (@Option.some.{0} Lean.Json (Lean.Json.str fileRaw))) (And (NoCommentsSpecification.Healthy.ValidRelFile fileRaw fileOut) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "comments") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk comments (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Int Int.instLTInt comments (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lines") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk lines (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Int Int.instLTInt lines (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "fingerprints") (@Option.some.{0} Lean.Json (Lean.Json.arr fpsJson))) (And (@Eq.{1} (List.{0} Lean.Json) (@Array.toList.{0} Lean.Json fpsJson) (@List.map.{0, 0} String Lean.Json Lean.Json.str fpsStrs)) (And (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} String fpsStrs)) comments) (And (∀ (fp : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) fpsStrs fp → NoCommentsSpecification.Healthy.isFingerprintStr fp) (@List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) fpsStrs))))))))))))))))))
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
| ### NoCommentsSpecification.Healthy.isFingerprintStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => And (@Eq.{1} Nat (String.length s) (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (∀ (c : Char), @Membership.mem.{0, 0} Char (List.{0} Char) (@List.instMembership.{0} Char) (String.toList s) c → @Eq.{1} Bool (NoCommentsSpecification.Healthy.isHexLowerChar c) Bool.true)
| ```
| 
| ### NoCommentsSpecification.Healthy.isHexLowerChar
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (c : Char), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (c : Char) => Bool.or (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 48)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 48)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 57))) (Char.instDecidableLe c (Char.ofNat (nat_lit 57))))) (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 97)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 97)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 102))) (Char.instDecidableLe c (Char.ofNat (nat_lit 102)))))
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

def delegated_parseRatchet : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-parseRatchet
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.RatchetRecords.parseRatchetRecord
revision 825
| # The intent record NoCommentsSpecification.RatchetRecords.parseRatchetRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} String (fun (a : String) => Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))
| ```
| 
| - **Requires:** parseRatchetJson is a total pure function from String to Except String (HashMap String RatchetEntry).
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
| ### ok_valid_ratchet_map
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), ∀ (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.ok.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m) → NoCommentsSpecification.RatchetSpec.ValidRatchetJson text m
| ```
| 
| - **Requires:** Accepts only JSON arrays of distinct normalized file entries with positive counts and sorted valid fingerprints.
| - **Rules out:** Zero comment/line entries, unsorted fingerprints, duplicate files, unknown keys, or invalid paths/hashes.
| - **Still allows:** Canonical HashMap keyed by normalized file path.
| - **Freedom O5 leaves:** HashMap bucket layout.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.error.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) msg) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| - **Requires:** Returns .error only when RatchetRefusal holds.
| - **Rules out:** Rejecting valid canonical ratchet manifests.
| - **Still allows:** Refusing invalid manifests with arbitrary error strings.
| - **Freedom O5 leaves:** Error wording left free.
| 
| ## Vocabulary
| 
| ### ValidRatchetJson, a predicate over `Prod.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)`
| 
| ```lean
| fun (p : Prod.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => NoCommentsSpecification.RatchetSpec.ValidRatchetJson (@Prod.fst.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) p) (@Prod.snd.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) p)
| ```
| 
| - **Requires:** ValidRatchetJson enforces schema, normalized paths, positive counts, sorted valid hex digests, and unique files.
| - **Rules out:** Empty, unsorted, duplicate, or malformed ratchet entries.
| - **Still allows:** Valid ratchet maps.
| - **Freedom O5 leaves:** Exact map lookup equivalence.
| 
| ### RatchetRefusal, a predicate over `String`
| 
| ```lean
| NoCommentsSpecification.RatchetSpec.RatchetRefusal
| ```
| 
| - **Requires:** RatchetRefusal enumerates every invalid ratchet input cause.
| - **Rules out:** Healthy ratchet manifests.
| - **Still allows:** All malformed ratchet JSON inputs.
| - **Freedom O5 leaves:** Disjoint from ValidRatchetJson.
| 
| ## Consequences
| 
| ### succeeds on every healthy ratchet manifest, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => ∀ (text : String), NoCommentsSpecification.Healthy.RatchetText text → @Exists.{1} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f text) (@Except.ok.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m))
| ```
| 
| - **Requires:** Every healthy ratchet JSON text parses to .ok m.
| - **Rules out:** Spurious rejections on valid ratchets.
| - **Still allows:** Any compliant ratchet parser.
| - **Freedom O5 leaves:** Success guaranteed on healthy ratchet manifests.
| 
| ### leaves refusal message string free on unparseable JSON, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => (∀ (j : Lean.Json), @Ne.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse "") (@Except.ok.{0, 0} String Lean.Json j)) → @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f "") (@Except.error.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) "denied")
| ```
| 
| - **Requires:** Some conforming ratchet parser returns "denied" on empty text.
| - **Rules out:** Nothing; documents diagnostic message freedom.
| - **Still allows:** Custom error messages.
| - **Freedom O5 leaves:** Error text decided below owner level (O5 ParseRatchetFreedom).
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
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.ParseRatchetFn
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
| String → Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidRatchetJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), ∀ (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (text : String) => fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} NoComments.RatchetCore.RatchetEntry) (fun (entries : List.{0} NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr))) (And (@Eq.{1} Nat (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries) (@Array.size.{0} Lean.Json arr)) (And (∀ (i : Nat), ∀ (_h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries)) (fun (_he : @LT.lt.{0} Nat instLTNat i (@List.length.{0} NoComments.RatchetCore.RatchetEntry entries)) => NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i _h) (@GetElem.getElem.{0, 0, 0} (List.{0} NoComments.RatchetCore.RatchetEntry) Nat NoComments.RatchetCore.RatchetEntry (fun (as : List.{0} NoComments.RatchetCore.RatchetEntry) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} NoComments.RatchetCore.RatchetEntry as)) (@List.instGetElemNatLtLength.{0} NoComments.RatchetCore.RatchetEntry) entries i _he))) (And (@List.Nodup.{0} String (@List.map.{0, 0} NoComments.RatchetCore.RatchetEntry String (fun (x : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.file x) entries)) (∀ (k : String), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (x : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) x a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m k) (@List.find?.{0} NoComments.RatchetCore.RatchetEntry (fun (x : NoComments.RatchetCore.RatchetEntry) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.RatchetEntry.file x) k) entries)))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (e : NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (e : NoComments.RatchetCore.RatchetEntry) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (fileRaw : String) => @Exists.{1} (Array.{0} Lean.Json) (fun (fpsJson : Array.{0} Lean.Json) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "file" (@List.cons.{0} String "comments" (@List.cons.{0} String "lines" (@List.cons.{0} String "fingerprints" (@List.nil.{0} String))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "file") (@Option.some.{0} Lean.Json (Lean.Json.str fileRaw))) (And (NoCommentsSpecification.ConfigSpec.NormRelFile fileRaw (NoComments.RatchetCore.RatchetEntry.file e)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "comments") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk (@Nat.cast.{0} Int instNatCastInt (NoComments.RatchetCore.RatchetEntry.comments e)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Nat instLTNat (NoComments.RatchetCore.RatchetEntry.comments e) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lines") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk (@Nat.cast.{0} Int instNatCastInt (NoComments.RatchetCore.RatchetEntry.lines e)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Nat instLTNat (NoComments.RatchetCore.RatchetEntry.lines e) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "fingerprints") (@Option.some.{0} Lean.Json (Lean.Json.arr fpsJson))) (And (@Eq.{1} (List.{0} Lean.Json) (@Array.toList.{0} Lean.Json fpsJson) (@List.map.{0, 0} String Lean.Json Lean.Json.str (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))))) (And (@Eq.{1} Nat (@Array.size.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (NoComments.RatchetCore.RatchetEntry.comments e)) (∀ (fp : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) fp → NoCommentsSpecification.CoreSpec.IsFingerprint fp))))))))))))))
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
| ### NoComments.RatchetCore.RatchetEntry.file
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.CoreSpec.IsFingerprint
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => And (@Eq.{1} Nat (String.length s) (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (∀ (c : Char), @Membership.mem.{0, 0} Char (List.{0} Char) (@List.instMembership.{0} Char) (String.toList s) c → @Eq.{1} Bool (NoCommentsSpecification.CoreSpec.isHexLowerChar c) Bool.true)
| ```
| 
| ### NoCommentsSpecification.CoreSpec.isHexLowerChar
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (c : Char), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (c : Char) => Bool.or (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 48)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 48)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 57))) (Char.instDecidableLe c (Char.ofNat (nat_lit 57))))) (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 97)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 97)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 102))) (Char.instDecidableLe c (Char.ofNat (nat_lit 102)))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.RatchetRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), Prop
| ```
| 
| Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.badJson
| 
| ```lean
| ∀ {text : String}, (∀ (j : Lean.Json), @Ne.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json j)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.notArray
| 
| ```lean
| ∀ {text : String}, ∀ {j : Lean.Json}, @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json j) → (∀ (arr : Array.{0} Lean.Json), @Ne.{1} Lean.Json j (Lean.Json.arr arr)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.invalidEntry
| 
| ```lean
| ∀ {text : String}, ∀ {arr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr)) → (∀ (e : NoComments.RatchetCore.RatchetEntry), Not (NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i hi) e)) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.RatchetRefusal.duplicateFile
| 
| ```lean
| ∀ {text : String}, ∀ {arr : Array.{0} Lean.Json}, ∀ {i : Nat}, ∀ {j : Nat}, ∀ {e1 : NoComments.RatchetCore.RatchetEntry}, ∀ {e2 : NoComments.RatchetCore.RatchetEntry}, ∀ (hi : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), ∀ (hj : @LT.lt.{0} Nat instLTNat j (@Array.size.{0} Lean.Json arr)), @Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr)) → @Ne.{1} Nat i j → NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i hi) e1 → NoCommentsSpecification.RatchetSpec.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr j hj) e2 → @Eq.{1} String (NoComments.RatchetCore.RatchetEntry.file e1) (NoComments.RatchetCore.RatchetEntry.file e2) → NoCommentsSpecification.RatchetSpec.RatchetRefusal text
| ```
| 
| ### NoCommentsSpecification.Healthy.RatchetText
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (text : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (text : String) => @Exists.{1} (Array.{0} Lean.Json) (fun (arr : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (files : List.{0} String) => And (@Eq.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse text) (@Except.ok.{0, 0} String Lean.Json (Lean.Json.arr arr))) (And (@Eq.{1} Nat (@List.length.{0} String files) (@Array.size.{0} Lean.Json arr)) (And (@List.Nodup.{0} String files) (∀ (i : Nat), ∀ (h : @LT.lt.{0} Nat instLTNat i (@Array.size.{0} Lean.Json arr)), @Exists.{0} (@LT.lt.{0} Nat instLTNat i (@List.length.{0} String files)) (fun (hf : @LT.lt.{0} Nat instLTNat i (@List.length.{0} String files)) => NoCommentsSpecification.Healthy.ValidRatchetEntryJson (@GetElem.getElem.{0, 0, 0} (Array.{0} Lean.Json) Nat Lean.Json (fun (xs : Array.{0} Lean.Json) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@Array.size.{0} Lean.Json xs)) (@Array.instGetElemNatLtSize.{0} Lean.Json) arr i h) (@GetElem.getElem.{0, 0, 0} (List.{0} String) Nat String (fun (as : List.{0} String) => fun (x : Nat) => @LT.lt.{0} Nat instLTNat x (@List.length.{0} String as)) (@List.instGetElemNatLtLength.{0} String) files i hf)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidRatchetEntryJson
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (j : Lean.Json), ∀ (fileOut : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (j : Lean.Json) => fun (fileOut : String) => @Exists.{1} (Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) (fun (obj : Std.TreeMap.Raw.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd)) => @Exists.{1} String (fun (fileRaw : String) => @Exists.{1} Int (fun (comments : Int) => @Exists.{1} Int (fun (lines : Int) => @Exists.{1} (Array.{0} Lean.Json) (fun (fpsJson : Array.{0} Lean.Json) => @Exists.{1} (List.{0} String) (fun (fpsStrs : List.{0} String) => And (@Eq.{1} Lean.Json j (Lean.Json.obj obj)) (And (∀ (kv : Prod.{0, 0} String Lean.Json), @Membership.mem.{0, 0} (Prod.{0, 0} String Lean.Json) (List.{0} (Prod.{0, 0} String Lean.Json)) (@List.instMembership.{0} (Prod.{0, 0} String Lean.Json)) (@Std.TreeMap.Raw.toList.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj) kv → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@List.cons.{0} String "file" (@List.cons.{0} String "comments" (@List.cons.{0} String "lines" (@List.cons.{0} String "fingerprints" (@List.nil.{0} String))))) (@Prod.fst.{0, 0} String Lean.Json kv)) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "file") (@Option.some.{0} Lean.Json (Lean.Json.str fileRaw))) (And (NoCommentsSpecification.Healthy.ValidRelFile fileRaw fileOut) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "comments") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk comments (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Int Int.instLTInt comments (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "lines") (@Option.some.{0} Lean.Json (Lean.Json.num (Lean.JsonNumber.mk lines (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (And (@GT.gt.{0} Int Int.instLTInt lines (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (And (@Eq.{1} (Option.{0} Lean.Json) (@Std.TreeMap.Raw.get?.{0, 0} String Lean.Json (@Ord.compare.{0} String String.instOrd) obj "fingerprints") (@Option.some.{0} Lean.Json (Lean.Json.arr fpsJson))) (And (@Eq.{1} (List.{0} Lean.Json) (@Array.toList.{0} Lean.Json fpsJson) (@List.map.{0, 0} String Lean.Json Lean.Json.str fpsStrs)) (And (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} String fpsStrs)) comments) (And (∀ (fp : String), @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) fpsStrs fp → NoCommentsSpecification.Healthy.isFingerprintStr fp) (@List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) fpsStrs))))))))))))))))))
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
| ### NoCommentsSpecification.Healthy.isFingerprintStr
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (s : String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (s : String) => And (@Eq.{1} Nat (String.length s) (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (∀ (c : Char), @Membership.mem.{0, 0} Char (List.{0} Char) (@List.instMembership.{0} Char) (String.toList s) c → @Eq.{1} Bool (NoCommentsSpecification.Healthy.isHexLowerChar c) Bool.true)
| ```
| 
| ### NoCommentsSpecification.Healthy.isHexLowerChar
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (c : Char), Bool
| ```
| 
| Its value:
| 
| ```lean
| fun (c : Char) => Bool.or (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 48)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 48)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 57))) (Char.instDecidableLe c (Char.ofNat (nat_lit 57))))) (Bool.and (@Decidable.decide (@LE.le.{0} Char Char.instLE (Char.ofNat (nat_lit 97)) c) (Char.instDecidableLe (Char.ofNat (nat_lit 97)) c)) (@Decidable.decide (@LE.le.{0} Char Char.instLE c (Char.ofNat (nat_lit 102))) (Char.instDecidableLe c (Char.ofNat (nat_lit 102)))))
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
consequence leaves refusal message string free on unparseable JSON
shown as possibility
predicate 422
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.ParseRatchetFn) => (∀ (j : Lean.Json), @Ne.{1} (Except.{0, 0} String Lean.Json) (Lean.Json.parse "") (@Except.ok.{0, 0} String Lean.Json j)) → @Eq.{1} (Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (f "") (@Except.error.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) "denied")
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.ParseRatchetFn
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
| String → Except.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
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

def restatement_checkExactSync : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-checkExactSync
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.RatchetRecords.checkExactSyncRecord
revision 597
| # The intent record NoCommentsSpecification.RatchetRecords.checkExactSyncRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.RatchetCore.FileAnalysis (fun (a : NoComments.RatchetCore.FileAnalysis) => Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String)
| ```
| 
| - **Requires:** checkExactSync is a total pure function from FileAnalysis and Option RatchetEntry to Array String.
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
| ### empty_errors_iff_exact_sync
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Iff (@Eq.{1} Bool (@Array.isEmpty.{0} String (f analysis entry?)) Bool.true) (NoCommentsSpecification.RatchetSpec.ExactSyncOk analysis entry?)
| ```
| 
| - **Requires:** Returns an empty error array iff ExactSyncOk holds between live analysis and checked-in entry.
| - **Rules out:** Unrecorded comments, stale entries, line-count mismatches, or multiset drift.
| - **Still allows:** Empty error array on exact sync; non-empty diagnostics otherwise.
| - **Freedom O5 leaves:** Error string messages when out of sync (O5 CheckExactSyncFreedom).
| 
| ## Vocabulary
| 
| ### ExactSyncOk, a predicate over `Prod.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry)) => NoCommentsSpecification.RatchetSpec.ExactSyncOk (@Prod.fst.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry) p) (@Prod.snd.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry) p)
| ```
| 
| - **Requires:** ExactSyncOk requires zero comments/lines when absent, and equal comment/line counts and fingerprint multiset when present.
| - **Rules out:** Any comment count, line count, or multiset discrepancy.
| - **Still allows:** Exact match.
| - **Freedom O5 leaves:** Fixes pass/fail verdict.
| 
| ## Consequences
| 
| ### emits no errors when live comments match ratchet entry, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => ∀ (a : NoComments.RatchetCore.FileAnalysis), ∀ (e : Option.{0} NoComments.RatchetCore.RatchetEntry), NoCommentsSpecification.RatchetSpec.ExactSyncOk a e → @Eq.{1} Bool (@Array.isEmpty.{0} String (f a e)) Bool.true
| ```
| 
| - **Requires:** Exact sync guarantees empty error array.
| - **Rules out:** False sync failures.
| - **Still allows:** Any compliant sync checker.
| - **Freedom O5 leaves:** Verdict fixed on exact sync.
| 
| ### leaves error array contents unconstrained on sync mismatch, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| - **Requires:** Some conforming sync checker returns ["denied"] on mismatch.
| - **Rules out:** Nothing; establishes error-list freedom.
| - **Still allows:** Custom diagnostic arrays.
| - **Freedom O5 leaves:** Diagnostic formatting decided below owner level (O5 CheckExactSyncFreedom).
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
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.CheckExactSyncFn
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
| NoComments.RatchetCore.FileAnalysis → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (NoCommentsSpecification.CoreSpec.MultisetEq (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis))) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Array.{0} NoComments.Core.Comment
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoCommentsSpecification.CoreSpec.MultisetEq
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (xs : List.{0} String), ∀ (ys : List.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (xs : List.{0} String) => fun (ys : List.{0} String) => ∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a xs) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a ys)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis
| ```
| 
| Its value:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis.mk "Foo.lean" (@List.toArray.{0} NoComments.Core.Comment (@List.cons.{0} NoComments.Core.Comment NoCommentsSpecification.AdequacyCore.sampleComment1 (@List.nil.{0} NoComments.Core.Comment))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))) NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1)
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.sampleComment1
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.Comment
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.Comment.mk "line" (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) NoCommentsSpecification.AdequacyCore.zeroFp
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.zeroFp
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| String
| ```
| 
| Its value:
| 
| ```lean
| "0000000000000000"
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))
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

def delegated_checkExactSync : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-checkExactSync
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.RatchetRecords.checkExactSyncRecord
revision 597
| # The intent record NoCommentsSpecification.RatchetRecords.checkExactSyncRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} NoComments.RatchetCore.FileAnalysis (fun (a : NoComments.RatchetCore.FileAnalysis) => Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String)
| ```
| 
| - **Requires:** checkExactSync is a total pure function from FileAnalysis and Option RatchetEntry to Array String.
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
| ### empty_errors_iff_exact_sync
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Iff (@Eq.{1} Bool (@Array.isEmpty.{0} String (f analysis entry?)) Bool.true) (NoCommentsSpecification.RatchetSpec.ExactSyncOk analysis entry?)
| ```
| 
| - **Requires:** Returns an empty error array iff ExactSyncOk holds between live analysis and checked-in entry.
| - **Rules out:** Unrecorded comments, stale entries, line-count mismatches, or multiset drift.
| - **Still allows:** Empty error array on exact sync; non-empty diagnostics otherwise.
| - **Freedom O5 leaves:** Error string messages when out of sync (O5 CheckExactSyncFreedom).
| 
| ## Vocabulary
| 
| ### ExactSyncOk, a predicate over `Prod.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry)`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry)) => NoCommentsSpecification.RatchetSpec.ExactSyncOk (@Prod.fst.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry) p) (@Prod.snd.{0, 0} NoComments.RatchetCore.FileAnalysis (Option.{0} NoComments.RatchetCore.RatchetEntry) p)
| ```
| 
| - **Requires:** ExactSyncOk requires zero comments/lines when absent, and equal comment/line counts and fingerprint multiset when present.
| - **Rules out:** Any comment count, line count, or multiset discrepancy.
| - **Still allows:** Exact match.
| - **Freedom O5 leaves:** Fixes pass/fail verdict.
| 
| ## Consequences
| 
| ### emits no errors when live comments match ratchet entry, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => ∀ (a : NoComments.RatchetCore.FileAnalysis), ∀ (e : Option.{0} NoComments.RatchetCore.RatchetEntry), NoCommentsSpecification.RatchetSpec.ExactSyncOk a e → @Eq.{1} Bool (@Array.isEmpty.{0} String (f a e)) Bool.true
| ```
| 
| - **Requires:** Exact sync guarantees empty error array.
| - **Rules out:** False sync failures.
| - **Still allows:** Any compliant sync checker.
| - **Freedom O5 leaves:** Verdict fixed on exact sync.
| 
| ### leaves error array contents unconstrained on sync mismatch, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| - **Requires:** Some conforming sync checker returns ["denied"] on mismatch.
| - **Rules out:** Nothing; establishes error-list freedom.
| - **Still allows:** Custom diagnostic arrays.
| - **Freedom O5 leaves:** Diagnostic formatting decided below owner level (O5 CheckExactSyncFreedom).
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
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.CheckExactSyncFn
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
| NoComments.RatchetCore.FileAnalysis → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (NoCommentsSpecification.CoreSpec.MultisetEq (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis))) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Array.{0} NoComments.Core.Comment
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoCommentsSpecification.CoreSpec.MultisetEq
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (xs : List.{0} String), ∀ (ys : List.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (xs : List.{0} String) => fun (ys : List.{0} String) => ∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a xs) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a ys)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis
| ```
| 
| Its value:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis.mk "Foo.lean" (@List.toArray.{0} NoComments.Core.Comment (@List.cons.{0} NoComments.Core.Comment NoCommentsSpecification.AdequacyCore.sampleComment1 (@List.nil.{0} NoComments.Core.Comment))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))) NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1)
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.sampleComment1
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.Comment
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.Comment.mk "line" (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) NoCommentsSpecification.AdequacyCore.zeroFp
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.zeroFp
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| String
| ```
| 
| Its value:
| 
| ```lean
| "0000000000000000"
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))
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
consequence leaves error array contents unconstrained on sync mismatch
shown as possibility
predicate 504
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckExactSyncFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.CheckExactSyncFn
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
| NoComments.RatchetCore.FileAnalysis → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis
| ```
| 
| Its value:
| 
| ```lean
| NoComments.RatchetCore.FileAnalysis.mk "Foo.lean" (@List.toArray.{0} NoComments.Core.Comment (@List.cons.{0} NoComments.Core.Comment NoCommentsSpecification.AdequacyCore.sampleComment1 (@List.nil.{0} NoComments.Core.Comment))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))) NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1)
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.sampleComment1
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.Comment
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.Comment.mk "line" (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) NoCommentsSpecification.AdequacyCore.zeroFp
| ```
| 
| ### NoCommentsSpecification.AdequacyCore.zeroFp
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| String
| ```
| 
| Its value:
| 
| ```lean
| "0000000000000000"
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.nonEmptyAnalysis._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.cons.{0} String NoCommentsSpecification.AdequacyCore.zeroFp (@List.nil.{0} String))
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

def restatement_checkMonotonicFile : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-checkMonotonicFile
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.RatchetRecords.checkMonotonicFileRecord
revision 491
| # The intent record NoCommentsSpecification.RatchetRecords.checkMonotonicFileRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} String (fun (a : String) => NoComments.Core.SortedFingerprints → Nat → Nat → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String)
| ```
| 
| - **Requires:** checkMonotonicFile is a total pure function from path, live fingerprints, live counts, and optional base entry to Array String.
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
| ### empty_errors_iff_monotonic
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => ∀ (file : String), ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveComments : Nat), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Iff (@Eq.{1} Bool (@Array.isEmpty.{0} String (f file liveFps liveComments liveLines baseEntry?)) Bool.true) (NoCommentsSpecification.RatchetSpec.MonotonicOk liveFps liveLines baseEntry?)
| ```
| 
| - **Requires:** Returns empty error array iff live fingerprints are a sub-multiset of base and liveLines <= base lines.
| - **Rules out:** New or modified comment fingerprints, comment line growth, or comments in files absent from base.
| - **Still allows:** Draining comments downward or keeping identical baseline.
| - **Freedom O5 leaves:** Error string messages when regression occurs (O5 CheckMonotonicFreedom).
| 
| ## Vocabulary
| 
| ### MonotonicOk, a predicate over `Prod.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry))`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry))) => NoCommentsSpecification.RatchetSpec.MonotonicOk (@Prod.fst.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p) (@Prod.fst.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry) (@Prod.snd.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p)) (@Prod.snd.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry) (@Prod.snd.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p))
| ```
| 
| - **Requires:** MonotonicOk requires every live fingerprint count <= base count and liveLines <= baseLines.
| - **Rules out:** Any added fingerprint or increased line count.
| - **Still allows:** Monotonic reduction toward zero.
| - **Freedom O5 leaves:** Fixes exact monotonicity predicate.
| 
| ## Consequences
| 
| ### passes when fingerprints and line count do not regress, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => ∀ (file : String), ∀ (fps : NoComments.Core.SortedFingerprints), ∀ (cs : Nat), ∀ (ls : Nat), ∀ (b : Option.{0} NoComments.RatchetCore.RatchetEntry), NoCommentsSpecification.RatchetSpec.MonotonicOk fps ls b → @Eq.{1} Bool (@Array.isEmpty.{0} String (f file fps cs ls b)) Bool.true
| ```
| 
| - **Requires:** Monotonic inputs always yield empty error array.
| - **Rules out:** Blocking valid comment deletions.
| - **Still allows:** Any compliant monotonicity checker.
| - **Freedom O5 leaves:** Pass verdict guaranteed when MonotonicOk holds.
| 
| ### leaves error array contents unconstrained on regression, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f "Foo.lean" NoComments.Core.SortedFingerprints.empty (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| - **Requires:** Some conforming checker returns ["denied"] when line count grows.
| - **Rules out:** Nothing; establishes error-array freedom.
| - **Still allows:** Custom diagnostic messages.
| - **Freedom O5 leaves:** Error array formatting decided below owner level (O5 CheckMonotonicFreedom).
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
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.CheckMonotonicFn
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
| String → NoComments.Core.SortedFingerprints → Nat → Nat → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.SortedFingerprints
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.nil.{0} String)) NoComments.Core.SortedFingerprints.empty._proof_1
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.nil.{0} String)
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

def delegated_checkMonotonicFile : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-checkMonotonicFile
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.RatchetRecords.checkMonotonicFileRecord
revision 491
| # The intent record NoCommentsSpecification.RatchetRecords.checkMonotonicFileRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} String (fun (a : String) => NoComments.Core.SortedFingerprints → Nat → Nat → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String)
| ```
| 
| - **Requires:** checkMonotonicFile is a total pure function from path, live fingerprints, live counts, and optional base entry to Array String.
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
| ### empty_errors_iff_monotonic
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => ∀ (file : String), ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveComments : Nat), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Iff (@Eq.{1} Bool (@Array.isEmpty.{0} String (f file liveFps liveComments liveLines baseEntry?)) Bool.true) (NoCommentsSpecification.RatchetSpec.MonotonicOk liveFps liveLines baseEntry?)
| ```
| 
| - **Requires:** Returns empty error array iff live fingerprints are a sub-multiset of base and liveLines <= base lines.
| - **Rules out:** New or modified comment fingerprints, comment line growth, or comments in files absent from base.
| - **Still allows:** Draining comments downward or keeping identical baseline.
| - **Freedom O5 leaves:** Error string messages when regression occurs (O5 CheckMonotonicFreedom).
| 
| ## Vocabulary
| 
| ### MonotonicOk, a predicate over `Prod.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry))`
| 
| ```lean
| fun (p : Prod.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry))) => NoCommentsSpecification.RatchetSpec.MonotonicOk (@Prod.fst.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p) (@Prod.fst.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry) (@Prod.snd.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p)) (@Prod.snd.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry) (@Prod.snd.{0, 0} NoComments.Core.SortedFingerprints (Prod.{0, 0} Nat (Option.{0} NoComments.RatchetCore.RatchetEntry)) p))
| ```
| 
| - **Requires:** MonotonicOk requires every live fingerprint count <= base count and liveLines <= baseLines.
| - **Rules out:** Any added fingerprint or increased line count.
| - **Still allows:** Monotonic reduction toward zero.
| - **Freedom O5 leaves:** Fixes exact monotonicity predicate.
| 
| ## Consequences
| 
| ### passes when fingerprints and line count do not regress, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => ∀ (file : String), ∀ (fps : NoComments.Core.SortedFingerprints), ∀ (cs : Nat), ∀ (ls : Nat), ∀ (b : Option.{0} NoComments.RatchetCore.RatchetEntry), NoCommentsSpecification.RatchetSpec.MonotonicOk fps ls b → @Eq.{1} Bool (@Array.isEmpty.{0} String (f file fps cs ls b)) Bool.true
| ```
| 
| - **Requires:** Monotonic inputs always yield empty error array.
| - **Rules out:** Blocking valid comment deletions.
| - **Still allows:** Any compliant monotonicity checker.
| - **Freedom O5 leaves:** Pass verdict guaranteed when MonotonicOk holds.
| 
| ### leaves error array contents unconstrained on regression, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f "Foo.lean" NoComments.Core.SortedFingerprints.empty (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| - **Requires:** Some conforming checker returns ["denied"] when line count grows.
| - **Rules out:** Nothing; establishes error-array freedom.
| - **Still allows:** Custom diagnostic messages.
| - **Freedom O5 leaves:** Error array formatting decided below owner level (O5 CheckMonotonicFreedom).
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
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.CheckMonotonicFn
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
| String → NoComments.Core.SortedFingerprints → Nat → Nat → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.SortedFingerprints
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.nil.{0} String)) NoComments.Core.SortedFingerprints.empty._proof_1
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.nil.{0} String)
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
consequence leaves error array contents unconstrained on regression
shown as possibility
predicate 444
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.CheckMonotonicFn) => @Eq.{1} (List.{0} String) (@Array.toList.{0} String (f "Foo.lean" NoComments.Core.SortedFingerprints.empty (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Option.none.{0} NoComments.RatchetCore.RatchetEntry))) (@List.cons.{0} String "denied" (@List.nil.{0} String))
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.CheckMonotonicFn
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
| String → NoComments.Core.SortedFingerprints → Nat → Nat → Option.{0} NoComments.RatchetCore.RatchetEntry → Array.{0} String
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| NoComments.Core.SortedFingerprints
| ```
| 
| Its value:
| 
| ```lean
| NoComments.Core.SortedFingerprints.mk (@List.toArray.{0} String (@List.nil.{0} String)) NoComments.Core.SortedFingerprints.empty._proof_1
| ```
| 
| ### NoComments.Core.SortedFingerprints.empty._proof_1
| 
| A theorem, whose proof is not printed: any two proofs of a proposition are equal by definitional proof irrelevance, so a term that uses it depends on nothing but its statement. It has no universe parameter. Its type:
| 
| ```lean
| @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@List.nil.{0} String)
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

def restatement_validateCheck : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id restatement-validateCheck
date 2026-11-22
reference https://github.com/rbeauchamp/lean-no-comments/issues/2#issuecomment-7079657185
by rbeauchamp
as owner
record NoCommentsSpecification.RatchetRecords.validateCheckRecord
revision 817
| # The intent record NoCommentsSpecification.RatchetRecords.validateCheckRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (fun (a : Array.{0} NoComments.RatchetCore.FileAnalysis) => Array.{0} String → Array.{0} String → @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString → Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Option.{0} String → Except.{0, 0} String Unit)
| ```
| 
| - **Requires:** validateCheck is a total pure function from analyses, file lists, current/base ratchets, and optional target to Except String Unit.
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
| ### ok_only_when_valid
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checked : Array.{0} String), ∀ (excluded : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (base? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (target? : Option.{0} String), @Eq.{1} (Except.{0, 0} String Unit) (f analyses checked excluded cur base? target?) (@Except.ok.{0, 0} String Unit Unit.unit) → NoCommentsSpecification.RatchetSpec.ValidateOk analyses checked excluded cur base? target?
| ```
| 
| - **Requires:** Returns .ok () only when current/base ratchets contain no excluded/untracked files and target/all analyses satisfy ExactSyncOk and MonotonicOk.
| - **Rules out:** Stale excluded entries, dropped file coverage, missing target analysis, out-of-sync manifests, or merge-base regressions.
| - **Still allows:** Full repository or single-file passing checks.
| - **Freedom O5 leaves:** Error formatting.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checked : Array.{0} String), ∀ (excluded : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (base? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (target? : Option.{0} String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String Unit) (f analyses checked excluded cur base? target?) (@Except.error.{0, 0} String Unit msg) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checked excluded cur base? target?
| ```
| 
| - **Requires:** Returns .error only when ValidateRefusal holds.
| - **Rules out:** Rejecting healthy valid checks.
| - **Still allows:** Refusing violations with arbitrary error messages.
| - **Freedom O5 leaves:** Error wording left free (O5 ValidateCheckFreedom).
| 
| ## Vocabulary
| 
| ### ValidateOk, a predicate over `Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))`
| 
| ```lean
| fun (p : Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))) => NoCommentsSpecification.RatchetSpec.ValidateOk (@Prod.fst.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))) (@Prod.fst.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))) (@Prod.fst.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))))) (@Prod.snd.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))))
| ```
| 
| - **Requires:** ValidateOk enforces current/base coverage invariants and sync + monotonicity over target or all analyses.
| - **Rules out:** Coverage holes, excluded ratchet entries, or ratchet regressions.
| - **Still allows:** Clean sync and downward-monotonic checks.
| - **Freedom O5 leaves:** Exact overall validation predicate.
| 
| ### ValidateRefusal, a predicate over `Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))`
| 
| ```lean
| fun (p : Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))) => NoCommentsSpecification.RatchetSpec.ValidateRefusal (@Prod.fst.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))) (@Prod.fst.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))) (@Prod.fst.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))))) (@Prod.snd.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))))
| ```
| 
| - **Requires:** ValidateRefusal enumerates missing targets, excluded/untracked ratchet entries, sync mismatches, and regressions.
| - **Rules out:** Healthy passing check inputs.
| - **Still allows:** All check failures.
| - **Freedom O5 leaves:** Disjoint from ValidateOk.
| 
| ## Consequences
| 
| ### passes every healthy check input, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (a : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (c : Array.{0} String), ∀ (e : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (b : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (t : Option.{0} String), NoCommentsSpecification.Healthy.ValidateInput a c e cur b t → @Eq.{1} (Except.{0, 0} String Unit) (f a c e cur b t) (@Except.ok.{0, 0} String Unit Unit.unit)
| ```
| 
| - **Requires:** Healthy validation inputs always return .ok ().
| - **Rules out:** False failures on compliant builds.
| - **Still allows:** Any conforming check validator.
| - **Freedom O5 leaves:** Success guaranteed on healthy input.
| 
| ### leaves refusal error wording unconstrained on missing target, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => @Eq.{1} (Except.{0, 0} String Unit) (f (@List.toArray.{0} NoComments.RatchetCore.FileAnalysis (@List.nil.{0} NoComments.RatchetCore.FileAnalysis)) (@List.toArray.{0} String (@List.nil.{0} String)) (@List.toArray.{0} String (@List.nil.{0} String)) NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (@Option.some.{0} String "Foo.lean")) (@Except.error.{0, 0} String Unit "denied")
| ```
| 
| - **Requires:** Some conforming validator returns "denied" when target analysis is missing.
| - **Rules out:** Nothing; establishes error-message freedom.
| - **Still allows:** Custom failure diagnostic strings.
| - **Freedom O5 leaves:** Error wording decided below owner level (O5 ValidateCheckFreedom).
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
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.ValidateCheckFn
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
| Array.{0} NoComments.RatchetCore.FileAnalysis → Array.{0} String → Array.{0} String → @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString → Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Option.{0} String → Except.{0, 0} String Unit
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis) => fun (checkedFiles : Array.{0} String) => fun (excludedFiles : Array.{0} String) => fun (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (targetFile? : Option.{0} String) => And (∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → And (Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f)) (And (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => ∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (fun («_» : Unit) => True)) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_3.{1} (fun (x : Option.{0} String) => Prop) targetFile? (fun (target : String) => @Exists.{1} NoComments.RatchetCore.FileAnalysis (fun (live : NoComments.RatchetCore.FileAnalysis) => And (@Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live)) (And (NoCommentsSpecification.RatchetSpec.ExactSyncOk live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) (fun («_» : Unit) => True))))) (fun («_» : Unit) => ∀ (a : NoComments.RatchetCore.FileAnalysis), @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → And (NoCommentsSpecification.RatchetSpec.ExactSyncOk a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) (fun (x : Unit) => True)))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))), motive baseRatchet?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))) => @Option.casesOn.{u_1, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => motive x) baseRatchet? (h_2 Unit.unit) (fun (val : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk.match_3
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} String → Sort u_1), ∀ (targetFile? : Option.{0} String), ∀ (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)), motive targetFile?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} String → Sort u_1) => fun (targetFile? : Option.{0} String) => fun (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)) => @Option.casesOn.{u_1, 0} String (fun (x : Option.{0} String) => motive x) targetFile? (h_2 Unit.unit) (fun (val : String) => h_1 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.file
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (NoCommentsSpecification.CoreSpec.MultisetEq (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis))) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Array.{0} NoComments.Core.Comment
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoCommentsSpecification.CoreSpec.MultisetEq
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (xs : List.{0} String), ∀ (ys : List.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (xs : List.{0} String) => fun (ys : List.{0} String) => ∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a xs) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a ys)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Of the arguments its type takes, the first 6 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.currentRatchetExcluded
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.currentRatchetUnknown
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.baseRatchetExcluded
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.missingTargetAnalysis
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.none.{0} NoComments.RatchetCore.FileAnalysis) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.targetSyncFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, ∀ {live : NoComments.RatchetCore.FileAnalysis}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live) → Not (NoCommentsSpecification.RatchetSpec.ExactSyncOk live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.targetMonotonicFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, ∀ {live : NoComments.RatchetCore.FileAnalysis}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live) → Not (NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.analysisSyncFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {a : NoComments.RatchetCore.FileAnalysis}, @Eq.{1} (Option.{0} String) targetFile? (@Option.none.{0} String) → @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → Not (NoCommentsSpecification.RatchetSpec.ExactSyncOk a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.analysisMonotonicFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {a : NoComments.RatchetCore.FileAnalysis}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, @Eq.{1} (Option.{0} String) targetFile? (@Option.none.{0} String) → @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → Not (NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis) => fun (checkedFiles : Array.{0} String) => fun (excludedFiles : Array.{0} String) => fun (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (targetFile? : Option.{0} String) => And (∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → And (Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f)) (And (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => ∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (fun («_» : Unit) => True)) (NoCommentsSpecification.Healthy.ValidateInput.match_3.{1} (fun (x : Option.{0} String) => Prop) targetFile? (fun (target : String) => @Exists.{1} NoComments.RatchetCore.FileAnalysis (fun (live : NoComments.RatchetCore.FileAnalysis) => And (@Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live)) (And (NoCommentsSpecification.Healthy.ExactSyncHolds live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.Healthy.MonotonicHolds (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) (fun («_» : Unit) => True))))) (fun («_» : Unit) => ∀ (a : NoComments.RatchetCore.FileAnalysis), @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → And (NoCommentsSpecification.Healthy.ExactSyncHolds a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.Healthy.MonotonicHolds (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) (fun (x : Unit) => True)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))), motive baseRatchet?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))) => @Option.casesOn.{u_1, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => motive x) baseRatchet? (h_2 Unit.unit) (fun (val : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput.match_3
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} String → Sort u_1), ∀ (targetFile? : Option.{0} String), ∀ (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)), motive targetFile?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} String → Sort u_1) => fun (targetFile? : Option.{0} String) => fun (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)) => @Option.casesOn.{u_1, 0} String (fun (x : Option.{0} String) => motive x) targetFile? (h_2 Unit.unit) (fun (val : String) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.ExactSyncHolds
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.Healthy.ExactSyncHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis)))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ExactSyncHolds.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.MonotonicHolds
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.Healthy.MonotonicHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.Healthy.MonotonicHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.Healthy.MonotonicHolds.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString
| ```
| 
| Its value:
| 
| ```lean
| @EmptyCollection.emptyCollection.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instEmptyCollection.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
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

def delegated_validateCheck : String :=
r###"lean-intent statement 1
kind answer
project lean-no-comments
id delegated-validateCheck
date 2026-11-22
words 1
| Decided below owner level under agent delegation and confirmed against the system contract on 2026-11-22.
by antigravity
under agent-delegation
record NoCommentsSpecification.RatchetRecords.validateCheckRecord
revision 817
| # The intent record NoCommentsSpecification.RatchetRecords.validateCheckRecord
| 
| Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened. The plain words after it are written by a model and are trusted, not proved.
| 
| ## Shape
| 
| ### The subject
| 
| ```lean
| LeanIntent.Shape.function.{0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (fun (a : Array.{0} NoComments.RatchetCore.FileAnalysis) => Array.{0} String → Array.{0} String → @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString → Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Option.{0} String → Except.{0, 0} String Unit)
| ```
| 
| - **Requires:** validateCheck is a total pure function from analyses, file lists, current/base ratchets, and optional target to Except String Unit.
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
| ### ok_only_when_valid
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checked : Array.{0} String), ∀ (excluded : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (base? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (target? : Option.{0} String), @Eq.{1} (Except.{0, 0} String Unit) (f analyses checked excluded cur base? target?) (@Except.ok.{0, 0} String Unit Unit.unit) → NoCommentsSpecification.RatchetSpec.ValidateOk analyses checked excluded cur base? target?
| ```
| 
| - **Requires:** Returns .ok () only when current/base ratchets contain no excluded/untracked files and target/all analyses satisfy ExactSyncOk and MonotonicOk.
| - **Rules out:** Stale excluded entries, dropped file coverage, missing target analysis, out-of-sync manifests, or merge-base regressions.
| - **Still allows:** Full repository or single-file passing checks.
| - **Freedom O5 leaves:** Error formatting.
| 
| ### refusal_sound
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checked : Array.{0} String), ∀ (excluded : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (base? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (target? : Option.{0} String), ∀ (msg : String), @Eq.{1} (Except.{0, 0} String Unit) (f analyses checked excluded cur base? target?) (@Except.error.{0, 0} String Unit msg) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checked excluded cur base? target?
| ```
| 
| - **Requires:** Returns .error only when ValidateRefusal holds.
| - **Rules out:** Rejecting healthy valid checks.
| - **Still allows:** Refusing violations with arbitrary error messages.
| - **Freedom O5 leaves:** Error wording left free (O5 ValidateCheckFreedom).
| 
| ## Vocabulary
| 
| ### ValidateOk, a predicate over `Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))`
| 
| ```lean
| fun (p : Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))) => NoCommentsSpecification.RatchetSpec.ValidateOk (@Prod.fst.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))) (@Prod.fst.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))) (@Prod.fst.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))))) (@Prod.snd.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))))
| ```
| 
| - **Requires:** ValidateOk enforces current/base coverage invariants and sync + monotonicity over target or all analyses.
| - **Rules out:** Coverage holes, excluded ratchet entries, or ratchet regressions.
| - **Still allows:** Clean sync and downward-monotonic checks.
| - **Freedom O5 leaves:** Exact overall validation predicate.
| 
| ### ValidateRefusal, a predicate over `Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))`
| 
| ```lean
| fun (p : Prod.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))))) => NoCommentsSpecification.RatchetSpec.ValidateRefusal (@Prod.fst.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)) (@Prod.fst.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))) (@Prod.fst.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))) (@Prod.fst.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p))))) (@Prod.snd.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String) (@Prod.snd.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))) (@Prod.snd.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String)))) (@Prod.snd.{0, 0} (Array.{0} NoComments.RatchetCore.FileAnalysis) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (Array.{0} String) (Prod.{0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (Prod.{0, 0} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (Option.{0} String))))) p)))))
| ```
| 
| - **Requires:** ValidateRefusal enumerates missing targets, excluded/untracked ratchet entries, sync mismatches, and regressions.
| - **Rules out:** Healthy passing check inputs.
| - **Still allows:** All check failures.
| - **Freedom O5 leaves:** Disjoint from ValidateOk.
| 
| ## Consequences
| 
| ### passes every healthy check input, an entailment: every subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => ∀ (a : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (c : Array.{0} String), ∀ (e : Array.{0} String), ∀ (cur : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (b : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (t : Option.{0} String), NoCommentsSpecification.Healthy.ValidateInput a c e cur b t → @Eq.{1} (Except.{0, 0} String Unit) (f a c e cur b t) (@Except.ok.{0, 0} String Unit Unit.unit)
| ```
| 
| - **Requires:** Healthy validation inputs always return .ok ().
| - **Rules out:** False failures on compliant builds.
| - **Still allows:** Any conforming check validator.
| - **Freedom O5 leaves:** Success guaranteed on healthy input.
| 
| ### leaves refusal error wording unconstrained on missing target, a possibility: some subject that meets the record satisfies it
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => @Eq.{1} (Except.{0, 0} String Unit) (f (@List.toArray.{0} NoComments.RatchetCore.FileAnalysis (@List.nil.{0} NoComments.RatchetCore.FileAnalysis)) (@List.toArray.{0} String (@List.nil.{0} String)) (@List.toArray.{0} String (@List.nil.{0} String)) NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (@Option.some.{0} String "Foo.lean")) (@Except.error.{0, 0} String Unit "denied")
| ```
| 
| - **Requires:** Some conforming validator returns "denied" when target analysis is missing.
| - **Rules out:** Nothing; establishes error-message freedom.
| - **Still allows:** Custom failure diagnostic strings.
| - **Freedom O5 leaves:** Error wording decided below owner level (O5 ValidateCheckFreedom).
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
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.ValidateCheckFn
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
| Array.{0} NoComments.RatchetCore.FileAnalysis → Array.{0} String → Array.{0} String → @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString → Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Option.{0} String → Except.{0, 0} String Unit
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis) => fun (checkedFiles : Array.{0} String) => fun (excludedFiles : Array.{0} String) => fun (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (targetFile? : Option.{0} String) => And (∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → And (Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f)) (And (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => ∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (fun («_» : Unit) => True)) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_3.{1} (fun (x : Option.{0} String) => Prop) targetFile? (fun (target : String) => @Exists.{1} NoComments.RatchetCore.FileAnalysis (fun (live : NoComments.RatchetCore.FileAnalysis) => And (@Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live)) (And (NoCommentsSpecification.RatchetSpec.ExactSyncOk live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) (fun («_» : Unit) => True))))) (fun («_» : Unit) => ∀ (a : NoComments.RatchetCore.FileAnalysis), @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → And (NoCommentsSpecification.RatchetSpec.ExactSyncOk a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) (NoCommentsSpecification.RatchetSpec.ValidateOk.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) (fun (x : Unit) => True)))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))), motive baseRatchet?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))) => @Option.casesOn.{u_1, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => motive x) baseRatchet? (h_2 Unit.unit) (fun (val : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateOk.match_3
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} String → Sort u_1), ∀ (targetFile? : Option.{0} String), ∀ (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)), motive targetFile?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} String → Sort u_1) => fun (targetFile? : Option.{0} String) => fun (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)) => @Option.casesOn.{u_1, 0} String (fun (x : Option.{0} String) => motive x) targetFile? (h_2 Unit.unit) (fun (val : String) => h_1 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.file
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), String
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (NoCommentsSpecification.CoreSpec.MultisetEq (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis))) (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry))))))
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ExactSyncOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Array.{0} NoComments.Core.Comment
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.comments
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 2, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.lines
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 3, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), Nat
| ```
| 
| ### NoCommentsSpecification.CoreSpec.MultisetEq
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (xs : List.{0} String), ∀ (ys : List.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (xs : List.{0} String) => fun (ys : List.{0} String) => ∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a xs) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a ys)
| ```
| 
| ### NoComments.Core.SortedFingerprints.values
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 1, counted after the parameters in the type of NoComments.Core.SortedFingerprints's constructor, of its argument number 1, a value of NoComments.Core.SortedFingerprints. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.Core.SortedFingerprints), Array.{0} String
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.FileAnalysis's constructor, of its argument number 1, a value of NoComments.RatchetCore.FileAnalysis. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.FileAnalysis), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry.fingerprints
| 
| A function that reads a field of a structure: its value is `fun` over its first 1 arguments and returns field number 4, counted after the parameters in the type of NoComments.RatchetCore.RatchetEntry's constructor, of its argument number 1, a value of NoComments.RatchetCore.RatchetEntry. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (self : NoComments.RatchetCore.RatchetEntry), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.MonotonicOk.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.RatchetSpec.ValidateRefusal
| 
| An inductive type. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Of the arguments its type takes, the first 6 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.currentRatchetExcluded
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.currentRatchetUnknown
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.baseRatchetExcluded
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {f : String}, ∀ {e : NoComments.RatchetCore.RatchetEntry}, @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → @Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.missingTargetAnalysis
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.none.{0} NoComments.RatchetCore.FileAnalysis) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.targetSyncFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, ∀ {live : NoComments.RatchetCore.FileAnalysis}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live) → Not (NoCommentsSpecification.RatchetSpec.ExactSyncOk live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.targetMonotonicFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {target : String}, ∀ {live : NoComments.RatchetCore.FileAnalysis}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, @Eq.{1} (Option.{0} String) targetFile? (@Option.some.{0} String target) → @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live) → Not (NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.analysisSyncFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {a : NoComments.RatchetCore.FileAnalysis}, @Eq.{1} (Option.{0} String) targetFile? (@Option.none.{0} String) → @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → Not (NoCommentsSpecification.RatchetSpec.ExactSyncOk a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| #### NoCommentsSpecification.RatchetSpec.ValidateRefusal.analysisMonotonicFailed
| 
| ```lean
| ∀ {analyses : Array.{0} NoComments.RatchetCore.FileAnalysis}, ∀ {checkedFiles : Array.{0} String}, ∀ {excludedFiles : Array.{0} String}, ∀ {currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, ∀ {baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)}, ∀ {targetFile? : Option.{0} String}, ∀ {a : NoComments.RatchetCore.FileAnalysis}, ∀ {base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString}, @Eq.{1} (Option.{0} String) targetFile? (@Option.none.{0} String) → @Eq.{1} (Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) baseRatchet? (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base) → @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → Not (NoCommentsSpecification.RatchetSpec.MonotonicOk (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) → NoCommentsSpecification.RatchetSpec.ValidateRefusal analyses checkedFiles excludedFiles currentRatchet baseRatchet? targetFile?
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis), ∀ (checkedFiles : Array.{0} String), ∀ (excludedFiles : Array.{0} String), ∀ (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (targetFile? : Option.{0} String), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analyses : Array.{0} NoComments.RatchetCore.FileAnalysis) => fun (checkedFiles : Array.{0} String) => fun (excludedFiles : Array.{0} String) => fun (currentRatchet : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (targetFile? : Option.{0} String) => And (∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → And (Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String checkedFiles) f)) (And (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => ∀ (f : String), ∀ (e : NoComments.RatchetCore.RatchetEntry), @Eq.{1} (Option.{0} NoComments.RatchetCore.RatchetEntry) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base f) (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e) → Not (@Membership.mem.{0, 0} String (List.{0} String) (@List.instMembership.{0} String) (@Array.toList.{0} String excludedFiles) f)) (fun («_» : Unit) => True)) (NoCommentsSpecification.Healthy.ValidateInput.match_3.{1} (fun (x : Option.{0} String) => Prop) targetFile? (fun (target : String) => @Exists.{1} NoComments.RatchetCore.FileAnalysis (fun (live : NoComments.RatchetCore.FileAnalysis) => And (@Eq.{1} (Option.{0} NoComments.RatchetCore.FileAnalysis) (@Array.find?.{0} NoComments.RatchetCore.FileAnalysis (fun (x : NoComments.RatchetCore.FileAnalysis) => @BEq.beq.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) (NoComments.RatchetCore.FileAnalysis.file x) target) analyses) (@Option.some.{0} NoComments.RatchetCore.FileAnalysis live)) (And (NoCommentsSpecification.Healthy.ExactSyncHolds live (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet target)) (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.Healthy.MonotonicHolds (NoComments.RatchetCore.FileAnalysis.fingerprints live) (NoComments.RatchetCore.FileAnalysis.lines live) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (a : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m a) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base target)) (fun («_» : Unit) => True))))) (fun («_» : Unit) => ∀ (a : NoComments.RatchetCore.FileAnalysis), @Membership.mem.{0, 0} NoComments.RatchetCore.FileAnalysis (List.{0} NoComments.RatchetCore.FileAnalysis) (@List.instMembership.{0} NoComments.RatchetCore.FileAnalysis) (@Array.toList.{0} NoComments.RatchetCore.FileAnalysis analyses) a → And (NoCommentsSpecification.Healthy.ExactSyncHolds a (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) currentRatchet (NoComments.RatchetCore.FileAnalysis.file a))) (NoCommentsSpecification.Healthy.ValidateInput.match_1.{1} (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => Prop) baseRatchet? (fun (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => NoCommentsSpecification.Healthy.MonotonicHolds (NoComments.RatchetCore.FileAnalysis.fingerprints a) (NoComments.RatchetCore.FileAnalysis.lines a) (@GetElem?.getElem?.{0, 0, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) String NoComments.RatchetCore.RatchetEntry (fun (m : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => fun (x : String) => @Membership.mem.{0, 0} String (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instMembership.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) m x) (@Std.HashMap.instGetElem?Mem.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base (NoComments.RatchetCore.FileAnalysis.file a))) (fun (x : Unit) => True)))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1), ∀ (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)), ∀ (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))), motive baseRatchet?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Sort u_1) => fun (baseRatchet? : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => fun (h_1 : ∀ (base : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString), motive (@Option.some.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) base)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString))) => @Option.casesOn.{u_1, 0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (fun (x : Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) => motive x) baseRatchet? (h_2 Unit.unit) (fun (val : @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.ValidateInput.match_3
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} String → Sort u_1), ∀ (targetFile? : Option.{0} String), ∀ (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)), motive targetFile?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} String → Sort u_1) => fun (targetFile? : Option.{0} String) => fun (h_1 : ∀ (target : String), motive (@Option.some.{0} String target)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} String)) => @Option.casesOn.{u_1, 0} String (fun (x : Option.{0} String) => motive x) targetFile? (h_2 Unit.unit) (fun (val : String) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.ExactSyncHolds
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (analysis : NoComments.RatchetCore.FileAnalysis), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (analysis : NoComments.RatchetCore.FileAnalysis) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => NoCommentsSpecification.Healthy.ExactSyncHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Prop) entry? (fun («_» : Unit) => And (@Eq.{1} Bool (@Array.isEmpty.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis)) Bool.true) (@Eq.{1} Nat (NoComments.RatchetCore.FileAnalysis.lines analysis) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (fun (entry : NoComments.RatchetCore.RatchetEntry) => And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.comments entry) (@Array.size.{0} NoComments.Core.Comment (NoComments.RatchetCore.FileAnalysis.comments analysis))) (And (@Eq.{1} Nat (NoComments.RatchetCore.RatchetEntry.lines entry) (NoComments.RatchetCore.FileAnalysis.lines analysis)) (∀ (a : String), @Eq.{1} Nat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.FileAnalysis.fingerprints analysis)))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints entry)))))))
| ```
| 
| ### NoCommentsSpecification.Healthy.ExactSyncHolds.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), ∀ (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)), motive entry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (entry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => fun (h_2 : ∀ (entry : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry entry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) entry? (h_1 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_2 val)
| ```
| 
| ### NoCommentsSpecification.Healthy.MonotonicHolds
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| ∀ (liveFps : NoComments.Core.SortedFingerprints), ∀ (liveLines : Nat), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), Prop
| ```
| 
| Its value:
| 
| ```lean
| fun (liveFps : NoComments.Core.SortedFingerprints) => fun (liveLines : Nat) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => have expFps : List.{0} String := NoCommentsSpecification.Healthy.MonotonicHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => List.{0} String) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => @Array.toList.{0} String (NoComments.Core.SortedFingerprints.values (NoComments.RatchetCore.RatchetEntry.fingerprints e))) (fun («_» : Unit) => @List.nil.{0} String); have expLines : Nat := NoCommentsSpecification.Healthy.MonotonicHolds.match_1.{1} (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => Nat) baseEntry? (fun (e : NoComments.RatchetCore.RatchetEntry) => NoComments.RatchetCore.RatchetEntry.lines e) (fun («_» : Unit) => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))); And (∀ (a : String), @LE.le.{0} Nat instLENat (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a (@Array.toList.{0} String (NoComments.Core.SortedFingerprints.values liveFps))) (@List.count.{0} String (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) a expFps)) (@LE.le.{0} Nat instLENat liveLines expLines)
| ```
| 
| ### NoCommentsSpecification.Healthy.MonotonicHolds.match_1
| 
| A definition. It has the universe parameter u_1. Its type:
| 
| ```lean
| ∀ (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1), ∀ (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry), ∀ (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)), ∀ (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)), motive baseEntry?
| ```
| 
| Its value:
| 
| ```lean
| fun (motive : Option.{0} NoComments.RatchetCore.RatchetEntry → Sort u_1) => fun (baseEntry? : Option.{0} NoComments.RatchetCore.RatchetEntry) => fun (h_1 : ∀ (e : NoComments.RatchetCore.RatchetEntry), motive (@Option.some.{0} NoComments.RatchetCore.RatchetEntry e)) => fun (h_2 : ∀ («_» : Unit), motive (@Option.none.{0} NoComments.RatchetCore.RatchetEntry)) => @Option.casesOn.{u_1, 0} NoComments.RatchetCore.RatchetEntry (fun (x : Option.{0} NoComments.RatchetCore.RatchetEntry) => motive x) baseEntry? (h_2 Unit.unit) (fun (val : NoComments.RatchetCore.RatchetEntry) => h_1 val)
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString
| ```
| 
| Its value:
| 
| ```lean
| @EmptyCollection.emptyCollection.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instEmptyCollection.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
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
consequence leaves refusal error wording unconstrained on missing target
shown as possibility
predicate 468
| # A consequence's predicate
| 
| Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks, binder names and metadata aside, from the root namespace with nothing opened.
| 
| ```lean
| fun (f : NoCommentsSpecification.ValidateCheckFn) => @Eq.{1} (Except.{0, 0} String Unit) (f (@List.toArray.{0} NoComments.RatchetCore.FileAnalysis (@List.nil.{0} NoComments.RatchetCore.FileAnalysis)) (@List.toArray.{0} String (@List.nil.{0} String)) (@List.toArray.{0} String (@List.nil.{0} String)) NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap (@Option.none.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)) (@Option.some.{0} String "Foo.lean")) (@Except.error.{0, 0} String Unit "denied")
| ```
| 
| ## Definitions the predicate reaches
| 
| Each is printed in full, as in the rendering of a record, with what an answer to it asks of every later revision (`LeanIntent.Answer.KeptBy`).
| 
| ### NoCommentsSpecification.ValidateCheckFn
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
| Array.{0} NoComments.RatchetCore.FileAnalysis → Array.{0} String → Array.{0} String → @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString → Option.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) → Option.{0} String → Except.{0, 0} String Unit
| ```
| 
| ### NoComments.RatchetCore.FileAnalysis
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.FileAnalysis.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Array.{0} NoComments.Core.Comment), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.FileAnalysis
| ```
| 
| ### NoComments.Core.Comment
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.Comment.mk
| 
| ```lean
| ∀ (kind : String), ∀ (startLine : Nat), ∀ (endLine : Nat), ∀ (fingerprint : String), NoComments.Core.Comment
| ```
| 
| ### NoComments.Core.SortedFingerprints
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.Core.SortedFingerprints.mk
| 
| ```lean
| ∀ (values : Array.{0} String), ∀ (sorted : @List.Pairwise.{0} String (fun (x1 : String) => fun (x2 : String) => @LE.le.{0} String String.instLE x1 x2) (@Array.toList.{0} String values)), NoComments.Core.SortedFingerprints
| ```
| 
| ### NoComments.RatchetCore.RatchetEntry
| 
| A structure: an inductive type with one constructor, whose arguments after its parameters are the structure's fields, in order. It has no universe parameter. Its type:
| 
| ```lean
| Type
| ```
| 
| Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its recursor is the one Lean's kernel derives from this declaration. Its constructors, in order, each with its type:
| 
| #### NoComments.RatchetCore.RatchetEntry.mk
| 
| ```lean
| ∀ (file : String), ∀ (comments : Nat), ∀ (lines : Nat), ∀ (fingerprints : NoComments.Core.SortedFingerprints), NoComments.RatchetCore.RatchetEntry
| ```
| 
| ### NoCommentsSpecification.AdequacyRatchet.emptyRatchetMap
| 
| A definition. It has no universe parameter. Its type:
| 
| ```lean
| @Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString
| ```
| 
| Its value:
| 
| ```lean
| @EmptyCollection.emptyCollection.{0} (@Std.HashMap.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString) (@Std.HashMap.instEmptyCollection.{0, 0} String NoComments.RatchetCore.RatchetEntry (@Std.PreorderPackage.toBEq.{0} String (@Std.LinearPreorderPackage.toPreorderPackage.{0} String (@Std.LinearOrderPackage.toLinearPreorderPackage.{0} String String.instLinearOrderPackage))) instHashableString)
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

end NoCommentsSpecification.OwnersLogEntriesRatchet
