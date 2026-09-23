import Googology.Core.Std
import Googology.Core.Morphism

/-!
# Goal records

Section 6 of `spec.md` fixes one proposition per column of the README tables.
This file holds the types that record, as Lean values, which of those
propositions are proved for a notation (section 7 of `spec.md`).

* `Rewrite.Std.WF`: one step, restricted to the standard forms, is well
  founded.  It is the well-foundedness of section 6.
* `Goal P`: `P` is proved, refuted, or not yet proved.
* `Runs R`: the expansion of `R` runs, on codes.
* `Incl R Q`: `R` is `Q` on part of its states.
* `NotationGoals`, `NonStdGoals`: the columns of the first table.
* `AuditLine`: one line of the audit, one per record and column.

A record type takes the objects its propositions talk about as parameters of
the type, not as fields.  So the proposition behind each column is visible in
the type of a record, and a record is computable even when its systems are not.
The records of translations are in `Googology/Goals/Basic.lean`, because they
talk about ordinals.
-/

namespace Googology

/-! ## Well-foundedness on the standard forms -/

/-- One step, restricted to the standard forms, is well founded. -/
def Rewrite.Std.WF {R : Rewrite} (S : R.Std) : Prop :=
  WellFounded (fun b a : {s // S.Standard s} => R.Rel b.1 a.1)

namespace Rewrite.Std

variable {R : Rewrite} (S : R.Std)

/-- Well-foundedness on all states gives it on the standard forms. -/
theorem wf_of_wf (h : R.WF) : S.WF :=
  InvImage.wf Subtype.val h

/-- A chain that starts at a standard state stays standard. -/
theorem chain_std (f : Nat → R.State) (h0 : S.Standard (f 0))
    (hf : ∀ n, ∃ k, f (n + 1) = R.step (f n) k) : ∀ n, S.Standard (f n)
  | 0 => h0
  | n + 1 => by
    obtain ⟨k, hk⟩ := hf n
    rw [hk]
    exact S.step_std _ k (chain_std f h0 hf n)

/-- Well-foundedness on the standard forms gives termination from them. -/
theorem terminates_of_wf (h : S.WF) : S.Terminates := by
  intro f h0 hf
  apply Classical.byContradiction
  intro hc
  have hall : ∀ n, ¬ R.halted (f n) := fun n hn => hc ⟨n, hn⟩
  exact not_descending h (fun n => ⟨f n, S.chain_std f h0 hf n⟩)
    (fun n => ⟨hall n, hf n⟩)

end Rewrite.Std

/-! ## Proved, refuted, not yet proved -/

/-- Where a record stands on one proposition, as the audit prints it. -/
inductive Status where
  | proved
  | refuted
  | todo
  deriving DecidableEq, Repr

/-- `"proved"`, `"refuted"`, `"open"`.  `open` is a Lean keyword, so the
constructor is `todo`. -/
def Status.token : Status → String
  | .proved => "proved"
  | .refuted => "refuted"
  | .todo => "open"

/-- Where a record stands on one proposition `P`: a proof of `P`, a proof of
`¬ P`, or nothing yet. -/
inductive Goal (P : Prop) : Type where
  | proved (h : P)
  | refuted (h : ¬ P)
  | todo

/-- The status of a goal. -/
def Goal.status {P : Prop} : Goal P → Status
  | .proved _ => .proved
  | .refuted _ => .refuted
  | .todo => .todo

/-! ## The first table: notations -/

/-- The expansion runs: `run` computes one step on codes, and `halt` decides
halting on codes.  `enc` must compile too: a noncomputable `enc` could hold
the whole future of a state.  `enc` need not be injective. -/
structure Runs (R : Rewrite) where
  /-- The codes. -/
  Code : Type
  /-- The code of a state. -/
  enc : R.State → Code
  /-- One step, on codes. -/
  run : Code → Nat → Code
  /-- Halting, on codes. -/
  halt : Code → Bool
  /-- `run` is the step. -/
  enc_step : ∀ s k, enc (R.step s k) = run (enc s) k
  /-- `halt` is halting. -/
  halt_iff : ∀ s, halt (enc s) = true ↔ R.halted s
  /-- What ties `run` to the source, e.g. the theorem `step = BM4.expand` on
  the entries, or the number of cases checked against the official program. -/
  source : String

/-- `R` is `Q` on part of its states: the same rule on more states. -/
structure Incl (R Q : Rewrite) where
  /-- The inclusion. -/
  map : R.State → Q.State
  /-- It is one to one. -/
  map_inj : ∀ a b, map a = map b → a = b
  /-- It commutes with the step, bracket for bracket. -/
  map_step : ∀ s k, map (R.step s k) = Q.step (map s) k
  /-- It halts where the source halts. -/
  map_halted : ∀ s, Q.halted (map s) ↔ R.halted s

/-- The goals of a notation: the columns "expansion defined" and
"well-foundedness" of the first table.  `Idx` indexes a family: `Nat` for
"every number of rows", `Unit` for one system. -/
structure NotationGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std) where
  /-- The row label in `README.md`. -/
  labelEn : String
  /-- The row label in `README-ja.md`. -/
  labelJa : String
  /-- Expansion defined: `some` is proved, `none` is open. -/
  expansion : Option ((i : Idx) → Runs (sys i))
  /-- Well-foundedness on the standard forms. -/
  wf : Goal (∀ i, (std i).WF)

/-- The goal "well-foundedness (non-standard)": the rule of `sys` on the
larger set of states `all`. -/
structure NonStdGoals {Idx : Type} (sys all : Idx → Rewrite) where
  /-- The row label in `README.md`. -/
  labelEn : String
  /-- The row label in `README-ja.md`. -/
  labelJa : String
  /-- `sys` is `all` on part of the states. -/
  incl : ∀ i, Nonempty (Incl (sys i) (all i))
  /-- Well-foundedness on all states. -/
  wf : Goal (∀ i, (all i).WF)

/-! ## The audit -/

/-- One line of the audit: one record and one column. -/
structure AuditLine where
  /-- `"notation"`, `"ordinal"` or `"between"`. -/
  table : String
  /-- The full Lean name of the record. -/
  record : String
  /-- The row label in `README.md`. -/
  rowEn : String
  /-- The row label in `README-ja.md`. -/
  rowJa : String
  /-- The target label in `README.md`; `""` unless `table = "between"`. -/
  targetEn : String
  /-- The target label in `README-ja.md`; `""` unless `table = "between"`. -/
  targetJa : String
  /-- A column id of section 7.4 of `spec.md`. -/
  column : String
  /-- The status. -/
  status : Status

/-- The line as the audit prints it: `GOAL` and eight fields, separated by
tabs. -/
def AuditLine.render (l : AuditLine) : String :=
  "\t".intercalate ["GOAL", l.table, l.record, l.rowEn, l.rowJa, l.targetEn, l.targetJa,
    l.column, l.status.token]

/-- The audit, in format `1`: `GOALS-BEGIN`, the lines, `GOALS-END`. -/
def AuditLine.printAll (ls : List AuditLine) : IO Unit := do
  IO.println "GOALS-BEGIN\t1"
  for l in ls do
    IO.println l.render
  IO.println s!"GOALS-END\t{ls.length}"

/-- The lines of a `NotationGoals` record: `expansion` and `wf`.  It is
`@[macro_inline]` so that the systems, which may be `noncomputable`, are
dropped before compiling. -/
@[macro_inline] def NotationGoals.lines {Idx : Type} {sys : Idx → Rewrite}
    {std : (i : Idx) → (sys i).Std} (g : NotationGoals sys std) (name : String) :
    List AuditLine :=
  [ ⟨"notation", name, g.labelEn, g.labelJa, "", "", "expansion",
      match g.expansion with
      | some _ => .proved
      | none => .todo⟩,
    ⟨"notation", name, g.labelEn, g.labelJa, "", "", "wf", g.wf.status⟩ ]

/-- The line of a `NonStdGoals` record: `wf-nonstd`. -/
@[macro_inline] def NonStdGoals.lines {Idx : Type} {sys all : Idx → Rewrite}
    (g : NonStdGoals sys all) (name : String) : List AuditLine :=
  [ ⟨"notation", name, g.labelEn, g.labelJa, "", "", "wf-nonstd", g.wf.status⟩ ]

end Googology
