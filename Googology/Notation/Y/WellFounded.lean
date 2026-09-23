import Googology.Notation.Y.Basic
import Googology.Rank
import Googology.Notation.Y.WellOrder.Por.WellOrdering
import Googology.Notation.Y.WellOrder.Equiv.Lower

/-!
# The Y sequence terminates

`WellOrder/` holds the port of two Lean 4.33.1 projects:

* [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) proves that the
  1-Y expansion `OneY.Numeric.expand` of Phyrion's formalization is well
  founded on every legal sequence (`Por.expansion_wellFounded`);
* [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv)
  proves that the transcription of the official program computes the same
  function (`Yukito.expand_eq`), given enough fuel.

This file puts the two together for `expand` of `Basic.lean`.

A sequence is *legal* (`ZeroY.Legal`) when its entries are positive and, if it
is not empty, its first entry is `1`. Every standard form is legal
(`YStd.legal`).

* `expand_eq_numeric`: on a legal sequence, `expand` is Phyrion's expansion.
* `ySys_wf`, `ySys_terminates`, `yStd_terminates`: the Y sequence is well
  founded and terminates on its standard forms; `yEval` is its rank.
* `yLegal_wf`, `yLegal_terminates`: the same on every legal sequence.
* `expand_terminates`: the same for `expand` on plain lists.
* `yStd_iff_generated`, `yStd_strictWellOrder`: the standard forms are
  Phyrion's generated sequences, and the lexicographic order well-orders them.
-/

namespace Googology.Notation.Y

/-! ## `expand` is Phyrion's expansion -/

/-- The empty sequence expands to itself. -/
theorem expand_nil (n : Nat) : expand [] n = [] := by
  have hM : calcMountain [] 2 = ([#[]] : List Rowj) := by
    simp [calcMountain, calcMountainFrom, row0, assignParents, mountainGo]
  have hD : dropEmptyTop ([#[]] : List Rowj) = [] := by
    rw [dropEmptyTop]
    simp [dropEmptyTop]
  show expandOut (expandJS n 2 1 (calcMountain [] 2)) = []
  rw [hM]
  unfold expandJS
  simp only [rowAt, List.getD_cons_zero, Array.size_empty, Nat.zero_sub, Nat.lt_irrefl,
    dite_false, Bool.not_false, if_true, List.set_cons_zero, Array.pop_empty, hD]
  rfl

private theorem foldl_max_eq (a : Nat) (s : List Nat) :
    s.foldl max a = max a (s.foldr max 0) := by
  induction s generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, List.foldr_cons, ih, Nat.max_assoc]

/-- `bound` is Phyrion's `sequenceBound`. -/
theorem bound_eq_sequenceBound (s : List Nat) : bound s = OneY.Numeric.sequenceBound s := by
  simp only [bound, OneY.Numeric.sequenceBound, ZeroY.maxValue, foldl_max_eq, Nat.zero_max]

/-- **On a legal sequence, `expand` is Phyrion's expansion.** -/
theorem expand_eq_numeric (s : List Nat) (hs : ZeroY.Legal s) (n : Nat) :
    expand s n = (OneY.Numeric.expand ⟨s, hs⟩ n).values := by
  by_cases hn : s = []
  · subst hn
    rw [expand_nil]
    exact (congrArg ZeroY.Expr.values (OneY.Numeric.expand_empty n)).symm
  · have hb := bound_eq_sequenceBound s
    exact Yukito.expand_eq s hs n (bound s + s.length) (bound s) (by omega) (by omega)
      (by omega) (List.length_pos_iff.mpr hn)

/-- Expansion keeps a sequence legal. -/
theorem legal_expand {s : List Nat} (hs : ZeroY.Legal s) (n : Nat) : ZeroY.Legal (expand s n) := by
  rw [expand_eq_numeric s hs n]
  exact (OneY.Numeric.expand ⟨s, hs⟩ n).legal

/-- Every standard form is legal. -/
theorem YStd.legal {s : List Nat} (h : YStd s) : ZeroY.Legal s := by
  induction h with
  | init h => exact (ZeroY.Expr.seed h).legal
  | step n _ ih => exact legal_expand ih n

/-! ## Every legal sequence -/

/-- **The Y sequence on every legal sequence**, standard or not. -/
def yLegal : Rewrite where
  State := {s : List Nat // ZeroY.Legal s}
  step := fun s n => ⟨expand s.1 n, legal_expand s.2 n⟩
  halted := fun s => s.1 = []

/-- A legal sequence as an expression of Phyrion's formalization. -/
def toExpr (s : yLegal.State) : ZeroY.Expr := ⟨s.1, s.2⟩

theorem toExpr_step (s : yLegal.State) (n : Nat) :
    toExpr (yLegal.step s n) = OneY.Numeric.expand (toExpr s) n :=
  ZeroY.Expr.ext (expand_eq_numeric s.1 s.2 n)

/-- One step of `yLegal` is one nontrivial step of Phyrion's expansion. -/
theorem step_of_rel {a b : yLegal.State} (h : yLegal.Rel b a) :
    OneY.Numeric.Step (toExpr b) (toExpr a) := by
  obtain ⟨ha, k, rfl⟩ := h
  exact OneY.Numeric.step_iff_nonempty.mpr ⟨ha, k, (toExpr_step a k).symm⟩

/-- **Well-foundedness on every legal sequence.** -/
theorem yLegal_wf : yLegal.WF :=
  Subrelation.wf (fun h => step_of_rel h) (InvImage.wf toExpr Por.expansion_wellFounded)

/-- **Termination on every legal sequence.** -/
theorem yLegal_terminates : yLegal.Terminates :=
  yLegal.terminates_of_wf yLegal_wf

/-! ## The standard forms -/

/-- The standard forms sit inside the legal sequences. -/
def stdSim : Sim ySys yLegal where
  map := fun s => ⟨s.1, s.2.legal⟩
  map_rel := by
    rintro a b ⟨ha, k, rfl⟩
    exact ⟨ha, k, rfl⟩

/-- **Well-foundedness of the Y sequence.** -/
theorem ySys_wf : ySys.WF := stdSim.wf yLegal_wf

/-- **The Y sequence terminates.** -/
theorem ySys_terminates : ySys.Terminates := ySys.terminates_of_wf ySys_wf

/-- **From a seed, every expansion sequence ends.** -/
theorem yStd_terminates : yStd.Terminates := yStd.of_terminates ySys_terminates

/-- The Y sequence carries an ordinal measure: the rank of one-step expansion. -/
noncomputable def yEval : Eval ySys (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval ySys_wf

/-- **`expand` on plain lists**: from a legal sequence, whatever the brackets,
the chain reaches the empty sequence. -/
theorem expand_terminates (f : Nat → List Nat) (h0 : ZeroY.Legal (f 0))
    (hf : ∀ n, ∃ k, f (n + 1) = expand (f n) k) : ∃ n, f n = [] := by
  have hL : ∀ n, ZeroY.Legal (f n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
        obtain ⟨k, hk⟩ := hf n
        rw [hk]
        exact legal_expand ih k
  exact yLegal_terminates (fun n => ⟨f n, hL n⟩)
    (fun n => (hf n).imp fun k hk => Subtype.ext hk)

/-! ## The order of the standard forms -/

/-- The standard forms are Phyrion's sequences generated from the seeds. -/
theorem yStd_iff_generated (s : List Nat) (hs : ZeroY.Legal s) :
    YStd s ↔ OneY.Numeric.Generated ⟨s, hs⟩ := by
  constructor
  · intro h
    induction h with
    | init h => exact ⟨h, .refl _⟩
    | step n hstd ih =>
        obtain ⟨m, hp⟩ := ih hstd.legal
        refine ⟨m, ?_⟩
        have he : (⟨expand _ n, hs⟩ : ZeroY.Expr) = OneY.Numeric.expand ⟨_, hstd.legal⟩ n :=
          ZeroY.Expr.ext (expand_eq_numeric _ hstd.legal n)
        rw [he]
        exact hp.tail n
  · rintro ⟨m, hp⟩
    suffices ∀ t : ZeroY.Expr, OneY.Numeric.ExpansionPath (ZeroY.Expr.seed m) t → YStd t.values from
      this _ hp
    intro t ht
    induction ht with
    | refl => exact YStd.init m
    | tail _ N ih =>
        rw [← expand_eq_numeric]
        exact YStd.step N ih

/-- The standard forms. -/
abbrev YStdSeq := {s : List Nat // YStd s}

/-- The lexicographic order, a proper prefix being smaller. -/
def YStdLt (s t : YStdSeq) : Prop := ZeroY.SeqLt s.1 t.1

/-- **The lexicographic order well-orders the standard forms.** -/
theorem yStd_strictWellOrder : Por.StrictWellOrder YStdSeq YStdLt := by
  have hW := OneY.Numeric.generated_strictWellOrder Por.expansion_wellFounded
  let g : YStdSeq → OneY.Numeric.GeneratedExpr := fun s =>
    ⟨⟨s.1, s.2.legal⟩, (yStd_iff_generated s.1 s.2.legal).mp s.2⟩
  exact
    { wellFounded := Subrelation.wf (fun h => h) (InvImage.wf g hW.wellFounded)
      transitive := fun h1 h2 => hW.transitive (first := g _) (second := g _) (third := g _) h1 h2
      trichotomy := fun a b => by
        rcases hW.trichotomy (g a) (g b) with he | hab | hba
        · exact Or.inl (Subtype.ext (congrArg (fun e => e.1.values) he))
        · exact Or.inr (Or.inl hab)
        · exact Or.inr (Or.inr hba) }

end Googology.Notation.Y
