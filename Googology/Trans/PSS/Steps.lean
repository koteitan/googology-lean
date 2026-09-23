import Googology.Trans.PSS.Expansion
import Googology.Notation.ExBuchholz.Cofinal
import Googology.Notation.ExBuchholz.RankVal

/-!
# Pair sequences → extended Buchholz's ψ: one step goes to finitely many steps

`Expansion.lean` shows that the translation `pairOrdTerm` does not send one
expansion step of the pair sequences to one step `X ↦ X[idx X n]` of extended
Buchholz's ψ.  This file proves the weaker statement that does hold: one step
goes to **one or more** steps, and in fact the translation is an isomorphism of
the reachability relations.

Write `b ⊲⁺ a` for "`b` is reached from `a` by one or more steps"
(`Relation.TransGen R.Rel b a`).  The results:

* `transGen_iff_rank_lt`: in a well-founded system whose rank is injective,
  `b ⊲⁺ a ↔ rank b < rank a`.
* `pairL_transGen_iff`: for pair sequences, `b ⊲⁺ a ↔ b <ₚ a` (lexicographic).
* `exbOT_transGen_iff`: for countable standard forms, `B ⊲⁺ A ↔ B < A`.
* `pairToExbOT_transGen_iff`: `pairToExbOT b ⊲⁺ pairToExbOT a ↔ b ⊲⁺ a`.
* `pairToExbOT_transGen_of_rel`: **one step `a → b` of the pair sequences goes
  to finitely many (at least one) steps `pairOrdTerm a → ⋯ → pairOrdTerm b`.**
* `pairOrdTerm_gen1_two_steps`: for the counterexample of `Expansion.lean`,
  `(0,0)(1,1)[0] = (0,0)` goes to `ψ_0(Ω_1) → ψ_0(1) → 1`, two steps, with the
  indices `0` and `1`.

The number of steps is not bounded by a constant: a numerical search finds that
`(0,0)(1,1)⋯(n,n)(n+1,n)[2]` needs `n + 1` steps with the least index at each
step (`[2, 0, …, 0, 1]`).  That is a measurement, not a theorem of this file.
-/

namespace Googology.Trans.PSS

open Googology.Trans.BMS (pairL PairState pairL_wf pairStd)
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Relation

/-! ## Reachability and rank -/

section Generic

variable {α : Type} {r : α → α → Prop} [IsWellFounded α r]

/-- The rank goes down along a chain of steps. -/
theorem rank_lt_of_transGen {a b : α} (h : TransGen r b a) :
    IsWellFounded.rank r b < IsWellFounded.rank r a := by
  induction h with
  | single h => exact IsWellFounded.rank_lt_of_rel h
  | tail _ h ih => exact _root_.lt_trans ih (IsWellFounded.rank_lt_of_rel h)

/-- **In a well-founded system with injective rank, `b` is reached from `a`
exactly when its rank is smaller.** -/
theorem transGen_of_rank_lt (hinj : Function.Injective (IsWellFounded.rank r)) :
    ∀ a b : α, IsWellFounded.rank r b < IsWellFounded.rank r a → TransGen r b a := by
  intro a
  induction a using WellFounded.induction (IsWellFounded.wf (r := r)) with
  | _ a ih =>
    intro b hb
    rw [IsWellFounded.rank_eq (r := r) a] at hb
    obtain ⟨⟨s, hs⟩, h⟩ := (Ordinal.lt_iSup_iff).mp hb
    rcases (Order.lt_succ_iff.mp h).lt_or_eq with h1 | h1
    · exact TransGen.tail (ih s hs b h1) hs
    · rw [hinj h1]
      exact TransGen.single hs

theorem transGen_iff_rank_lt (hinj : Function.Injective (IsWellFounded.rank r)) (a b : α) :
    TransGen r b a ↔ IsWellFounded.rank r b < IsWellFounded.rank r a :=
  ⟨rank_lt_of_transGen, transGen_of_rank_lt hinj a b⟩

end Generic

/-! ## Pair sequences -/

theorem rank_pairL_injective : Function.Injective (IsWellFounded.rank pairL.Rel) := by
  intro a b h
  rw [rank_pairL_eq, rank_pairL_eq] at h
  exact pairOrd_injective h

/-- **A pair sequence `b` is reached from `a` by one or more expansions exactly
when `b <ₚ a`.** -/
theorem pairL_transGen_iff (a b : PairState) : TransGen pairL.Rel b a ↔ b.1 <ₚ a.1 := by
  rw [transGen_iff_rank_lt rank_pairL_injective, rank_pairL_eq, rank_pairL_eq]
  exact (ltPS_iff_pairOrd_lt b a).symm

/-! ## Countable standard forms of extended Buchholz's ψ -/

theorem rank_exbOT_injective : Function.Injective (IsWellFounded.rank exbOT.Rel) := by
  intro A B h
  rw [rank_exbOT_eq_val, rank_exbOT_eq_val] at h
  exact Subtype.ext (val_inj_of_OT A.2.1 B.2.1 h)

/-- **A countable standard form `B` is reached from `A` by one or more steps
`X ↦ X[idx X n]` exactly when `B < A`.** -/
theorem exbOT_transGen_iff (A B : exbOT.State) : TransGen exbOT.Rel B A ↔ B.1 < A.1 := by
  rw [transGen_iff_rank_lt rank_exbOT_injective, rank_exbOT_eq_val, rank_exbOT_eq_val]
  exact (lt_iff_val_lt B.2.1 A.2.1).symm

/-! ## The translation -/

theorem pairOrdTerm_lt_psiOmegaOmega (l : PairState) : pairOrdTerm l.1 < psiOmegaOmega := by
  have hm : pairOrdEval.val l ∈ Set.Iio (val psiOmegaOmega) :=
    range_pairOrd ▸ Set.mem_range_self l
  have hv : val (pairOrdTerm l.1) < val psiOmegaOmega := by
    rw [val_pairOrdTerm l.2]
    exact hm
  exact (lt_iff_val_lt (OT_pairOrdTerm l.2) (by decide)).mpr hv

/-- A pair sequence as a countable standard form: `pairOrdTerm`. -/
def pairToExbOT (l : PairState) : exbOT.State :=
  ⟨pairOrdTerm l.1, OT_pairOrdTerm l.2, lt_tW_of_lt_psiOmegaOmega (pairOrdTerm_lt_psiOmegaOmega l)⟩

theorem pairToExbOT_lt_iff (a b : PairState) :
    (pairToExbOT b).1 < (pairToExbOT a).1 ↔ b.1 <ₚ a.1 := by
  rw [ltPS_iff_pairOrd_lt]
  show pairOrdTerm b.1 < pairOrdTerm a.1 ↔ pairOrdL b.1 < pairOrdL a.1
  rw [← val_pairOrdTerm b.2, ← val_pairOrdTerm a.2]
  exact lt_iff_val_lt (OT_pairOrdTerm b.2) (OT_pairOrdTerm a.2)

/-- **The translation is an isomorphism of reachability**: `pairOrdTerm b` is
reached from `pairOrdTerm a` by one or more steps of extended Buchholz's ψ
exactly when `b` is reached from `a` by one or more expansions. -/
theorem pairToExbOT_transGen_iff (a b : PairState) :
    TransGen exbOT.Rel (pairToExbOT b) (pairToExbOT a) ↔ TransGen pairL.Rel b a := by
  rw [exbOT_transGen_iff, pairL_transGen_iff, pairToExbOT_lt_iff]

/-- **One expansion step goes to finitely many steps**: if `b = a[k]`, then
`pairOrdTerm b` is reached from `pairOrdTerm a` by one or more steps
`X ↦ X[idx X n]`, with suitable `n` at each step. -/
theorem pairToExbOT_transGen_of_rel {a b : PairState} (h : pairL.Rel b a) :
    TransGen exbOT.Rel (pairToExbOT b) (pairToExbOT a) :=
  (pairToExbOT_transGen_iff a b).mpr (TransGen.single h)

/-- The same on terms: a chain `pairOrdTerm a = X₀, X₁, …, X_m = pairOrdTerm b`
with `m ≥ 1`, `X_i ≠ 0` and `X_{i+1} = X_i[idx X_i n_i]`. -/
theorem pairOrdTerm_transGen_of_rel {a b : PairState} (h : pairL.Rel b a) :
    TransGen (fun Y X : Term => X ≠ nil ∧ ∃ n, Y = fs X (idx X n))
      (pairOrdTerm b.1) (pairOrdTerm a.1) :=
  TransGen.lift Subtype.val (fun _ _ ⟨hne, n, hn⟩ => ⟨hne, n, congrArg Subtype.val hn⟩)
    (pairToExbOT_transGen_of_rel h)

/-! ## The counterexample, in two steps -/

/-- `ψ_0(1) = ω` as a term. -/
abbrev tOmegaNat : Term := psi nil t1

private theorem dom_tEps0 : dom tEps0 = tw := by decide

private theorem fs_t1_nil : fs t1 nil = nil := by
  rw [fs]; simp only [dom_nil, if_true]

theorem fs_tEps0_idx0 : fs tEps0 (idx tEps0 0) = tOmegaNat := by
  have hi : idx tEps0 0 = nil := by
    rw [idx, dom_tEps0]; rfl
  rw [hi, fs]
  have h1 : ¬ dom tOmega1 = nil := by decide
  have h2 : ¬ dom tOmega1 = t1 := by decide
  have h3 : ¬ dom tOmega1 = tw := by decide
  have h4 : ¬ dom tOmega1 < cons nil tOmega1 nil := by decide
  have h5 : subOf (dom tOmega1) = t1 := by decide
  simp only [h1, h2, h3, h4, if_false, fs_tOmega1, h5, fs_t1_nil]
  simp

theorem fs_tOmegaNat_idx1 : fs tOmegaNat (idx tOmegaNat 1) = t1 := by
  have hd : dom t1 = t1 := by decide
  have hi : idx tOmegaNat 1 = numeral 1 := by
    rw [idx, dom_psi_of_one hd]; rfl
  rw [hi, fs_psi_of_one_numeral hd, fs_t1_nil]
  rfl

/-- **`(0,0)(1,1)[0] = (0,0)` goes to two steps**: `ψ_0(Ω_1) →[0] ψ_0(1) →[1] 1`. -/
theorem pairOrdTerm_gen1_two_steps :
    pairOrdTerm (pairL.step (pairStd.gen 1) 0).1
      = fs (fs (pairOrdTerm (pairStd.gen 1).1) (idx (pairOrdTerm (pairStd.gen 1).1) 0))
          (idx (fs (pairOrdTerm (pairStd.gen 1).1) (idx (pairOrdTerm (pairStd.gen 1).1) 0)) 1) := by
  rw [pairOrdTerm_gen1_step0, pairStd_gen1, pairOrdTerm_gen1, fs_tEps0_idx0, fs_tOmegaNat_idx1]

end Googology.Trans.PSS
