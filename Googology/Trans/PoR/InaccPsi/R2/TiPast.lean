import Googology.Trans.PoR.InaccPsi.R2.TiDat
import Googology.Trans.PoR.InaccPsi.R2.LdFix

/-!
# `B_Γ = ψ_{Ω₂}(Ω₂)`: the plateau of `ψ_{Ω₂}` on `[B_Γ, Ω₂]`, the move and the data of `B_Γ`

`ψ_{Ω₂}(α) = S.psi α Ω₂`, `B_Γ = Tf.tfBG` (the least fixed point of `Γ` above `Ω₁`), `F = Ld.ldF S = ψ_{Ω₂}(Ω₂)`,
`B_n = Bc.bcB S n`, `tiDat` the data read on normal forms (`R2.TiDat`).  Below `B_Γ` the collapse is `ψ_{Ω₂}(α) =
Γ_{Ω₁+1+α}` (`Tf.tf_psi`); from `B_Γ` on it stays at `B_Γ` until the argument reaches `Ω₂`, so the atoms past `B_Γ` are
`ψ_{Ω₂}(a)` with `a > Ω₂` (`B_Γ` itself is `ψ_{Ω₂}(Ω₂)`):

* `ti_psi_le_BG` (**`ψ_{Ω₂}(α) ≤ B_Γ` for every `α ≤ Ω₂`**: every member `< Ω₂` of `Cl(α, B_Γ)` is `< B_Γ`, by induction
  on the hull; a collapse `ψ_{Ω₂}(e)` there has `e < α ≤ Ω₂`, so `e < B_Γ` and `ψ_{Ω₂}(e) = Γ_{Ω₁+1+e} < B_Γ`);
* `ti_F_eq` (**`ψ_{Ω₂}(Ω₂) = B_Γ`**), `ti_psi_plateau` (**`ψ_{Ω₂}(α) = B_Γ` for `B_Γ ≤ α ≤ Ω₂`**);
* `tiB_BG` (**`B_n(B_Γ) = B_Γ`**, `B_Γ ∈ MvD`), `tiDat_Om2` (`tiDat Ω₂ = 0`), `tiDat_BG` (**`tiDat B_Γ = 0`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tf

variable {S : InaccSeq.{0}}

/-- **`ψ_{Ω₂}(α) ≤ B_Γ` for every `α ≤ Ω₂`.** -/
theorem ti_psi_le_BG (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα : α ≤ Om (1 + 1)) :
    S.psi α (Om (1 + 1)) ≤ tfBG := by
  refine psi_le_of_good (Mx.mxOm2_mem _ _) ?_
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => tfBG_SC.1
  | inacc n =>
    intro h
    exact absurd (h.trans (Mx.mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro h
    exact absurd (h.trans Mx.mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h
    exact tfBG_SC.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact tfBG_SC.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 h
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact tfBG_SC.1
    · rw [h1, ← Rj.rj_Om1]; exact tfBG_gt
  | @coll π e hπ _ _ _ ihe =>
    intro h
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (Mx.mxOm2_mem _ _) (Mx.mxOm2_lt_I n)
      exact absurd (h2.trans h) (lt_irrefl _)
    rcases eq_or_ne s 0 with rfl | hs0
    · have := psi_lt (InR_Om_succ (S := S) 0) e.1
      rw [zero_add] at this ⊢
      exact this.trans (by rw [← Rj.rj_Om1]; exact tfBG_gt)
    rcases eq_or_ne s 1 with rfl | hs1
    · have heB : e.1 < tfBG := ihe (e.2.trans_le hα)
      exact (tf_psi_lt_iff S).2 heB
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans h) (lt_irrefl _)

/-- **`ψ_{Ω₂}(Ω₂) = B_Γ`.** -/
theorem ti_F_eq (S : InaccSeq.{0}) : Ld.ldF S = tfBG := by
  refine le_antisymm (ti_psi_le_BG S le_rfl) ?_
  unfold Ld.ldF
  conv_lhs => rw [← tf_psi_BG S]
  exact (psi_mono (S := S) (InR_Om_succ 1) tfBG_lt_Om2.le).1

/-- **The plateau**: `ψ_{Ω₂}(α) = B_Γ` for `B_Γ ≤ α ≤ Ω₂`. -/
theorem ti_psi_plateau (S : InaccSeq.{0}) {α : Ordinal.{0}} (h1 : tfBG ≤ α) (h2 : α ≤ Om (1 + 1)) :
    S.psi α (Om (1 + 1)) = tfBG := by
  refine le_antisymm (ti_psi_le_BG S h2) ?_
  conv_lhs => rw [← tf_psi_BG S]
  exact (psi_mono (S := S) (InR_Om_succ 1) h1).1

/-- **`B_n(B_Γ) = B_Γ`**, and `B_Γ` is in the normal-form domain of `B_n`. -/
theorem tiB_BG {n : ℕ} : Mv.MvD S tfBG ∧ Bc.bcB S n tfBG = tfBG := by
  rw [← ti_F_eq S]; exact Ld.ldB_F

/-- `tiDat Ω₂ = 0`. -/
theorem tiDat_Om2 : tiDat S (Om (1 + 1)) = 0 := by
  have hD := Ld.ldTwoT_D (S := S)
  have e : Bc.bcNf S (Om (1 + 1)) = Ld.ldTwoT := by
    rw [← Ld.ldTwoT_val (S := S)]; exact Bc.bcNf_val S hD.1
  have hbig : ¬ val S Ld.ldTwoT < Om 1 := by
    rw [Ld.ldTwoT_val]; exact not_lt.2 (Om_le_Om.2 (le_add_self))
  unfold tiDat
  rw [e]
  exact tiDatT_om hbig

/-- **`tiDat B_Γ = 0`** (`B_Γ = ψ_{Ω₂}(Ω₂)`). -/
theorem tiDat_BG : tiDat S tfBG = 0 := by
  rw [← ti_F_eq S]
  unfold Ld.ldF
  rw [tiDat_psi2 (Set.mem_iUnion.2 ⟨0, Mx.mxOm2_mem _ _⟩) (Mx.mxOm2_mem _ _), tiDat_Om2]

end Googology.Trans.PoR.InaccPsi.R2.Ti
