import Googology.Trans.PoR.InaccPsi.R2.QcFx
import Googology.Trans.PoR.InaccPsi.R2.VaCuS

/-!
# QcGate: A CODE BELOW `B₂` OVER A STRONGLY CRITICAL `Z ≤ Ω₁` HAS ITS GATE BELOW `Z`

As `Va.vs_gate` for `Qc.qcG` and the codes of `Uc.UcCl`: below `X` it is `Va.vs_gate`; from `X` on by the derivation of
the code, the sums, powers and Veblen values through `Qc.QcGx`, and an atom `H_γ(y)`: `Γ(y)` (`γ = 0`) has the gate
of `y`; a fixed point `H_γ(y)` of `Γ` (`γ ≠ 0`) has the gates of the components of `γ` and of the parts `p`,
`y − (p+1)` of its index, `p` the largest fixed point of `H_γ` below `y`, a code by `Qc.qc_fpH_cl`.

* `qc_H_fixG` (**`H_γ(y)` is a fixed point of `Γ` for `γ ≠ 0`**), `qc_gate` (**a code has its gate below `Z`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **`H_γ(y)` is a fixed point of `Γ` for `γ ≠ 0`**: `Γ(H_γ(y)) = H_γ(y)` and the index of the atom is itself. -/
theorem qc_H_fixG {γ y : Ordinal.{0}} (hγ : γ ≠ 0) : gcG (ucH γ y) = ucH γ y ∧ yhJ (ucH γ y) = ucH γ y := by
  have h0 : ucH 0 (ucH γ y) = ucH γ y :=
    ucG_fix_lower (pos_iff_ne_zero.2 hγ) ⟨y, rfl⟩ (by rw [ucC_small uc_SC_Om2.1]; exact (ucH_SC γ y).1)
  rw [qc_H0] at h0
  refine ⟨h0, ?_⟩
  conv_lhs => rw [← h0]
  exact yhJ_gcG _

/-- **A code below `B₂` over a strongly critical `Z ≤ Ω₁` has its gate below `Z`.** -/
theorem qc_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ c, UcCl Z c → c < ucB → qcG c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  have hlow : ∀ c, UcCl Z c → c < tlX → qcG c < Z := fun c hc hcX => by
    rw [qcG_low hcX]; exact vs_gate hZ hZ1 c (uc_cl_lt_X hc hcX) hcX
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  revert IH
  induction hc with
  | @small x h => exact fun _ _ => hlow _ (UcCl.small h) ((h.trans_le hZ1).trans tlX_gt)
  | om => exact fun _ _ => hlow _ UcCl.om tlX_gt
  | @add x y hx hy ihx ihy =>
    intro IH hB
    rcases lt_or_ge (x + y) tlX with hlt | hge
    · exact hlow _ (UcCl.add hx hy) hlt
    exact qc_add hZa hωZ x y hB
      (ihx (fun c' hc' => IH c' (hc'.trans_le le_self_add)) (lt_of_le_of_lt le_self_add hB))
      (ihy (fun c' hc' => IH c' (hc'.trans_le le_add_self)) (lt_of_le_of_lt le_add_self hB))
  | @phi x y hx hy ihx ihy =>
    intro IH hB
    rcases lt_or_ge (veblen x y) tlX with hlt | hge
    · exact hlow _ (UcCl.phi hx hy) hlt
    have hgy := ihy (fun c' hc' => IH c' (hc'.trans_le (right_le_veblen x y)))
      (lt_of_le_of_lt (right_le_veblen x y) hB)
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at hB ⊢
      exact qc_opow_gate hZw hωZ y hB hgy
    · exact qc_phi_gate hωZ hx0 (qc_G0_lt_X.le.trans hge) hB
        (ihx (fun c' hc' => IH c' (hc'.trans_le (left_le_veblen x y))) (lt_of_le_of_lt (left_le_veblen x y) hB)) hgy
  | @tl x h => exact fun _ _ => hlow _ (UcCl.tl h) (uc_tl_lt_X hZ1 h)
  | @hatom γ y hγ hcomp hy hX ihc ihy =>
    intro IH hB
    have hyc : y ≤ ucH γ y := ucH_le_self γ y
    have hgy : qcG y < Z := ihy (fun c' hc' => IH c' (hc'.trans_le hyc)) (hyc.trans_lt hB)
    rcases hyc.lt_or_eq with hyc' | hyc'
    swap
    · rw [← hyc']; exact hgy
    obtain ⟨hl, hi⟩ := ucLev_H hγ hyc'
    rcases eq_or_ne γ 0 with rfl | hγ0
    · -- `Γ(y)`, `y < Γ(y)`: the gate of `y`
      rw [qc_H0] at hB hyc' ⊢
      rw [qcG_atom' hyc' hB]
      exact (qcQ_le y).trans_lt hgy
    · -- a fixed point `H_γ(y)` of `Γ`
      obtain ⟨-, hJ⟩ := qc_H_fixG (y := y) hγ0
      have hA : YhAt (ucH γ y) := ⟨ucH_SC γ y, ucH_gt γ y⟩
      have hi' : ¬ yhJ (ucH γ y) < ucH γ y := by rw [hJ]; exact lt_irrefl _
      have hN : ucI (ucLev (ucH γ y)) (ucH γ y) < ucH γ y := by rw [hl, hi]; exact hyc'
      have hE : InE (ucH γ y) := Low.opow_eq_self_of_SC (ucH_SC γ y)
      rw [qcG_base hE hX hB, qcQE_fix hX hB hA hi' hN, hl, hi]
      refine max_lt ((ucFold_lt_iff _ hZ.1 γ).2 fun d hd => ?_) ?_
      · split_ifs with hdc
        · have hdB : d < ucB := hdc.trans hB
          exact (qcQ_le d).trans_lt (ihc d hd (fun c' hc' => IH c' (hc'.trans hdc)) hdB)
        · exact hZ.1
      · have hne : ucH γ y ≠ y := ne_of_gt hyc'
        unfold qcKQ
        split_ifs with hF
        · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
          have hpC : UcCl Z (qcFpH γ y) := qc_fpH_cl hZ1 hy hne hF
          have hp1 : UcCl Z (qcFpH γ y + 1) := UcCl.add hpC (UcCl.one hZ.1)
          have hoC : UcCl Z (y - (qcFpH γ y + 1)) := (ucDec hZ hZ1 y hy).1 _ hp1 (Order.add_one_le_of_lt hpy)
          have hoy : y - (qcFpH γ y + 1) < ucH γ y := (Ordinal.sub_le_self _ _).trans_lt hyc'
          refine max_lt ((qcQ_le _).trans_lt (IH _ (hpy.trans hyc') hpC ((hpy.trans hyc').trans hB)))
            ((qcQ_le _).trans_lt (IH _ hoy hoC (hoy.trans hB)))
        · exact (qcQ_le y).trans_lt hgy

end Googology.Trans.PoR.InaccPsi.R2.Qc
