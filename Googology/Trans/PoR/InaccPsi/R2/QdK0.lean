import Googology.Trans.PoR.InaccPsi.R2.QdCl
import Googology.Trans.PoR.InaccPsi.R2.QtK

/-!
# QdK0: BELOW `B₃` THE CODES `QdCl Z` ARE THE MEMBERS OF `K⁽⁰⁾_Z`

`K⁽⁰⁾_q = Ul.UlK S 0 q`, `B₃ = Qd.qdB ≤ θ`.  Below `B₂` the codes of `Uc.UcCl` are `K⁽⁰⁾` (`Uo.uo_cl_iffK`).  A Veblen
level `γ < Γ_{Ω₂+1}` is in `K⁽⁰⁾_q` iff its leaves are (`K⁽⁰⁾` is closed under `+`, `ω^·`, `φ`, `Ω_·`, and splits
along them, `Qt.ulK_veb_parts`, `Ul.ulK_dec`, `Ul.ulK_mod`), and an atom `Hᵛ_γ(y) = Hˡ_γ(y)` is in `K⁽⁰⁾_q` iff `γ`
and `y` are (`Vd.vd_atom_K`).  So, for a strongly critical `Z ≤ Ω₁`:

* `qd_K0_of_comps`, `qd_comps_K0` (**a Veblen level is in `K⁽⁰⁾_q` iff its leaves are**);
* `qd_cl_K0`, `qd_K0_cl`, `qd_cl_iffK` (**`QdCl Z x ↔ x ∈ K⁽⁰⁾_Z` for `x < B₃`**), `qd_cl_qt` (**the codes of `qtU`
  below `B₃` are the codes `QdCl Z`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Vd Googology.Trans.PoR.InaccPsi.R2.Qt Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **A Veblen level whose leaves are in `K⁽⁰⁾_q` is in `K⁽⁰⁾_q`.** -/
theorem qd_K0_of_comps {q : Ordinal.{0}} : ∀ γ, γ < qdG2 → (∀ d ∈ qdComps γ, UlK S 0 q d) → UlK S 0 q γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ h
  rcases lt_trichotomy γ OmTwo with h2 | rfl | h2
  · exact h γ (by rw [qdComps_small h2]; exact mem_singleton γ)
  · rw [uc_Om2_eq]; exact UlK.om (UlK.add UlK.one UlK.one)
  · have hz : OmTwo < γ ∧ γ < qdG2 := ⟨h2, hγ⟩
    by_cases hE : ω ^ γ = γ
    · have e : qdComps γ = qdComps (invVeblen₁ γ) ∪ qdComps (invVeblen₂ γ) := by
        rw [qdComps, dif_pos hz, dif_pos hE]
      rw [e] at h
      have h1 := IH _ (qd_inv1_lt hz.1 hz.2) ((qd_inv1_lt hz.1 hz.2).trans hγ) fun d hd => h d (Or.inl hd)
      have h2' := IH _ (Ss.ss_inv2_lt hE) ((Ss.ss_inv2_lt hE).trans hγ) fun d hd => h d (Or.inr hd)
      rw [← qd_veb_inv hE]; exact UlK.phi h1 h2'
    · have e : qdComps γ = qdComps (log ω γ) ∪ qdComps (γ % ω ^ log ω γ) := by
        rw [qdComps, dif_pos hz, dif_neg hE]
      rw [e] at h
      obtain ⟨hdec, -, -, hn, -, hl⟩ := qd_cnf_parts h2 hE
      have hγ0 : γ ≠ 0 := (qd_Om2_pos.trans h2).ne'
      have hlK := IH _ hl (hl.trans hγ) fun d hd => h d (Or.inl hd)
      have hrK := IH _ (Rj.rj_mod_lt hγ0) ((Rj.rj_mod_lt hγ0).trans hγ) fun d hd => h d (Or.inr hd)
      obtain ⟨n, hn'⟩ := lt_omega0.1 hn
      rw [← hdec, hn']
      exact UlK.add (UlK.mul_nat hlK.opow n) hrK

/-- **The leaves of a Veblen level in `K⁽⁰⁾_q` are in `K⁽⁰⁾_q`** (`q` strongly critical). -/
theorem qd_comps_K0 {q : Ordinal.{0}} (hq : SC q) :
    ∀ γ, γ < qdG2 → UlK S 0 q γ → ∀ d ∈ qdComps γ, UlK S 0 q d := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ h d hd
  rcases lt_trichotomy γ OmTwo with h2 | rfl | h2
  · rw [qdComps_small h2] at hd; rw [mem_singleton_iff.1 hd]; exact h
  · have e : qdComps OmTwo = ∅ := by
      rw [qdComps, dif_neg (fun h => lt_irrefl _ h.1), if_neg (lt_irrefl _)]
    rw [e] at hd; exact absurd hd (Set.notMem_empty _)
  · have hz : OmTwo < γ ∧ γ < qdG2 := ⟨h2, hγ⟩
    by_cases hE : ω ^ γ = γ
    · have e : qdComps γ = qdComps (invVeblen₁ γ) ∪ qdComps (invVeblen₂ γ) := by
        rw [qdComps, dif_pos hz, dif_pos hE]
      rw [e] at hd
      have hv : veblen (invVeblen₁ γ) (invVeblen₂ γ) = γ := qd_veb_inv hE
      have hparts := ulK_veb_parts (S := S) (s := 0) (q := q) (by rw [hv]; exact h)
        (by rw [hv]; exact qd_inv1_lt hz.1 hz.2) (by rw [hv]; exact Ss.ss_inv2_lt hE)
      rcases hd with hd | hd
      · exact IH _ (qd_inv1_lt hz.1 hz.2) ((qd_inv1_lt hz.1 hz.2).trans hγ) hparts.1 d hd
      · exact IH _ (Ss.ss_inv2_lt hE) ((Ss.ss_inv2_lt hE).trans hγ) hparts.2 d hd
    · have e : qdComps γ = qdComps (log ω γ) ∪ qdComps (γ % ω ^ log ω γ) := by
        rw [qdComps, dif_pos hz, dif_neg hE]
      rw [e] at hd
      obtain ⟨-, -, -, -, -, hl⟩ := qd_cnf_parts h2 hE
      have hγ0 : γ ≠ 0 := (qd_Om2_pos.trans h2).ne'
      rcases hd with hd | hd
      · exact IH _ hl (hl.trans hγ) (ulK_dec hq γ h).2 d hd
      · exact IH _ (Rj.rj_mod_lt hγ0) ((Rj.rj_mod_lt hγ0).trans hγ) (ulK_mod hq γ h _) d hd

variable {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1)
include hZ hZ1

/-- **A code `QdCl Z x` below `B₃` is in `K⁽⁰⁾_Z`.** -/
theorem qd_cl_K0 : ∀ x, QdCl Z x → x < qdB → UlK S 0 Z x := by
  intro x hx
  induction hx with
  | uc h => exact fun _ => Uo.uo_ucK hZ hZ1 _ h
  | @add x y _ _ ihx ihy =>
    exact fun h => UlK.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => UlK.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @hatom γ y hγ _ _ _ ihc ihy =>
    intro h
    have hyK := ihy ((qdH_le_self γ y).trans_lt h)
    have hcK : ∀ d ∈ qdComps γ, UlK S 0 Z d := fun d hd =>
      ihc d hd (((qdFold_lt_iff (lt_of_le_of_lt zero_le (qdH_D_lt γ y)) γ).1 (qdH_D_lt γ y) d hd).trans h)
    rcases eq_or_lt_of_le (qdH_le_self γ y) with hfix | hlt
    · rw [← hfix]; exact hyK
    · have hγK := qd_K0_of_comps γ hγ hcK
      have hW : ulH S 1 γ y < Om (1 + 1) := by
        rw [← qdH_eq_ul S hγ]; exact h.trans_le ((qd_B3_le_th (S := S)).trans (Ui.ui_th_lt_Om2 (S := S)).le)
      rw [qdH_eq_ul S hγ] at hlt ⊢
      exact (vd_atom_K (hγ.trans (qd_G2_lt_Om3 S)) hlt hW hZ (by rw [← Rj.rj_Om1]; exact hZ1)).2 ⟨hγK, hyK⟩

/-- **A member of `K⁽⁰⁾_Z` below `B₃` is a code `QdCl Z`.** -/
theorem qd_K0_cl : ∀ x, UlK S 0 Z x → x < qdB → QdCl Z x := by
  have hθ2 : ConjT.th S < Om (1 + 1) := Ui.ui_th_lt_Om2
  have hB3θ : qdB ≤ ConjT.th S := qd_B3_le_th
  have hZ1' : Z ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hZ1
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxB
  rcases lt_or_ge x ucB with hxB2 | hxB2
  · exact QdCl.uc ((Uo.uo_cl_iffK hZ hZ1 hxB2).2 hx)
  have h1 : Om1 < x := ucB_gt.trans_le hxB2
  have h1' : Om 1 < x := by rw [← Rj.rj_Om1]; exact h1
  have hx2 : x < Om (1 + 1) := hxB.trans_le (hB3θ.trans hθ2.le)
  have h0 : x ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  by_cases hP : IsPrincipal (· + ·) x
  · rcases ulK_prin_cases hx (hZ1'.trans h1'.le) hP h0 with
      ⟨n, rfl⟩ | rfl | ⟨p, r, hp, hr, hpx, hrx, rfl⟩ | ⟨p, -, -, rfl⟩ | ⟨π, e, hπ, -, rfl⟩
    · exact absurd hx2 (not_lt.2 (mxOm2_lt_I n).le)
    · exact absurd hx2 (not_lt.2 mxOm2_lt_Iw.le)
    · exact QdCl.phi (IH p hpx hp (hpx.trans hxB)) (IH r hrx hr (hrx.trans hxB))
    · have hp1 : p ≤ 1 := le_of_Om_lt_Om_succ hx2
      exact absurd (Om_lt_Om.1 h1') (not_lt.2 hp1)
    · have hSC : SC (S.psi e π) := SC_psi hπ e
      have hne := qd_nf_of_lt hSC h1 hxB
      obtain ⟨hlG, hlF, -, -, -⟩ := qdLev_spec hSC h1 hne
      obtain ⟨hH, hy⟩ := qd_nf hSC h1 hne
      set z := S.psi e π with hz
      have hxu : ulH S 1 (qdLev z) (qdI (qdLev z) z) = z := by rw [← qdH_eq_ul S hlG]; exact hH
      have hK := (vd_atom_K (hlG.trans (qd_G2_lt_Om3 S)) (by rw [hxu]; exact hy) (by rw [hxu]; exact hx2)
        hZ hZ1').1 (by rw [hxu]; exact hx)
      have hcK := qd_comps_K0 hZ _ hlG hK.1
      have hcl : ∀ d ∈ qdComps (qdLev z), QdCl Z d := fun d hd => by
        have hdz : d < z := (qdFold_lt_iff hSC.1 _).1 hlF d hd
        exact IH d hdz (hcK d hd) (hdz.trans hxB)
      rw [← hH]
      exact QdCl.hatom hlG hcl (IH _ hy hK.2 (hy.trans hxB)) (by rw [hH]; exact hxB2)
  · obtain ⟨hl, ht⟩ := ulK_lead_tail hZ hx h0
    have hlx : lead x < x := lt_of_le_of_ne (lead_le h0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htx : tail x < x := tail_lt h0
    rw [← lead_add_tail h0]
    exact QdCl.add (IH _ hlx hl (hlx.trans hxB)) (IH _ htx ht (htx.trans hxB))

/-- **Below `B₃` the codes `QdCl Z` are the members of `K⁽⁰⁾_Z`.** -/
theorem qd_cl_iffK {x : Ordinal.{0}} (hx : x < qdB) : QdCl Z x ↔ UlK S 0 Z x :=
  ⟨fun h => qd_cl_K0 hZ hZ1 x h hx, fun h => qd_K0_cl hZ hZ1 x h hx⟩

/-- **Below `B₃` the codes of `qtU` are the codes `QdCl Z`.** -/
theorem qd_cl_qt {x : Ordinal.{0}} (hx : x < qdB) : GxCl Z (qtAt S Z) x ↔ QdCl Z x := by
  have hZ1' : Z ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hZ1
  rw [qt_codes hZ hZ1' (hx.trans_le qd_B3_le_th), qd_cl_iffK hZ hZ1 hx]

end Googology.Trans.PoR.InaccPsi.R2.Qd
