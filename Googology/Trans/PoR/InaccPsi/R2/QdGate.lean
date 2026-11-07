import Googology.Trans.PoR.InaccPsi.R2.QdFx
import Googology.Trans.PoR.InaccPsi.R2.QcGate

/-!
# QdGate: A CODE BELOW `B₃` OVER A STRONGLY CRITICAL `Z ≤ Ω₁` HAS ITS GATE BELOW `Z`

As `Qc.qc_gate` for `Qd.qdGt`: below `B₂` it is `Qc.qc_gate`; from `B₂` on by induction on the code through its
membership in `K⁽⁰⁾_Z` (the splitting facts `Qt.ulK_lead_tail`, `Qt.ulK_prin_cases`, the sums, powers and Veblen values
through `Qd.QdGx`), and at an atom `Hᵛ_γ(y)`: `Γ(y)` (`γ = 0`) has the gate of `y`; a fixed point `Hᵛ_γ(y)` of `Γ`
(`γ ≠ 0`) has the gates of the leaves of `γ` and of the parts `p`, `y − (p+1)` of its index (`p` a code,
`Qd.qd_fpH_cl`).

* `qdFold_lt_iff'` (**the largest value `f d` over the leaves is below `v` iff every one is**), `qd_H_fixG`;
* `qd_gate_K`, `qd_gate` (**a code `QdCl Z` below `B₃` has its gate below `Z`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Qt Googology.Trans.PoR.InaccPsi.R2.Qc Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Gc

/-- **The largest value `f d` over the leaves `d` of `z` is below `v > 0` iff every one is.** -/
theorem qdFold_lt_iff' (f : Ordinal.{0} → Ordinal.{0}) {v : Ordinal.{0}} (hv : 0 < v) :
    ∀ z : Ordinal.{0}, qdFold f z < v ↔ ∀ d ∈ qdComps z, f d < v := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  rcases lt_trichotomy z OmTwo with h2 | rfl | h2
  · rw [qdFold_small f h2, qdComps_small h2]
    exact ⟨fun h d hd => by rw [mem_singleton_iff.1 hd]; exact h, fun h => h z rfl⟩
  · rw [qdFold_Om2 f, qdComps_Om2]
    exact ⟨fun _ d hd => absurd hd (Set.notMem_empty _), fun _ => hv⟩
  · by_cases hzG : z < qdG2
    · by_cases hE : ω ^ z = z
      · rw [qdFold_phi f h2 hzG hE, qdComps_phi h2 hzG hE, max_lt_iff, IH _ (qd_inv1_lt h2 hzG),
          IH _ (Ss.ss_inv2_lt hE)]
        exact ⟨fun h d hd => hd.elim (h.1 d) (h.2 d), fun h => ⟨fun d hd => h d (Or.inl hd),
          fun d hd => h d (Or.inr hd)⟩⟩
      · have hz0 : z ≠ 0 := (qd_Om2_pos.trans h2).ne'
        rw [qdFold_cnf f h2 hzG hE, qdComps_cnf h2 hzG hE, max_lt_iff, IH _ (Ss.ss_log_lt hz0 hE),
          IH _ (Rj.rj_mod_lt hz0)]
        exact ⟨fun h d hd => hd.elim (h.1 d) (h.2 d), fun h => ⟨fun d hd => h d (Or.inl hd),
          fun d hd => h d (Or.inr hd)⟩⟩
    · have e1 : qdFold f z = 0 := by
        rw [qdFold, dif_neg (fun h => hzG h.2), if_neg (not_lt.2 h2.le)]
      have e2 : qdComps z = ∅ := qdComps_big (not_lt.1 hzG)
      rw [e1, e2]
      exact ⟨fun _ d hd => absurd hd (Set.notMem_empty _), fun _ => hv⟩

/-- **`Hᵛ_γ(y)` is a fixed point of `Γ` for `γ ≠ 0`**, and the index of the atom is itself (through `S`). -/
theorem qd_H_fixG (S : InaccSeq.{0}) {γ y : Ordinal.{0}} (hγ : γ ≠ 0) :
    gcG (qdH γ y) = qdH γ y ∧ yhJ (qdH γ y) = qdH γ y := by
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  have h0 : qdH 0 (qdH γ y) = qdH γ y :=
    ucG_fix_lower (pos_iff_ne_zero.2 hγ) ⟨y, rfl⟩ (by rw [qdFold_small id qd_Om2_pos]; exact (qdH_SC γ y).1)
  rw [qd_uc_H S h0E, qc_H0] at h0
  refine ⟨h0, ?_⟩
  conv_lhs => rw [← h0]
  exact yhJ_gcG _

variable {S : InaccSeq.{0}}

/-- **A member of `K⁽⁰⁾_Z` below `B₃` has its gate below `Z`** (`Z ≤ Ω₁` strongly critical). -/
theorem qd_gate_K {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ c, UlK S 0 Z c → c < qdB → qdGt c < Z := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv => hZ.isPrincipal hu hv
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv => hZ.2 u hu v hv
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ.1 hu; rwa [veblen_zero_apply] at this
  have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
  have hZ1' : Z ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hZ1
  have hθ2 : ConjT.th S < Om (1 + 1) := Ui.ui_th_lt_Om2
  have hB3θ : qdB ≤ ConjT.th S := qd_B3_le_th
  have hlow : ∀ c, UlK S 0 Z c → c < ucB → qdGt c < Z := fun c hc hcB => by
    rw [qdGt_low hcB]; exact qc_gate hZ hZ1 c ((Uo.uo_cl_iffK hZ hZ1 hcB).2 hc) hcB
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcB
  rcases lt_or_ge c ucB with hlt | hge
  · exact hlow c hc hlt
  have h1 : Om1 < c := ucB_gt.trans_le hge
  have h1' : Om 1 < c := by rw [← Rj.rj_Om1]; exact h1
  have hc2 : c < Om (1 + 1) := hcB.trans_le (hB3θ.trans hθ2.le)
  have h0 : c ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  by_cases hP : IsPrincipal (· + ·) c
  · rcases ulK_prin_cases hc (hZ1'.trans h1'.le) hP h0 with
      ⟨n, rfl⟩ | rfl | ⟨p, r, hp, hr, hpx, hrx, rfl⟩ | ⟨p, -, -, rfl⟩ | ⟨π, e, hπ, -, rfl⟩
    · exact absurd hc2 (not_lt.2 (mxOm2_lt_I n).le)
    · exact absurd hc2 (not_lt.2 mxOm2_lt_Iw.le)
    · have hgr := IH r hrx hr (hrx.trans hcB)
      rcases eq_or_ne p 0 with rfl | hp0
      · rw [veblen_zero_apply] at hcB ⊢
        exact qd_opow_gate hZw hωZ r hcB hgr
      · exact qd_phi_gate hωZ hp0 (qd_G0_lt_B2.le.trans hge) hcB (IH p hpx hp (hpx.trans hcB)) hgr
    · exact absurd (Om_lt_Om.1 h1') (not_lt.2 (le_of_Om_lt_Om_succ hc2))
    · -- an atom `Hᵛ_γ(y)`
      have hSC : SC (S.psi e π) := SC_psi hπ e
      set z := S.psi e π with hz
      have hne := qd_nf_of_lt hSC h1 hcB
      obtain ⟨hlG, hlF, -, -, -⟩ := qdLev_spec hSC h1 hne
      obtain ⟨hH, hy⟩ := qd_nf hSC h1 hne
      set γ := qdLev z with hγdef
      set y := qdI γ z with hydef
      have hxu : ulH S 1 γ y = z := by rw [← qdH_eq_ul S hlG]; exact hH
      have hK := (Vd.vd_atom_K (hlG.trans (qd_G2_lt_Om3 S)) (by rw [hxu]; exact hy) (by rw [hxu]; exact hc2)
        hZ hZ1').1 (by rw [hxu]; exact hc)
      have hgy : qdGt y < Z := IH y hy hK.2 (hy.trans hcB)
      rcases eq_or_ne γ 0 with hγ0 | hγ0
      · -- `Γ(y)`, `y < Γ(y)`: the gate of `y`
        have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
        have hg : gcG y = z := by
          have h := hH; rw [hγ0, qd_uc_H S h0E, qc_H0] at h; exact h
        rw [← hg] at hcB hy ⊢
        rw [qdGt_atom' hy hcB]
        exact (qdQt_le y).trans_lt hgy
      · -- a fixed point `Hᵛ_γ(y)` of `Γ`
        obtain ⟨-, hJ⟩ := qd_H_fixG S (y := y) hγ0
        rw [hH] at hJ
        have hA : YhAt z := ⟨hSC, h1⟩
        have hi' : ¬ yhJ z < z := by rw [hJ]; exact lt_irrefl _
        have hE : InE z := Low.opow_eq_self_of_SC hSC
        rw [qdGt_base hE hge hcB, qdQEt_fix hge hcB hA hi' hy]
        refine max_lt ((qdFold_lt_iff' _ hZ.1 γ).2 fun d hd => ?_) ?_
        · show (if d < z then qdQt d else 0) < Z
          split_ifs with hdc
          · exact (qdQt_le d).trans_lt (IH d hdc (qd_comps_K0 hZ γ hlG hK.1 d hd) (hdc.trans hcB))
          · exact hZ.1
        · have hne' : qdH γ y ≠ y := by rw [hH]; exact ne_of_gt hy
          unfold qdKQ
          split_ifs with hF
          · obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne' hF
            have hyB : y < qdB := hy.trans hcB
            have hyC : QdCl Z y := qd_K0_cl hZ hZ1 y hK.2 hyB
            have hpC : QdCl Z (qdFpH γ y) := qd_fpH_cl S hZ1 hyC hne' hF
            have hpK : UlK S 0 Z (qdFpH γ y) := qd_cl_K0 hZ hZ1 _ hpC (hpy.trans hyB)
            have hp1K : UlK S 0 Z (qdFpH γ y + 1) := UlK.add hpK UlK.one
            have hoK : UlK S 0 Z (y - (qdFpH γ y + 1)) :=
              (ulK_dec hZ y hK.2).1 _ hp1K (Order.add_one_le_of_lt hpy)
            have hoy : y - (qdFpH γ y + 1) < z := (Ordinal.sub_le_self _ _).trans_lt hy
            exact max_lt ((qdQt_le _).trans_lt (IH _ (hpy.trans hy) hpK ((hpy.trans hy).trans hcB)))
              ((qdQt_le _).trans_lt (IH _ hoy hoK (hoy.trans hcB)))
          · exact (qdQt_le y).trans_lt hgy
  · obtain ⟨hl, ht⟩ := ulK_lead_tail hZ hc h0
    have hlx : lead c < c := lt_of_le_of_ne (lead_le h0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htx : tail c < c := tail_lt h0
    rw [← lead_add_tail h0] at hcB ⊢
    exact qd_add hZa hωZ _ _ hcB (IH _ hlx hl (hlx.trans (lead_add_tail h0 ▸ hcB)))
      (IH _ htx ht (htx.trans (lead_add_tail h0 ▸ hcB)))

/-- **A code `QdCl Z` below `B₃` over a strongly critical `Z ≤ Ω₁` has its gate below `Z`.** -/
theorem qd_gate (S : InaccSeq.{0}) {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) :
    ∀ c, QdCl Z c → c < qdB → qdGt c < Z :=
  fun c hc hcB => qd_gate_K (S := S) hZ hZ1 c (qd_cl_K0 hZ hZ1 c hc hcB) hcB

end Googology.Trans.PoR.InaccPsi.R2.Qd
