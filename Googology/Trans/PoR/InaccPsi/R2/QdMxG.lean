import Googology.Trans.PoR.InaccPsi.R2.QdAtS
import Googology.Trans.PoR.InaccPsi.R2.QcMxG

/-!
# QdMxG: THE LARGEST FIXED POINT OF `Hᵛ_μ` UP TO A CODE KEEPS ITS GATE BELOW `B₃`

As `Qc.qc_mx_gate` for the Veblen levels and the gates `Qd.qdGt`: the largest fixed point `F` of `Hᵛ_μ` (`μ ≠ 0`) in
`(Ω₁, c]` has `qdGt F ≤ max ω (qdGt c)`.  Below `B₂` a fixed point of `Hᵛ_μ` has `μ < E₂` (`qd_fix_lt_B2`: a
strongly critical `f ∈ (Ω₁, B₂)` has a level `ucLev f < E₂` that does not fix it, and every `Hᵛ_μ` with `μ` above it
fixes `f` only if that level does), where `Hᵛ_μ = H_μ` (through `S`), so it is `Qc.qc_mx_gate`.  From `B₂` on by the
bracket of `c`, the index of a base atom, the index or a leaf of the level of a fixed point of `Γ`
(`Qd.qd_key_H`), the level and index of a non-atom.

* `qd_fold_ge` (a leaf reads at most the fold), `qd_fix_lt_B2`, `qd_P_gamma`;
* `qd_mx_gate` (**the gate of the largest fixed point**), `qd_fpH_gate`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **A leaf reads at most the fold.** -/
theorem qd_fold_ge (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : ∀ d ∈ qdComps z, f d ≤ qdFold f z :=
  fun d hd => Order.lt_add_one_iff.1
    ((qdFold_lt_iff' f (lt_of_le_of_lt zero_le (lt_add_one _)) z).1 (lt_add_one _) d hd)

variable (S : InaccSeq.{0})
include S

/-- **A fixed point of `Hᵛ_μ` below `B₂` has `μ < E₂`.** -/
theorem qd_fix_lt_B2 {μ f : Ordinal.{0}} (hf : qdH μ f = f) (hfB : f < ucB) : μ < ucE := by
  by_contra hμ
  push Not at hμ
  have hS : SC f := by rw [← hf]; exact qdH_SC μ f
  have hO : Om1 < f := by rw [← hf]; exact qdH_gt μ f
  obtain ⟨hl, hC, hne, -, -⟩ := ucLev_spec hS hO (uc_nf_of_lt hS hO hfB)
  apply hne
  rw [← qd_uc_H S hl]
  exact ucG_fix_mono (hl.le.trans hμ) hf ((qd_uc_vis S hl hS hO).2 hC)

/-- A fixed point of `Hᵛ_μ` (`μ ≠ 0`) is a fixed point of `Γ`. -/
theorem qd_P_gamma {μ f : Ordinal.{0}} (hμ0 : μ ≠ 0) (hf : qdH μ f = f) : gamma f = f := by
  have hOf : Om1 < f := by rw [← hf]; exact qdH_gt μ f
  have h1O : (1 : Ordinal.{0}) < Om1 := by rw [Rj.rj_Om1]; exact Nm.one_lt_Om1
  have h1Ω : (1 : Ordinal.{0}) < OmTwo := h1O.trans qc_Om1_lt_Om2
  have h1E : (1 : Ordinal.{0}) < ucE := h1Ω.trans ucE_gt
  have h1 : qdH 1 f = f := ucG_fix_mono (one_le_iff_ne_zero.2 hμ0) hf (by
    rw [qdFold_small id h1Ω]; exact h1O.trans hOf)
  rw [qd_uc_H S h1E] at h1
  exact qc_P_gamma one_ne_zero h1

/-- **The largest fixed point of `Hᵛ_μ` in `(Ω₁, c]` keeps the gate of `c` up to `ω`** (`μ ≠ 0`, `c < B₃`). -/
theorem qd_mx_gate {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) : ∀ c, c < qdB → (∃ f, qdH μ f = f ∧ Om1 < f ∧ f ≤ c) →
    qdGt (vsMx (fun f => qdH μ f = f) c) ≤ max ω (qdGt c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB hex
  -- below `B₂`: `Hᵛ_μ = H_μ` and `Qc.qc_mx_gate`
  rcases lt_or_ge c ucB with hcX | hXc
  · obtain ⟨f₀, hf₀, -, hf₀c⟩ := id hex
    have hμE := qd_fix_lt_B2 S hf₀ (hf₀c.trans_lt hcX)
    have hH := qd_uc_H S hμE
    have hFle := vs_mx_le (fun f => qdH μ f = f) hex
    rw [qdGt_low (hFle.trans_lt hcX), qdGt_low hcX, hH]
    rw [hH] at hex
    exact qc_mx_gate hμ0 c hcX hex
  have hfix := qd_fpH_closed μ c hex
  obtain ⟨hFS, hOF, hFc⟩ := qd_mx_SC hex
  set F := vsMx (fun f => qdH μ f = f) c with hFdef
  have hFE : InE F := Low.opow_eq_self_of_SC hFS
  have hGc : gcG 0 ≤ c := qd_B2_G0.trans hXc
  obtain ⟨hXe, heB⟩ := qd_guE_B hXc hcB
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  -- a part `s ≤ c` with `F ≤ s`: the largest fixed point up to `s` is `F`
  have hpart : ∀ s, s < c → F ≤ s → qdGt F ≤ max ω (qdGt s) := fun s hsc hFs => by
    obtain ⟨e1, hex'⟩ := qd_mx_part hex hsc.le hFs
    have := IH s hsc (hsc.trans hcB) hex'
    rwa [e1] at this
  have hFe : F ≤ guE c := gl_E_max hFE hOF hFc
  have hge : qdGt (guE c) ≤ qdGt c := by
    rw [qdGt_base heE hXe heB, qdGt_dec hXc hcB]; exact (le_max_left _ _).trans (le_max_left _ _)
  rcases hec.lt_or_eq with hlt | heq
  · exact (hpart _ hlt hFe).trans (max_le_max le_rfl hge)
  have hcE : InE c := by rw [← heq]; exact heE
  have hcl : qdGt c = qdQEt c := qdGt_base hcE hXc hcB
  by_cases hPc : qdH μ c = c
  · have h : F = c := le_antisymm hFc (vs_mx_ge _ hPc (ucB_gt.trans_le hXc) le_rfl)
    rw [h]; exact le_max_right _ _
  have hFlt : F < c := lt_of_le_of_ne hFc fun h => hPc (by rw [← h]; exact hfix)
  by_cases hA : YhAt c
  · by_cases hi : yhJ c < c
    · -- a base atom `Γ(j)`: the fixed points of `Hᵛ_μ` up to it are up to `j`
      obtain ⟨j, hj⟩ := yhAt_iff.1 hA
      have hFj : F ≤ yhJ c := by
        have hgF : gcG F = F := vs_gcG_fix (qd_P_gamma S hμ0 hfix) hOF
        rw [hj, yhJ_gcG]
        have h1 : gcG F ≤ gcG j := by rw [hgF, ← hj]; exact hFc
        exact gcG_strictMono.le_iff_le.1 h1
      refine (hpart _ hi hFj).trans ?_
      rw [qd_maxQ le_rfl (yhJ c), hcl, qdQEt_atom hXc hcB hA hi]
    · -- a fixed point `Hᵛ_ν(w)` of `Γ` that `Hᵛ_μ` does not fix
      obtain ⟨-, -, hνc, hwc, hnf, hne⟩ := qd_fix_data S hA hi hXc hcB
      have hQ := qdQEt_fix hXc hcB hA hi hwc
      have hc' : qdH μ (qdH (qdLev c) (qdI (qdLev c) c)) ≠ qdH (qdLev c) (qdI (qdLev c) c) := by
        rw [hnf]; exact hPc
      have hFc' : F < qdH (qdLev c) (qdI (qdLev c) c) := by rw [hnf]; exact hFlt
      rcases qd_key_H hc' hfix hFc' with hFw | ⟨d, hd, hFd⟩
      · -- below the index `w`
        have hKQ : qdKQ (qdLev c) (qdI (qdLev c) c) ≤ qdQEt c := by rw [hQ]; exact le_max_right _ _
        unfold qdKQ at hKQ
        split_ifs at hKQ with hF
        · obtain ⟨-, -, hpw⟩ := qd_fpH_mem hne hF
          set p := qdFpH (qdLev c) (qdI (qdLev c) c) with hpdef
          set w := qdI (qdLev c) c with hwdef
          have ht : p + 1 + (w - (p + 1)) = w := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpw)
          by_cases hFp : F ≤ p
          · refine (hpart _ (hpw.trans hwc) hFp).trans ?_
            rw [qd_maxQ le_rfl p, hcl]
            exact max_le_max le_rfl ((le_max_left _ _).trans hKQ)
          · have hFt : F ≤ w - (p + 1) := by
              by_contra hFt
              push Not at hFt hFp
              have h1 : p + 1 < F := hFS.isSuccLimit.add_one_lt hFp
              have h2 : p + 1 + (w - (p + 1)) < F := hFS.isPrincipal h1 hFt
              rw [ht] at h2
              exact absurd hFw (not_le.2 h2)
            refine (hpart _ ((Ordinal.sub_le_self _ _).trans_lt hwc) hFt).trans ?_
            rw [qd_maxQ le_rfl, hcl]
            exact max_le_max le_rfl ((le_max_right _ _).trans hKQ)
        · refine (hpart _ hwc hFw).trans ?_
          rw [qd_maxQ le_rfl, hcl]
          exact max_le_max le_rfl hKQ
      · -- below a leaf `d` of the level
        have hdc : d < c := (qdFold_lt_iff hcE.pos (qdLev c)).1 hνc d hd
        refine (hpart _ hdc hFd).trans ?_
        rw [qd_maxQ le_rfl d, hcl, hQ]
        refine max_le_max le_rfl ((le_of_eq ?_).trans ((qd_fold_ge _ _ d hd).trans (le_max_left _ _)))
        rw [if_pos hdc]
  · -- a non-atom: the largest fixed point is up to the level or the index
    have hGc' : gcG 0 < c := lt_of_le_of_ne hGc fun h => hA (h ▸ yhAt_gcG 0)
    obtain ⟨-, hkc, hic, hpsi⟩ := va_data hcE hGc' hA
    have hcle : F ≤ yhK c ∨ F ≤ yhI c := by
      by_contra hcon
      push Not at hcon
      have h := yhPsi_lt_SC hFS hOF hcon.1 hcon.2
      rw [hpsi] at h
      exact absurd hFc (not_le.2 h)
    have hQ : max ω (qdGt c) = max ω (max (qdQt (yhK c)) (qdQt (yhI c))) := by
      rw [hcl, qdQEt_psi hXc hcB hA]
    rw [hQ]
    rcases hcle with h | h
    · refine (hpart _ hkc h).trans ?_
      rw [qd_maxQ le_rfl (yhK c)]
      exact max_le_max le_rfl (le_max_left _ _)
    · refine (hpart _ hic h).trans ?_
      rw [qd_maxQ le_rfl (yhI c)]
      exact max_le_max le_rfl (le_max_right _ _)

/-- **The largest fixed point `p < y` of `Hᵛ_μ` keeps the gate of `y` up to `ω`** (`y` not fixed by `Hᵛ_μ`). -/
theorem qd_fpH_gate {μ y : Ordinal.{0}} (hμ0 : μ ≠ 0) (hyB : y < qdB) (hne : qdH μ y ≠ y) (hF : QdFixH μ y) :
    qdGt (qdFpH μ y) ≤ max ω (qdGt y) := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact qdH_gt μ f
  rw [qd_fpH_eq hne]
  exact qd_mx_gate S hμ0 y hyB ⟨f, hf, hOf, hfy.le⟩

end Googology.Trans.PoR.InaccPsi.R2.Qd
