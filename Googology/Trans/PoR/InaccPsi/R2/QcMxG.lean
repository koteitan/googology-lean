import Googology.Trans.PoR.InaccPsi.R2.QcFr

/-!
# QcMxG: THE LARGEST FIXED POINT OF `H_μ` UP TO A CODE KEEPS ITS GATE

As `Va.vs_mx_gate` for the class of the fixed points of `H_μ` (`μ ≠ 0`) and the gates `Qc.qcG` below `B₂`: the
largest fixed point `F` of `H_μ` in `(Ω₁, c]` has `qcG F ≤ max ω (qcG c)`.  Below `X` it is `Va.vs_mx_gate` (a fixed
point `F_β(z) < X` of `Γ` that `H_μ` does not fix has the fixed points of `H_μ` below it below `z`, `qc_hat`); from
`X` on by the bracket of `c`, the index of a base atom, the level and index of a fixed point of `Γ` (`Qc.qc_key_H`;
the gate of `H_ν(w)` holds the gates of the components of `ν` and of the parts of `w`), the level and index of a
non-atom.

* `qc_P_gamma`, `qc_hat`, `qc_mx_gate` (**the gate of the largest fixed point**), `qc_fpH_gate`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk

/-- A fixed point of `H_μ` (`μ ≠ 0`) is a fixed point of `Γ`. -/
theorem qc_P_gamma {μ f : Ordinal.{0}} (hμ0 : μ ≠ 0) (hf : ucH μ f = f) : gamma f = f := by
  have hOf : Om1 < f := by rw [← hf]; exact ucH_gt μ f
  have h0 : ucH 0 f = f :=
    ucG_fix_mono (zero_le : (0 : Ordinal.{0}) ≤ μ) hf (by rw [ucC_small uc_SC_Om2.1]; exact Rj.rj_Om1_pos.trans hOf)
  rw [qc_H0] at h0
  have hSC : SC f := by rw [← hf]; exact ucH_SC μ f
  have hE : InE f := Low.opow_eq_self_of_SC hSC
  rw [tf_gcG, gl_absorb hE hOf] at h0
  exact h0

/-- **A fixed point `e < X` of `Γ` that `H_μ` does not fix** has the fixed points of `H_μ` below it below its index. -/
theorem qc_hat {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) : ∀ e, YhAt e → ¬ yhJ e < e → ¬ (ucH μ e = e) → e < tlX →
    ∀ f, ucH μ f = f → f < e → f ≤ tlI (tlLev e) e := by
  intro e hA hi hPe heX f hf hfe
  obtain ⟨h1, hlc, hyc, hnf, -⟩ := vs_fix_data hA hi heX
  have hO : Om1 < rhF (tlLev e) (tlI (tlLev e) e) := by rw [hnf]; exact hA.2
  have hX' : rhF (tlLev e) (tlI (tlLev e) e) < tlX := by rw [hnf]; exact heX
  have hβc : tlLev e < rhF (tlLev e) (tlI (tlLev e) e) := by rw [hnf]; exact hlc
  rw [← hnf] at hPe hfe
  rcases qc_key_F hO hX' hβc hPe hf hfe with h | h
  · exact h
  · exfalso
    have hCf : ucC μ < f := by rw [← hf]; exact ucH_C_lt μ f
    rcases lt_or_ge μ OmTwo with hμ2 | hμ2
    · rw [ucC_small hμ2] at hCf
      have hμβ : μ < tlLev e := hCf.trans_le h
      have hFμ : rhF μ (rhF (tlLev e) (tlI (tlLev e) e)) = rhF (tlLev e) (tlI (tlLev e) e) := rhF_fix_lower hμβ _
      apply hPe
      rw [hnf] at hFμ ⊢
      exact (ucH_fix_iff_F hμ2 (max_lt hA.2 ((hCf.trans_le h).trans hlc))).2 hFμ
    · have hOf : Om1 < f := by rw [← hf]; exact ucH_gt μ f
      have h2 : ucH OmTwo f = f := ucG_fix_mono hμ2 hf (by rw [ucC_Om2]; exact tf_one_lt_Om1.trans hOf)
      have hXf := uc_X_le_H ⟨f, h2⟩
      exact absurd ((hfe.trans_le (by rw [hnf])).trans heX) (not_lt.2 hXf)

/-- **The largest fixed point of `H_μ` in `(Ω₁, c]` keeps the gate of `c` up to `ω`** (`μ ≠ 0`, `c < B₂`). -/
theorem qc_mx_gate {μ : Ordinal.{0}} (hμ0 : μ ≠ 0) : ∀ c, c < ucB → (∃ f, ucH μ f = f ∧ Om1 < f ∧ f ≤ c) →
    qcG (vsMx (fun f => ucH μ f = f) c) ≤ max ω (qcG c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB hex
  -- below `X`: `Va.vs_mx_gate`
  rcases lt_or_ge c tlX with hcX | hXc
  · have hFle := vs_mx_le (fun f => ucH μ f = f) hex
    rw [qcG_low (hFle.trans_lt hcX), qcG_low hcX]
    exact vs_mx_gate (fun f => ucH μ f = f) (fun f hf => qc_P_gamma hμ0 hf) (fun c hc => qc_fpH_closed μ c hc)
      (qc_hat hμ0) c hcX hex
  have hfix := qc_fpH_closed μ c hex
  obtain ⟨hFS, hOF, hFc⟩ := qc_mx_SC hex
  set F := vsMx (fun f => ucH μ f = f) c with hFdef
  have hFE : InE F := Low.opow_eq_self_of_SC hFS
  have hGc : gcG 0 ≤ c := qc_G0_lt_X.le.trans hXc
  obtain ⟨hXe, heB⟩ := qc_guE_X hXc hcB
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := qc_G0_lt_X.le.trans hXe
  -- a part `s ≤ c` with `F ≤ s`: the largest fixed point up to `s` is `F`
  have hpart : ∀ s, s < c → F ≤ s → qcG F ≤ max ω (qcG s) := fun s hsc hFs => by
    obtain ⟨e1, hex'⟩ := qc_mx_part hex hsc.le hFs
    have := IH s hsc (hsc.trans hcB) hex'
    rwa [e1] at this
  have hFe : F ≤ guE c := gl_E_max hFE hOF hFc
  have hge : qcG (guE c) ≤ qcG c := by
    rw [qcG_base heE hXe heB, qcG_dec hXc hcB]; exact (le_max_left _ _).trans (le_max_left _ _)
  rcases hec.lt_or_eq with hlt | heq
  · exact (hpart _ hlt hFe).trans (max_le_max le_rfl hge)
  have hcE : InE c := by rw [← heq]; exact heE
  have hcl : qcG c = qcQE c := qcG_base hcE hXc hcB
  by_cases hPc : ucH μ c = c
  · have h : F = c := le_antisymm hFc (vs_mx_ge _ hPc (tlX_gt.trans_le hXc) le_rfl)
    rw [h]; exact le_max_right _ _
  have hFlt : F < c := lt_of_le_of_ne hFc fun h => hPc (by rw [← h]; exact hfix)
  by_cases hA : YhAt c
  · by_cases hi : yhJ c < c
    · -- a base atom `Γ(j)`: the fixed points of `H_μ` up to it are up to `j`
      obtain ⟨j, hj⟩ := yhAt_iff.1 hA
      have hFj : F ≤ yhJ c := by
        have hgF : gcG F = F := by
          have h := qc_P_gamma hμ0 hfix
          exact vs_gcG_fix h hOF
        rw [hj, yhJ_gcG]
        have h1 : gcG F ≤ gcG j := by rw [hgF, ← hj]; exact hFc
        exact gcG_strictMono.le_iff_le.1 h1
      refine (hpart _ hi hFj).trans ?_
      rw [qc_maxQ le_rfl (yhJ c), hcl, qcQE_atom hXc hcB hA hi]
    · -- a fixed point `H_ν(w)` of `Γ` that `H_μ` does not fix
      obtain ⟨-, -, hνc, hwc, hnf, hne⟩ := qc_fix_data hA hi hXc hcB
      have hQ := qcQE_fix hXc hcB hA hi hwc
      have hc' : ucH μ (ucH (ucLev c) (ucI (ucLev c) c)) ≠ ucH (ucLev c) (ucI (ucLev c) c) := by rw [hnf]; exact hPc
      have hFc' : F < ucH (ucLev c) (ucI (ucLev c) c) := by rw [hnf]; exact hFlt
      rcases qc_key_H hc' hfix hFc' with hFw | ⟨d, hd, hFd⟩
      · -- below the index `w`
        have hKQ : qcKQ (ucLev c) (ucI (ucLev c) c) ≤ qcQE c := by rw [hQ]; exact le_max_right _ _
        unfold qcKQ at hKQ
        split_ifs at hKQ with hF
        · obtain ⟨-, -, hpw⟩ := qc_fpH_mem hne hF
          set p := qcFpH (ucLev c) (ucI (ucLev c) c) with hpdef
          set w := ucI (ucLev c) c with hwdef
          have ht : p + 1 + (w - (p + 1)) = w := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpw)
          by_cases hFp : F ≤ p
          · refine (hpart _ (hpw.trans hwc) hFp).trans ?_
            rw [qc_maxQ le_rfl p, hcl]
            exact max_le_max le_rfl ((le_max_left _ _).trans hKQ)
          · have hFt : F ≤ w - (p + 1) := by
              by_contra hFt
              push Not at hFt hFp
              have h1 : p + 1 < F := hFS.isSuccLimit.add_one_lt hFp
              have h2 : p + 1 + (w - (p + 1)) < F := hFS.isPrincipal h1 hFt
              rw [ht] at h2
              exact absurd hFw (not_le.2 h2)
            refine (hpart _ ((Ordinal.sub_le_self _ _).trans_lt hwc) hFt).trans ?_
            rw [qc_maxQ le_rfl, hcl]
            exact max_le_max le_rfl ((le_max_right _ _).trans hKQ)
        · refine (hpart _ hwc hFw).trans ?_
          rw [qc_maxQ le_rfl, hcl]
          exact max_le_max le_rfl hKQ
      · -- below a component `d` of the level
        have hdc : d < c := (le_ucC hd).trans_lt hνc
        refine (hpart _ hdc hFd).trans ?_
        rw [qc_maxQ le_rfl d, hcl, hQ]
        refine max_le_max le_rfl ((le_of_eq ?_).trans ((ucFold_le_of_mem _ _ d hd).trans (le_max_left _ _)))
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
    have hQ : max ω (qcG c) = max ω (max (qcQ (yhK c)) (qcQ (yhI c))) := by
      rw [hcl, qcQE_psi hXc hcB hA]
    rw [hQ]
    rcases hcle with h | h
    · refine (hpart _ hkc h).trans ?_
      rw [qc_maxQ le_rfl (yhK c)]
      exact max_le_max le_rfl (le_max_left _ _)
    · refine (hpart _ hic h).trans ?_
      rw [qc_maxQ le_rfl (yhI c)]
      exact max_le_max le_rfl (le_max_right _ _)

/-- **The largest fixed point `p < y` of `H_μ` keeps the gate of `y` up to `ω`** (`y` not fixed by `H_μ`). -/
theorem qc_fpH_gate {μ y : Ordinal.{0}} (hμ0 : μ ≠ 0) (hyB : y < ucB) (hne : ucH μ y ≠ y) (hF : QcFixH μ y) :
    qcG (qcFpH μ y) ≤ max ω (qcG y) := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact ucH_gt μ f
  rw [qc_fpH_eq hne]
  exact qc_mx_gate hμ0 y hyB ⟨f, hf, hOf, hfy.le⟩

end Googology.Trans.PoR.InaccPsi.R2.Qc
