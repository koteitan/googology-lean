import Googology.Trans.PoR.InaccPsi.R2.QcFxA

/-!
# QcFxB: THE FIXED POINT `E = H_λ(y)` OF `Γ` IN `[X, B₂)` — ITS DATA, PARTS AND READING

As the first part of `Va.VaFixS` from `X` on.  The parts of the reading `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` of every fixed
point `e < B₂` of `Γ` keep its gate (`qs_fix_gates`: from `X` on by `Qc.qcQE_fix`, below `X` by `Va.vs_fix_gate_l`,
`Va.vs_fix_gate_f`, `Va.vs_fix_gate_0` and the correspondence of the two forms, `qc_corr_low`).

* `qc_corr_low`, `qs_fix_gates`;
* `qs_fx_dat` (**the data of `E`**), `qs_fx_parts` (the parts of the reading), `qs_fx_V` (**the reading of `E`: a closed
  point of `Tˣ ∩ (x, Ω₁)` below a generic-level point**).

No new axiom.  No new definition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **The two forms of a fixed point `e < X` of `Γ`**: `ucLev e = tlLev e`, `z = s_β + y`, the same largest fixed
point below the index, the same offsets. -/
theorem qc_corr_low {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : e < tlX) :
    ucLev e = tlLev e ∧ tlI (tlLev e) e = ucS (tlLev e) + ucI (tlLev e) e ∧
      (VaFixL (tlLev e) (tlI (tlLev e) e) ↔ QcFixH (tlLev e) (ucI (tlLev e) e)) ∧
      vaFpL (tlLev e) (tlI (tlLev e) e) = qcFpH (tlLev e) (ucI (tlLev e) e) ∧
      (QcFixH (tlLev e) (ucI (tlLev e) e) →
        tlI (tlLev e) e - (qcFpH (tlLev e) (ucI (tlLev e) e) + 1) =
          ucI (tlLev e) e - (qcFpH (tlLev e) (ucI (tlLev e) e) + 1)) ∧
      tlI (tlLev e) e - glY0 (tlLev e) = ucI (tlLev e) e ∧
      ucH (tlLev e) (ucI (tlLev e) e) ≠ ucI (tlLev e) e := by
  obtain ⟨h1, hlc, hyc, hnf, -⟩ := vs_fix_data hA hi hX
  have hβ0 : tlLev e ≠ 0 := one_le_iff_ne_zero.1 h1
  have hβX : tlLev e < tlX := hlc.trans hX
  have hβ2 : tlLev e < OmTwo := hβX.trans tlX_lt_OmTwo
  have hidx := qc_idx_low hβ2 (max_lt hA.2 hlc) ⟨_, hnf⟩
  have hsets := qc_fix_sets (y := ucI (tlLev e) e) hβ0 hβ2
  have hH : e ∈ range (ucH (tlLev e)) := (uc_range_F hβ2 (max_lt hA.2 hlc)).2 ⟨_, hnf⟩
  have hne : ucH (tlLev e) (ucI (tlLev e) e) ≠ ucI (tlLev e) e := by
    rw [ucI_spec hH]; exact ne_of_gt (le_add_self.trans_lt (hidx ▸ hyc))
  rw [← hidx]
  have hFiff : VaFixL (tlLev e) (ucS (tlLev e) + ucI (tlLev e) e) ↔ QcFixH (tlLev e) (ucI (tlLev e) e) := by
    constructor
    · rintro ⟨f, h1, h2, h3⟩
      have : f ∈ {f | ucH (tlLev e) f = f ∧ f < ucI (tlLev e) e} := hsets ▸ (show f ∈ {f | rhF (tlLev e) f = f ∧
        Om1 < f ∧ f < ucS (tlLev e) + ucI (tlLev e) e} from ⟨h1, h2, h3⟩)
      exact ⟨f, this.1, this.2⟩
    · rintro ⟨f, h1, h2⟩
      have : f ∈ {f | rhF (tlLev e) f = f ∧ Om1 < f ∧ f < ucS (tlLev e) + ucI (tlLev e) e} :=
        hsets.symm ▸ (show f ∈ {f | ucH (tlLev e) f = f ∧ f < ucI (tlLev e) e} from ⟨h1, h2⟩)
      exact ⟨f, this.1, this.2.1, this.2.2⟩
  have hp : vaFpL (tlLev e) (ucS (tlLev e) + ucI (tlLev e) e) = qcFpH (tlLev e) (ucI (tlLev e) e) := by
    unfold vaFpL qcFpH; rw [hsets]
  refine ⟨qc_lev_low hA.1 hA.2 hX, rfl, hFiff, hp, fun hF => ?_, ?_, hne⟩
  · obtain ⟨hpf, hpO, hpy⟩ := qc_fpH_mem hne hF
    have hβ2' := hβ2
    have hSC : SC (qcFpH (tlLev e) (ucI (tlLev e) e)) := by rw [← hpf]; exact ucH_SC _ _
    have hβp : tlLev e < qcFpH (tlLev e) (ucI (tlLev e) e) := by
      have h := ucH_C_lt (tlLev e) (qcFpH (tlLev e) (ucI (tlLev e) e)); rw [hpf, ucC_small hβ2] at h; exact h
    have hS : ucS (tlLev e) + qcFpH (tlLev e) (ucI (tlLev e) e) = qcFpH (tlLev e) (ucI (tlLev e) e) :=
      (isPrincipal_add_iff_add_left_eq_self.1 hSC.isPrincipal) _ (ucS_lt (max_lt hpO hβp) hSC)
    set p := qcFpH (tlLev e) (ucI (tlLev e) e) with hpdef
    obtain ⟨t, ht⟩ := exists_add_of_le (Order.add_one_le_of_lt hpy)
    rw [ht, ← add_assoc, ← add_assoc, hS, Ordinal.add_sub_cancel]
  · rw [qc_ucS_low hβX, Ordinal.add_sub_cancel]

/-- **The parts of the reading of a fixed point `e < B₂` of `Γ` keep its gate.** -/
theorem qs_fix_gates {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hB : e < ucB) :
    (∀ d ∈ ucComps (ucLev e), qcG d ≤ max ω (qcQE e)) ∧
      (QcFixH (ucLev e) (ucI (ucLev e) e) →
        qcG (qcFpH (ucLev e) (ucI (ucLev e) e)) ≤ max ω (qcQE e) ∧
          qcG (ucI (ucLev e) e - (qcFpH (ucLev e) (ucI (ucLev e) e) + 1)) ≤ max ω (qcQE e)) ∧
      (¬ QcFixH (ucLev e) (ucI (ucLev e) e) → qcG (ucI (ucLev e) e) ≤ max ω (qcQE e)) := by
  rcases lt_or_ge e tlX with hX | hX
  · obtain ⟨hlev, hz, hFiff, hp, hsub, hsub0, hne⟩ := qc_corr_low hA hi hX
    obtain ⟨-, hlc, hyc, -, -⟩ := vs_fix_data hA hi hX
    have hβ2 : tlLev e < OmTwo := (hlc.trans hX).trans tlX_lt_OmTwo
    have hzX : tlI (tlLev e) e < tlX := hyc.trans hX
    have hyX : ucI (tlLev e) e < tlX := (hz ▸ le_add_self : ucI (tlLev e) e ≤ tlI (tlLev e) e).trans_lt hzX
    rw [hlev, qcQE_low hX]
    refine ⟨fun d hd => ?_, fun hF => ?_, fun hF => ?_⟩
    · rw [ucComps_small hβ2, mem_singleton_iff] at hd
      rw [hd, qcG_low (hlc.trans hX)]; exact vs_fix_gate_l hA hi hX
    · obtain ⟨hgf, hgo⟩ := vs_fix_gate_f hA hi hX (hFiff.2 hF)
      rw [hp] at hgf hgo
      rw [hsub hF] at hgo
      obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      rw [qcG_low (hpy.trans hyX), qcG_low ((Ordinal.sub_le_self _ _).trans_lt hyX)]
      exact ⟨hgf, hgo⟩
    · have h := vs_fix_gate_0 hA hi hX
      rw [hsub0] at h
      rw [qcG_low hyX]; exact h
  · have hN := (qc_fix_data hA hi hX hB).2.2.2.1
    have hQ := qcQE_fix hX hB hA hi hN
    have hc := (qc_fix_data hA hi hX hB).2.2.1
    refine ⟨fun d hd => ?_, fun hF => ?_, fun hF => ?_⟩
    · have hde : d < e := (le_ucC hd).trans_lt hc
      have h1 : qcQ d ≤ qcQE e := by
        rw [hQ]
        refine (le_of_eq ?_).trans ((ucFold_le_of_mem _ _ d hd).trans (le_max_left _ _))
        rw [if_pos hde]
      calc qcG d ≤ max ω (qcG d) := le_max_right _ _
        _ = max ω (qcQ d) := qc_maxQ le_rfl d
        _ ≤ max ω (qcQE e) := max_le_max le_rfl h1
    · have hK : qcKQ (ucLev e) (ucI (ucLev e) e) ≤ qcQE e := by rw [hQ]; exact le_max_right _ _
      unfold qcKQ at hK
      rw [if_pos hF] at hK
      refine ⟨?_, ?_⟩
      · calc qcG _ ≤ max ω (qcG _) := le_max_right _ _
          _ = max ω (qcQ _) := qc_maxQ le_rfl _
          _ ≤ max ω (qcQE e) := max_le_max le_rfl ((le_max_left _ _).trans hK)
      · calc qcG _ ≤ max ω (qcG _) := le_max_right _ _
          _ = max ω (qcQ _) := qc_maxQ le_rfl _
          _ ≤ max ω (qcQE e) := max_le_max le_rfl ((le_max_right _ _).trans hK)
    · have hK : qcKQ (ucLev e) (ucI (ucLev e) e) ≤ qcQE e := by rw [hQ]; exact le_max_right _ _
      unfold qcKQ at hK
      rw [if_neg hF] at hK
      calc qcG _ ≤ max ω (qcG _) := le_max_right _ _
        _ = max ω (qcQ _) := qc_maxQ le_rfl _
        _ ≤ max ω (qcQE e) := max_le_max le_rfl hK

/-! ## The fixed point `E` -/

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < ucB) (hXE : tlX ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hA hi hXE hEB in
/-- **The data of the fixed point `E = H_λ(y)`.** -/
theorem qs_fx_dat :
    gamma E = E ∧ ucLev E ≠ 0 ∧ ucLev E < ucE ∧ ucC (ucLev E) < E ∧ ucI (ucLev E) E < E ∧
      ucH (ucLev E) (ucI (ucLev E) E) = E ∧ ucH (ucLev E) (ucI (ucLev E) E) ≠ ucI (ucLev E) E ∧ vaFB E = E := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := qc_fix_data hA hi hXE hEB
  have hfix := vs_fixatom hA hi
  exact ⟨hfix, h1, h2, h3, h4, h5, h6, vs_FB_self hfix hA.2⟩

include hE hBE hEB hXE hlim hIH hA hi hx hx1

/-- **The parts of the reading of `E`.** -/
theorem qs_fx_parts (hgx : max ω (qcQE E) < x) :
    (∀ d ∈ ucComps (ucLev E), d < E ∧ qcG d < x) ∧ 1 ≤ qcLvx E (ucLev E) x ∧
      Om1 + qcLvx E (ucLev E) x < ggE ∧ rjDat (Om1 + qcLvx E (ucLev E) x) ∈ Tset x ∧
      qcK (ucLev E) (ucI (ucLev E) E) x ∈ Tset x ∧ qcK (ucLev E) (ucI (ucLev E) E) x < Om1 ∧
      QcBd x (max (rjDat (Om1 + qcLvx E (ucLev E) x)) (qcK (ucLev E) (ucI (ucLev E) E) x)) := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨-, hl0, hlE, hlc, hyc, -, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨hgcomp, hgF, hg0⟩ := qs_fix_gates hA hi hEB
  have hcode : ∀ c, c < E → qcG c < x → vQ c x ∈ Tset x ∧ vQ c x < Om1 := fun c hc hgc =>
    ⟨(qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩
  have hmono : ∀ b c, b < c → c < E → qcG b < x → qcG c < x → vQ b x < vQ c x := fun b c hbc hc hgb hgc =>
    qs_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc
  obtain ⟨hL1, hNE, hNT, hKT, hK1⟩ := qc_fix_lev hx hx1 hA hi hXE hEB hgx hcode hmono
  have hcomp : ∀ d ∈ ucComps (ucLev E), d < E ∧ qcG d < x := fun d hd =>
    ⟨(le_ucC hd).trans_lt hlc, (hgcomp d hd).trans_lt hgx⟩
  -- the data of the level is at most the largest reading of a component
  set f : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vQ d x else 0 with hfdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : f 0 = 0 := by simp only [hfdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < E ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qcG d < x) d → f d < Om1 := fun d hd => by
    simp only [hfdef, if_pos hd.1]; exact (hcode d hd.1 hd.2).2
  have hfm : ∀ d d', (fun d => d < E ∧ qcG d < x) d → (fun d => d < E ∧ qcG d < x) d' → d < d' → f d < f d' :=
    fun d d' hd hd' hdd => by
      simp only [hfdef, if_pos hd.1, if_pos hd'.1]; exact hmono d d' hdd hd'.1 hd.2 hd'.2
  obtain ⟨hLE, hLdat, -, -⟩ := qcLv_main f (fun d => d < E ∧ qcG d < x) hf0 hD0 hfΩ hfm _ hlE hcomp
  have hlx : qcLvx E (ucLev E) x = qcLv f (ucLev E) := rfl
  have hdatle : rjDat (Om1 + qcLvx E (ucLev E) x) ≤ ucFold f (ucLev E) := by
    rw [hlx]
    rcases lt_or_ge (qcLv f (ucLev E)) Om1 with hs | hs
    · rw [rjDat_Om1_add (one_le_iff_ne_zero.1 (hlx ▸ hL1)) hs]; have h := hLdat; rwa [rjDat_small hs] at h
    · rw [si_rjDat_Om1_add hs hLE]; exact hLdat
  have hfold : QcBd x (ucFold f (ucLev E)) := qcBd_fold hx hx1 f _ fun d hd => by
    obtain ⟨hdE, hgd⟩ := hcomp d hd
    simp only [hfdef, if_pos hdE]
    exact (qs_T hE hBE hEB hlim hIH hx hx1 hdE hgd).2.2
  have hKbd : QcBd x (qcK (ucLev E) (ucI (ucLev E) E) x) := by
    unfold qcK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      exact qcBd_add hx hx1 (qs_T hE hBE hEB hlim hIH hx hx1 (hpy.trans hyc) (hgp.trans_lt hgx)).2.2
        (qs_T hE hBE hEB hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hyc) (hgo.trans_lt hgx)).2.2
    · exact (qs_T hE hBE hEB hlim hIH hx hx1 hyc ((hg0 hF).trans_lt hgx)).2.2
  exact ⟨hcomp, hL1, hNE, hNT, hKT, hK1, qcBd_max (qcBd_mono hdatle hfold) hKbd⟩

/-- **The reading of the fixed point**: a closed point of `Tˣ ∩ (x, Ω₁)` below a generic-level point. -/
theorem qs_fx_V (hgx : max ω (qcQE E) < x) :
    qcA E x = vt x (Om1 * (Om1 + qcLvx E (ucLev E) x) + qcK (ucLev E) (ucI (ucLev E) E) x) ∧
      YwClosed x (qcA E x) ∧ qcA E x ∈ Tset x ∧ InE (qcA E x) ∧ x < qcA E x ∧ QcBd x (qcA E x) ∧
      qcA E x < Om1 := by
  obtain ⟨-, hL1, hNE, hNT, hKT, hK1, hbd⟩ := qs_fx_parts hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
  have heq := qcA_fix hA hi hXE hEB x
  have hcl := qc_fix_cl hx hx1 hA hi hXE hEB hgx
    (fun c hc hgc => ⟨(qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).1, (qs_T hE hBE hEB hlim hIH hx hx1 hc hgc).2.1⟩)
    (fun b c hbc hc hgb hgc => qs_mono hE hBE hEB hlim hIH hx hx1 hbc hc hgb hgc)
  have hO1 : Om1 ≤ Om1 + qcLvx E (ucLev E) x := le_self_add
  have hargT := rjArg_mem hx hx1 hO1 hNE hNT hKT hK1
  have harg2 := qc_arg_lt hNE hK1
  obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hx hx1 hargT harg2
  obtain ⟨hxv, hvE⟩ := (vt_E_iff hx hx1 hargT harg2).2 (le_mul_of_one_le_right' (one_le_iff_ne_zero.2
    (by intro h; rw [h] at hO1; exact absurd (Rj.rj_Om1_pos) (not_lt.2 hO1))) |>.trans le_self_add)
  rw [heq] at hcl ⊢
  exact ⟨rfl, hcl, hvT, hvE, hxv, qcBd_vt hx hx1 hNE hNT hKT hK1 hbd, hv1⟩

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qc
