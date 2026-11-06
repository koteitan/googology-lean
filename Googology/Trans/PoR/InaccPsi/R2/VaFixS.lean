import Googology.Trans.PoR.InaccPsi.R2.VaAtS

/-!
# VaFixS: THE TOP DATA AT A FIXED POINT OF `Γ` — THE NEW SEGMENT BASE

A fixed point `E = F_λ(y)` of `Γ` (`B_Γ < E < X`, `1 ≤ λ = tlLev E`, `y = tlI λ E`) reads the closed point
`D(x) = ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` (`Yw.ywV`), `K = vK λ y`.  With the systems at every `ε`-number below `E`:

* every code below `E` reads below `D(x)` (`vs_fx_lt`): `D(x)` is closed (under `gq`, `ϑˣ(Ω₁·α + η)`, the sums), and a
  smaller fixed point `F' = F_μ(z)` reads below it by the levels: `μ < λ` (`Yw.ywV_lt_lower`), `μ = λ` (`z < y`, the
  index readings are ordered, `vs_fx_Kmono`), `μ > λ` (`F'` is a fixed point of `F_λ` below `y`, read below `K(x)`);
* the readings are cofinal in `D(x)` (`vs_fx_top`): their supremum `u` is closed (above every reading `vR b` is the
  reading `gq(F(x) + b(x))` of the atom `Γ(F + 1 + b)`, `vs_fx_atomAbove`), so `u = ϑˣ(Ω₁·(Ω₁+j) + σ)`
  (`Yw.ywC_rep`) with `j < λ(x)` or `j = λ(x)`, `σ < K(x)` (`Yw.ywV_lt_inv`), and a code `F_μ(z) < E` reads above
  `u` (`vs_fx_rd`, `vs_fx_codeAbove`);
* `vsTopFix` (**THE TOP DATA AT A FIXED POINT OF `Γ`**, the segment base `vaFB E = E` read `D(x)` itself).

No new axiom.  New definition: `vsTopFix`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## The arguments of `F_λ` -/

theorem vs_SC_Om1 : SC (Om1 : Ordinal.{0}) := by rw [Br.Om1_eq]; exact SC_Om one_ne_zero

/-- `F_{Ω₁}(0) ≤ Ω₁`: `Ω₁` is a fixed point of every `F_β`, `β < Ω₁`. -/
theorem vs_rhF_Om1_zero : rhF Om1 0 ≤ Om1 := by
  obtain ⟨e, he⟩ := rhF_range vs_SC_Om1 fun j hj => tl_rhF_Om1 hj
  exact ((rhF_le Om1).2 zero_le).trans_eq he

/-- **`y₀(λ) ≤ z` once `F_λ(z) > Ω₁`.** -/
theorem vs_y0_le {l z : Ordinal.{0}} (hz : Om1 < rhF l z) : glY0 l ≤ z := by
  unfold glY0
  split_ifs with h1 h2
  · by_contra hc
    push Not at hc
    have hzO : z ≤ Om1 := Order.lt_add_one_iff.1 hc
    have h := (rhF_le l).2 hzO
    rw [tl_rhF_Om1 h1] at h
    exact absurd hz (not_lt.2 h)
  · by_contra hc
    push Not at hc
    have hz0 : z = 0 := Order.lt_one_iff.1 hc
    rw [hz0, h2] at hz
    exact absurd hz (not_lt.2 vs_rhF_Om1_zero)
  · exact zero_le

/-- **An argument `z ≥ y₀(λ)` that is not a fixed point of `F_λ` above `Ω₁` is below `F_λ(z)`.** -/
theorem vs_lt_rhF {l z : Ordinal.{0}} (hz : glY0 l ≤ z) (hnf : ¬ (rhF l z = z ∧ Om1 < z)) : z < rhF l z := by
  refine lt_of_le_of_ne (rhF_le_self l z) fun h => ?_
  by_cases hOz : Om1 < z
  · exact hnf ⟨h.symm, hOz⟩
  push Not at hOz
  have hlz : l ≤ z := (rhF_left_le l z).trans h.symm.le
  unfold glY0 at hz
  split_ifs at hz with h1 h2
  · exact absurd (hz.trans hOz) (not_le.2 (lt_add_one _))
  · subst h2
    have hzO : z = Om1 := le_antisymm hOz hlz
    have h01 : rhF Om1 0 < rhF Om1 z := (rhF_lt Om1).2 (by rw [hzO]; exact Rj.rj_Om1_pos)
    have h3 := (rhF_left_le Om1 0).trans_lt h01
    rw [← h, hzO] at h3
    exact lt_irrefl _ h3
  · exact absurd (hlz.trans hOz) (not_le.2 (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)))

/-- **The largest fixed point of `F_λ` below `z`, from a witness.** -/
theorem vs_fpL_of {l z f : Ordinal.{0}} (hf : rhF l f = f) (hOf : Om1 < f) (hfz : f < z)
    (hmax : ∀ f', rhF l f' = f' → Om1 < f' → f' < z → f' ≤ f) : VaFixL l z ∧ vaFpL l z = f :=
  ⟨⟨f, hf, hOf, hfz⟩, by
    unfold vaFpL
    exact IsGreatest.csSup_eq ⟨⟨hf, hOf, hfz⟩, fun f' hf' => hmax f' hf'.1 hf'.2.1 hf'.2.2⟩⟩

theorem vK_fix {l z x : Ordinal.{0}} (h : VaFixL l z) :
    vK l z x = vR (vaFpL l z) x + vR (z - (vaFpL l z + 1)) x := by unfold vK; rw [if_pos h]

theorem vK_nofix {l z x : Ordinal.{0}} (h : ¬ VaFixL l z) : vK l z x = vR (z - glY0 l) x := by
  unfold vK; rw [if_neg h]

theorem vs_sub_lt' {a z y : Ordinal.{0}} (h1 : a ≤ z) (h : z < y) : z - a < y - a := by
  obtain ⟨o', rfl⟩ := exists_add_of_le h1
  obtain ⟨o, rfl⟩ := exists_add_of_le (h1.trans h.le)
  rw [Ordinal.add_sub_cancel, Ordinal.add_sub_cancel]; exact (add_lt_add_iff_left _).1 h

/-- **The largest fixed point of `F_λ` in `(Ω₁, c]` keeps the gate of `c`.** -/
theorem vs_mxL_gate {l c : Ordinal.{0}} (hcX : c < tlX) (hex : ∃ f, rhF l f = f ∧ Om1 < f ∧ f ≤ c) :
    yrG (vsMx (fun f => rhF l f = f) c) ≤ max ω (yrG c) := by
  refine vs_mx_gate (fun f => rhF l f = f) (fun f hf => ?_) (fun c hc => vs_fpL_closed l c hc)
    (fun e hA hi hPe heX f hf hfe => ?_) c hcX hex
  · have h := rhF_fix_mono (zero_le : (0 : Ordinal.{0}) ≤ l) hf; rwa [rhF_zero] at h
  · obtain ⟨hnf, -, -⟩ := tl_nf hA.1 hA.2 heX
    have hle : tlLev e ≤ l := csInf_le' (show rhF l e ≠ e from hPe)
    have hf' : rhF (tlLev e) f = f := rhF_fix_mono hle hf
    have h : rhF (tlLev e) f < rhF (tlLev e) (tlI (tlLev e) e) := by rw [hf', hnf]; exact hfe
    exact ((rhF_lt _).1 h).le

/-- **The reading and the gate of `F_μ(z)`** (`1 ≤ μ`, `z < F_μ(z)`). -/
theorem vs_fx_rd {μ z : Ordinal.{0}} (hμ1 : 1 ≤ μ) (hzr : z < rhF μ z) (hO : Om1 < rhF μ z)
    (haX : rhF μ z < tlX) :
    (∀ x, vR (rhF μ z) x = ywV (vR μ x) (vK μ z x) x) ∧
      yrG (rhF μ z) = max (yrQ μ) (yrQ (z - glY0 μ)) := by
  have hSC := rhF_SC μ z
  have hA : YhAt (rhF μ z) := ⟨hSC, hO⟩
  have hfix : gamma (rhF μ z) = rhF μ z := rhF_gamma (one_le_iff_ne_zero.1 hμ1) z
  have hi : ¬ yhJ (rhF μ z) < rhF μ z := by
    have h := yhJ_gcG (rhF μ z); rw [vs_gcG_fix hfix hO] at h; rw [h]; exact lt_irrefl _
  have hlev : tlLev (rhF μ z) = μ := tlLev_F hzr
  have hidx : tlI μ (rhF μ z) = z := tlI_rhF μ z
  obtain ⟨-, hyc, hlc⟩ := tl_nf hA.1 hA.2 haX
  have hL : tlLev (rhF μ z) < rhF μ z ∧ tlI (tlLev (rhF μ z)) (rhF μ z) < rhF μ z := ⟨hlc, hyc⟩
  have hE : InE (rhF μ z) := Low.opow_eq_self_of_SC hSC
  have hG : gcG 0 ≤ rhF μ z := gl_G0_le hSC hO
  refine ⟨fun x => ?_, ?_⟩
  · rw [vR_base hE hG, vA_atom_fix hA hi hL, hlev, hidx]
  · rw [yrG_base hE hG, yrQE_atom_fixL hA hi hL, hlev, hidx]

/-- **`F_λ(z) > Ω₁`** for an argument `z ≥ y₀(λ)` below `F_λ(z)`. -/
theorem vs_O_rhF {l z : Ordinal.{0}} (hz0 : glY0 l ≤ z) (hzr : z < rhF l z) : Om1 < rhF l z := by
  unfold glY0 at hz0
  split_ifs at hz0 with h1 h2
  · exact ((lt_add_one _).trans_le hz0).trans hzr
  · subst h2
    have hz1 : (0 : Ordinal.{0}) < z := zero_lt_one.trans_le hz0
    exact (rhF_left_le Om1 0).trans_lt ((rhF_lt Om1).2 hz1)
  · exact (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)).trans_le (rhF_left_le l z)

/-! ## The fixed point `E` -/

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEX : E < tlX)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hA hi hEX in
/-- **The data of the fixed point.** -/
theorem vs_fx_dat :
    gamma E = E ∧ 1 ≤ tlLev E ∧ tlLev E < E ∧ tlI (tlLev E) E < E ∧ rhF (tlLev E) (tlI (tlLev E) E) = E ∧
      rhF (tlLev E) (tlI (tlLev E) E) ≠ tlI (tlLev E) E ∧ vaFB E = E ∧ glY0 (tlLev E) ≤ tlI (tlLev E) E := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := vs_fix_data hA hi hEX
  have hfix := vs_fixatom hA hi
  refine ⟨hfix, h1, h2, h3, h4, h5, vs_FB_self hfix hA.2, vs_y0_le (by rw [h4]; exact hA.2)⟩

include hE hBE hEX hlim hIH hA hi hx hx1

/-- **The parts of the reading.** -/
theorem vs_fx_parts (hgx : max ω (yrQE E) < x) :
    yrG (tlLev E) < x ∧ vR (tlLev E) x ∈ Tset x ∧ vR (tlLev E) x < Om1 ∧ vR (tlLev E) x < ywX x ∧
      1 ≤ vR (tlLev E) x ∧ vK (tlLev E) (tlI (tlLev E) E) x ∈ Tset x ∧
      vK (tlLev E) (tlI (tlLev E) E) x < Om1 ∧ vK (tlLev E) (tlI (tlLev E) E) x < ywX x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨-, hl1, hlE, hyE, -, hne, -, -⟩ := vs_fx_dat hEX hA hi
  have hgl : yrG (tlLev E) < x := (vs_fix_gate_l hA hi hEX).trans_lt hgx
  obtain ⟨hlT, hl1', hlX⟩ := vs_T hE hBE hlim hIH hx hx1 hlE hgl
  have hv1 : 1 ≤ vR (tlLev E) x := by
    have h := vs_le_mono hE hBE hlim hIH hx hx1 hl1 hlE
      (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate];
          exact (natCast_lt_omega0 1).trans hωx) hgl
    rwa [vR_one] at h
  have hXE : InE (ywX x) := (ywX_facts hx hx1).2.2.2
  have hK : vK (tlLev E) (tlI (tlLev E) E) x ∈ Tset x ∧ vK (tlLev E) (tlI (tlLev E) E) x < Om1 ∧
      vK (tlLev E) (tlI (tlLev E) E) x < ywX x := by
    by_cases hF : VaFixL (tlLev E) (tlI (tlLev E) E)
    · rw [vK_fix hF]
      obtain ⟨hgf, hgo⟩ := vs_fix_gate_f hA hi hEX hF
      obtain ⟨-, -, hfy⟩ := vs_fpL_mem hne hF
      obtain ⟨hfT, hf1, hfX⟩ := vs_T hE hBE hlim hIH hx hx1 (hfy.trans hyE) (hgf.trans_lt hgx)
      obtain ⟨hoT, ho1, hoX⟩ := vs_T hE hBE hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hyE)
        (hgo.trans_lt hgx)
      exact ⟨vzT_add hx hx1 hfT hoT, (inE_indec gl_Om1_E).add_lt hf1 ho1, (inE_indec hXE).add_lt hfX hoX⟩
    · rw [vK_nofix hF]
      exact vs_T hE hBE hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hyE)
        ((vs_fix_gate_0 hA hi hEX).trans_lt hgx)
  exact ⟨hgl, hlT, hl1', hlX, hv1, hK⟩

/-- **The reading of the fixed point**: a closed point of `Tˣ ∩ (x, X^x)`. -/
theorem vs_fx_V (hgx : max ω (yrQE E) < x) :
    vA E x = ywV (vR (tlLev E) x) (vK (tlLev E) (tlI (tlLev E) E) x) x ∧ YwClosed x (vA E x) ∧
      vA E x ∈ Tset x ∧ InE (vA E x) ∧ x < vA E x ∧ vA E x < ywX x ∧ vA E x < Om1 := by
  obtain ⟨-, -, hlE, hyE, -, -, -, -⟩ := vs_fx_dat hEX hA hi
  obtain ⟨-, hlT, hl1', hlX, hv1, hKT, hK1, hKX⟩ := vs_fx_parts hE hBE hEX hlim hIH hA hi hx hx1 hgx
  have heq : vA E x = ywV (vR (tlLev E) x) (vK (tlLev E) (tlI (tlLev E) E) x) x :=
    vA_atom_fix hA hi ⟨hlE, hyE⟩ x
  obtain ⟨hvT, hxv, hv1', hvE, -, -, -⟩ := ywV_facts hx hx1 hlT hl1' hKT hK1
  rw [heq]
  exact ⟨rfl, ywV_closed hx hx1 (zero_lt_one.trans_le hv1) hlT hl1' hKT hK1, hvT, hvE, hxv,
    ywV_lt_X hx hx1 hlT hl1' hKT hK1 hlX hKX, hv1'⟩

/-- **The readings of the `ε`-number codes below `E` are `ε`-numbers.** -/
theorem vs_fx_eps {e' : Ordinal.{0}} (he' : InE e') (hBe' : tfBG ≤ e') (he'E : e' < E) (hg : yrG e' < x) :
    InE (vR e' x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hGe : gcG 0 ≤ e' := va_G_le_BG.trans hBe'
  obtain ⟨M, -, hEg, hV, -⟩ := hIH e' he' hBe' he'E
  have hgM : M.Eg < x := by rw [hEg]; exact max_lt hωx (by rw [← yrG_base he' hGe]; exact hg)
  have h := (M.V_T x hx hx1 hgM).2.1
  rwa [hV x hx hx1 hgM, ← vR_base he' hGe] at h

/-- **The parts of a fixed point `F' = F_μ(z) < E` of `Γ`** with gate below `x`: in `Tˣ ∩ Ω₁`, and its reading. -/
theorem vs_fx_partsOf {F' : Ordinal.{0}} (hAF : YhAt F') (hiF : ¬ yhJ F' < F') (hF'E : F' < E)
    (hgF : max ω (yrQE F') < x) :
    yrG (tlLev F') < x ∧ vR (tlLev F') x ∈ Tset x ∧ vR (tlLev F') x < Om1 ∧
      vK (tlLev F') (tlI (tlLev F') F') x ∈ Tset x ∧ vK (tlLev F') (tlI (tlLev F') F') x < Om1 ∧
      vR F' x = ywV (vR (tlLev F') x) (vK (tlLev F') (tlI (tlLev F') F') x) x := by
  have hF'X : F' < tlX := hF'E.trans hEX
  obtain ⟨-, hμF, hzF, -, hzne⟩ := vs_fix_data hAF hiF hF'X
  have hgμ : yrG (tlLev F') < x := (vs_fix_gate_l hAF hiF hF'X).trans_lt hgF
  obtain ⟨hμT, hμ1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (hμF.trans hF'E) hgμ
  have hK : vK (tlLev F') (tlI (tlLev F') F') x ∈ Tset x ∧ vK (tlLev F') (tlI (tlLev F') F') x < Om1 := by
    by_cases hF : VaFixL (tlLev F') (tlI (tlLev F') F')
    · rw [vK_fix hF]
      obtain ⟨hgf, hgo⟩ := vs_fix_gate_f hAF hiF hF'X hF
      obtain ⟨-, -, hfy⟩ := vs_fpL_mem hzne hF
      obtain ⟨hfT, hf1, -⟩ := vs_T hE hBE hlim hIH hx hx1 ((hfy.trans hzF).trans hF'E) (hgf.trans_lt hgF)
      obtain ⟨hoT, ho1, -⟩ := vs_T hE hBE hlim hIH hx hx1 (((Ordinal.sub_le_self _ _).trans_lt hzF).trans hF'E)
        (hgo.trans_lt hgF)
      exact ⟨vzT_add hx hx1 hfT hoT, (inE_indec gl_Om1_E).add_lt hf1 ho1⟩
    · rw [vK_nofix hF]
      obtain ⟨h1, h2, -⟩ := vs_T hE hBE hlim hIH hx hx1 (((Ordinal.sub_le_self _ _).trans_lt hzF).trans hF'E)
        ((vs_fix_gate_0 hAF hiF hF'X).trans_lt hgF)
      exact ⟨h1, h2⟩
  have hE' : InE F' := Low.opow_eq_self_of_SC hAF.1
  have hG' : gcG 0 ≤ F' := gl_G0_le hAF.1 hAF.2
  exact ⟨hgμ, hμT, hμ1, hK.1, hK.2, by rw [vR_base hE' hG', vA_atom_fix hAF hiF ⟨hμF, hzF⟩]⟩

/-- **The index readings of `F_λ` are ordered** below `E = F_λ(y)`: `vK λ z x < K(x)` for `y₀(λ) ≤ z < y`, `z` not a
fixed point of `F_λ`. -/
theorem vs_fx_Kmono (hgx : max ω (yrQE E) < x) {z : Ordinal.{0}} (hzy : z < tlI (tlLev E) E)
    (hz0 : glY0 (tlLev E) ≤ z) (hzr : rhF (tlLev E) z ≠ z)
    (hgf : VaFixL (tlLev E) z → yrG (vaFpL (tlLev E) z) < x ∧ yrG (z - (vaFpL (tlLev E) z + 1)) < x)
    (hg0 : ¬ VaFixL (tlLev E) z → yrG (z - glY0 (tlLev E)) < x) :
    vK (tlLev E) z x < vK (tlLev E) (tlI (tlLev E) E) x := by
  obtain ⟨-, -, hlE, hyE, -, hne, -, -⟩ := vs_fx_dat hEX hA hi
  by_cases hFy : VaFixL (tlLev E) (tlI (tlLev E) E)
  · obtain ⟨hgfy, hgoy⟩ := vs_fix_gate_f hA hi hEX hFy
    obtain ⟨hffy, hOfy, hfyy⟩ := vs_fpL_mem hne hFy
    rw [vK_fix hFy]
    by_cases hFz : VaFixL (tlLev E) z
    · obtain ⟨hgfz, hgoz⟩ := hgf hFz
      obtain ⟨hffz, hOfz, hfzz⟩ := vs_fpL_mem hzr hFz
      rw [vK_fix hFz]
      have hfle : vaFpL (tlLev E) z ≤ vaFpL (tlLev E) (tlI (tlLev E) E) := by
        unfold vaFpL
        exact le_csSup ⟨_, fun _ h => h.2.2.le⟩ ⟨hffz, hOfz, hfzz.trans hzy⟩
      rcases hfle.lt_or_eq with hflt | hfeq
      · -- `f_z < f_y`: then `z < f_y`, and `f_y(x)` is an `ε`-number above the parts
        have hzfy : z < vaFpL (tlLev E) (tlI (tlLev E) E) := by
          rcases lt_or_ge z (vaFpL (tlLev E) (tlI (tlLev E) E)) with h | h
          · exact h
          · exfalso
            rcases h.lt_or_eq with h' | h'
            · have h2 : vaFpL (tlLev E) (tlI (tlLev E) E) ≤ vaFpL (tlLev E) z := by
                unfold vaFpL
                exact le_csSup ⟨_, fun _ h => h.2.2.le⟩ ⟨hffy, hOfy, h'⟩
              exact absurd h2 (not_le.2 hflt)
            · exact hzr (by rw [← h']; exact hffy)
        have hfyG : gamma (vaFpL (tlLev E) (tlI (tlLev E) E)) = vaFpL (tlLev E) (tlI (tlLev E) E) := by
          have h := rhF_fix_mono (zero_le : (0 : Ordinal.{0}) ≤ tlLev E) hffy; rwa [rhF_zero] at h
        have hfyE : InE (vR (vaFpL (tlLev E) (tlI (tlLev E) E)) x) :=
          vs_fx_eps hE hBE hEX hlim hIH hA hi hx hx1 (zm_fix_E (zm_fix_of_gamma hfyG)) (tfBG_le hfyG hOfy)
            (hfyy.trans hyE) (hgfy.trans_lt hgx)
        have hp : vR (vaFpL (tlLev E) z) x + vR (z - (vaFpL (tlLev E) z + 1)) x <
            vR (vaFpL (tlLev E) (tlI (tlLev E) E)) x :=
          (inE_indec hfyE).add_lt
            (vs_mono hE hBE hlim hIH hx hx1 hflt (hfyy.trans hyE) hgfz (hgfy.trans_lt hgx))
            (vs_mono hE hBE hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hzfy) (hfyy.trans hyE) hgoz
              (hgfy.trans_lt hgx))
        exact hp.trans_le le_self_add
      · -- the same largest fixed point: the offsets are ordered
        have hfz' : vaFpL (tlLev E) (tlI (tlLev E) E) < z := by rw [← hfeq]; exact hfzz
        have hgoz' : yrG (z - (vaFpL (tlLev E) (tlI (tlLev E) E) + 1)) < x := by rw [← hfeq]; exact hgoz
        rw [hfeq]
        exact (add_lt_add_iff_left _).2 (vs_mono hE hBE hlim hIH hx hx1
          (vs_sub_lt (Order.add_one_le_of_lt hfz') hzy) ((Ordinal.sub_le_self _ _).trans_lt hyE) hgoz'
          (hgoy.trans_lt hgx))
    · -- no fixed point of `F_λ` below `z`: `z < f_y`
      rw [vK_nofix hFz]
      have hzfy : z < vaFpL (tlLev E) (tlI (tlLev E) E) := by
        rcases lt_or_ge z (vaFpL (tlLev E) (tlI (tlLev E) E)) with h | h
        · exact h
        · exfalso
          rcases h.lt_or_eq with h' | h'
          · exact hFz ⟨_, hffy, hOfy, h'⟩
          · exact hzr (by rw [← h']; exact hffy)
      exact (vs_mono hE hBE hlim hIH hx hx1 ((Ordinal.sub_le_self _ _).trans_lt hzfy) (hfyy.trans hyE) (hg0 hFz)
        (hgfy.trans_lt hgx)).trans_le le_self_add
  · -- no fixed point below `y`, none below `z`
    have hFz : ¬ VaFixL (tlLev E) z := fun ⟨f, h1, h2, h3⟩ => hFy ⟨f, h1, h2, h3.trans hzy⟩
    rw [vK_nofix hFy, vK_nofix hFz]
    exact vs_mono hE hBE hlim hIH hx hx1 (vs_sub_lt' hz0 hzy) ((Ordinal.sub_le_self _ _).trans_lt hyE) (hg0 hFz)
      ((vs_fix_gate_0 hA hi hEX).trans_lt hgx)

/-- **Every code below the fixed point reads below `D(x)`.** -/
theorem vs_fx_lt (hgx : max ω (yrQE E) < x) : ∀ c, c < E → yrG c < x → vR c x < vA E x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hfixE, hl1, hlE, hyE, hFy, hne, -, hy0⟩ := vs_fx_dat hEX hA hi
  obtain ⟨hVeq, hcl, hVT, hVE, hxV, hVX, hV1⟩ := vs_fx_V hE hBE hEX hlim hIH hA hi hx hx1 hgx
  obtain ⟨hgl, hlT, hl1', hlX, hv1, hKT, hK1, hKX⟩ := vs_fx_parts hE hBE hEX hlim hIH hA hi hx hx1 hgx
  have hglA : ∀ a t, a < vA E x → t < vA E x → glA a t x < vA E x := by
    intro a t ha ht
    have hmT : max a t ∈ Tset x := vz_T_down hx hx1 hVT hV1 (max_lt ha ht).le
    have hm1 : max a t < Om1 := (max_lt ha ht).trans hV1
    have hq := gmq_gt hx hx1 hmT hm1
    exact (xkA_lt hx hx1 hmT hm1 ((le_max_left _ _).trans_lt hq) ((le_max_right _ _).trans_lt hq)).trans
      (hcl _ hmT (max_lt ha ht))
  have hDB : ywV 1 0 x ≤ vA E x := (ywBG hx hx1).2.2 _ hxV hcl
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < tfBG
  · rw [vR_yr c hcB x]; exact (zmYr.lt c x hx hx1 hcB hg).trans_le hDB
  have hcB' : tfBG ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  rw [yrG_dec hGc] at hg
  have hgQE : yrQE (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : yrG (log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : yrG (c / guE c ^ log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : yrG (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  have hgeG : yrG (guE c) < x := by rw [yrG_base heE hGe]; exact hgQE
  have hA' : vA (guE c) x < vA E x := by
    rcases vs_atom_cases heB with hB | ⟨hAc, hjB, hjE'⟩ | hnA
    · -- a fixed point `F'` of `Γ` below `E`: compare the levels
      have hF'fix : gamma (guE c) = guE c := by rw [hB]; exact vs_FB_fix heB
      have hOF' : Om1 < guE c := tfBG_gt.trans_le heB
      have hAF : YhAt (guE c) := ⟨by rw [← hF'fix]; exact Lq.lq_gamma_SC _, hOF'⟩
      have hiF : ¬ yhJ (guE c) < guE c := by
        have h := yhJ_gcG (guE c); rw [vs_gcG_fix hF'fix hOF'] at h; rw [h]; exact lt_irrefl _
      have hF'E : guE c < E := hec.trans_lt hc
      have hF'X : guE c < tlX := hF'E.trans hEX
      obtain ⟨-, hμF, hzF, hFz, hzne⟩ := vs_fix_data hAF hiF hF'X
      have hgxF : max ω (yrQE (guE c)) < x := max_lt hωx hgQE
      obtain ⟨hgμ, hμT, hμ1', hK'T, hK'1, hRF⟩ :=
        vs_fx_partsOf hE hBE hEX hlim hIH hA hi hx hx1 hAF hiF hF'E hgxF
      -- the parts of `F'` read below `D(x)`
      have hK' : vK (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c)) x < vA E x := by
        by_cases hF : VaFixL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c))
        · rw [vK_fix hF]
          obtain ⟨hgf, hgo⟩ := vs_fix_gate_f hAF hiF hF'X hF
          obtain ⟨-, -, hfy⟩ := vs_fpL_mem hzne hF
          have h1 := (hfy.trans hzF).trans_le hec
          have h2 : tlI (tlLev (guE c)) (guE c) - (vaFpL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c)) + 1) < c :=
            ((Ordinal.sub_le_self _ _).trans_lt hzF).trans_le hec
          exact (inE_indec hVE).add_lt (IH _ h1 (h1.trans hc) (hgf.trans_lt hgxF))
            (IH _ h2 (h2.trans hc) (hgo.trans_lt hgxF))
        · rw [vK_nofix hF]
          have h2 : tlI (tlLev (guE c)) (guE c) - glY0 (tlLev (guE c)) < c :=
            ((Ordinal.sub_le_self _ _).trans_lt hzF).trans_le hec
          exact IH _ h2 (h2.trans hc) ((vs_fix_gate_0 hAF hiF hF'X).trans_lt hgxF)
      rw [← vR_base heE hGe, hRF, hVeq]
      rcases lt_trichotomy (tlLev (guE c)) (tlLev E) with hlt | heq | hgt
      · -- a lower level
        refine ywV_lt_lower hx hx1 hμT hμ1' hK'T hK'1 hlT hl1' hKT hK1
          (vs_mono hE hBE hlim hIH hx hx1 hlt hlE hgμ hgl) ?_
        rw [← hVeq]; exact hK'
      · -- the same level: `z < y`
        have hzy : tlI (tlLev (guE c)) (guE c) < tlI (tlLev E) E := by
          have h1 : rhF (tlLev E) (tlI (tlLev (guE c)) (guE c)) = guE c := by rw [← heq]; exact hFz
          have h : rhF (tlLev E) (tlI (tlLev (guE c)) (guE c)) < rhF (tlLev E) (tlI (tlLev E) E) := by
            rw [h1, hFy]; exact hF'E
          exact (rhF_lt _).1 h
        have hz0 : glY0 (tlLev (guE c)) ≤ tlI (tlLev (guE c)) (guE c) := vs_y0_le (by rw [hFz]; exact hOF')
        have hgf' : VaFixL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c)) →
            yrG (vaFpL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c))) < x ∧
              yrG (tlI (tlLev (guE c)) (guE c) - (vaFpL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c)) + 1)) < x :=
          fun hF => ⟨(vs_fix_gate_f hAF hiF hF'X hF).1.trans_lt hgxF, (vs_fix_gate_f hAF hiF hF'X hF).2.trans_lt hgxF⟩
        have hg0' : ¬ VaFixL (tlLev (guE c)) (tlI (tlLev (guE c)) (guE c)) →
            yrG (tlI (tlLev (guE c)) (guE c) - glY0 (tlLev (guE c))) < x :=
          fun _ => (vs_fix_gate_0 hAF hiF hF'X).trans_lt hgxF
        rw [heq] at hzy hz0 hzne hgf' hg0' hK'T hK'1 ⊢
        exact ywV_lt_same hx hx1 hK'T hlT hl1' hKT hK1
          (vs_fx_Kmono hE hBE hEX hlim hIH hA hi hx hx1 hgx hzy hz0 hzne hgf' hg0')
      · -- a higher level: `F'` is a fixed point of `F_λ` below `y`
        have hfixl : rhF (tlLev E) (guE c) = guE c := by
          have h := rhF_fix_lower hgt (tlI (tlLev (guE c)) (guE c))
          rwa [hFz] at h
        have hF'y : guE c < tlI (tlLev E) E := by
          have h : rhF (tlLev E) (guE c) < rhF (tlLev E) (tlI (tlLev E) E) := by rw [hfixl, hFy]; exact hF'E
          exact (rhF_lt _).1 h
        have hFy' : VaFixL (tlLev E) (tlI (tlLev E) E) := ⟨guE c, hfixl, hOF', hF'y⟩
        obtain ⟨hgf, -⟩ := vs_fix_gate_f hA hi hEX hFy'
        obtain ⟨-, -, hfy⟩ := vs_fpL_mem hne hFy'
        have hF'f : guE c ≤ vaFpL (tlLev E) (tlI (tlLev E) E) := by
          unfold vaFpL; exact le_csSup ⟨_, fun _ h => h.2.2.le⟩ ⟨hfixl, hOF', hF'y⟩
        have h1 : vR (guE c) x ≤ vR (vaFpL (tlLev E) (tlI (tlLev E) E)) x :=
          vs_le_mono hE hBE hlim hIH hx hx1 hF'f (hfy.trans hyE) hgeG (hgf.trans_lt hgx)
        have h2 : vR (vaFpL (tlLev E) (tlI (tlLev E) E)) x ≤ vK (tlLev E) (tlI (tlLev E) E) x := by
          rw [vK_fix hFy']; exact le_self_add
        have h3 := (ywV_facts hx hx1 hlT hl1' hKT hK1).2.2.2.2.2.1
        rw [← hRF]
        exact (h1.trans h2).trans_lt h3
    · -- an atom `Γ(j)` past its segment base: the index reading is below `D(x)`
      rw [vA_atom hAc hjE', vs_vI heB hjB hjE'.le]
      have hFe : vaFB (guE c) < c := hjB.trans (hjE'.trans_le hec)
      have hgF : yrG (vaFB (guE c)) < x := (vs_FB_gate _ heB).trans_lt (max_lt hωx hgeG)
      have hgj : yrG (yhJ (guE c)) < x := by rw [yrQE_atom hAc hjE'] at hgQE; exact yrG_of_Q hωx hgQE
      have hgo := (vs_off_gate (vs_FB_E heB) (va_G_le_BG.trans (vs_FB_ge heB)) hjB).trans_lt (max_lt hωx hgj)
      have ho : yhJ (guE c) - (vaFB (guE c) + 1) < c := (Ordinal.sub_le_self _ _).trans_lt (hjE'.trans_le hec)
      have hI : vR (vaFB (guE c)) x + vR (yhJ (guE c) - (vaFB (guE c) + 1)) x < vA E x :=
        (inE_indec hVE).add_lt (IH _ hFe (hFe.trans hc) hgF) (IH _ ho (ho.trans hc) hgo)
      exact hcl _ (vz_T_down hx hx1 hVT hV1 hI.le) hI
    · rw [vA_psi hnA]
      have hK := yh_lev_lt hGc hnA
      have hI := yh_idx_lt hGc hnA
      rw [yrQE_psi hnA] at hgQE
      exact hglA _ _ (IH _ hK (hK.trans hc) (yrG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI (hI.trans hc) (yrG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vR_dec hGc]
  exact (inE_indec hVE).add_lt (InE.mul_lt hVE (zm_opow_lt hVE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Va
