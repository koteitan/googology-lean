import Googology.Trans.PoR.InaccPsi.R2.TbRoad
import Googology.Trans.PoR.InaccPsi.R2.GmQ3
import Googology.Trans.PoR.InaccPsi.R2.SxGl

/-!
# Above `Γ_{x+1}²`: `ϑˣ(E) = ω^E`, Lemma EXACT for `ω^E`, and the codes `Γ_{Ω₁+1}·γ + c'` as offsets

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Between `Γ_{x+1}` and the next `ε`-number `ε_{Γ_{x+1}+1}` there is no `ε`-number, so [W07a] Lemma 4.2 (`vt_wbar`,
through `wbar_eq` with the pseudo-base `Γ_{x+1}`) gives `ϑˣ(E) = ω^E` for every `E ∈ [Γ_{x+1}+ω, ε_{Γ_{x+1}+1})`,
and [W07a] Def 5.1 (`pi_vt`) gives Lemma EXACT for `ω^E` whenever `E` and `π(E)` lie in these ranges.

* `tbExp_add`, `tbExp_lt`, `tbExp_opow_mul` (the last exponent `e(·)` of sums and of `ω^E·n`);
* `tbVt_eq` (**`ϑˣ(E) = ω^E`**), `tbOpow_pi` (**`π_{σ,ρ}(ω^E) = ω^{π_{σ,ρ}(E)}`**);
* `tbMq_lt_sq` (**the readings of the codes `c < Γ_{Ω₁+1}²` of `R2.GmQ0` lie below `Γ_{x+1}²`**), `tbMq_ex`
  (**every `ν < Γ_{x+1}²` is such a reading**, from `Sx.sxGl_ex`), `tbMq_two` (the code `Γ_{Ω₁+1}·2` reads
  `Γ_{x+1}·2`, gate `0`), `tbMq_ld` (**Lemma EXACT for the last exponent of every limit code below
  `Γ_{Ω₁+1}²`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## The last exponent -/

/-- `e(y + z) = e(z)` when `ω^{e(z)+1} ∣ y` and `z ≠ 0`. -/
theorem tbExp_add {y z : Ordinal.{0}} (hz : z ≠ 0) (hd : ω ^ (cdExp z + 1) ∣ y) :
    cdExp (y + z) = cdExp z := by
  have hd0 : ω ^ cdExp z ∣ y := (opow_dvd_opow ω le_self_add).trans hd
  have hyz : y + z ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hz) le_add_self).ne'
  refine cdExp_eq hyz ((Ordinal.dvd_add_iff hd0).2 (cdExp_dvd hz)) ?_
  rw [Ordinal.dvd_add_iff hd]
  exact cdExp_not_dvd hz

/-- `e(z) < E` for `0 < z < ω^E`. -/
theorem tbExp_lt {z E : Ordinal.{0}} (hz : z ≠ 0) (h : z < ω ^ E) : cdExp z < E :=
  (opow_lt_opow_iff_right one_lt_omega0).1 ((Ordinal.le_of_dvd hz (cdExp_dvd hz)).trans_lt h)

/-- `e(ω^E·n) = E` for `0 < n < ω`. -/
theorem tbExp_opow_mul {E n : Ordinal.{0}} (hn0 : 0 < n) (hn : n < ω) : cdExp (ω ^ E * n) = E := by
  have hp : (0 : Ordinal.{0}) < ω ^ E := opow_pos E omega0_pos
  have hne : ω ^ E * n ≠ 0 := (mul_pos hp hn0).ne'
  refine cdExp_eq hne (dvd_mul_right _ _) fun hd => ?_
  have h1 := Ordinal.le_of_dvd hne hd
  have h2 : ω ^ E * n < ω ^ (E + 1) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ hp).2 hn
  exact absurd h1 (not_le.2 h2)

/-! ## `ϑˣ(E) = ω^E` above `Γ_{x+1} + ω` -/

/-- **`ϑˣ(E) = ω^E`** for `Γ_{x+1} + ω ≤ E < ε_{Γ_{x+1}+1}` ([W07a] Lemma 4.2 through `vt_wbar`, `wbar_eq` with the
pseudo-base `Γ_{x+1}`). -/
theorem tbVt_eq {x E : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : lgG x + ω ≤ E) (h2 : E < eN (lgG x)) :
    vt x E = ω ^ E := by
  obtain ⟨-, hxG, hG1, he, -⟩ := lgG_facts hx hx1
  obtain ⟨β, hEβ⟩ : ∃ β, E = lgG x + β := ⟨E - lgG x, (Ordinal.add_sub_cancel_of_le (le_self_add.trans h1)).symm⟩
  have hωβ : ω ≤ β := by
    by_contra h
    push Not at h
    have : E < lgG x + ω := by rw [hEβ]; exact (add_lt_add_iff_left _).2 h
    exact absurd h1 (not_le.2 this)
  have hE1 : E < Om1 := h2.trans (eN_lt_Om1K hG1)
  have hωE : ω ≤ E := hωβ.trans (le_add_self.trans_eq hEβ.symm)
  have hxa : x + lgG x = lgG x := by
    have := add_omega0_opow (a := x) (b := lgG x) (by rw [he]; exact hxG)
    rwa [he] at this
  have h1β : 1 + β = β := one_add_of_omega0_le hωβ
  calc vt x E = vt x (1 + E) := by rw [one_add_of_omega0_le hωE]
    _ = wbar (x + E) := vt_wbar hx hx1 hE1
    _ = wbar (lgG x + β) := by rw [hEβ, ← add_assoc, hxa]
    _ = ω ^ (lgG x + 1 + β) := wbar_eq he β fun u hu1 hu2 huE => by
        rw [add_assoc, h1β, ← hEβ] at hu2
        exact absurd (hu2.trans_lt h2) (not_lt.2 (eN_le hu1 huE))
    _ = ω ^ E := by rw [add_assoc, h1β, hEβ]

/-- **Lemma EXACT for `ω^E`**: `π_{σ,ρ}(ω^E) = ω^{π_{σ,ρ}(E)}` when `E ∈ Tᵖ[σ]` lies in
`[Γ_{ρ+1} + ω, ε_{Γ_{ρ+1}+1})` and `π_{σ,ρ}(E)` in `[Γ_{σ+1} + ω, ε_{Γ_{σ+1}+1})` ([W07a] Def 5.1, fourth clause). -/
theorem tbOpow_pi {σ ρ E : Ordinal.{0}} (hB : Bases σ ρ) (hET : E ∈ TB ρ σ) (h1 : lgG ρ + ω ≤ E)
    (h2 : E < eN (lgG ρ)) (h1' : lgG σ + ω ≤ pi σ ρ E) (h2' : pi σ ρ E < eN (lgG σ)) :
    ω ^ E ∈ TB ρ σ ∧ pi σ ρ (ω ^ E) = ω ^ pi σ ρ E := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hE1 : E < Om1 := h2.trans (eN_lt_Om1K (lgG_facts hB.2.1 hρ1).2.2.1)
  have hv := tbVt_eq hB.2.1 hρ1 h1 h2
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hET.1 hE1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hET.2⟩, ?_⟩
  rw [← hv, pi_vt hB hET hE1, tbVt_eq hB.1 hσ1 h1' h2']

/-! ## The codes below `Γ_{Ω₁+1}²` (`R2.GmQ0`) as offsets -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The readings of the codes `c < Γ_{Ω₁+1}²` lie below `Γ_{x+1}²`.** -/
theorem tbMq_lt_sq {c : Ordinal.{0}} (hc : c < mqB) (hg : mqG c < x) : mqR c x < lgG x * lgG x := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  obtain ⟨hgγ, hgc⟩ := mq_gates hx hx1 hg
  rw [mqR_split γ hc' x]
  refine (mq_lt_next hx hx1 hγ hc' hgγ hgc).trans_le (mul_le_mul_right ?_ _)
  exact Order.add_one_le_of_lt (glR_lt_G hx hx1 hγ hgγ)

/-- **Every `ν < Γ_{x+1}²` is the reading of a code `c < Γ_{Ω₁+1}²` with gate below `x`.** -/
theorem tbMq_ex {ν : Ordinal.{0}} (hν : ν < lgG x * lgG x) : ∃ c, c < mqB ∧ mqG c < x ∧ mqR c x = ν := by
  have hG0 : lgG x ≠ 0 := (lgG_pos hx hx1).ne'
  have hq : ν / lgG x < lgG x := (Ordinal.lt_mul_iff_div_lt hG0).1 hν
  have hr : ν % lgG x < lgG x := Ordinal.mod_lt ν hG0
  obtain ⟨g, hg, hgg, hrg⟩ := Sx.sxGl_ex hx hx1 _ hq
  obtain ⟨c', hc', hgc', hrc'⟩ := Sx.sxGl_ex hx hx1 _ hr
  refine ⟨gcG 0 * g + c', ?_, ?_, ?_⟩
  · calc gcG 0 * g + c' < gcG 0 * g + gcG 0 := (add_lt_add_iff_left _).2 hc'
      _ = gcG 0 * (g + 1) := by rw [mul_add_one]
      _ ≤ gcG 0 * gcG 0 := mul_le_mul_right (Order.add_one_le_of_lt hg) _
  · rw [mqG_split g hc']; exact max_lt ((glQ_le g).trans_lt hgg) hgc'
  · rw [mqR_split g hc' x, hrg, hrc']; exact Ordinal.div_add_mod ν (lgG x)

end Base

/-- **The code `Γ_{Ω₁+1}·2` reads `Γ_{x+1}·2`**, with gate `0`. -/
theorem tbMq_two (x : Ordinal.{0}) :
    gcG 0 + gcG 0 < mqB ∧ mqR (gcG 0 + gcG 0) x = lgG x * 2 ∧ mqG (gcG 0 + gcG 0) = 0 := by
  have e : gcG 0 + gcG 0 = gcG 0 * (2 : ℕ) + 0 := by
    rw [add_zero, show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
  have h2 : glQ ((2 : ℕ) : Ordinal.{0}) = 0 := by unfold glQ; rw [if_pos (natCast_lt_omega0 2)]
  refine ⟨?_, ?_, ?_⟩
  · rw [e, add_zero]
    exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 ((natCast_lt_omega0 2).trans (omega0_lt_inE gl_G0_E))
  · rw [e, mqR_split _ gl_G0_E.pos x, glR_nat, glR_zero, add_zero, Nat.cast_ofNat]
  · rw [e, mqG_split _ gl_G0_E.pos, h2, glG_zero, max_self]

/-- The last exponent of the reading of a limit code `Γ_{Ω₁+1}·γ + c'` (`0 < c'`) is that of `c'(x)`. -/
theorem tbMq_exp_rest {x γ c' : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc' : c' < gcG 0) (hc0 : c' ≠ 0)
    (hg : glG c' < x) : cdExp (lgG x * glR γ x + glR c' x) = cdExp (glR c' x) := by
  have hE := (lgG_facts hx hx1).2.2.2.1
  have hz0 : glR c' x ≠ 0 := by
    have := glR_mono hx hx1 hc' (pos_iff_ne_zero.2 hc0) hg (by rw [glG_zero]; exact hx.pos)
    rw [glR_zero] at this; exact this.ne'
  have hzG : glR c' x < ω ^ lgG x := by rw [hE]; exact glR_lt_G hx hx1 hc' hg
  refine tbExp_add hz0 ?_
  have h1 : ω ^ (cdExp (glR c' x) + 1) ∣ ω ^ lgG x :=
    opow_dvd_opow ω (Order.add_one_le_of_lt (tbExp_lt hz0 hzG))
  rw [hE] at h1
  exact h1.trans (dvd_mul_right _ _)

/-- **Lemma EXACT for the last exponent of every limit code `c < Γ_{Ω₁+1}²`** (gate below `σ`). -/
theorem tbMq_ld {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hl : IsSuccLimit c) (hc : c < mqB) (hg : mqG c < σ) :
    cdExp (mqR c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (mqR c ρ)) = cdExp (mqR c σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  have hgc' : glG c' < σ := lt_of_le_of_lt (le_max_right _ _) hg
  rw [mqR_split γ hc' ρ, mqR_split γ hc' σ]
  rcases eq_or_ne c' 0 with rfl | hc0
  · -- `c = Γ_{Ω₁+1}·γ`
    rw [glR_zero, glR_zero, add_zero, add_zero]
    rcases Ordinal.zero_or_succ_or_isSuccLimit γ with h0 | ⟨d, hd⟩ | hγl
    · subst h0
      exact absurd hl (by rw [mul_zero, add_zero]; exact not_isSuccLimit_bot)
    · have hd' : γ = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
      have hexp : ∀ y, InE y → y < Om1 → cdExp (lgG y * glR γ y) = lgG y := fun y hy hy1 => by
        have hE := (lgG_facts hy hy1).2.2.2.1
        have e : lgG y * glR γ y = lgG y * glR d y + ω ^ lgG y := by
          rw [hd', glR_succ_all, mul_add_one, hE]
        rw [e]
        exact Ge.lg_add_opow (by rw [hE]; exact dvd_mul_right _ _)
      rw [hexp ρ hB.2.1 hρ1, hexp σ hB.1 hσ1]
      exact mg_lgG_pi hB
    · obtain ⟨cp, lp, T, -, -, hdec, hpi⟩ := gl_ld γ hγl hγ
      have hωγ : ω ≤ γ := omega0_le_of_isSuccLimit hγl
      have hgγ : glG γ < σ := by
        have := lt_of_le_of_lt (le_max_left _ _) hg; rwa [mq_glQ_inf hωγ] at this
      have hexp : ∀ y, InE y → y < Om1 → glG γ < y → cdExp (lgG y * glR γ y) = lgG y + T y := by
        intro y hy hy1 hgy
        have hE := (lgG_facts hy hy1).2.2.2.1
        obtain ⟨e1, e2, -, -⟩ := hdec y hy hy1 hgy
        have e : lgG y * glR γ y = lgG y * lp y + ω ^ (lgG y + T y) := by
          rw [e1, mul_add, opow_add, hE]
        rw [e]
        refine Ge.lg_add_opow ?_
        rw [opow_add]
        nth_rewrite 2 [← hE]
        exact mul_dvd_mul_left _ e2
      rw [hexp ρ hB.2.1 hρ1 (hgγ.trans hB.2.2.1), hexp σ hB.1 hσ1 hgγ]
      obtain ⟨h1, h2⟩ := mg_lgG_pi hB
      obtain ⟨h3, h4⟩ := hpi σ ρ hB hgγ
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      exact ⟨h5, by rw [h6, h2, h4]⟩
  · -- `c' ≠ 0`: `c'` is a limit, the last exponent is that of `c'(x)`
    have hl' : IsSuccLimit c' := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit c' with h0 | ⟨d, hd⟩ | hlim
      · exact absurd h0 hc0
      · exfalso
        have hd' : c' = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
        have hlt : gcG 0 * γ + d < gcG 0 * γ + c' := by
          rw [hd']; exact (add_lt_add_iff_left _).2 (lt_add_one d)
        have := hl.succ_lt hlt
        rw [succ_eq_add_one, add_assoc, ← hd'] at this
        exact lt_irrefl _ this
      · exact hlim
    rw [tbMq_exp_rest hB.2.1 hρ1 hc' hc0 (hgc'.trans hB.2.2.1), tbMq_exp_rest hB.1 hσ1 hc' hc0 hgc']
    exact Sx.sxGl_ld hB hl' hc' hgc'

end Googology.Trans.PoR.InaccPsi.R2.Tb
