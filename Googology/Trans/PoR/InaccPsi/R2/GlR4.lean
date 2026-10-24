import Googology.Trans.PoR.InaccPsi.R2.GlR3

/-!
# CODES BELOW `Γ_{Ω₁+1}`: cofinality and countability

* `gl_cofPow` (**the codes below `e^κ` have readings cofinal in `e(x)^{κ(x)}`**, `e` an `ε`-number code of any
  level), `glR_cof` (**cofinality**, one induction over all brackets and levels), `glR_cofE` (the field `cof` of a
  reading system);
* `gl_count` (the codes below `c ≤ Γ_{Ω₁+1}` with gate below `y` are countably many).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The codes below `e^κ` have cofinal readings in `e(x)^{κ(x)}`**, once cofinality holds below `N > κ` and at the
level and the index of `e`. -/
theorem gl_cofPow {N e : Ordinal.{0}} (hC : ∀ j, j < N → GlCof x j) (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0)
    (hge : glG e < x) (hcα : GlCof x (glK e)) (hcη : GlCof x (glI e)) :
    ∀ κ, κ < N → κ ≠ 0 → κ < gcG 0 → glG κ < x → κ < eN e →
    ∀ ν, ν < glR e x ^ glR κ x → ∃ t, t < e ^ κ ∧ glG t < x ∧ ν < glR t x := by
  set B := glR e x with hBdef
  have hBE : InE B := (gl_eps_read hx hx1 he hOe heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  have hbase := gl_baseCof hx hx1 he hOe heB hge hcα hcη
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ hκE ν hν
  have hEκ : e ≤ e ^ κ := by
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ e ^ κ := opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    have hκ'B : κ' + 1 < gcG 0 := hs ▸ hκB
    have r1 := glR_succ κ' hκ'B x
    have r2 := glG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : glG κ' < x := r2.trans_lt hgκ
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, glR_zero, opow_zero, one_mul] at hν
      obtain ⟨t, ht, hgt, hvt⟩ := hbase ν hν
      exact ⟨t, ht.trans_le hEκ, hgt, hvt⟩
    · have hne : B ^ glR κ' x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
      have hq : ν / B ^ glR κ' x < B := (Ordinal.div_lt hne).2 hν
      obtain ⟨t0, ht0, hgt0, hvt0⟩ := hbase _ hq
      have ht00 : t0 ≠ 0 := by
        rintro rfl; rw [glR_zero] at hvt0; exact absurd hvt0 (not_lt.2 zero_le)
      have hpow : e ^ κ' * t0 < e ^ κ := by
        rw [← hs, opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (opow_pos _ he.pos)).2 ht0
      have hκpow : e ^ κ < eN e := gu_pow_lt_eN he hκE
      have hv : e ^ κ' * t0 + 0 < eN e := by rw [add_zero]; exact hpow.trans hκpow
      have hvB : e ^ κ' * t0 + 0 < gcG 0 := hv.trans_le (eN_le heB gl_G0_E)
      have hr0 : (0 : Ordinal.{0}) < e ^ κ' := opow_pos _ he.pos
      refine ⟨e ^ κ' * t0 + 0, by rw [add_zero]; exact hpow, ?_, ?_⟩
      · rw [glG_cnf he hOe hκ'0 ht00 ht0 hr0 hv hvB, glG_zero]
        have hgE := glG_base he hOe heB
        rw [hgE] at hge
        exact max_lt (max_lt hge ((glQ_le _).trans_lt hgκ'))
          (max_lt ((glQ_le _).trans_lt hgt0) (lt_of_le_of_lt zero_le hx.pos))
      · rw [glR_cnf he hOe hκ'0 ht00 ht0 hr0 hv hvB, glR_zero, add_zero, ← glR_base he hOe heB]
        calc ν < B ^ glR κ' x * (ν / B ^ glR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (B ^ glR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ B ^ glR κ' x * glR t0 x := mul_le_mul_right (add_one_le_of_lt hvt0) _
  · have hlim := gl_lim_of_cof hx hx1 hl hκB hgκ (hC κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hBE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hC κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [glR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < B ^ glR κ' x :=
      hνμ.trans_le (opow_le_opow_right hBE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' (hκ'κ.trans hκE) ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right he.pos hκ'κ.le), hgt, hvt⟩

/-- **COFINALITY**: every `ν` below the reading of a code `c < Γ_{Ω₁+1}` is at most the reading of a smaller code
with gate below `x`. -/
theorem glR_cof : ∀ c, c < gcG 0 → GlCof x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hC : ∀ j, j < c → GlCof x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE] at hg
    rw [glR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := rdc_surj hx hx1.le hcE hg hν
    exact ⟨b, hb, by rw [glG_low (hb.trans hcE)]; exact hgb, by rw [glR_low (hb.trans hcE), eb]⟩
  -- an `ε`-number code: the base cofinality
  by_cases hcI : InE c
  · have hOc : Om1 < c := Om1_lt_eW.trans_le hcE
    have hkc := (glData_spec hcI hOc hc).2.1
    have hηc := (glData_spec hcI hOc hc).2.2.1
    obtain ⟨t, htc, hgt, hνt⟩ := gl_baseCof hx hx1 hcI hOc hc hg (hC _ hkc) (hC _ hηc) ν hν
    exact ⟨t, htc, hgt, hνt.le⟩
  have hEc := gl_E_lt_self hcE hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0n, g0, g1, g2⟩ := gl_parts_g hωx hcE hc hg
  obtain ⟨q0n, q0, -, -⟩ := gl_parts_Q hcE hc hg
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hOe : Om1 < e := gl_Om1_lt_E hcE
  have heB : e < gcG 0 := hEc.trans hc
  have hge : glG e < x := gl_E_g hcE hc hg
  set k := log e c with hkdef
  set d := c / e ^ k with hddef
  set r := c % e ^ k with hrdef
  set B := glR e x with hBdef
  have hBE : InE B := (gl_eps_read hx hx1 he hOe heB hge).2.2.2.2.2.2.2.2.2.2.2.1
  have hcN' : c < eN e := gl_lt_eN hcE
  have hcη : GlCof x (glI e) := hC _ ((glData_spec he hOe heB).2.2.1.trans hEc)
  have hcα : GlCof x (glK e) := hC _ ((glData_spec he hOe heB).2.1.trans hEc)
  rw [glR_dec hcE hc, ← gl_At_eq hcE hc] at hν
  have hgate : ∀ d' t, d' ≠ 0 → d' < e → t < e ^ k → e ^ k * d' + t ≤ c → glG d' < x → glG t < x →
      glG (e ^ k * d' + t) < x := by
    intro d' t hd' hd'E ht hle hgd' hgt
    rw [glG_cnf he hOe hk hd' hd'E ht (hle.trans_lt hcN') (hle.trans_lt hc)]
    exact max_lt (max_lt q0n q0) (max_lt ((glQ_le _).trans_lt hgd') hgt)
  rcases lt_or_ge ν (B ^ glR k x * glR d x) with hν1 | hν1
  · have hne : B ^ glR k x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
    have hμ : ν / B ^ glR k x < glR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := hC d hdc g1 _ hμ
    have hρ : ν % B ^ glR k x < B ^ glR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := gl_cofPow hx hx1 hC he hOe heB hge hcα hcη k hkc hk (hkc.trans hc) g0
      (hkc.trans hcN') _ hρ
    have hd'E : d' < e := hd'd.trans hdE
    have hkd : e ^ k ≤ c := by
      rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    have hνe : ν = B ^ glR k x * (ν / B ^ glR k x) + ν % B ^ glR k x := (Ordinal.div_add_mod ν _).symm
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hd'0, glR_zero] at ed'
      rw [hνe, nonpos_iff_eq_zero.1 ed', mul_zero, zero_add]; exact hvt.le
    · have hlt : e ^ k * d' + t < c := by
        calc e ^ k * d' + t < e ^ k * d' + e ^ k := (add_lt_add_iff_left _).2 htk
          _ = e ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ e ^ k * d := mul_le_mul_right (add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      refine ⟨e ^ k * d' + t, hlt, hgate d' t hd'0 hd'E htk hlt.le hgd' hgt, ?_⟩
      rw [glR_cnf he hOe hk hd'0 hd'E htk (hlt.le.trans_lt hcN') (hlt.trans hc), ← glR_base he hOe heB, hνe]
      exact add_le_add (mul_le_mul_right ed' _) hvt.le
  · have e1 : B ^ glR k x * glR d x + (ν - B ^ glR k x * glR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - B ^ glR k x * glR d x < glR r x := by
      rw [← e1] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hC r hrc g2 _ hν'
    have hb'k : b' < e ^ k := hb'r.trans hr
    have hlt : e ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨e ^ k * d + b', hlt, hgate d b' hd0 hdE hb'k hlt.le g1 hgb', ?_⟩
    rw [glR_cnf he hOe hk hd0 hdE hb'k (hlt.le.trans_lt hcN') (hlt.trans hc), ← glR_base he hOe heB, ← e1]
    exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem glR_cofE {c : Ordinal.{0}} (hc : c < gcG 0) (hEc : gfE < c) (hg : glG c < x) {ν : Ordinal.{0}}
    (hν : ν < glR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ glG b < x ∧ ν ≤ glR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := glR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [glG_E]; exact hx.pos, ?_⟩
    rw [glG_low hbE] at hgb
    rw [glR_low hbE] at hνb
    rw [glR_E]
    exact hνb.trans (rdc_lt_eN hx b hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-- **The codes below `c ≤ Γ_{Ω₁+1}` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem gl_count {c y : Ordinal.{0}} (hc : c ≤ gcG 0) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // glG b.1 < y} := by
  have hq1 : gq 0 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gfq0_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // glG b.1 < y} → Iio (gq 0 y) := fun b =>
    ⟨glR b.1.1 y, glR_lt0 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : glR b.1.1 y = glR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (glR_mono hy hy1 (lt_of_lt_of_le b'.1.2 hc) h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (glR_mono hy hy1 (lt_of_lt_of_le b.1.2 hc) h b.2 b'.2).ne'

end Googology.Trans.PoR.InaccPsi.R2.Gl
