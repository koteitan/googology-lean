import Googology.Trans.PoR.InaccPsi.R2.GkU3

/-!
# CODES BELOW `ζ_{Ω₁+1}`: cofinality and countability

* `gu_cofPow` (**the codes below `E^κ` have readings cofinal in `ε_{x+n(x)}^{κ(x)}`**, `E = ε_{Ω₁+n}`), `guR_cof`
  (**cofinality**, one induction over all brackets), `guR_cofE` (the field `cof` of a reading system);
* `gu_count` (the codes below `c ≤ ζ_{Ω₁+1}` with gate below `y` are countably many).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx

/-- **The codes below `E^κ` have cofinal readings in `ε_{x+n(x)}^{κ(x)}`**, once cofinality holds below `N > κ, n`. -/
theorem gu_cofPow {N n : Ordinal.{0}} (hC : ∀ j, j < N → GuCof x j) (hn1 : 1 ≤ n) (hnN : n < N) (hnB : n < guB)
    (hgn : guG n < x) : ∀ κ, κ < N → κ ≠ 0 → κ < guB → guG κ < x → κ < eN (evA Om1 n) →
    ∀ ν, ν < guA x (guR n x) ^ guR κ x → ∃ t, t < evA Om1 n ^ κ ∧ guG t < x ∧ ν < guR t x := by
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  set B := guA x (guR n x) with hBdef
  have hBE : InE B := guA_E _ _
  have hbase := gu_baseCof hx hn1 hnB hgn (hC n hnN)
  have hEN : eN E = evA Om1 (n + 1) := by rw [hEdef, evA_add_one]
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ hκE ν hν
  have hEκ : E ≤ E ^ κ := by
    calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ E ^ κ := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    have hκ'B : κ' + 1 < guB := hs ▸ hκB
    have r1 := guR_succ κ' hκ'B x
    have r2 := guG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : guG κ' < x := r2.trans_lt hgκ
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, guR_zero, opow_zero, one_mul] at hν
      obtain ⟨t, ht, hgt, hvt⟩ := hbase ν hν
      exact ⟨t, ht.trans_le hEκ, hgt, hvt⟩
    · have hne : B ^ guR κ' x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
      have hq : ν / B ^ guR κ' x < B := (Ordinal.div_lt hne).2 hν
      obtain ⟨t0, ht0, hgt0, hvt0⟩ := hbase _ hq
      have ht00 : t0 ≠ 0 := by
        rintro rfl; rw [guR_zero] at hvt0; exact absurd hvt0 (not_lt.2 zero_le)
      have hpow : E ^ κ' * t0 < E ^ κ := by
        rw [← hs, opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (opow_pos _ hE.pos)).2 ht0
      have hκpow : E ^ κ < eN E := gu_pow_lt_eN hE hκE
      have hv : E ^ κ' * t0 + 0 < evA Om1 (n + 1) := by rw [add_zero, ← hEN]; exact hpow.trans hκpow
      have hvB : E ^ κ' * t0 + 0 < guB := hv.trans (gu_evA_lt ((guB_lim).add_one_lt hnB))
      have hr0 : (0 : Ordinal.{0}) < E ^ κ' := opow_pos _ hE.pos
      refine ⟨E ^ κ' * t0 + 0, by rw [add_zero]; exact hpow, ?_, ?_⟩
      · rw [guG_cnf hn1 hκ'0 ht00 ht0 hr0 hv hvB, guG_zero]
        exact max_lt (max_lt ((guQ_le _).trans_lt hgn) ((guQ_le _).trans_lt hgκ'))
          (max_lt ((guQ_le _).trans_lt hgt0) (lt_of_le_of_lt zero_le hx.pos))
      · rw [guR_cnf hn1 hκ'0 ht00 ht0 hr0 hv hvB, guR_zero, add_zero]
        calc ν < B ^ guR κ' x * (ν / B ^ guR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (B ^ guR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ B ^ guR κ' x * guR t0 x := mul_le_mul_right (add_one_le_of_lt hvt0) _
  · have hlim := gu_lim_of_cof hx hl hκB hgκ (hC κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hBE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hC κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [guR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < B ^ guR κ' x :=
      hνμ.trans_le (opow_le_opow_right hBE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' (hκ'κ.trans hκE) ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right hE.pos hκ'κ.le), hgt, hvt⟩

include hx1

/-- **COFINALITY**: every `ν` below the reading of a code `c < ζ_{Ω₁+1}` is at most the reading of a smaller code with
gate below `x`. -/
theorem guR_cof : ∀ c, c < guB → GuCof x c := by
  have hωx := omega0_lt_inE hx
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hC : ∀ j, j < c → GuCof x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE] at hg
    rw [guR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := rdc_surj hx hx1.le hcE hg hν
    exact ⟨b, hb, by rw [guG_low (hb.trans hcE)]; exact hgb, by rw [guR_low (hb.trans hcE), eb]⟩
  obtain ⟨hn1, -, hcn, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gu_parts hcE hc
  obtain ⟨g0n, g0, g1, g2⟩ := gu_parts_g hωx hcE hc hg
  obtain ⟨q0n, q0, -, -⟩ := gu_parts_Q hcE hc hg
  have hEc : guE c = evA Om1 (guN c) := rfl
  rw [hEc] at hk hd0 hdE hr hdec hkc hrc hdc g0 g1 g2 q0
  set n := guN c with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  set B := guA x (guR n x) with hBdef
  have hBE : InE B := guA_E _ _
  have hcN' : c < eN E := by rw [hEdef, ← evA_add_one]; exact hcn
  rw [guR_dec hcE hc] at hν
  have hnf : ∀ d' t, d' ≠ 0 → d' < E → t < E ^ k → E ^ k * d' + t < c ∨ E ^ k * d' + t = c →
      E ^ k * d' + t < evA Om1 (n + 1) ∧ E ^ k * d' + t < guB := by
    intro d' t _ _ _ h
    have hle : E ^ k * d' + t ≤ c := by rcases h with h | h; exact h.le; exact h.le
    exact ⟨hle.trans_lt hcn, hle.trans_lt hc⟩
  have hgate : ∀ d' t, d' ≠ 0 → d' < E → t < E ^ k → E ^ k * d' + t ≤ c → guG d' < x → guG t < x →
      guG (E ^ k * d' + t) < x := by
    intro d' t hd' hd'E ht hle hgd' hgt
    have hv : E ^ k * d' + t < evA Om1 (n + 1) := hle.trans_lt hcn
    rw [guG_cnf hn1 hk hd' hd'E ht hv (hle.trans_lt hc)]
    exact max_lt (max_lt q0n q0) (max_lt ((guQ_le _).trans_lt hgd') hgt)
  rcases lt_or_ge ν (B ^ guR k x * guR d x) with hν1 | hν1
  · have hne : B ^ guR k x ≠ 0 := opow_ne_zero _ hBE.pos.ne'
    have hμ : ν / B ^ guR k x < guR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := hC d hdc g1 _ hμ
    have hρ : ν % B ^ guR k x < B ^ guR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := gu_cofPow hx hC hn1 hnc hnB g0n k hkc hk (hkc.trans hc) g0 (hkc.trans hcN') _ hρ
    have hd'E : d' < E := hd'd.trans hdE
    have hkd : E ^ k ≤ c := by
      rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    have hνe : ν = B ^ guR k x * (ν / B ^ guR k x) + ν % B ^ guR k x := (Ordinal.div_add_mod ν _).symm
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hd'0, guR_zero] at ed'
      rw [hνe, nonpos_iff_eq_zero.1 ed', mul_zero, zero_add]; exact hvt.le
    · have hlt : E ^ k * d' + t < c := by
        calc E ^ k * d' + t < E ^ k * d' + E ^ k := (add_lt_add_iff_left _).2 htk
          _ = E ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ E ^ k * d := mul_le_mul_right (add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      obtain ⟨hv, hvB⟩ := hnf d' t hd'0 hd'E htk (Or.inl hlt)
      refine ⟨E ^ k * d' + t, hlt, hgate d' t hd'0 hd'E htk hlt.le hgd' hgt, ?_⟩
      rw [guR_cnf hn1 hk hd'0 hd'E htk hv hvB, hνe]
      exact add_le_add (mul_le_mul_right ed' _) hvt.le
  · have e : B ^ guR k x * guR d x + (ν - B ^ guR k x * guR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - B ^ guR k x * guR d x < guR r x := by
      rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hC r hrc g2 _ hν'
    have hb'k : b' < E ^ k := hb'r.trans hr
    have hlt : E ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    obtain ⟨hv, hvB⟩ := hnf d b' hd0 hdE hb'k (Or.inl hlt)
    refine ⟨E ^ k * d + b', hlt, hgate d b' hd0 hdE hb'k hlt.le g1 hgb', ?_⟩
    rw [guR_cnf hn1 hk hd0 hdE hb'k hv hvB, ← e]
    exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem guR_cofE {c : Ordinal.{0}} (hc : c < guB) (hEc : gfE < c) (hg : guG c < x) {ν : Ordinal.{0}}
    (hν : ν < guR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ guG b < x ∧ ν ≤ guR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := guR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [guG_E]; exact hx.pos, ?_⟩
    rw [guG_low hbE] at hgb
    rw [guR_low hbE] at hνb
    rw [guR_E]
    exact hνb.trans (rdc_lt_eN hx b hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-- **The codes below `c ≤ ζ_{Ω₁+1}` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem gu_count {c y : Ordinal.{0}} (hc : c ≤ guB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // guG b.1 < y} := by
  have hq1 : gq 0 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gfq0_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // guG b.1 < y} → Iio (gq 0 y) := fun b =>
    ⟨guR b.1.1 y, guR_lt0 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : guR b.1.1 y = guR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (guR_mono hy (lt_of_lt_of_le b'.1.2 hc) h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (guR_mono hy (lt_of_lt_of_le b.1.2 hc) h b.2 b'.2).ne'

end Googology.Trans.PoR.InaccPsi.R2.Gk
