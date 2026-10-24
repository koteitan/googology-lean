import Googology.Trans.PoR.InaccPsi.R2.GiWr

/-!
# THE CODES BELOW `ε_{Ω₁+1}^ω`: cofinality, Lemma EXACT at every pair of bases, the code system

* `gw_cofPow` (**every `ν < ε_{x+1}^{n+1}` is below the reading of a code `t < E^{n+1}` with gate `≤ 1`**), `gwR_cof`,
  `gwR_cofE` (**every `ν` below the reading of a code `c > ε_{Ω₁+1}` is at most the reading of a code
  `b ∈ [ε_{Ω₁+1}, c)` with gate below `x`**);
* `gw_eAtomK_pi` (**Lemma EXACT for the atom `ω^{ε_{ρ+1}·(n+2)+β}`** at every pair of bases: it is
  `ϑ^ρ(ε_{ρ+1} + β')`, `β' = ε_{ρ+1}·(n+1) + β` (`vt_eN2`, [W07a] Lemma 4.2), and `π(ϑ^ρ(ξ)) = ϑ^σ(π ξ)`),
  `gw_eNr_pi` (`π(ε_{ρ+1}^n·γ(ρ)) = ε_{σ+1}^n·γ(σ)`, `n ≥ 1`), `gwR_pi` (**Lemma EXACT for every code below
  `ε_{Ω₁+1}^ω`**);
* `gw_count`, `gwK` (**THE CODE SYSTEM below `ε_{Ω₁+1}^ω`**).

No new axiom.  New definition: `gwK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx

theorem gw_one_lt_x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx

/-- **The codes below `E^{n+1}` have cofinal readings in `ε_{x+1}^{n+1}`.** -/
theorem gw_cofPow (n : ℕ) {ν : Ordinal.{0}} (hν : ν < eN x ^ ((n : Ordinal.{0}) + 1)) :
    ∃ t, t < gfE ^ ((n : Ordinal.{0}) + 1) ∧ gwG t < x ∧ ν < gwR t x := by
  have hne : eN x ^ (n : Ordinal.{0}) ≠ 0 := opow_ne_zero _ (eN_E x).pos.ne'
  have hEle : gfE ≤ gfE ^ ((n : Ordinal.{0}) + 1) := by
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right eW_E.pos le_add_self
  have hq : ν / eN x ^ (n : Ordinal.{0}) < eN x := by
    rw [Ordinal.div_lt hne, ← opow_succ, succ_eq_add_one]; exact hν
  obtain ⟨i, hi⟩ := ghTw_cof hx hq
  have htw := ghTw_lt i
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨ghTw i, htw.trans_le hEle, by rw [gwG_low htw]; exact (ghTw_gtc i).trans_lt (gw_one_lt_x hx), ?_⟩
    rw [gwR_low htw]
    simpa using hi
  · have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn.ne'
    have htw0 : ghTw i ≠ 0 := ghTw_pos i
    refine ⟨gfE ^ (n : Ordinal.{0}) * ghTw i + 0, ?_, ?_, ?_⟩
    · rw [add_zero, opow_add, opow_one]
      exact (mul_lt_mul_iff_right₀ (opow_pos _ eW_E.pos)).2 htw
    · rw [gwG_cnf hn0 htw0 htw (opow_pos _ eW_E.pos), gwG_zero, max_eq_left zero_le]
      exact (giQ_le _).trans_lt ((ghTw_gtc i).trans_lt (gw_one_lt_x hx))
    · rw [gwR_cnf hn0 htw0 htw (opow_pos _ eW_E.pos), gwR_low eW_E.pos, rdc_zero, add_zero]
      calc ν < eN x ^ (n : Ordinal.{0}) * (ν / eN x ^ (n : Ordinal.{0}) + 1) := by
            rw [mul_add_one]
            conv_lhs => rw [← Ordinal.div_add_mod ν (eN x ^ (n : Ordinal.{0}))]
            exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
        _ ≤ eN x ^ (n : Ordinal.{0}) * rdc (ghTw i) x := mul_le_mul_left' (Order.add_one_le_of_lt hi) _

include hx1

/-- **Cofinality**: every `ν` below the reading of a code `c` is at most the reading of a smaller code with gate below
`x`. -/
theorem gwR_cof : ∀ c, c < gwB → gwG c < x → ∀ ν, ν < gwR c x → ∃ b, b < c ∧ gwG b < x ∧ ν ≤ gwR b x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE] at hg
    rw [gwR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := rdc_surj hx hx1.le hcE hg hν
    exact ⟨b, hb, by rw [gwG_low (hb.trans hcE)]; exact hgb, by rw [gwR_low (hb.trans hcE), eb]⟩
  obtain ⟨hk, hd0, hdE, hr, hdec⟩ := gw_parts hcE
  obtain ⟨g1, g2⟩ := gw_parts_g hx hcE hg
  obtain ⟨n, hn⟩ := gw_nat_of_lt hc hcE
  set k := log gfE c with hkdef
  set d := c / gfE ^ k with hddef
  set r := c % gfE ^ k with hrdef
  have hrc : r < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  have hgc : gwG c = max (giQ d) (gwG r) := gwG_dec hcE
  rw [gwR_dec hcE] at hν
  rcases lt_or_ge ν (eN x ^ k * rdc d x) with hν1 | hν1
  · -- `ν = ε_{x+1}^k·μ + ρ'`, `μ < d(x)`
    have hne : eN x ^ k ≠ 0 := opow_ne_zero _ (eN_E x).pos.ne'
    have hμ : ν / eN x ^ k < rdc d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := rdc_surj hx hx1.le hdE g1 hμ
    have hρ : ν % eN x ^ k < eN x ^ k := Ordinal.mod_lt ν hne
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : Ordinal.{0}) + 1 := by
      have hn0 : n ≠ 0 := by rintro rfl; exact hk (by rw [hn, Nat.cast_zero])
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ⟨m, by rw [hn, Nat.cast_succ]⟩
    rw [hm] at hρ
    obtain ⟨t, htk, hgt, hvt⟩ := gw_cofPow hx m hρ
    rw [← hm] at htk hvt
    have hd'E : d' < gfE := hd'd.trans hdE
    have hνe : ν = eN x ^ k * rdc d' x + ν % eN x ^ k := by
      rw [ed']; exact (Ordinal.div_add_mod ν (eN x ^ k)).symm
    have hkd : gfE ^ k ≤ c := by
      rw [← hdec]
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hνe, hd'0, rdc_zero, mul_zero, zero_add]; exact hvt.le
    · refine ⟨gfE ^ k * d' + t, ?_, ?_, ?_⟩
      · calc gfE ^ k * d' + t < gfE ^ k * d' + gfE ^ k := (add_lt_add_iff_left _).2 htk
          _ = gfE ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ gfE ^ k * d := mul_le_mul_left' (Order.add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      · rw [gwG_cnf hk hd'0 hd'E htk]
        exact max_lt ((giQ_le _).trans_lt hgd') hgt
      · rw [gwR_cnf hk hd'0 hd'E htk, hνe]
        exact add_le_add le_rfl hvt.le
  · -- `ν = ε_{x+1}^k·d(x) + ν'`, `ν' < r(x)`
    have e : eN x ^ k * rdc d x + (ν - eN x ^ k * rdc d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - eN x ^ k * rdc d x < gwR r x := by
      rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := IH r hrc (hrc.trans hc) g2 _ hν'
    have hb'k : b' < gfE ^ k := hb'r.trans hr
    refine ⟨gfE ^ k * d + b', ?_, ?_, ?_⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    · rw [gwG_cnf hk hd0 hdE hb'k]
      exact max_lt ((le_max_left _ _).trans_lt (hgc ▸ hg)) hgb'
    · rw [gwR_cnf hk hd0 hdE hb'k, ← e]
      exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem gwR_cofE {c : Ordinal.{0}} (hc : c < gwB) (hEc : gfE < c) (hg : gwG c < x) {ν : Ordinal.{0}}
    (hν : ν < gwR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ gwG b < x ∧ ν ≤ gwR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := gwR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [gwG_E]; exact hx.pos, ?_⟩
    rw [gwG_low hbE] at hgb
    rw [gwR_low hbE] at hνb
    rw [gwR_E]
    exact hνb.trans (rdc_lt_eN hx b hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for the atom `ω^{ε_{ρ+1}·(n+2)+β}`** (`β ∈ Tᵖ[σ]`, `β < ε_{ρ+1}`) at every pair of bases. -/
theorem gw_eAtomK_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ)
    (hβe : β < eN ρ) :
    ω ^ (eN ρ * ((n + 2 : ℕ) : Ordinal.{0}) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * ((n + 2 : ℕ) : Ordinal.{0}) + β)) = ω ^ (eN σ * ((n + 2 : ℕ) : Ordinal.{0}) + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := gh_eN_pi hB
  have hπβ : pi σ ρ β < eN σ := by rw [← hpe]; exact (pi_bijOn hB).2 hβTB heTB hβe
  obtain ⟨hmTB, hmpi⟩ := gh_eNm_pi hB (n + 1)
  obtain ⟨h1, h2⟩ := pi_add hB hmTB hβTB
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB h1
  rw [h2, hmpi, hpe] at hpξ
  -- `ε·(n+2) + β = ε + (ε·(n+1) + β)` and `1 + (ε·(n+1) + β) = ε·(n+1) + β`
  have hsplit : ∀ y : Ordinal.{0}, ∀ b : Ordinal.{0},
      eN y * ((n + 2 : ℕ) : Ordinal.{0}) + b = eN y + 1 + (eN y * ((n + 1 : ℕ) : Ordinal.{0}) + b) := by
    intro y b
    have hω : ω ≤ eN y * ((n + 1 : ℕ) : Ordinal.{0}) + b :=
      (omega0_le_eN y).trans ((le_mul_of_one_le_right' (by exact_mod_cast Nat.succ_pos n)).trans le_self_add)
    have e2 : ((n + 2 : ℕ) : Ordinal.{0}) = 1 + ((n + 1 : ℕ) : Ordinal.{0}) := by
      rw [show n + 2 = 1 + (n + 1) by omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc (eN y) 1, one_add_of_omega0_le hω, ← add_assoc, e2, mul_add, mul_one]
  have hbig : ∀ y : Ordinal.{0}, InE y → y < Om1 → ∀ b, b < eN y →
      eN y + (eN y * ((n + 1 : ℕ) : Ordinal.{0}) + b) < eN (eN y) ∧
        eN y + (eN y * ((n + 1 : ℕ) : Ordinal.{0}) + b) < Om1 := by
    intro y hy hy1 b hb
    have he1 : eN y < Om1 := Ge.eN_lt_Om1' hy hy1
    have hE2 := eN_E (eN y)
    have hlt := lt_eN (eN y)
    have hm : eN y * ((n + 1 : ℕ) : Ordinal.{0}) < eN (eN y) :=
      hE2.mul_lt hlt ((natCast_lt_omega0 _).trans (omega0_lt_inE hE2))
    have hm1 : eN y * ((n + 1 : ℕ) : Ordinal.{0}) < Om1 :=
      Rj.rj_Om1_inE.mul_lt he1 ((natCast_lt_omega0 _).trans omega_lt_Om1)
    exact ⟨(inE_indec hE2).add_lt hlt ((inE_indec hE2).add_lt hm (hb.trans hlt)),
      Om1_add_lt he1 (Om1_add_lt hm1 (hb.trans he1))⟩
  obtain ⟨hb1, hb2⟩ := hbig ρ hB.2.1 hρ1 β hβe
  obtain ⟨hb1', hb2'⟩ := hbig σ hB.1 hσ1 _ hπβ
  have hv := vt_eN2 hB.2.1 hρ1 hb1 hb2
  rw [← hsplit] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hb2
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hv' := vt_eN2 hB.1 hσ1 hb1' hb2'
  rw [← hsplit] at hv'
  rw [← hv, pi_vt hB hξTB hb2, hpξ, hv']

end Googology.Trans.PoR.InaccPsi.R2.Gi
