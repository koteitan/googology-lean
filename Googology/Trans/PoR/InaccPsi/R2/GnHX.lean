import Googology.Trans.PoR.InaccPsi.R2.GnHR

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}`: cofinality, Lemma EXACT at every pair of bases, the code system

The port of `R2.GjHX`, with Lemma EXACT for the atoms `ω^{Γ_{ρ+1}·K+β}` from `R2.GnA` (`gn_opowG_pi`):

* `GnCofAt`, `gn_lim_of_cof` (**a limit code has a limit reading**), `gn_cofPow_of` (**every
  `ν < Γ_{x+1}^{κ(x)}` is below the reading of a code `t < G^κ`**), `gnR_cof`, `gnR_cofE` (**cofinality**);
* `gn_mulGn_pi` (`π(Γ_{ρ+1}·(n+1)) = Γ_{σ+1}·(n+1)`), `gn_GkAtom_pi` (**Lemma EXACT for the atom
  `ω^{Γ_{ρ+1}·K+β}`**, `K ≥ 1`, once `π(Γ_{ρ+1}·K) = Γ_{σ+1}·K'`), `gn_Gr_pi` (**`π(Γ_{ρ+1}^K·d(ρ)) =
  Γ_{σ+1}^{K'}·d(σ)`** for every digit `d < G`, `Gl.gl_dig`), `gnR_pi` (**Lemma EXACT for every code below
  `ε_{G+1}`**, by induction on the code: the exponent `k ≥ ω` enters through the smaller code `G·k`), `gn_mulG_pi`;
* `gn_count`, `gnK` (**THE CODE SYSTEM below `ε_{Γ_{Ω₁+1}+1}`**: a `Gm.GmCS` whose codes contain the atom
  `Γ_{Ω₁+1}` in any position).

No new axiom.  New definitions: `GnCofAt`, `gnK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def GnCofAt (x j : Ordinal.{0}) : Prop :=
  gnG j < x → ∀ ν, ν < gnR j x → ∃ b, b < j ∧ gnG b < x ∧ ν ≤ gnR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A limit code has a limit reading** (from cofinality, `+1` and the order). -/
theorem gn_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < gnB) (hg : gnG κ < x)
    (hc : GnCofAt x κ) : IsSuccLimit (gnR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (gnR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (gnR_pos hx hx1 hκ0 hκB hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : gnR b x < gnR κ x := gnR_mono hx hx1 κ hκB b hb hg hgb
    have hbe : gnR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : gnG (b + 1) < x := gnG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := gnR_mono hx hx1 κ hκB (b + 1) hb1 hg hgb1
    rw [gnR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **The codes below `G^κ` have cofinal readings in `Γ_{x+1}^{κ(x)}`**, once cofinality holds below `N > κ`. -/
theorem gn_cofPow_of {N : Ordinal.{0}} (hN : ∀ j, j < N → GnCofAt x j) : ∀ κ, κ < N → κ ≠ 0 → κ < gnB →
    gnG κ < x → ∀ ν, ν < lgG x ^ gnR κ x → ∃ t, t < gcG 0 ^ κ ∧ gnG t < x ∧ ν < gnR t x := by
  have hGE := (lgG_facts hx hx1).2.2.2.1
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ ν hν
  have hEκ : gcG 0 ≤ gcG 0 ^ κ := by
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gcG 0 ^ κ := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'B : κ' + 1 < gnB := hs ▸ hκB
    have r1 := gnR_succ κ' hκ'B x
    have r2 := gnG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : gnG κ' < x := r2.trans_lt hgκ
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, gnR_zero, opow_zero, one_mul] at hν
      obtain ⟨b, -, hbG, hgb, hb⟩ := mg_cof_G hx hx1 hν
      refine ⟨b, hbG.trans_le hEκ, ?_, ?_⟩
      · rw [gnG_low hbG, hgb]; exact hx.pos
      · rw [gnR_low hbG]; exact hb
    · have hne : lgG x ^ gnR κ' x ≠ 0 := opow_ne_zero _ hGE.pos.ne'
      have hq : ν / lgG x ^ gnR κ' x < lgG x := (Ordinal.div_lt hne).2 hν
      obtain ⟨b, -, hbG, hgb, hb⟩ := mg_cof_G hx hx1 hq
      have hb0 : b ≠ 0 := by rintro rfl; rw [glR_zero] at hb; exact absurd hb (not_lt.2 zero_le)
      have htB : gcG 0 ^ κ' * b + 0 < gnB := by
        rw [add_zero]; exact gn_mul_lt (hκ'κ.trans hκB) hbG
      refine ⟨gcG 0 ^ κ' * b + 0, ?_, ?_, ?_⟩
      · rw [add_zero, ← hs, opow_add, opow_one]
        exact (mul_lt_mul_iff_right₀ (opow_pos _ gl_G0_E.pos)).2 hbG
      · rw [gnG_cnf hκ'0 hb0 hbG (opow_pos _ gl_G0_E.pos) htB, gnG_zero]
        refine max_lt (max_lt ((gnQ_le _).trans_lt hgκ') ((glQ_le _).trans_lt ?_)) hx.pos
        rw [hgb]; exact hx.pos
      · rw [gnR_cnf hκ'0 hb0 hbG (opow_pos _ gl_G0_E.pos) htB, gnR_zero, add_zero]
        calc ν < lgG x ^ gnR κ' x * (ν / lgG x ^ gnR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (lgG x ^ gnR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ lgG x ^ gnR κ' x * glR b x := mul_le_mul_left' (Order.add_one_le_of_lt hb) _
  · have hlim := gn_lim_of_cof hx hx1 hl hκB hgκ (hN κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hGE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hN κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [gnR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < lgG x ^ gnR κ' x :=
      hνμ.trans_le (opow_le_opow_right hGE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right gl_G0_E.pos hκ'κ.le), hgt, hvt⟩

/-- **Cofinality**: every `ν` below the reading of a code `c < ε_{G+1}` is at most the reading of a smaller code with
gate below `x`. -/
theorem gnR_cof : ∀ c, c < gnB → GnCofAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hIH : ∀ j, j < c → GnCofAt x j := fun j hj => IH j hj (hj.trans hc)
  have hGE := (lgG_facts hx hx1).2.2.2.1
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg
    rw [gnR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := glR_cof hx hx1 c hcE hg ν hν
    exact ⟨b, hb, by rw [gnG_low (hb.trans hcE)]; exact hgb, by rw [gnR_low (hb.trans hcE)]; exact eb⟩
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := gn_parts hcE hc
  obtain ⟨g0, g1, g2⟩ := gn_parts_g (omega0_lt_inE hx) hcE hc hg
  set k := log (gcG 0) c with hkdef
  set d := c / gcG 0 ^ k with hddef
  set r := c % gcG 0 ^ k with hrdef
  have hgc : gnG c = max (max (gnQ k) (glQ d)) (gnG r) := gnG_dec hcE hc
  have hgk : gnQ k < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt (hgc ▸ hg))
  have hkd : gcG 0 ^ k ≤ c := by
    rw [← hdec]
    exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
  rw [gnR_dec hcE hc] at hν
  set P := lgG x ^ gnR k x with hP
  have hne : P ≠ 0 := opow_ne_zero _ hGE.pos.ne'
  rcases lt_or_ge ν (P * glR d x) with hν1 | hν1
  · have hμ : ν / P < glR d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := glR_cof hx hx1 d hdE g1 _ hμ
    have hd'E : d' < gcG 0 := hd'd.trans hdE
    have hlt' : ∀ t, t < gcG 0 ^ k → d' ≠ 0 → gcG 0 ^ k * d' + t < c := by
      intro t ht _
      calc gcG 0 ^ k * d' + t < gcG 0 ^ k * d' + gcG 0 ^ k := (add_lt_add_iff_left _).2 ht
        _ = gcG 0 ^ k * (d' + 1) := by rw [mul_add_one]
        _ ≤ gcG 0 ^ k * d := mul_le_mul_left' (Order.add_one_le_of_lt hd'd) _
        _ ≤ c := by rw [← hdec]; exact le_self_add
    rcases ed'.lt_or_eq with hq | hq
    · -- `ν < P·(q+1) ≤ P·d'(x)`
      have hd'0 : d' ≠ 0 := by rintro rfl; rw [glR_zero] at hq; exact absurd hq (not_lt.2 zero_le)
      have hlt := hlt' 0 (opow_pos _ gl_G0_E.pos) hd'0
      refine ⟨gcG 0 ^ k * d' + 0, hlt, ?_, ?_⟩
      · rw [gnG_cnf hk hd'0 hd'E (opow_pos _ gl_G0_E.pos) (hlt.trans hc), gnG_zero]
        exact max_lt (max_lt hgk ((glQ_le _).trans_lt hgd')) hx.pos
      · rw [gnR_cnf hk hd'0 hd'E (opow_pos _ gl_G0_E.pos) (hlt.trans hc), gnR_zero, add_zero]
        refine le_of_lt ?_
        calc ν = P * (ν / P) + ν % P := (Ordinal.div_add_mod ν P).symm
          _ < P * (ν / P) + P := (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ = P * (ν / P + 1) := by rw [mul_add_one]
          _ ≤ P * glR d' x := mul_le_mul_left' (Order.add_one_le_of_lt hq) _
    · have hρ : ν % P < P := Ordinal.mod_lt ν hne
      obtain ⟨t, htk, hgt, hvt⟩ := gn_cofPow_of hx hx1 hIH k hkc hk (hkc.trans hc) g0 _ hρ
      have hνe : ν = P * glR d' x + ν % P := by
        rw [← hq]; exact (Ordinal.div_add_mod ν P).symm
      rcases eq_or_ne d' 0 with hd'0 | hd'0
      · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
        rw [hνe, hd'0, glR_zero, mul_zero, zero_add]; exact hvt.le
      · have hlt := hlt' t htk hd'0
        refine ⟨gcG 0 ^ k * d' + t, hlt, ?_, ?_⟩
        · rw [gnG_cnf hk hd'0 hd'E htk (hlt.trans hc)]
          exact max_lt (max_lt hgk ((glQ_le _).trans_lt hgd')) hgt
        · rw [gnR_cnf hk hd'0 hd'E htk (hlt.trans hc), hνe]
          exact add_le_add le_rfl hvt.le
  · have e : P * glR d x + (ν - P * glR d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - P * glR d x < gnR r x := by
      rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hIH r hrc g2 _ hν'
    have hb'k : b' < gcG 0 ^ k := hb'r.trans hr
    have hlt : gcG 0 ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨gcG 0 ^ k * d + b', hlt, ?_, ?_⟩
    · rw [gnG_cnf hk hd0 hdE hb'k (hlt.trans hc)]
      exact max_lt ((le_max_left _ _).trans_lt (hgc ▸ hg)) hgb'
    · rw [gnR_cnf hk hd0 hdE hb'k (hlt.trans hc), ← e]
      exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem gnR_cofE {c : Ordinal.{0}} (hc : c < gnB) (hEc : gfE < c) (hg : gnG c < x) {ν : Ordinal.{0}}
    (hν : ν < gnR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ gnG b < x ∧ ν ≤ gnR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := gnR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [gnG_low gfE_lt_G0, glG_E]; exact hx.pos, ?_⟩
    have hbG : b < gcG 0 := hbE.trans gfE_lt_G0
    rw [gnG_low hbG] at hgb
    rw [gnR_low hbG] at hνb
    rw [gnR_low gfE_lt_G0, glR_E]
    rw [glR_low hbE] at hνb
    rw [glG_low hbE] at hgb
    exact hνb.trans (rdc_lt_eN hx b hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- `π(Γ_{ρ+1}·n) = Γ_{σ+1}·n`. -/
theorem gn_mulGn_pi : ∀ n : ℕ, lgG ρ * (n : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * (n : Ordinal.{0})) =
    lgG σ * (n : Ordinal.{0})
  | 0 => by
    simp only [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := gn_mulGn_pi n
    obtain ⟨g1, g2⟩ := mg_lgG_pi hB
    obtain ⟨h3, h4⟩ := pi_add hB h1 g1
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h3, by rw [h4, h2, g2]⟩

/-- **Lemma EXACT for the atom `ω^{Γ_{ρ+1}·K+β}`** (`K ≥ 1`, `Γ_{ρ+1}·K < ε_{Γ_{ρ+1}+1}`, `β < Γ_{ρ+1}`), once
`π(Γ_{ρ+1}·K) = Γ_{σ+1}·K'`. -/
theorem gn_GkAtom_pi {K K' β : Ordinal.{0}} (hK : 1 ≤ K) (hKe : lgG ρ * K < eN (lgG ρ))
    (hm : lgG ρ * K ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * K) = lgG σ * K') (hβTB : β ∈ TB ρ σ) (hβe : β < lgG ρ) :
    ω ^ (lgG ρ * K + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (lgG ρ * K + β)) = ω ^ (lgG σ * K' + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨hmTB, hmpi⟩ := hm
  obtain ⟨h1, h2⟩ := pi_add hB hmTB hβTB
  have hGX : lgG ρ ≤ lgG ρ * K + β := (le_mul_of_one_le_right' hK).trans le_self_add
  have hXe : lgG ρ * K + β < eN (lgG ρ) :=
    (inE_indec (eN_E _)).add_lt hKe (hβe.trans (lt_eN _))
  obtain ⟨h3, h4⟩ := gn_opowG_pi hB h1 hGX hXe
  exact ⟨h3, by rw [h4, h2, hmpi]⟩

/-- **The digits**: `π(Γ_{ρ+1}^K·d(ρ)) = Γ_{σ+1}^{K'}·d(σ)` for every code `d < G` with gate below `σ`, once the atoms
`ω^{Γ_{ρ+1}·K+β}` (`β < Γ_{ρ+1}`) are exact (`Gl.gl_dig`). -/
theorem gn_Gr_pi {P P' : Ordinal.{0}}
    (hat : ∀ β, β ∈ TB ρ σ → β < lgG ρ → ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β))
    {d : Ordinal.{0}} (hd : d < gcG 0) (hg : glG d < σ) :
    ω ^ P * glR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * glR d ρ) = ω ^ P' * glR d σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨n, hn⟩ := gmC_cof hd
  have he : InE (gmC n) := by
    rcases n with _ | n
    · show InE (glPsi ((0 + 1 : ℕ) : Ordinal.{0}) 0)
      exact glPsi_E (by simp) 0
    · rw [gmC_succ]
      have hO : Om1 < gmC n := Om1_lt_eW.trans_le (gmC_spec n).1
      rw [gl_veb0_psi hO (gmC_lt_G0 n)]
      exact glPsi_E (one_le_iff_pos.2 (lt_of_le_of_lt zero_le hO)) 0
  have hOe : Om1 < gmC n := Om1_lt_eW.trans_le (gmC_spec n).1
  have hge : glG (gmC n) < σ := by rw [(gmC_spec n).2.2]; exact hB.1.pos
  have hgeρ : glG (gmC n) < ρ := by rw [(gmC_spec n).2.2]; exact hB.2.1.pos
  exact gl_dig hB he hOe (gmC_lt_G0 n) hge (fun j hj hgj => gl_pi hB j (hj.trans (gmC_lt_G0 n)) hgj) d hn hg
    P P' (fun β hβ hβe => hat β hβ (hβe.trans (glR_lt_G hB.2.1 hρ1 (gmC_lt_G0 n) hgeρ)))

/-- **Lemma EXACT for every code `c < ε_{Γ_{Ω₁+1}+1}`** at every pair of bases above its gate. -/
theorem gnR_pi : ∀ c, c < gnB → gnG c < σ → gnR c ρ ∈ TB ρ σ ∧ pi σ ρ (gnR c ρ) = gnR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg
    rw [gnR_low hcE, gnR_low hcE]
    exact gl_pi hB c hcE hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := gn_parts hcE hc
  obtain ⟨g0, g1, g2⟩ := gn_parts_g (omega0_lt_inE hσE) hcE hc hg
  set k := log (gcG 0) c with hkdef
  have hkB : k < gnB := hkc.trans hc
  have g0ρ : gnG k < ρ := g0.trans hB.2.2.1
  obtain ⟨h1, h2⟩ := IH _ hrc (hrc.trans hc) g2
  -- `π(Γ_{ρ+1}·k(ρ)) = Γ_{σ+1}·k(σ)`
  have hmk : lgG ρ * gnR k ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * gnR k ρ) = lgG σ * gnR k σ := by
    rcases lt_or_ge k ω with hω | hω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      rw [hn, gnR_nat, gnR_nat]
      exact gn_mulGn_pi hB n
    · have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 hω
      obtain ⟨hEkB, hgEk, hREk⟩ := gn_mulG k hk hkB
      have hlt : gcG 0 * k < c := (gn_mulG_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      obtain ⟨m1, m2⟩ := IH _ hlt hEkB (hgEk.trans_lt g0)
      rw [hREk ρ hρE hρ1 g0ρ] at m1 m2
      rw [hREk σ hσE hσ1 g0] at m2
      exact ⟨m1, m2⟩
  have hKe : lgG ρ * gnR k ρ < eN (lgG ρ) := by
    have h3 := gnR_lt_eNG hρE hρ1 (gn_mulG k hk hkB).1 ((gn_mulG k hk hkB).2.1.trans_lt g0ρ)
    rwa [(gn_mulG k hk hkB).2.2 ρ hρE hρ1 g0ρ] at h3
  have hK1 : 1 ≤ gnR k ρ := one_le_iff_pos.2 (gnR_pos hρE hρ1 hk hkB g0ρ)
  have hat : ∀ β, β ∈ TB ρ σ → β < lgG ρ → ω ^ (lgG ρ * gnR k ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (lgG ρ * gnR k ρ + β)) = ω ^ (lgG σ * gnR k σ + pi σ ρ β) :=
    fun β hβ hβe => gn_GkAtom_pi hB hK1 hKe hmk hβ hβe
  obtain ⟨h3, h4⟩ := gn_Gr_pi hB hat hdE g1
  rw [← gn_Gpow hρE hρ1] at h3 h4
  rw [← gn_Gpow hσE hσ1] at h4
  rw [gnR_dec hcE hc, gnR_dec hcE hc]
  obtain ⟨h5, h6⟩ := pi_add hB h3 h1
  exact ⟨h5, by rw [h6, h4, h2]⟩

/-- **`π(Γ_{ρ+1}·k(ρ)) = Γ_{σ+1}·k(σ)`** for every code `1 ≤ k < ε_{G+1}` with gate below `σ`. -/
theorem gn_mulG_pi {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < gnB) (hg : gnG k < σ) :
    lgG ρ * gnR k ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * gnR k ρ) = lgG σ * gnR k σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨hEkB, hgEk, hREk⟩ := gn_mulG k hk hkB
  obtain ⟨m1, m2⟩ := gnR_pi hB _ hEkB (hgEk.trans_lt hg)
  rw [hREk ρ hB.2.1 hρ1 (hg.trans hB.2.2.1)] at m1 m2
  rw [hREk σ hB.1 hσ1 hg] at m2
  exact ⟨m1, m2⟩

end Pi

/-- **The codes below `c ≤ ε_{G+1}` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem gn_count {c y : Ordinal.{0}} (hc : c ≤ gnB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // gnG b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // gnG b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨gnR b.1.1 y, gnR_lt1 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : gnR b.1.1 y = gnR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (gnR_mono hy hy1 _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (gnR_mono hy hy1 _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'

/-- **THE CODE SYSTEM below `ε_{Γ_{Ω₁+1}+1}`** (hereditary codes to the base `Γ_{Ω₁+1}`). -/
noncomputable def gnK : GmCS where
  B := gnB
  gt := gnG
  B_V := gnB_V
  gt_zero := gnG_zero
  gt_lt := gnG_lt_Om1
  gt_succ := fun b _ hZ hb hg => gnG_succ hZ b hb hg
  mem := fun _ _ _ c hc hca hg => gn_mem (lt_of_le_of_lt zero_le hca) c hc hg
  B_mem := fun _ _ _ ha => gnB_mem (lt_of_le_of_lt zero_le ha)
  code_gate := fun _ hZ1 hZ0 hZa hZp _ hc hcB => gn_code_gate hZ1 hZ0 hZa hZp hc hcB
  count := fun _ _ hc hy hy1 => gn_count hc hy hy1

theorem gnK_B : gnK.B = gnB := rfl

theorem gnK_gt : gnK.gt = gnG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gn
