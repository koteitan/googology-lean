import Googology.Trans.PoR.InaccPsi.R2.GjHR

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}`: cofinality, Lemma EXACT at every pair of bases, the code system

* `JhCofAt`, `jh_lim_of_cof` (**a limit code has a limit reading**, from cofinality), `jh_cofPow_of` (**every
  `ν < ε_{x+1}^{κ(x)}` is below the reading of a code `t < E^κ`**, by induction on the code `κ`), `jhR_cof`,
  `jhR_cofE` (**cofinality**);
* `jh_eAtom_pi` (**Lemma EXACT for the atom `ω^{ε_{ρ+1}·K+β}`, `K ≥ ω`, `K < ε_{ρ+2}`**, once `π(ε_{ρ+1}·K) =
  ε_{σ+1}·K'`: it is `ϑ^ρ(ε_{ρ+1} + ε_{ρ+1}·K + β)`, `vt_eN2`, [W07a] Lemma 4.2, and `π(ϑ^ρ(ξ)) = ϑ^σ(π ξ)`),
  `jh_eNr_pi`, `jhR_pi` (**Lemma EXACT for every code below `ε_{Ω₁+2}`**, by induction on the code: the exponent `k ≥ ω`
  enters through the smaller code `E·k`), `jh_eNk_pi` (`π(ε_{ρ+1}·k(ρ)) = ε_{σ+1}·k(σ)`);
* `jh_count`, `jhK` (**THE CODE SYSTEM below `ε_{Ω₁+2}`**).

No new axiom.  New definitions: `JhCofAt`, `jhK`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def JhCofAt (x j : Ordinal.{0}) : Prop :=
  jhG j < x → ∀ ν, ν < jhR j x → ∃ b, b < j ∧ jhG b < x ∧ ν ≤ jhR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx

/-- **A limit code has a limit reading** (from cofinality, `+1` and the order). -/
theorem jh_lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < jhB) (hg : jhG κ < x)
    (hc : JhCofAt x κ) : IsSuccLimit (jhR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (jhR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (jhR_pos hx hκ0 hκB).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : jhR b x < jhR κ x := jhR_mono hx κ hκB b hb hg hgb
    have hbe : jhR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : jhG (b + 1) < x := jhG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := jhR_mono hx κ hκB (b + 1) hb1 hg hgb1
    rw [jhR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **The codes below `E^κ` have cofinal readings in `ε_{x+1}^{κ(x)}`**, once cofinality holds below a bound `N > κ`. -/
theorem jh_cofPow_of {N : Ordinal.{0}} (hN : ∀ j, j < N → JhCofAt x j) : ∀ κ, κ < N → κ ≠ 0 → κ < jhB →
    jhG κ < x → ∀ ν, ν < eN x ^ jhR κ x → ∃ t, t < gfE ^ κ ∧ jhG t < x ∧ ν < jhR t x := by
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ ν hν
  have hEκ : gfE ≤ gfE ^ κ := by
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ κ := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'B : κ' + 1 < jhB := hs ▸ hκB
    have r1 := jhR_succ κ' hκ'B x
    have r2 := jhG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : jhG κ' < x := r2.trans_lt hgκ
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, jhR_zero, opow_zero, one_mul] at hν
      obtain ⟨i, hi⟩ := ghTw_cof hx hν
      refine ⟨ghTw i, (ghTw_lt i).trans_le hEκ, ?_, ?_⟩
      · rw [jhG_low (ghTw_lt i)]; exact (ghTw_gtc i).trans_lt (Lu.lu_one_lt_E hx)
      · rw [jhR_low (ghTw_lt i)]; exact hi
    · have hne : eN x ^ jhR κ' x ≠ 0 := opow_ne_zero _ (eN_E x).pos.ne'
      have hq : ν / eN x ^ jhR κ' x < eN x := (Ordinal.div_lt hne).2 hν
      obtain ⟨i, hi⟩ := ghTw_cof hx hq
      have htw0 : ghTw i ≠ 0 := ghTw_pos i
      have htB : gfE ^ κ' * ghTw i + 0 < jhB := by
        rw [add_zero]; exact jh_mul_lt (hκ'κ.trans hκB) (ghTw_lt i)
      refine ⟨gfE ^ κ' * ghTw i + 0, ?_, ?_, ?_⟩
      · rw [add_zero, ← hs, opow_add, opow_one]
        exact (mul_lt_mul_iff_right₀ (opow_pos _ eW_E.pos)).2 (ghTw_lt i)
      · rw [jhG_cnf hκ'0 htw0 (ghTw_lt i) (opow_pos _ eW_E.pos) htB, jhG_zero]
        refine max_lt (max_lt ((jhQ_le _).trans_lt hgκ') ((giQ_le _).trans_lt ?_)) hx.pos
        exact (ghTw_gtc i).trans_lt (Lu.lu_one_lt_E hx)
      · rw [jhR_cnf hκ'0 htw0 (ghTw_lt i) (opow_pos _ eW_E.pos) htB, jhR_zero, add_zero]
        calc ν < eN x ^ jhR κ' x * (ν / eN x ^ jhR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (eN x ^ jhR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ eN x ^ jhR κ' x * rdc (ghTw i) x := mul_le_mul_left' (Order.add_one_le_of_lt hi) _
  · have hlim := jh_lim_of_cof hx hl hκB hgκ (hN κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit (eN_E x).pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hN κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [jhR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < eN x ^ jhR κ' x :=
      hνμ.trans_le (opow_le_opow_right (eN_E x).pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right eW_E.pos hκ'κ.le), hgt, hvt⟩

include hx1

/-- **Cofinality**: every `ν` below the reading of a code `c < ε_{Ω₁+2}` is at most the reading of a smaller code with
gate below `x`. -/
theorem jhR_cof : ∀ c, c < jhB → JhCofAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hIH : ∀ j, j < c → JhCofAt x j := fun j hj => IH j hj (hj.trans hc)
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE] at hg
    rw [jhR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := rdc_surj hx hx1.le hcE hg hν
    exact ⟨b, hb, by rw [jhG_low (hb.trans hcE)]; exact hgb, by rw [jhR_low (hb.trans hcE), eb]⟩
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := jh_parts hcE hc
  obtain ⟨g0, g1, g2⟩ := jh_parts_g hx hcE hc hg
  set k := log gfE c with hkdef
  set d := c / gfE ^ k with hddef
  set r := c % gfE ^ k with hrdef
  have hgc : jhG c = max (max (jhQ k) (giQ d)) (jhG r) := jhG_dec hcE hc
  have hgk : jhQ k < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt (hgc ▸ hg))
  rw [jhR_dec hcE hc] at hν
  rcases lt_or_ge ν (eN x ^ jhR k x * rdc d x) with hν1 | hν1
  · have hne : eN x ^ jhR k x ≠ 0 := opow_ne_zero _ (eN_E x).pos.ne'
    have hμ : ν / eN x ^ jhR k x < rdc d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := rdc_surj hx hx1.le hdE g1 hμ
    have hρ : ν % eN x ^ jhR k x < eN x ^ jhR k x := Ordinal.mod_lt ν hne
    obtain ⟨t, htk, hgt, hvt⟩ := jh_cofPow_of hx hIH k hkc hk (hkc.trans hc) g0 _ hρ
    have hd'E : d' < gfE := hd'd.trans hdE
    have hνe : ν = eN x ^ jhR k x * rdc d' x + ν % eN x ^ jhR k x := by
      rw [ed']; exact (Ordinal.div_add_mod ν (eN x ^ jhR k x)).symm
    have hkd : gfE ^ k ≤ c := by
      rw [← hdec]
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
    rcases eq_or_ne d' 0 with hd'0 | hd'0
    · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
      rw [hνe, hd'0, rdc_zero, mul_zero, zero_add]; exact hvt.le
    · have hlt : gfE ^ k * d' + t < c := by
        calc gfE ^ k * d' + t < gfE ^ k * d' + gfE ^ k := (add_lt_add_iff_left _).2 htk
          _ = gfE ^ k * (d' + 1) := by rw [mul_add_one]
          _ ≤ gfE ^ k * d := mul_le_mul_left' (Order.add_one_le_of_lt hd'd) _
          _ ≤ c := by rw [← hdec]; exact le_self_add
      refine ⟨gfE ^ k * d' + t, hlt, ?_, ?_⟩
      · rw [jhG_cnf hk hd'0 hd'E htk (hlt.trans hc)]
        exact max_lt (max_lt hgk ((giQ_le _).trans_lt hgd')) hgt
      · rw [jhR_cnf hk hd'0 hd'E htk (hlt.trans hc), hνe]
        exact add_le_add le_rfl hvt.le
  · have e : eN x ^ jhR k x * rdc d x + (ν - eN x ^ jhR k x * rdc d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - eN x ^ jhR k x * rdc d x < jhR r x := by
      rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hIH r hrc g2 _ hν'
    have hb'k : b' < gfE ^ k := hb'r.trans hr
    have hlt : gfE ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨gfE ^ k * d + b', hlt, ?_, ?_⟩
    · rw [jhG_cnf hk hd0 hdE hb'k (hlt.trans hc)]
      exact max_lt ((le_max_left _ _).trans_lt (hgc ▸ hg)) hgb'
    · rw [jhR_cnf hk hd0 hdE hb'k (hlt.trans hc), ← e]
      exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem jhR_cofE {c : Ordinal.{0}} (hc : c < jhB) (hEc : gfE < c) (hg : jhG c < x) {ν : Ordinal.{0}}
    (hν : ν < jhR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ jhG b < x ∧ ν ≤ jhR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := jhR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [jhG_E]; exact hx.pos, ?_⟩
    rw [jhG_low hbE] at hgb
    rw [jhR_low hbE] at hνb
    rw [jhR_E]
    exact hνb.trans (rdc_lt_eN hx b hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for the atom `ω^{ε_{ρ+1}·K+β}`** (`ω ≤ K < ε_{ρ+2}`, its image `K'` likewise) at every pair of bases,
once `π(ε_{ρ+1}·K) = ε_{σ+1}·K'`. -/
theorem jh_eAtom_pi {σ ρ K K' β : Ordinal.{0}} (hB : Bases σ ρ) (hK : ω ≤ K) (hK' : ω ≤ K')
    (hKe : K < eN (eN ρ)) (hK'e : K' < eN (eN σ))
    (hm : eN ρ * K ∈ TB ρ σ ∧ pi σ ρ (eN ρ * K) = eN σ * K') (hβTB : β ∈ TB ρ σ) (hβe : β < eN ρ) :
    ω ^ (eN ρ * K + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ * K + β)) = ω ^ (eN σ * K' + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := gh_eN_pi hB
  have hπβ : pi σ ρ β < eN σ := by rw [← hpe]; exact (pi_bijOn hB).2 hβTB heTB hβe
  obtain ⟨hmTB, hmpi⟩ := hm
  obtain ⟨h1, h2⟩ := pi_add hB hmTB hβTB
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB h1
  rw [h2, hmpi, hpe] at hpξ
  have hsplit : ∀ y L : Ordinal.{0}, ω ≤ L → ∀ b : Ordinal.{0}, eN y * L + b = eN y + 1 + (eN y * L + b) := by
    intro y L hL b
    have hω : ω ≤ eN y * L + b :=
      (omega0_le_eN y).trans ((le_mul_of_one_le_right' (one_lt_omega0.le.trans hL)).trans le_self_add)
    have e1 : eN y + eN y * L = eN y * L := by
      calc eN y + eN y * L = eN y * 1 + eN y * L := by rw [mul_one]
        _ = eN y * (1 + L) := (mul_add _ _ _).symm
        _ = eN y * L := by rw [one_add_of_omega0_le hL]
    rw [add_assoc (eN y) 1, one_add_of_omega0_le hω, ← add_assoc, e1]
  have hbig : ∀ y L : Ordinal.{0}, y < Om1 → L < eN (eN y) → ∀ b, b < eN y →
      eN y + (eN y * L + b) < eN (eN y) ∧ eN y + (eN y * L + b) < Om1 := by
    intro y L hy1 hL b hb
    have hE2 := eN_E (eN y)
    have hlt := lt_eN (eN y)
    have h1' : eN y + (eN y * L + b) < eN (eN y) :=
      (inE_indec hE2).add_lt hlt ((inE_indec hE2).add_lt (hE2.mul_lt hlt hL) (hb.trans hlt))
    exact ⟨h1', h1'.trans (eN_lt_Om1K (eN_lt_Om1K hy1))⟩
  obtain ⟨hb1, hb2⟩ := hbig ρ K hρ1 hKe β hβe
  obtain ⟨hb1', hb2'⟩ := hbig σ K' hσ1 hK'e _ hπβ
  have hv := vt_eN2 hB.2.1 hρ1 hb1 hb2
  rw [← hsplit ρ K hK] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hb2
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hv' := vt_eN2 hB.1 hσ1 hb1' hb2'
  rw [← hsplit σ K' hK'] at hv'
  rw [← hv, pi_vt hB hξTB hb2, hpξ, hv']

/-- **`π(ε_{ρ+1}^K·γ(ρ)) = ε_{σ+1}^{K'}·γ(σ)`** (a code `γ < E` with gate below `σ`), once Lemma EXACT holds for the
atoms `ω^{ε_{ρ+1}·K+β}`. -/
theorem jh_eNr_pi {σ ρ K K' : Ordinal.{0}} (hB : Bases σ ρ)
    (hat : ∀ β, β ∈ TB ρ σ → β < eN ρ →
      ω ^ (eN ρ * K + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ * K + β)) = ω ^ (eN σ * K' + pi σ ρ β)) :
    ∀ γ, γ < gfE → gtc γ < σ →
    eN ρ ^ K * rdc γ ρ ∈ TB ρ σ ∧ pi σ ρ (eN ρ ^ K * rdc γ ρ) = eN σ ^ K' * rdc γ σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγW hg
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [rdc_zero, rdc_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  obtain ⟨-, hqΩ, -, -, hrγ, -⟩ := parts hγ0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hγ0 hγW
  set l := log Om1 γ with hldef
  set q := γ / Om1 ^ l with hqdef
  set r := γ % Om1 ^ l with hrdef
  obtain ⟨h1, h2⟩ := IH r hrγ (hrγ.trans hγW) (gr.trans_lt hg)
  have hqσ : q < σ := gq.trans_lt hg
  have hcb : OT.CB (tcx l) σ := cb_tcx hσE.pos l (gl.trans_lt hg)
  have edec : ∀ x L, InE x →
      eN x ^ L * rdc γ x = ω ^ (eN x * L + OT.ev (tcx l) x) * q + eN x ^ L * rdc r x := by
    intro x L hx
    rw [rdc_dec hγ0 hγW, mul_add, ← mul_assoc, pw_eq' hx, gw_eNpow, ← opow_add, ev_tcx hx]
  have hatom : ∀ z, z < σ → ω ^ (eN ρ * K + (OT.ev (tcx l) ρ + z)) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * K + (OT.ev (tcx l) ρ + z))) = ω ^ (eN σ * K' + (OT.ev (tcx l) σ + z)) := by
    intro z hz
    have hcb' : OT.CB (OT.add (tcx l) (OT.k z)) σ := ⟨hcb, hz⟩
    obtain ⟨t1, t2⟩ := pi_ev hB _ hcb'
    simp only [OT.ev_add, OT.ev_k] at t1 t2
    have hlt : OT.ev (tcx l) ρ + z < eN ρ := by
      have := ev_lt_eN (OT.CB_mono hcb' hB.2.2.1.le)
      simpa only [OT.ev_add, OT.ev_k] using this
    obtain ⟨t3, t4⟩ := hat _ t1 hlt
    rw [t2] at t4
    exact ⟨t3, t4⟩
  have hmul : ∀ q', q' < σ → ω ^ (eN ρ * K + OT.ev (tcx l) ρ) * q' ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * K + OT.ev (tcx l) ρ) * q') = ω ^ (eN σ * K' + OT.ev (tcx l) σ) * q' := by
    intro q'
    induction q' using WellFoundedLT.induction with
    | ind q' IHq =>
    intro hq'
    rcases eq_or_ne q' 0 with rfl | hq0
    · rw [mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
    obtain ⟨q'', hgs, -, hq''⟩ := lg_split hq0
    have hz : lg q' < σ := lt_of_le_of_lt (lg_le hq0) hq'
    obtain ⟨k1, k2⟩ := IHq q'' hq'' (hq''.trans hq')
    obtain ⟨k3, k4⟩ := hatom _ hz
    rw [hgs, mul_add, mul_add, ← opow_add, ← opow_add, add_assoc, add_assoc]
    obtain ⟨k5, k6⟩ := pi_add hB k1 k3
    exact ⟨k5, by rw [k6, k2, k4]⟩
  obtain ⟨m1, m2⟩ := hmul q hqσ
  rw [edec ρ K hρE, edec σ K' hσE]
  obtain ⟨m3, m4⟩ := pi_add hB m1 h1
  exact ⟨m3, by rw [m4, m2, h2]⟩

/-- **Lemma EXACT for every code `c < ε_{Ω₁+2}`** at every pair of bases above its gate. -/
theorem jhR_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : ∀ c, c < jhB → jhG c < σ →
    jhR c ρ ∈ TB ρ σ ∧ pi σ ρ (jhR c ρ) = jhR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [jhG_low hcE] at hg
    rw [jhR_low hcE, jhR_low hcE]
    exact rdc_pi hB hcE hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := jh_parts hcE hc
  obtain ⟨g0, g1, g2⟩ := jh_parts_g hσE hcE hc hg
  set k := log gfE c with hkdef
  have hkB : k < jhB := hkc.trans hc
  have g0ρ : jhG k < ρ := g0.trans hB.2.2.1
  obtain ⟨h1, h2⟩ := IH _ hrc (hrc.trans hc) g2
  -- the atoms `ω^{ε_{ρ+1}·k(ρ)+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < eN ρ → ω ^ (eN ρ * jhR k ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * jhR k ρ + β)) = ω ^ (eN σ * jhR k σ + pi σ ρ β) := by
    intro β hβ hβe
    rcases lt_or_ge k ω with hω | hω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hk (by rw [hn, Nat.cast_zero])
        omega⟩
      rw [hn, jhR_nat, jhR_nat]
      exact gw_eAtomN_pi hB m hβ hβe
    · have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 hω
      obtain ⟨hEkB, hgEk, hREk⟩ := jh_mulE k hk hkB
      have hlt : gfE * k < c := (jh_mulE_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      obtain ⟨m1, m2⟩ := IH _ hlt hEkB (hgEk.trans_lt g0)
      rw [hREk ρ hρE] at m1 m2
      rw [hREk σ hσE] at m2
      exact jh_eAtom_pi hB (jh_omega_le_jhR hρE hω hkB) (jh_omega_le_jhR hσE hω hkB)
        (jhR_lt_eNN hρE hkB g0ρ) (jhR_lt_eNN hσE hkB g0) ⟨m1, m2⟩ hβ hβe
  obtain ⟨h3, h4⟩ := jh_eNr_pi hB hat _ hdE g1
  rw [jhR_dec hcE hc, jhR_dec hcE hc]
  obtain ⟨h5, h6⟩ := pi_add hB h3 h1
  exact ⟨h5, by rw [h6, h4, h2]⟩

/-- **`π(ε_{ρ+1}·k(ρ)) = ε_{σ+1}·k(σ)`** for every code `1 ≤ k < ε_{Ω₁+2}` with gate below `σ`. -/
theorem jh_eNk_pi {σ ρ k : Ordinal.{0}} (hB : Bases σ ρ) (hk : k ≠ 0) (hkB : k < jhB) (hg : jhG k < σ) :
    eN ρ * jhR k ρ ∈ TB ρ σ ∧ pi σ ρ (eN ρ * jhR k ρ) = eN σ * jhR k σ := by
  obtain ⟨hEkB, hgEk, hREk⟩ := jh_mulE k hk hkB
  obtain ⟨m1, m2⟩ := jhR_pi hB _ hEkB (hgEk.trans_lt hg)
  rw [hREk ρ hB.2.1] at m1 m2
  rw [hREk σ hB.1] at m2
  exact ⟨m1, m2⟩

/-- **The codes below `c ≤ ε_{Ω₁+2}` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem jh_count {c y : Ordinal.{0}} (hc : c ≤ jhB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // jhG b.1 < y} := by
  have hq1 : gq 0 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gfq0_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // jhG b.1 < y} → Iio (gq 0 y) := fun b =>
    ⟨jhR b.1.1 y, jhR_lt0 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : jhR b.1.1 y = jhR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (jhR_mono hy _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (jhR_mono hy _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'

/-- **THE CODE SYSTEM below `ε_{Ω₁+2}`** (hereditary codes). -/
noncomputable def jhK : GiCS where
  B := jhB
  gt := jhG
  B_lt := jhB_lt_G0
  gt_zero := jhG_zero
  gt_lt := jhG_lt_Om1
  gt_succ := fun b _ hZ hb hg => jhG_succ hZ b hb hg
  mem := fun _ _ _ c hc hg => jh_mem c hc hg
  B_mem := fun _ _ _ => jhB_mem
  code_gate := fun _ _ hZ1 hZ0 hZa hZp hAt _ hc hcB => jh_code_gate hZ1 hZ0 hZa hZp hAt hc hcB
  count := fun _ _ hc hy hy1 => jh_count hc hy hy1

theorem jhK_B : jhK.B = jhB := rfl

theorem jhK_gt : jhK.gt = jhG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gj
