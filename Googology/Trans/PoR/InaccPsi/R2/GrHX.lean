import Googology.Trans.PoR.InaccPsi.R2.GrHR

/-!
# (port of `R2.GqHX` to the gated digit systems `GrD` whose base gate may pass `Γ₀`)

The proofs are those of `R2.GqHX`; they use no field of `GrD` that differs from `Gq.GqD`.

`R2.GoHX` for a gated digit system `D : GrD` (`R2.GrD`).  The cofinality part is that of `R2.GoHX`, at the bases
above the base gate (where the digit readings are cofinal in `b(x)`); Lemma EXACT for
the atoms `ω^{b(ρ)+β}`, for `π(b(ρ)·k(ρ))`, for every code `c < ε_{B+1}` (`GrD.hR_pi`) and the digit rule one level
up (`GrD.hdig`) are now proved at the pairs of bases `σ < ρ` above the base gate (`D.γ < σ`), where the fields
`b_pi`, `ba_pi` of a gated digit system hold.

No new axiom.  New definition: `GrD.HCofAt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GrD

variable (D : GrD)

/-- Cofinality at the code `j`: every `ν` below its reading is at most the reading of a smaller code. -/
def HCofAt (D : GrD) (x j : Ordinal.{0}) : Prop :=
  D.hG j < x → ∀ ν, ν < D.hR j x → ∃ b, b < j ∧ D.hG b < x ∧ ν ≤ D.hR b x

section Cof

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : D.γ < x)
include hx hx1 hγx

/-- **A limit code has a limit reading** (from cofinality, `+1` and the order). -/
theorem lim_of_cof {κ : Ordinal.{0}} (hl : IsSuccLimit κ) (hκB : κ < D.NB) (hg : D.hG κ < x)
    (hc : D.HCofAt x κ) : IsSuccLimit (D.hR κ x) := by
  have hκ0 : κ ≠ 0 := hl.bot_lt.ne'
  rcases zero_or_succ_or_isSuccLimit (D.hR κ x) with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd h0 (D.hR_pos hx hx1 hκ0 hκB hg).ne'
  · exfalso
    rw [succ_eq_add_one] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := hc hg ν (by rw [← hν]; exact lt_add_one ν)
    have hbκ : D.hR b x < D.hR κ x := D.hR_mono hx hx1 κ hκB b hb hg hgb
    have hbe : D.hR b x = ν := le_antisymm (Order.lt_add_one_iff.1 (hν ▸ hbκ)) hνb
    have hb1 : b + 1 < κ := hl.add_one_lt hb
    have hgb1 : D.hG (b + 1) < x := D.hG_succ (ev_isSuccLimit_of_inE hx) b (hb1.trans hκB) hgb
    have := D.hR_mono hx hx1 κ hκB (b + 1) hb1 hg hgb1
    rw [D.hR_succ b (hb1.trans hκB), hbe, hν] at this
    exact lt_irrefl _ this
  · exact hlim

/-- **The codes below `B^κ` have cofinal readings in `b(x)^{κ(x)}`**, once cofinality holds below `N > κ`. -/
theorem cofPow_of {N : Ordinal.{0}} (hN : ∀ j, j < N → D.HCofAt x j) : ∀ κ, κ < N → κ ≠ 0 → κ < D.NB →
    D.hG κ < x → ∀ ν, ν < D.b x ^ D.hR κ x → ∃ t, t < D.B ^ κ ∧ D.hG t < x ∧ ν < D.hR t x := by
  have hGE := (D.b_E x hx hx1)
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hκN hκ0 hκB hgκ ν hν
  have hEκ : D.B ≤ D.B ^ κ := by
    calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ D.B ^ κ := opow_le_opow_right D.B_E.pos (one_le_iff_ne_zero.2 hκ0)
  rcases zero_or_succ_or_isSuccLimit κ with h0 | ⟨κ', hs⟩ | hl
  · exact absurd h0 hκ0
  · rw [succ_eq_add_one] at hs
    have hκ'B : κ' + 1 < D.NB := hs ▸ hκB
    have r1 := D.hR_succ κ' hκ'B x
    have r2 := D.hG_le_succ κ' hκ'B
    rw [hs] at r1 r2
    have hgκ' : D.hG κ' < x := r2.trans_lt hgκ
    have hκ'κ : κ' < κ := by rw [← hs]; exact lt_add_one κ'
    rw [r1, opow_add, opow_one] at hν
    rcases eq_or_ne κ' 0 with h0 | hκ'0
    · rw [h0, D.hR_zero, opow_zero, one_mul] at hν
      obtain ⟨b, hbG, hgb, hb⟩ := D.b_cof x hx hx1 hγx _ hν
      refine ⟨b, hbG.trans_le hEκ, ?_, ?_⟩
      · rw [D.hG_low hbG]; exact hgb
      · rw [D.hR_low hbG]; exact hb
    · have hne : D.b x ^ D.hR κ' x ≠ 0 := opow_ne_zero _ hGE.pos.ne'
      have hq : ν / D.b x ^ D.hR κ' x < D.b x := (Ordinal.div_lt hne).2 hν
      obtain ⟨b, hbG, hgb, hb⟩ := D.b_cof x hx hx1 hγx _ hq
      have hb0 : b ≠ 0 := by rintro rfl; rw [D.R_zero] at hb; exact absurd hb (not_lt.2 zero_le)
      have htB : D.B ^ κ' * b + 0 < D.NB := by
        rw [add_zero]; exact D.mul_lt (hκ'κ.trans hκB) hbG
      refine ⟨D.B ^ κ' * b + 0, ?_, ?_, ?_⟩
      · rw [add_zero, ← hs, opow_add, opow_one]
        exact (mul_lt_mul_iff_right₀ (opow_pos _ D.B_E.pos)).2 hbG
      · rw [D.hG_cnf hκ'0 hb0 hbG (opow_pos _ D.B_E.pos) htB, D.hG_zero]
        exact max_lt (max_lt ((D.hQ_le _).trans_lt hgκ') ((D.Q_le _).trans_lt hgb)) hx.pos
      · rw [D.hR_cnf hκ'0 hb0 hbG (opow_pos _ D.B_E.pos) htB, D.hR_zero, add_zero]
        calc ν < D.b x ^ D.hR κ' x * (ν / D.b x ^ D.hR κ' x + 1) := by
              rw [mul_add_one]
              conv_lhs => rw [← Ordinal.div_add_mod ν (D.b x ^ D.hR κ' x)]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ ≤ D.b x ^ D.hR κ' x * D.R b x := mul_le_mul_left' (Order.add_one_le_of_lt hb) _
  · have hlim := D.lim_of_cof hx hx1 hγx hl hκB hgκ (hN κ hκN)
    obtain ⟨μ, hμ, hνμ⟩ := (lt_opow_of_isSuccLimit hGE.pos.ne' hlim).1 hν
    obtain ⟨κ', hκ'κ, hgκ', eκ'⟩ := hN κ hκN hgκ (μ + 1) (hlim.add_one_lt hμ)
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl; rw [D.hR_zero] at eκ'
      exact absurd eκ' (not_le.2 (lt_of_le_of_lt zero_le (lt_add_one μ)))
    have hν' : ν < D.b x ^ D.hR κ' x :=
      hνμ.trans_le (opow_le_opow_right hGE.pos ((lt_add_one μ).le.trans eκ'))
    obtain ⟨t, ht, hgt, hvt⟩ := IH κ' hκ'κ (hκ'κ.trans hκN) hκ'0 (hκ'κ.trans hκB) hgκ' ν hν'
    exact ⟨t, ht.trans_le (opow_le_opow_right D.B_E.pos hκ'κ.le), hgt, hvt⟩

/-- **Cofinality**: every `ν` below the reading of a code `c < ε_{B+1}` is at most the reading of a smaller code with
gate below `x`. -/
theorem hR_cof : ∀ c, c < D.NB → D.HCofAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg ν hν
  have hIH : ∀ j, j < c → D.HCofAt x j := fun j hj => IH j hj (hj.trans hc)
  have hGE := (D.b_E x hx hx1)
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg
    rw [D.hR_low hcE] at hν
    obtain ⟨b, hb, hgb, eb⟩ := D.cof x hx hx1 c hcE hg ν hν
    exact ⟨b, hb, by rw [D.hG_low (hb.trans hcE)]; exact hgb, by rw [D.hR_low (hb.trans hcE)]; exact eb⟩
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := D.parts hcE hc
  obtain ⟨g0, g1, g2⟩ := D.parts_g (omega0_lt_inE hx) hcE hc hg
  set k := log (D.B) c with hkdef
  set d := c / D.B ^ k with hddef
  set r := c % D.B ^ k with hrdef
  have hgc : D.hG c = max (max (D.hQ k) (D.Q d)) (D.hG r) := D.hG_dec hcE hc
  have hgk : D.hQ k < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt (hgc ▸ hg))
  have hkd : D.B ^ k ≤ c := by
    rw [← hdec]
    exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
  rw [D.hR_dec hcE hc] at hν
  set P := D.b x ^ D.hR k x with hP
  have hne : P ≠ 0 := opow_ne_zero _ hGE.pos.ne'
  rcases lt_or_ge ν (P * D.R d x) with hν1 | hν1
  · have hμ : ν / P < D.R d x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨d', hd'd, hgd', ed'⟩ := D.cof x hx hx1 d hdE g1 _ hμ
    have hd'E : d' < D.B := hd'd.trans hdE
    have hlt' : ∀ t, t < D.B ^ k → d' ≠ 0 → D.B ^ k * d' + t < c := by
      intro t ht _
      calc D.B ^ k * d' + t < D.B ^ k * d' + D.B ^ k := (add_lt_add_iff_left _).2 ht
        _ = D.B ^ k * (d' + 1) := by rw [mul_add_one]
        _ ≤ D.B ^ k * d := mul_le_mul_left' (Order.add_one_le_of_lt hd'd) _
        _ ≤ c := by rw [← hdec]; exact le_self_add
    rcases ed'.lt_or_eq with hq | hq
    · -- `ν < P·(q+1) ≤ P·d'(x)`
      have hd'0 : d' ≠ 0 := by rintro rfl; rw [D.R_zero] at hq; exact absurd hq (not_lt.2 zero_le)
      have hlt := hlt' 0 (opow_pos _ D.B_E.pos) hd'0
      refine ⟨D.B ^ k * d' + 0, hlt, ?_, ?_⟩
      · rw [D.hG_cnf hk hd'0 hd'E (opow_pos _ D.B_E.pos) (hlt.trans hc), D.hG_zero]
        exact max_lt (max_lt hgk ((D.Q_le _).trans_lt hgd')) hx.pos
      · rw [D.hR_cnf hk hd'0 hd'E (opow_pos _ D.B_E.pos) (hlt.trans hc), D.hR_zero, add_zero]
        refine le_of_lt ?_
        calc ν = P * (ν / P) + ν % P := (Ordinal.div_add_mod ν P).symm
          _ < P * (ν / P) + P := (add_lt_add_iff_left _).2 (Ordinal.mod_lt ν hne)
          _ = P * (ν / P + 1) := by rw [mul_add_one]
          _ ≤ P * D.R d' x := mul_le_mul_left' (Order.add_one_le_of_lt hq) _
    · have hρ : ν % P < P := Ordinal.mod_lt ν hne
      obtain ⟨t, htk, hgt, hvt⟩ := D.cofPow_of hx hx1 hγx hIH k hkc hk (hkc.trans hc) g0 _ hρ
      have hνe : ν = P * D.R d' x + ν % P := by
        rw [← hq]; exact (Ordinal.div_add_mod ν P).symm
      rcases eq_or_ne d' 0 with hd'0 | hd'0
      · refine ⟨t, htk.trans_le hkd, hgt, ?_⟩
        rw [hνe, hd'0, D.R_zero, mul_zero, zero_add]; exact hvt.le
      · have hlt := hlt' t htk hd'0
        refine ⟨D.B ^ k * d' + t, hlt, ?_, ?_⟩
        · rw [D.hG_cnf hk hd'0 hd'E htk (hlt.trans hc)]
          exact max_lt (max_lt hgk ((D.Q_le _).trans_lt hgd')) hgt
        · rw [D.hR_cnf hk hd'0 hd'E htk (hlt.trans hc), hνe]
          exact add_le_add le_rfl hvt.le
  · have e : P * D.R d x + (ν - P * D.R d x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - P * D.R d x < D.hR r x := by
      rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb'r, hgb', hb'⟩ := hIH r hrc g2 _ hν'
    have hb'k : b' < D.B ^ k := hb'r.trans hr
    have hlt : D.B ^ k * d + b' < c := by rw [← hdec]; exact (add_lt_add_iff_left _).2 hb'r
    refine ⟨D.B ^ k * d + b', hlt, ?_, ?_⟩
    · rw [D.hG_cnf hk hd0 hdE hb'k (hlt.trans hc)]
      exact max_lt ((le_max_left _ _).trans_lt (hgc ▸ hg)) hgb'
    · rw [D.hR_cnf hk hd0 hdE hb'k (hlt.trans hc), ← e]
      exact add_le_add le_rfl hb'

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem hR_cofE {c : Ordinal.{0}} (hc : c < D.NB) (hEc : gfE < c) (hg : D.hG c < x) {ν : Ordinal.{0}}
    (hν : ν < D.hR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ D.hG b < x ∧ ν ≤ D.hR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := D.hR_cof hx hx1 hγx c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [D.hG_low D.E_lt_B, D.g_E]; exact hx.pos, ?_⟩
    have hbG : b < D.B := hbE.trans D.E_lt_B
    rw [D.hG_low hbG] at hgb
    rw [D.hR_low hbG] at hνb
    rw [D.hR_low D.E_lt_B]
    exact hνb.trans (D.mono x hx hx1 gfE D.E_lt_B b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

end Cof

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : D.γ < σ)
include hB hγ

/-- **Lemma EXACT for the atom `ω^{b(ρ)+β}`** (`β ∈ Tᵖ[σ]`, `b(ρ) + β < ε_{b(ρ)+1}`) at every pair of
bases. -/
theorem bAtom_pi {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβe : D.b ρ + β < eN (D.b ρ)) :
    ω ^ (D.b ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (D.b ρ + β)) = ω ^ (D.b σ + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := D.b_pi σ ρ hB hγ
  have hρG := D.x_lt_b ρ hB.2.1 hρ1
  have heE := D.b_E ρ hB.2.1 hρ1
  have hσG := D.x_lt_b σ hB.1 hσ1
  have hseE := D.b_E σ hB.1 hσ1
  have hN1 : eN (D.b ρ) < Om1 := (D.eN_b_lt1 hB.2.1 hρ1).trans (gm1_facts hB.2.1 hρ1).2.2.1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ D.b ρ = D.b ρ := heE
    have h2 : ω ^ D.b σ = D.b σ := hseE
    rw [pi_lt hB hB.1.pos, add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ1 : β < Om1 := (lt_of_le_of_lt le_add_self hβe).trans hN1
  have hβ'T : β' ∈ TB ρ σ ∧ 1 + pi σ ρ β' = pi σ ρ β := by
    rcases lt_or_ge β ω with hω | hω
    · have hβσ : β < σ := hω.trans (omega0_lt_inE hB.1)
      have hβ'σ : β' < σ := lt_of_le_of_lt (sub_le_self β 1) hβσ
      refine ⟨mem_TB_of_lt hB hβ'σ, ?_⟩
      rw [pi_lt hB hβ'σ, pi_lt hB hβσ, hb]
    · have e : β' = β := by
        have h := Ordinal.add_sub_cancel 1 β
        rw [one_add_of_omega0_le hω] at h
        rw [hβ']; exact h
      rw [e]
      refine ⟨hβTB, one_add_of_omega0_le ?_⟩
      rcases lt_or_ge β σ with hβσ | hσβ
      · rw [pi_lt hB hβσ]; exact hω
      · exact (omega0_lt_inE hB.1).le.trans (pi_ge hB hβTB hσβ)
  obtain ⟨hβ'TB, hπ1⟩ := hβ'T
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB hβ'TB
  rw [hpe] at hpξ
  -- the bounds at `ρ` and at `σ`
  have hξ1 : D.b ρ + β' < Om1 := lt_of_le_of_lt (add_le_add le_rfl (sub_le_self β 1)) (hβe.trans hN1)
  have hbρ : D.b ρ + 1 + β' < eN (D.b ρ) := by rw [add_assoc, hb]; exact hβe
  have hsum : D.b ρ + β ∈ TB ρ σ ∧ pi σ ρ (D.b ρ + β) = D.b σ + pi σ ρ β := by
    obtain ⟨s1, s2⟩ := pi_add hB heTB hβTB
    exact ⟨s1, by rw [s2, hpe]⟩
  have hbσ : D.b σ + 1 + pi σ ρ β' < eN (D.b σ) := by
    rw [add_assoc, hπ1, ← hsum.2]; exact D.pi_lt_eNb hB hγ hsum.1 hβe
  have hξ1' : D.b σ + pi σ ρ β' < Om1 :=
    lt_of_le_of_lt (add_le_add le_rfl le_add_self) (by
      rw [hπ1, ← hsum.2]
      exact (D.pi_lt_eNb hB hγ hsum.1 hβe).trans ((D.eN_b_lt1 hB.1 hσ1).trans (gm1_facts hB.1 hσ1).2.2.1))
  have hv := vt_ps hB.2.1 hρ1 heE hρG hbρ hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hv' := vt_ps hB.1 hσ1 hseE hσG hbσ hξ1'
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **`π(ω^X) = ω^{π X}`** for every `X ∈ Tᵖ[σ]` with `b(ρ) ≤ X < ε_{b(ρ)+1}`, at every pair of bases. -/
theorem opowB_pi {X : Ordinal.{0}} (hX : X ∈ TB ρ σ) (hGX : D.b ρ ≤ X) (hXe : X < eN (D.b ρ)) :
    ω ^ X ∈ TB ρ σ ∧ pi σ ρ (ω ^ X) = ω ^ (pi σ ρ X) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨heTB, hpe⟩ := D.b_pi σ ρ hB hγ
  have hX1 : X < Om1 := hXe.trans ((D.eN_b_lt1 hB.2.1 hρ1).trans (gm1_facts hB.2.1 hρ1).2.2.1)
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hX hGX hX1
  have e : D.b ρ + (X - D.b ρ) = X := Ordinal.add_sub_cancel_of_le hGX
  have hle : D.b σ ≤ pi σ ρ X := by
    rw [← hpe]; exact ((pi_bijOn hB).2.le_iff_le heTB hX).2 hGX
  obtain ⟨h1, h2⟩ := D.bAtom_pi hB hγ hβTB (by rw [e]; exact hXe)
  rw [e] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, hpβ, hpe, Ordinal.add_sub_cancel_of_le hle]



/-- `π(b(ρ)·n) = b(σ)·n`. -/
theorem mulBn_pi : ∀ n : ℕ, D.b ρ * (n : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ (D.b ρ * (n : Ordinal.{0})) =
    D.b σ * (n : Ordinal.{0})
  | 0 => by
    simp only [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := mulBn_pi n
    obtain ⟨g1, g2⟩ := D.b_pi σ ρ hB hγ
    obtain ⟨h3, h4⟩ := pi_add hB h1 g1
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h3, by rw [h4, h2, g2]⟩

/-- **Lemma EXACT for the atom `ω^{b(ρ)·K+β}`** (`K ≥ 1`, `b(ρ)·K < ε_{b(ρ)+1}`, `β < b(ρ)`), once
`π(b(ρ)·K) = b(σ)·K'`. -/
theorem bkAtom_pi {K K' β : Ordinal.{0}} (hK : 1 ≤ K) (hKe : D.b ρ * K < eN (D.b ρ))
    (hm : D.b ρ * K ∈ TB ρ σ ∧ pi σ ρ (D.b ρ * K) = D.b σ * K') (hβTB : β ∈ TB ρ σ) (hβe : β < D.b ρ) :
    ω ^ (D.b ρ * K + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (D.b ρ * K + β)) = ω ^ (D.b σ * K' + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨hmTB, hmpi⟩ := hm
  obtain ⟨h1, h2⟩ := pi_add hB hmTB hβTB
  have hGX : D.b ρ ≤ D.b ρ * K + β := (le_mul_of_one_le_right' hK).trans le_self_add
  have hXe : D.b ρ * K + β < eN (D.b ρ) :=
    (inE_indec (eN_E _)).add_lt hKe (hβe.trans (lt_eN _))
  obtain ⟨h3, h4⟩ := D.opowB_pi hB hγ h1 hGX hXe
  exact ⟨h3, by rw [h4, h2, hmpi]⟩

/-- **Lemma EXACT for every code `c < ε_{B+1}`** at every pair of bases above its gate. -/
theorem hR_pi : ∀ c, c < D.NB → D.hG c < σ → D.hR c ρ ∈ TB ρ σ ∧ pi σ ρ (D.hR c ρ) = D.hR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg
    rw [D.hR_low hcE, D.hR_low hcE]
    exact D.ex σ ρ hB c hcE hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := D.parts hcE hc
  obtain ⟨g0, g1, g2⟩ := D.parts_g (omega0_lt_inE hσE) hcE hc hg
  set k := log (D.B) c with hkdef
  have hkB : k < D.NB := hkc.trans hc
  have g0ρ : D.hG k < ρ := g0.trans hB.2.2.1
  obtain ⟨h1, h2⟩ := IH _ hrc (hrc.trans hc) g2
  -- `π(b(ρ)·k(ρ)) = b(σ)·k(σ)`
  have hmk : D.b ρ * D.hR k ρ ∈ TB ρ σ ∧ pi σ ρ (D.b ρ * D.hR k ρ) = D.b σ * D.hR k σ := by
    rcases lt_or_ge k ω with hω | hω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      rw [hn, D.hR_nat, D.hR_nat]
      exact D.mulBn_pi hB hγ n
    · have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 hω
      obtain ⟨hEkB, hgEk, hREk⟩ := D.mulB k hk hkB
      have hlt : D.B * k < c := (D.mulB_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      obtain ⟨m1, m2⟩ := IH _ hlt hEkB (hgEk.trans_lt g0)
      rw [hREk ρ hρE hρ1 g0ρ] at m1 m2
      rw [hREk σ hσE hσ1 g0] at m2
      exact ⟨m1, m2⟩
  have hKe : D.b ρ * D.hR k ρ < eN (D.b ρ) := by
    have h3 := D.hR_lt_eNb hρE hρ1 (D.mulB k hk hkB).1 ((D.mulB k hk hkB).2.1.trans_lt g0ρ)
    rwa [(D.mulB k hk hkB).2.2 ρ hρE hρ1 g0ρ] at h3
  have hK1 : 1 ≤ D.hR k ρ := one_le_iff_pos.2 (D.hR_pos hρE hρ1 hk hkB g0ρ)
  have hat : ∀ β, β ∈ TB ρ σ → β < D.b ρ → ω ^ (D.b ρ * D.hR k ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (D.b ρ * D.hR k ρ + β)) = ω ^ (D.b σ * D.hR k σ + pi σ ρ β) :=
    fun β hβ hβe => D.bkAtom_pi hB hγ hK1 hKe hmk hβ hβe
  obtain ⟨h3, h4⟩ := D.dig σ ρ hB _ hdE g1 _ _ hat
  rw [← D.bpow_eq hρE hρ1] at h3 h4
  rw [← D.bpow_eq hσE hσ1] at h4
  rw [D.hR_dec hcE hc, D.hR_dec hcE hc]
  obtain ⟨h5, h6⟩ := pi_add hB h3 h1
  exact ⟨h5, by rw [h6, h4, h2]⟩

/-- **`π(b(ρ)·k(ρ)) = b(σ)·k(σ)`** for every code `1 ≤ k < ε_{B+1}` with gate below `σ`. -/
theorem mulB_pi {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) (hg : D.hG k < σ) :
    D.b ρ * D.hR k ρ ∈ TB ρ σ ∧ pi σ ρ (D.b ρ * D.hR k ρ) = D.b σ * D.hR k σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨hEkB, hgEk, hREk⟩ := D.mulB k hk hkB
  obtain ⟨m1, m2⟩ := D.hR_pi hB hγ _ hEkB (hgEk.trans_lt hg)
  rw [hREk ρ hB.2.1 hρ1 (hg.trans hB.2.2.1)] at m1 m2
  rw [hREk σ hB.1 hσ1 hg] at m2
  exact ⟨m1, m2⟩

/-- **THE DIGIT RULE ONE LEVEL UP**: `π(ω^P·c(ρ)) = ω^{P'}·c(σ)` for every code `c < ε_{B+1}` with gate below `σ`,
once the atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < ε_{b(ρ)+1}`) are exact: the digit rule of `D` at `P + b(ρ)·k(ρ)`. -/
theorem hdig : ∀ c, c < D.NB → D.hG c < σ → ∀ P P' : Ordinal.{0},
    (∀ β, β ∈ TB ρ σ → β < eN (D.b ρ) →
      ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
    ω ^ P * D.hR c ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * D.hR c ρ) = ω ^ P' * D.hR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg P P' hat
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg
    rw [D.hR_low hcE, D.hR_low hcE]
    exact D.dig σ ρ hB c hcE hg P P' (fun β hβ hβe => hat β hβ (hβe.trans (lt_eN _)))
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := D.parts hcE hc
  obtain ⟨g0, g1, g2⟩ := D.parts_g (omega0_lt_inE hσE) hcE hc hg
  set k := log (D.B) c with hkdef
  have hkB : k < D.NB := hkc.trans hc
  have g0ρ : D.hG k < ρ := g0.trans hB.2.2.1
  obtain ⟨h1, h2⟩ := IH _ hrc (hrc.trans hc) g2 P P' hat
  obtain ⟨m1, m2⟩ := D.mulB_pi hB hγ hk hkB g0
  have hKe : D.b ρ * D.hR k ρ < eN (D.b ρ) := by
    have h3 := D.hR_lt_eNb hρE hρ1 (D.mulB k hk hkB).1 ((D.mulB k hk hkB).2.1.trans_lt g0ρ)
    rwa [(D.mulB k hk hkB).2.2 ρ hρE hρ1 g0ρ] at h3
  have hat' : ∀ β, β ∈ TB ρ σ → β < D.b ρ → ω ^ ((P + D.b ρ * D.hR k ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + D.b ρ * D.hR k ρ) + β)) = ω ^ ((P' + D.b σ * D.hR k σ) + pi σ ρ β) := by
    intro β hβ hβe
    obtain ⟨s1, s2⟩ := pi_add hB m1 hβ
    have hlt : D.b ρ * D.hR k ρ + β < eN (D.b ρ) := (inE_indec (eN_E _)).add_lt hKe (hβe.trans (lt_eN _))
    obtain ⟨t1, t2⟩ := hat _ s1 hlt
    rw [s2, m2] at t2
    rw [add_assoc, add_assoc]
    exact ⟨t1, t2⟩
  obtain ⟨h3, h4⟩ := D.dig σ ρ hB _ hdE g1 _ _ hat'
  have eρ : ω ^ P * D.hR c ρ = ω ^ (P + D.b ρ * D.hR k ρ) * D.R (c / D.B ^ k) ρ + ω ^ P * D.hR (c % D.B ^ k) ρ := by
    rw [D.hR_dec hcE hc, mul_add, D.bpow_eq hρE hρ1, ← mul_assoc, ← opow_add]
  have eσ : ω ^ P' * D.hR c σ = ω ^ (P' + D.b σ * D.hR k σ) * D.R (c / D.B ^ k) σ +
      ω ^ P' * D.hR (c % D.B ^ k) σ := by
    rw [D.hR_dec hcE hc, mul_add, D.bpow_eq hσE hσ1, ← mul_assoc, ← opow_add]
  obtain ⟨h5, h6⟩ := pi_add hB h3 h1
  rw [eρ, eσ]
  exact ⟨h5, by rw [h6, h4, h2]⟩

end Pi

/-- **The codes below `c ≤ ε_{B+1}` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem hcount {c y : Ordinal.{0}} (hc : c ≤ D.NB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // D.hG b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // D.hG b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨D.hR b.1.1 y, D.hR_lt1 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : D.hR b.1.1 y = D.hR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (D.hR_mono hy hy1 _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (D.hR_mono hy hy1 _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'


end GrD

end Googology.Trans.PoR.InaccPsi.R2.Gr
