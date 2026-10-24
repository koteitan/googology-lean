import Googology.Trans.PoR.InaccPsi.R2.GiSq

/-!
# THE READING OF A CODE `ε_{Ω₁+1}·γ + a` AT A BASE `x`: `ε_{x+1}·γ(x) + a(x)`, with Lemma EXACT at every pair of bases

* `giR` (the reading), `giR_E` (`ε_{Ω₁+1}` reads `ε_{x+1}`), `giR_lt0` (**below `Γ_{x+1}`**), `giR_mono` (**strictly
  increasing**), `giR_succ` (`(c+1)(x) = c(x) + 1`), `giR_cof` (**every `ν` below the reading of a code
  `c > ε_{Ω₁+1}` is at most the reading of a code `b ∈ [ε_{Ω₁+1}, c)` with gate below `x`**);
* `gi_eAtom_pi` (**Lemma EXACT for the atom `ω^{ε_{ρ+1}+β}` at every pair of bases** (no `υ`-point hypothesis):
  `ε_{ρ+1} = ϑ^ρ(Ω₁)` (`Gh.gh_eN_pi`), `ω^{ε_{ρ+1}+1+β'} = ϑ^ρ(ε_{ρ+1}+β')` (`vt_eN`), the clause
  `π(ϑ^ρ(ξ)) = ϑ^σ(π ξ)` (`pi_vt`)), `gi_eNr_pi` (**`π(ε_{ρ+1}·γ(ρ)) = ε_{σ+1}·γ(σ)`**, by the normal form of `γ`),
  `giR_pi` (**Lemma EXACT for every code below `ε_{Ω₁+1}²`**).

No new axiom.  New definition: `giR`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **The reading** of `c = ε_{Ω₁+1}·γ + a` at `x`: `ε_{x+1}·γ(x) + a(x)`. -/
noncomputable def giR (c x : Ordinal.{0}) : Ordinal.{0} := eN x * rdc (c / gfE) x + rdc (c % gfE) x

theorem giR_code {γ a : Ordinal.{0}} (ha : a < gfE) (x : Ordinal.{0}) :
    giR (gfE * γ + a) x = eN x * rdc γ x + rdc a x := by
  rw [giR, Ordinal.mul_add_div _ gfE_ne, Ordinal.div_eq_zero_of_lt ha, add_zero, Ordinal.mul_add_mod_self,
    Ordinal.mod_eq_of_lt ha]

theorem giQ_code {γ a : Ordinal.{0}} (ha : a < gfE) : giG (gfE * γ + a) = max (giQ γ) (gtc a) := by
  rw [giG, Ordinal.mul_add_div _ gfE_ne, Ordinal.div_eq_zero_of_lt ha, add_zero, Ordinal.mul_add_mod_self,
    Ordinal.mod_eq_of_lt ha]

theorem giR_E (x : Ordinal.{0}) : giR gfE x = eN x := by
  have h := giR_code (γ := 1) eW_E.pos x
  rwa [mul_one, add_zero, (rdc_const gf_one_lt_Om1 x).1, mul_one, rdc_zero, add_zero] at h

theorem giR_lt_E {c : Ordinal.{0}} (hc : c < gfE) (x : Ordinal.{0}) : giR c x = rdc c x := by
  rw [giR, Ordinal.div_eq_zero_of_lt hc, Ordinal.mod_eq_of_lt hc, rdc_zero, mul_zero, zero_add]

theorem giR_succ {b : Ordinal.{0}} (x : Ordinal.{0}) : giR (b + 1) x = giR b x + 1 := by
  have h1 : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  rw [giR, giR, gi_div_small b h1, gh_mod_small b h1, (rdc_succ _ (gh_mod_lt b) x).1, add_assoc]

theorem giG_le_succ (b : Ordinal.{0}) : giG b ≤ giG (b + 1) := by
  have h1 : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  rw [giG, giG, gi_div_small b h1, gh_mod_small b h1]
  exact max_le_max le_rfl (rdc_succ _ (gh_mod_lt b) 0).2.1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx

theorem gi_parts {c : Ordinal.{0}} (hc : c < giB) (hg : giG c < x) : gtc (c / gfE) < x ∧ gtc (c % gfE) < x :=
  giG_parts hc (omega0_lt_inE hx) hg

include hx1

/-- **The reading is below `Γ_{x+1}`.** -/
theorem giR_lt0 {c : Ordinal.{0}} (hc : c < giB) (hg : giG c < x) : giR c x < gq 0 x := by
  obtain ⟨g1, g2⟩ := gi_parts hx hc hg
  have hE := (gfq0_facts hx hx1).2.2.2
  have he := gh_eN_lt_gq0 hx hx1
  exact (inE_indec hE).add_lt (hE.mul_lt he ((rdc_lt_eN hx _ g1).trans he)) ((rdc_lt_eN hx _ g2).trans he)

theorem giR_lt1 {c : Ordinal.{0}} (hc : c < giB) (hg : giG c < x) : giR c x + 1 < gq 0 x := by
  have hE := (gfq0_facts hx hx1).2.2.2
  exact (inE_indec hE).add_lt (giR_lt0 hx hx1 hc hg) (one_lt_omega0.trans (omega0_lt_inE hE))

omit hx1 in
/-- **The reading is strictly increasing.** -/
theorem giR_mono {b c : Ordinal.{0}} (hc : c < giB) (hbc : b < c) (hgb : giG b < x) (hgc : giG c < x) :
    giR b x < giR c x := by
  have hb : b < giB := hbc.trans hc
  obtain ⟨gb1, gb2⟩ := gi_parts hx hb hgb
  obtain ⟨gc1, gc2⟩ := gi_parts hx hc hgc
  have hq : b / gfE ≤ c / gfE := (Ordinal.le_div gfE_ne).2 ((Ordinal.mul_div_le b gfE).trans hbc.le)
  rcases hq.lt_or_eq with hq | hq
  · have h1 : rdc (b / gfE) x < rdc (c / gfE) x := rdc_mono hx (gi_div_lt hc) hq gc1 gb1
    calc giR b x < eN x * rdc (b / gfE) x + eN x := (add_lt_add_iff_left _).2 (rdc_lt_eN hx _ gb2)
      _ = eN x * (rdc (b / gfE) x + 1) := by rw [mul_add_one]
      _ ≤ eN x * rdc (c / gfE) x := mul_le_mul_left' (Order.add_one_le_of_lt h1) _
      _ ≤ giR c x := le_self_add
  · have hr : b % gfE < c % gfE := by
      by_contra hle
      push Not at hle
      have := (add_le_add_iff_left (gfE * (b / gfE))).2 hle
      rw [gi_dec, hq, gi_dec] at this
      exact absurd hbc (not_lt.2 this)
    rw [giR, giR, hq]
    exact (add_lt_add_iff_left _).2 (rdc_mono hx (gh_mod_lt c) hr gc2 gb2)

/-- **Cofinality**: every `ν` below the reading of a code `c ∈ (ε_{Ω₁+1}, ε_{Ω₁+1}²)` is at most the reading of a code
`b ∈ [ε_{Ω₁+1}, c)` with gate below `x`. -/
theorem giR_cof {c : Ordinal.{0}} (hc : c < giB) (hEc : gfE < c) (hg : giG c < x) {ν : Ordinal.{0}}
    (hν : ν < giR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ giG b < x ∧ ν ≤ giR b x := by
  obtain ⟨g1, g2⟩ := gi_parts hx hc hg
  have hγW := gi_div_lt hc
  set γ := c / gfE with hγ
  set a := c % gfE with ha
  have hcdec : c = gfE * γ + a := (gi_dec c).symm
  have hγ1 : γ ≠ 0 := by
    intro h0
    have : c < gfE := by rw [hcdec, h0, mul_zero, zero_add]; exact gh_mod_lt c
    exact absurd hEc (not_lt.2 this.le)
  have hωx := omega0_lt_inE hx
  have hne : eN x ≠ 0 := (eN_E x).pos.ne'
  rcases lt_or_ge ν (eN x * rdc γ x) with hν1 | hν1
  · -- `ν = ε_{x+1}·μ + r`, `μ < γ(x)`
    have hμ : ν / eN x < rdc γ x := (Ordinal.div_lt hne).2 hν1
    obtain ⟨β, hβγ, hgβ, eβ⟩ := rdc_surj hx hx1.le hγW g1 hμ
    have hr : ν % eN x < eN x := Ordinal.mod_lt ν hne
    obtain ⟨k, hk⟩ := ghTw_cof hx hr
    rcases eq_or_ne β 0 with rfl | hβ0
    · refine ⟨gfE, le_rfl, hEc, by rw [giG_E]; exact hx.pos, ?_⟩
      rw [giR_E]
      have e : ν = eN x * (ν / eN x) + ν % eN x := (Ordinal.div_add_mod ν (eN x)).symm
      rw [← eβ, rdc_zero, mul_zero, zero_add] at e
      rw [e]; exact hr.le
    · have htw := ghTw_lt k
      refine ⟨gfE * β + ghTw k, ?_, ?_, ?_, ?_⟩
      · calc gfE = gfE * 1 := (mul_one _).symm
          _ ≤ gfE * β := mul_le_mul_left' (one_le_iff_ne_zero.2 hβ0) _
          _ ≤ _ := le_self_add
      · calc gfE * β + ghTw k < gfE * β + gfE := (add_lt_add_iff_left _).2 htw
          _ = gfE * (β + 1) := by rw [mul_add_one]
          _ ≤ gfE * γ := mul_le_mul_left' (Order.add_one_le_of_lt hβγ) _
          _ ≤ c := by rw [hcdec]; exact le_self_add
      · rw [giQ_code htw]
        exact max_lt ((giQ_le β).trans_lt hgβ) ((ghTw_gtc k).trans_lt (Lu.lu_one_lt_E hx))
      · rw [giR_code htw, eβ]
        conv_lhs => rw [← Ordinal.div_add_mod ν (eN x)]
        exact add_le_add le_rfl hk.le
  · -- `ν = ε_{x+1}·γ(x) + ν'`, `ν' < a(x)`
    have e : eN x * rdc γ x + (ν - eN x * rdc γ x) = ν := Ordinal.add_sub_cancel_of_le hν1
    have hν' : ν - eN x * rdc γ x < rdc a x := by
      rw [← e, giR] at hν; exact (add_lt_add_iff_left _).1 hν
    obtain ⟨a', ha'a, hga', ea'⟩ := rdc_surj hx hx1.le (gh_mod_lt c) g2 hν'
    have ha'E : a' < gfE := ha'a.trans (gh_mod_lt c)
    refine ⟨gfE * γ + a', ?_, ?_, ?_, ?_⟩
    · calc gfE = gfE * 1 := (mul_one _).symm
        _ ≤ gfE * γ := mul_le_mul_left' (one_le_iff_ne_zero.2 hγ1) _
        _ ≤ _ := le_self_add
    · rw [hcdec]; exact (add_lt_add_iff_left _).2 ha'a
    · rw [giQ_code ha'E]
      exact max_lt ((le_max_left _ _).trans_lt hg) hga'
    · rw [giR_code ha'E, ea', e]

end Base

/-! ## Lemma EXACT -/

/-- **Lemma EXACT for the atom `ω^{ε_{ρ+1}+β}` at every pair of bases** (`β ∈ Tᵖ[σ]`, `β < ε_{ρ+1}`). -/
theorem gi_eAtom_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ)
    (hβe : β < eN ρ) : ω ^ (eN ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ + β)) = ω ^ (eN σ + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := gh_eN_pi hB
  have he1 : eN ρ < Om1 := Ge.eN_lt_Om1' hB.2.1 hρ1
  have hes1 : eN σ < Om1 := Ge.eN_lt_Om1' hB.1 hσ1
  have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ eN ρ = eN ρ := eN_E ρ
    have h2 : ω ^ eN σ = eN σ := eN_E σ
    rw [pi_lt hB hB.1.pos, add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  have hπβ : pi σ ρ β < eN σ := by rw [← hpe]; exact (pi_bijOn hB).2 hβTB heTB hβe
  -- `β = 1 + β'`
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ'e : β' < eN ρ := lt_of_le_of_lt (sub_le_self β 1) hβe
  -- `β' ∈ Tᵖ[σ]` and `1 + π(β') = π(β)`
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
  have hξ1 : eN ρ + β' < Om1 := Om1_add_lt he1 (hβ'e.trans he1)
  have hv := vt_eN hB.2.1 hρ1 hβ'e hξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hπβ' : pi σ ρ β' < eN σ := lt_of_le_of_lt (by rw [← hπ1]; exact le_add_self) hπβ
  have hv' := vt_eN hB.1 hσ1 hπβ' (Om1_add_lt hes1 (hπβ'.trans hes1))
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **`π(ε_{ρ+1}·γ(ρ)) = ε_{σ+1}·γ(σ)`** at every pair of bases, for every code `γ < ε_{Ω₁+1}` with gate below `σ`. -/
theorem gi_eNr_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : ∀ γ, γ < gfE → gtc γ < σ →
    eN ρ * rdc γ ρ ∈ TB ρ σ ∧ pi σ ρ (eN ρ * rdc γ ρ) = eN σ * rdc γ σ := by
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
  have hl := log_lt hγ0 hγW
  set l := log Om1 γ with hldef
  set q := γ / Om1 ^ l with hqdef
  set r := γ % Om1 ^ l with hrdef
  obtain ⟨h1, h2⟩ := IH r hrγ (hrγ.trans hγW) (gr.trans_lt hg)
  have hqσ : q < σ := gq.trans_lt hg
  -- the term of `x·l(x)`
  have hcb : OT.CB (tcx l) σ := cb_tcx hσE.pos l (gl.trans_lt hg)
  -- `ε_{x+1}·γ(x) = ω^{ε_{x+1} + x·l(x)}·q + ε_{x+1}·r(x)`
  have edec : ∀ x, InE x → eN x * rdc γ x = ω ^ (eN x + OT.ev (tcx l) x) * q + eN x * rdc r x := by
    intro x hx
    rw [rdc_dec hγ0 hγW, mul_add, ← mul_assoc, pw_eq' hx, eN_mul_opow, ev_tcx hx]
  -- the atoms `ω^{ε_{x+1} + x·l(x) + z}`
  have hatom : ∀ z, z < σ → ω ^ (eN ρ + (OT.ev (tcx l) ρ + z)) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ + (OT.ev (tcx l) ρ + z))) = ω ^ (eN σ + (OT.ev (tcx l) σ + z)) := by
    intro z hz
    have hcb' : OT.CB (OT.add (tcx l) (OT.k z)) σ := ⟨hcb, hz⟩
    obtain ⟨t1, t2⟩ := pi_ev hB _ hcb'
    simp only [OT.ev_add, OT.ev_k] at t1 t2
    have hlt : OT.ev (tcx l) ρ + z < eN ρ := by
      have := ev_lt_eN (OT.CB_mono hcb' hB.2.2.1.le)
      simpa only [OT.ev_add, OT.ev_k] using this
    obtain ⟨t3, t4⟩ := gi_eAtom_pi hB t1 hlt
    rw [t2] at t4
    exact ⟨t3, t4⟩
  -- `ω^e·q` by the normal form of `q`
  have hmul : ∀ q', q' < σ → ω ^ (eN ρ + OT.ev (tcx l) ρ) * q' ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ + OT.ev (tcx l) ρ) * q') = ω ^ (eN σ + OT.ev (tcx l) σ) * q' := by
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
  rw [edec ρ hρE, edec σ hσE]
  obtain ⟨m3, m4⟩ := pi_add hB m1 h1
  exact ⟨m3, by rw [m4, m2, h2]⟩

/-- **Lemma EXACT for every code `c < ε_{Ω₁+1}²`** at every pair of bases above its gate. -/
theorem giR_pi {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < giB) (hg : giG c < σ) :
    giR c ρ ∈ TB ρ σ ∧ pi σ ρ (giR c ρ) = giR c σ := by
  obtain ⟨g1, g2⟩ := gi_parts hB.1 hc hg
  obtain ⟨h1, h2⟩ := gi_eNr_pi hB _ (gi_div_lt hc) g1
  obtain ⟨h3, h4⟩ := rdc_pi hB (gh_mod_lt c) g2
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [giR, h6, h2, h4, giR]⟩

end Googology.Trans.PoR.InaccPsi.R2.Gi
