import Googology.Trans.PoR.InaccPsi.R2.GmG0L

/-!
# THE CODES `Γ_{Ω₁+1}·γ + c` (`γ, c < Γ_{Ω₁+1}`): reading, gate, order, cofinality, Lemma EXACT

Every `c < Γ_{Ω₁+1}·Γ_{Ω₁+1}` is `Γ_{Ω₁+1}·γ + c'` with `γ = c / Γ_{Ω₁+1}` and `c' = c mod Γ_{Ω₁+1}` codes of
`R2.Gl`.  The reading is `mqR c x = Γ_{x+1}·γ(x) + c'(x)`; the gate is the larger of the gates of `γ` (taken `0` for
finite `γ`, `Gl.glQ`) and `c'`.  Below `Γ_{Ω₁+1}·ω` these are `mgR`, `mgG` of `R2.GmG0`.

* `mqB` (`Γ_{Ω₁+1}²`), `mqR`, `mqG`, `mq_split`, `mqR_split`, `mqG_split`, `mqR_low`, `mqG_low`;
* `mqR_lt1` (**below `Γ_{x+2}`**), `mqR_mono` (**strictly increasing**), `mqR_succ`, `mqG_le_succ`, `mqG_succ`,
  `mqR_cofE` (**cofinality**);
* `mq_vt_G` (**`ϑʳ(Γ_{r+1} + β') = ω^{Γ_{r+1}+1+β'}`** for `β' < Γ_{r+1}`, [W07a] Lemma 4.2 through `vt_wbar`,
  `wbar_eq` with the pseudo-base `Γ_{r+1}`), `mq_GAtom_pi` (**Lemma EXACT for the atom `ω^{Γ_{ρ+1}+β}`**,
  `β < Γ_{ρ+1}`),
  `mq_Gmul_pi` (**`π(Γ_{ρ+1}·γ(ρ)) = Γ_{σ+1}·γ(σ)`** by `Gl.gl_dig`), `mqR_pi` (**Lemma EXACT for every code below
  `Γ_{Ω₁+1}²`** at every pair of bases above the gate).

No new axiom.  New definitions: `mqB`, `mqR`, `mqG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The codes, the reading and the gate -/

/-- **The bound** `Γ_{Ω₁+1}²`. -/
noncomputable def mqB : Ordinal.{0} := gcG 0 * gcG 0

/-- **The reading** `Γ_{x+1}·γ(x) + c'(x)` of `c = Γ_{Ω₁+1}·γ + c'`. -/
noncomputable def mqR (c x : Ordinal.{0}) : Ordinal.{0} := lgG x * glR (c / gcG 0) x + glR (c % gcG 0) x

/-- **The gate**: the larger of the gate of `γ` (`0` for finite `γ`) and the gate of `c'`. -/
noncomputable def mqG (c : Ordinal.{0}) : Ordinal.{0} := max (glQ (c / gcG 0)) (glG (c % gcG 0))

theorem mq_split_eq (γ : Ordinal.{0}) {c : Ordinal.{0}} (hc : c < gcG 0) :
    (gcG 0 * γ + c) / gcG 0 = γ ∧ (gcG 0 * γ + c) % gcG 0 = c := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ mg_G0_ne, Ordinal.div_eq_zero_of_lt hc, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

/-- **Every code below `Γ_{Ω₁+1}²` is `Γ_{Ω₁+1}·γ + c'`.** -/
theorem mq_split {c : Ordinal.{0}} (hc : c < mqB) : ∃ γ c', γ < gcG 0 ∧ c' < gcG 0 ∧ c = gcG 0 * γ + c' :=
  ⟨c / gcG 0, c % gcG 0, (Ordinal.div_lt mg_G0_ne).2 hc, Ordinal.mod_lt c mg_G0_ne,
    (Ordinal.div_add_mod c (gcG 0)).symm⟩

theorem mqR_split (γ : Ordinal.{0}) {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) :
    mqR (gcG 0 * γ + c) x = lgG x * glR γ x + glR c x := by
  unfold mqR; rw [(mq_split_eq γ hc).1, (mq_split_eq γ hc).2]

theorem mqG_split (γ : Ordinal.{0}) {c : Ordinal.{0}} (hc : c < gcG 0) :
    mqG (gcG 0 * γ + c) = max (glQ γ) (glG c) := by
  unfold mqG; rw [(mq_split_eq γ hc).1, (mq_split_eq γ hc).2]

theorem mqR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : mqR c x = glR c x := by
  have := mqR_split 0 hc x
  rwa [mul_zero, zero_add, glR_zero, mul_zero, zero_add] at this

theorem mqG_low {c : Ordinal.{0}} (hc : c < gcG 0) : mqG c = glG c := by
  have := mqG_split 0 hc
  rwa [mul_zero, zero_add, glQ_zero, max_eq_right zero_le] at this

theorem mq_G0_lt_B : gcG 0 < mqB := by
  unfold mqB
  conv_lhs => rw [← mul_one (gcG 0)]
  exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 gl_one_lt_G0

theorem mqB_eq : mqB = ω ^ (gcG 0 + gcG 0) := by
  unfold mqB; rw [opow_add, geG_E]

theorem mqB_lim : IsSuccLimit mqB := by
  rw [mqB_eq]; exact Ph.ph_opow_lim (gl_G0_E.pos.trans_le le_self_add).ne'

theorem mq_E_lt_B : gfE < mqB := gfE_lt_G0.trans mq_G0_lt_B

theorem mq_glG_lt_Om1 (c : Ordinal.{0}) : glG c < Om1 := by
  rcases lt_or_ge c (gcG 0) with h | h
  · exact glG_lt_Om1 c h
  · rw [glG_high h]; exact lt_of_le_of_lt zero_le omega_lt_Om1

theorem mqG_lt_Om1 (c : Ordinal.{0}) : mqG c < Om1 :=
  max_lt ((glQ_le _).trans_lt (mq_glG_lt_Om1 _)) (mq_glG_lt_Om1 _)

theorem mqG_zero : mqG 0 = 0 := by rw [mqG_low gl_G0_E.pos, glG_zero]

theorem mqG_E : mqG gfE = 0 := by rw [mqG_low gfE_lt_G0, glG_E]

theorem mqG_lowE {c : Ordinal.{0}} (hc : c < gfE) : mqG c = gtc c := by
  rw [mqG_low (hc.trans gfE_lt_G0), glG_low hc]

theorem mqR_E (x : Ordinal.{0}) : mqR gfE x = eN x := by rw [mqR_low gfE_lt_G0, glR_E]

theorem mq_succ_parts (b : Ordinal.{0}) :
    (b + 1) / gcG 0 = b / gcG 0 ∧ (b + 1) % gcG 0 = b % gcG 0 + 1 ∧ b % gcG 0 + 1 < gcG 0 := by
  have hb : b % gcG 0 < gcG 0 := Ordinal.mod_lt b mg_G0_ne
  have e : b + 1 = gcG 0 * (b / gcG 0) + (b % gcG 0 + 1) := by rw [← add_assoc, Ordinal.div_add_mod]
  have h1 := gl_G0_lim.add_one_lt hb
  refine ⟨?_, ?_, h1⟩
  · rw [e, Ordinal.mul_add_div _ mg_G0_ne, Ordinal.div_eq_zero_of_lt h1, add_zero]
  · rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt h1]

theorem mqR_succ (b x : Ordinal.{0}) : mqR (b + 1) x = mqR b x + 1 := by
  obtain ⟨e1, e2, -⟩ := mq_succ_parts b
  unfold mqR; rw [e1, e2, glR_succ_all, add_assoc]

theorem mqG_le_succ (b : Ordinal.{0}) : mqG b ≤ mqG (b + 1) := by
  obtain ⟨e1, e2, -⟩ := mq_succ_parts b
  unfold mqG; rw [e1, e2]; exact max_le_max le_rfl (glG_le_succ_all _)

theorem mqG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (b : Ordinal.{0}) (hg : mqG b < Z) : mqG (b + 1) < Z := by
  obtain ⟨e1, e2, h1⟩ := mq_succ_parts b
  unfold mqG at hg ⊢; rw [e1, e2]
  exact max_lt (lt_of_le_of_lt (le_max_left _ _) hg)
    (glG_succ hZ _ h1 (lt_of_le_of_lt (le_max_right _ _) hg))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem mq_gates {γ c : Ordinal.{0}} (hg : max (glQ γ) (glG c) < x) : glG γ < x ∧ glG c < x :=
  ⟨glG_of_Q (omega0_lt_inE hx) (lt_of_le_of_lt (le_max_left _ _) hg), lt_of_le_of_lt (le_max_right _ _) hg⟩

theorem mq_lt_next {γ c : Ordinal.{0}} (hγ : γ < gcG 0) (hc : c < gcG 0) (hgγ : glG γ < x) (hgc : glG c < x) :
    lgG x * glR γ x + glR c x < lgG x * (glR γ x + 1) := by
  rw [mul_add_one]
  exact (add_lt_add_iff_left _).2 (glR_lt_G hx hx1 hc hgc)

/-- **Every reading is below `Γ_{x+2}`.** -/
theorem mqR_lt1 {c : Ordinal.{0}} (hc : c < mqB) (hg : mqG c < x) : mqR c x < gq 1 x := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  obtain ⟨hgγ, hgc⟩ := mq_gates hx hx1 hg
  rw [mqR_split γ hc' x]
  have hE := (gm1_facts hx hx1).2.2.2
  have hG := mg_lgG_lt_G1 hx hx1
  have hγ1 : glR γ x + 1 < gq 1 x :=
    (ev_isSuccLimit_of_inE hE).add_one_lt ((glR_lt_G hx hx1 hγ hgγ).trans hG)
  exact (mq_lt_next hx hx1 hγ hc' hgγ hgc).trans (InE.mul_lt hE hG hγ1)

/-- **The reading is strictly increasing** on the codes with gate below `x`. -/
theorem mqR_mono {b c : Ordinal.{0}} (hc : c < mqB) (hbc : b < c) (hgb : mqG b < x) (hgc : mqG c < x) :
    mqR b x < mqR c x := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  obtain ⟨δ, b', hδ, hb', rfl⟩ := mq_split (hbc.trans hc)
  rw [mqG_split γ hc'] at hgc
  rw [mqG_split δ hb'] at hgb
  obtain ⟨hgγ, hgc'⟩ := mq_gates hx hx1 hgc
  obtain ⟨hgδ, hgb'⟩ := mq_gates hx hx1 hgb
  rw [mqR_split γ hc' x, mqR_split δ hb' x]
  rcases lt_trichotomy δ γ with hδγ | rfl | hγδ
  · refine (mq_lt_next hx hx1 hδ hb' hgδ hgb').trans_le ?_
    refine le_trans ?_ le_self_add
    exact mul_le_mul_left' (Order.add_one_le_of_lt (glR_mono hx hx1 hγ hδγ hgγ hgδ)) _
  · have hbc' : b' < c' := (add_lt_add_iff_left _).1 hbc
    exact (add_lt_add_iff_left _).2 (glR_mono hx hx1 hc' hbc' hgc' hgb')
  · exfalso
    have h1 : gcG 0 * γ + c' < gcG 0 * (γ + 1) := by
      rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hc'
    have h2 : gcG 0 * (γ + 1) ≤ gcG 0 * δ + b' :=
      (mul_le_mul_left' (Order.add_one_le_of_lt hγδ) _).trans le_self_add
    exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)

/-- **Cofinality**: every `ν` below the reading of a code `c ∈ (ε_{Ω₁+1}, Γ_{Ω₁+1}²)` is at most the reading of a
code `b ∈ [ε_{Ω₁+1}, c)` with gate below `x`. -/
theorem mqR_cofE {c : Ordinal.{0}} (hc : c < mqB) (hEc : gfE < c) (hg : mqG c < x) {ν : Ordinal.{0}}
    (hν : ν < mqR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ mqG b < x ∧ ν ≤ mqR b x := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  obtain ⟨hgγ, hgc'⟩ := mq_gates hx hx1 hg
  rw [mqR_split γ hc' x] at hν
  have hG0 : (0 : Ordinal.{0}) < lgG x := lgG_pos hx hx1
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [mul_zero, zero_add] at hEc ⊢
    rw [glR_zero, mul_zero, zero_add] at hν
    obtain ⟨b, h1, h2, h3, h4⟩ := glR_cofE hx hx1 hc' hEc hgc' hν
    exact ⟨b, h1, h2, by rw [mqG_low (h2.trans hc')]; exact h3, by rw [mqR_low (h2.trans hc')]; exact h4⟩
  have hG0γ : gcG 0 ≤ gcG 0 * γ := le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 hγ0)
  rcases lt_or_ge ν (lgG x * glR γ x) with hνk | hνk
  · -- `ν = Γ·q + r` with `q < γ(x)`, `r < Γ`
    set q := ν / lgG x with hq
    set r := ν % lgG x with hr
    have hνe : ν = lgG x * q + r := (Ordinal.div_add_mod ν (lgG x)).symm
    have hq1 : q < glR γ x := (Ordinal.div_lt hG0.ne').2 hνk
    have hr1 : r < lgG x := Ordinal.mod_lt ν hG0.ne'
    obtain ⟨b', hb'γ, hgb', hqb'⟩ := glR_cof hx hx1 γ hγ hgγ q hq1
    obtain ⟨b'', hb''1, hb''2, hb''3, hb''4⟩ := mg_cof_G hx hx1 hr1
    refine ⟨gcG 0 * b' + b'', hb''1.trans le_add_self, ?_, ?_, ?_⟩
    · calc gcG 0 * b' + b'' < gcG 0 * (b' + 1) := by
            rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hb''2
        _ ≤ gcG 0 * γ := mul_le_mul_left' (Order.add_one_le_of_lt hb'γ) _
        _ ≤ gcG 0 * γ + c' := le_self_add
    · rw [mqG_split b' hb''2, hb''3]
      exact max_lt ((glQ_le _).trans_lt hgb') hx.pos
    · rw [mqR_split b' hb''2 x, hνe]
      exact add_le_add (mul_le_mul_left' hqb' _) hb''4.le
  · obtain ⟨ν', rfl⟩ : ∃ ν', ν = lgG x * glR γ x + ν' := ⟨_, (Ordinal.add_sub_cancel_of_le hνk).symm⟩
    have hν' : ν' < glR c' x := (add_lt_add_iff_left _).1 hν
    have hEG : gfE ≤ gcG 0 * γ := gfE_lt_G0.le.trans hG0γ
    rcases lt_or_ge gfE c' with hEc' | hc'E
    · obtain ⟨b, -, hb2, hb3, hb4⟩ := glR_cofE hx hx1 hc' hEc' hgc' hν'
      refine ⟨gcG 0 * γ + b, hEG.trans le_self_add, (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
      · rw [mqG_split γ (hb2.trans hc')]; exact max_lt ((glQ_le _).trans_lt hgγ) hb3
      · rw [mqR_split γ (hb2.trans hc') x]; exact add_le_add_right hb4 _
    · obtain ⟨b, hb2, hb3, hb4⟩ := glR_cof hx hx1 c' hc' hgc' ν' hν'
      refine ⟨gcG 0 * γ + b, hEG.trans le_self_add, (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
      · rw [mqG_split γ (hb2.trans hc')]; exact max_lt ((glQ_le _).trans_lt hgγ) hb3
      · rw [mqR_split γ (hb2.trans hc') x]; exact add_le_add_right hb4 _

/-- `ϑʳ(Γ_{r+1} + β') = ω^{Γ_{r+1}+1+β'}` for `β' < Γ_{r+1}` ([W07a] Lemma 4.2, `vt_wbar`, and `wbar_eq` with the
pseudo-base `Γ_{r+1}`). -/
theorem mq_vt_G {β' : Ordinal.{0}} (hβ : β' < lgG x) : vt x (lgG x + β') = ω ^ (lgG x + 1 + β') := by
  obtain ⟨-, hxG, hG1, he, -⟩ := lgG_facts hx hx1
  have he1 : lgG x + β' < Om1 := Om1_add_lt hG1 (hβ.trans hG1)
  have hω : ω ≤ lgG x + β' := (omega0_lt_inE he).le.trans le_self_add
  have hxa : x + lgG x = lgG x := by
    have := add_omega0_opow (a := x) (b := lgG x) (by rw [he]; exact hxG)
    rwa [he] at this
  rw [← one_add_of_omega0_le hω, vt_wbar hx hx1 he1, ← add_assoc, hxa]
  refine wbar_eq he β' ?_
  intro u hu1 hu2 huE
  have h1 : 1 + β' < lgG x := (inE_indec he).add_lt (one_lt_omega0.trans (omega0_lt_inE he)) hβ
  have h2 : lgG x + lgG x < u := (inE_indec huE).add_lt hu1 hu1
  rw [add_assoc] at hu2
  exact absurd (hu2.trans_lt ((add_lt_add_iff_left _).2 h1)) (not_lt.2 h2.le)

end Base

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for the atom `ω^{Γ_{ρ+1}+β}` at every pair of bases** (`β ∈ Tᵖ[σ]`, `β < Γ_{ρ+1}`). -/
theorem mq_GAtom_pi {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβe : β < lgG ρ) :
    ω ^ (lgG ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (lgG ρ + β)) = ω ^ (lgG σ + pi σ ρ β) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨heTB, hpe⟩ := mg_lgG_pi hB
  have he1 : lgG ρ < Om1 := (lgG_facts hB.2.1 hρ1).2.2.1
  have hes1 : lgG σ < Om1 := (lgG_facts hB.1 hσ1).2.2.1
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1 : ω ^ lgG ρ = lgG ρ := (lgG_facts hB.2.1 hρ1).2.2.2.1
    have h2 : ω ^ lgG σ = lgG σ := (lgG_facts hB.1 hσ1).2.2.2.1
    rw [pi_lt hB hB.1.pos, add_zero, add_zero, h1, h2]
    exact ⟨heTB, hpe⟩
  have hπβ : pi σ ρ β < lgG σ := by rw [← hpe]; exact (pi_bijOn hB).2 hβTB heTB hβe
  set β' := β - 1 with hβ'
  have hb : 1 + β' = β := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hβ0)
  have hβ'e : β' < lgG ρ := lt_of_le_of_lt (sub_le_self β 1) hβe
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
  have hξ1 : lgG ρ + β' < Om1 := Om1_add_lt he1 (hβ'e.trans he1)
  have hv := mq_vt_G hB.2.1 hρ1 hβ'e
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hπβ' : pi σ ρ β' < lgG σ := lt_of_le_of_lt (by rw [← hπ1]; exact le_add_self) hπβ
  have hv' := mq_vt_G hB.1 hσ1 hπβ'
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **`π(Γ_{ρ+1}·γ(ρ)) = Γ_{σ+1}·γ(σ)`** for every code `γ < Γ_{Ω₁+1}` with gate below `σ` (`Gl.gl_dig` below the
`ε`-number code `c_n > γ` of gate `0`, atoms `mq_GAtom_pi`). -/
theorem mq_Gmul_pi {γ : Ordinal.{0}} (hγ : γ < gcG 0) (hg : glG γ < σ) :
    lgG ρ * glR γ ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * glR γ ρ) = lgG σ * glR γ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨n, hn⟩ := gmC_cof hγ
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
  have h := gl_dig hB he hOe (gmC_lt_G0 n) hge (fun j hj hgj => gl_pi hB j (hj.trans (gmC_lt_G0 n)) hgj) γ hn hg
    (lgG ρ) (lgG σ) (fun β hβ hβe => mq_GAtom_pi hB hβ (hβe.trans (by
      rw [mgC_read hB.2.1 hρ1 n]; exact gT_lt_lgG hB.2.1 hρ1 n)))
  rw [(lgG_facts hB.2.1 hρ1).2.2.2.1, (lgG_facts hB.1 hσ1).2.2.2.1] at h
  exact h

/-- **Lemma EXACT for every code below `Γ_{Ω₁+1}²`** at every pair of bases above the gate. -/
theorem mqR_pi {c : Ordinal.{0}} (hc : c < mqB) (hg : mqG c < σ) :
    mqR c ρ ∈ TB ρ σ ∧ pi σ ρ (mqR c ρ) = mqR c σ := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rw [mqG_split γ hc'] at hg
  obtain ⟨hgγ, hgc⟩ := mq_gates hB.1 (hB.2.2.1.trans hB.2.2.2) hg
  rw [mqR_split γ hc' ρ, mqR_split γ hc' σ]
  obtain ⟨h1, h2⟩ := mq_Gmul_pi hB hγ hgγ
  obtain ⟨h3, h4⟩ := gl_pi hB c' hc' hgc
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [h6, h2, h4]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gm
