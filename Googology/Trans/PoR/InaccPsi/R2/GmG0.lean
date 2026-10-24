import Googology.Trans.PoR.InaccPsi.R2.GmLoc

/-!
# THE CODES `Γ_{Ω₁+1}·k + c` (`k < ω`, `c < Γ_{Ω₁+1}`): reading, gate, order, Lemma EXACT

The first codes past `Γ_{Ω₁+1}`: every `c < Γ_{Ω₁+1}·ω` is `Γ_{Ω₁+1}·k + c'` (`k = c / Γ_{Ω₁+1}` finite,
`c' = c mod Γ_{Ω₁+1}` a code of `R2.Gl`).  The reading replaces `Γ_{Ω₁+1}` by `Γ_{x+1} = lgG x = ϑˣ(Ω₁·Ω₁)` and reads
`c'` with `Gl.glR`: `mgR c x = Γ_{x+1}·k + c'(x)`; the gate is that of `c'`.

* `mgB` (`Γ_{Ω₁+1}·ω`), `mgR`, `mgG`, `mg_split` (`c = Γ_{Ω₁+1}·k + c'`), `mgR_split`, `mgG_split`, `mg_low`;
* `mgR_E` (`ε_{Ω₁+1}` reads `ε_{x+1}`), `mgR_lt1` (**below `Γ_{x+2}`**), `mgR_mono` (**strictly increasing**),
  `mgR_succ`, `mgG_le_succ`;
* `mg_gq0` (`Γ_{x+1} = ϑˣ(Ω₁·Ω₁)`), `mg_lgG_pi`, `mg_lgGk_pi` (**`π(Γ_{ρ+1}·k) = Γ_{σ+1}·k`**), `mgR_pi` (**Lemma EXACT
  for every code below `Γ_{Ω₁+1}·ω` at every pair of bases**);
* `mgC_read` (**the code `c_n` of `R2.GmSup` reads `gT n x`**, so the readings of the codes below `Γ_{Ω₁+1}` are cofinal
  in `Γ_{x+1}`: `mg_cof_G`), `mgR_cofE` (**every `ν` below the reading of a code `c > ε_{Ω₁+1}` is at most the
  reading of
  a smaller code `≥ ε_{Ω₁+1}` with gate below `x`**).

No new axiom.  New definitions: `mgB`, `mgR`, `mgG`.
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

/-- **The bound** `Γ_{Ω₁+1}·ω`. -/
noncomputable def mgB : Ordinal.{0} := gcG 0 * ω

/-- **The reading** `Γ_{x+1}·k + c'(x)` of `c = Γ_{Ω₁+1}·k + c'`. -/
noncomputable def mgR (c x : Ordinal.{0}) : Ordinal.{0} := lgG x * (c / gcG 0) + glR (c % gcG 0) x

/-- **The gate**: the gate of `c'`. -/
noncomputable def mgG (c : Ordinal.{0}) : Ordinal.{0} := glG (c % gcG 0)

theorem mg_G0_ne : gcG 0 ≠ 0 := gl_G0_E.pos.ne'

theorem mg_split_eq (k : ℕ) {c : Ordinal.{0}} (hc : c < gcG 0) :
    (gcG 0 * k + c) / gcG 0 = k ∧ (gcG 0 * k + c) % gcG 0 = c := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ mg_G0_ne, Ordinal.div_eq_zero_of_lt hc, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

/-- **Every code below `Γ_{Ω₁+1}·ω` is `Γ_{Ω₁+1}·k + c'`.** -/
theorem mg_split {c : Ordinal.{0}} (hc : c < mgB) : ∃ k : ℕ, ∃ c', c' < gcG 0 ∧ c = gcG 0 * k + c' := by
  have hk : c / gcG 0 < ω := (Ordinal.div_lt mg_G0_ne).2 hc
  obtain ⟨k, hk'⟩ := lt_omega0.1 hk
  refine ⟨k, c % gcG 0, Ordinal.mod_lt c mg_G0_ne, ?_⟩
  rw [← hk']; exact (Ordinal.div_add_mod c (gcG 0)).symm

theorem mgR_split (k : ℕ) {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) :
    mgR (gcG 0 * k + c) x = lgG x * k + glR c x := by
  unfold mgR; rw [(mg_split_eq k hc).1, (mg_split_eq k hc).2]

theorem mgG_split (k : ℕ) {c : Ordinal.{0}} (hc : c < gcG 0) : mgG (gcG 0 * k + c) = glG c := by
  unfold mgG; rw [(mg_split_eq k hc).2]

theorem mg_low_eq {c : Ordinal.{0}} (hc : c < gcG 0) : gcG 0 * ((0 : ℕ) : Ordinal.{0}) + c = c := by simp

theorem mgR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : mgR c x = glR c x := by
  have := mgR_split 0 hc x
  rwa [mg_low_eq hc, Nat.cast_zero, mul_zero, zero_add] at this

theorem mgG_low {c : Ordinal.{0}} (hc : c < gcG 0) : mgG c = glG c := by
  have := mgG_split 0 hc
  rwa [mg_low_eq hc] at this

theorem mg_G0_lt_B : gcG 0 < mgB := by
  unfold mgB
  conv_lhs => rw [← mul_one (gcG 0)]
  exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 one_lt_omega0

theorem mgB_lim : IsSuccLimit mgB := by
  unfold mgB
  have e : gcG 0 * ω = ω ^ (gcG 0 + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]; exact Ph.ph_opow_lim (by simp)

theorem mg_E_lt_B : gfE < mgB := gfE_lt_G0.trans mg_G0_lt_B

theorem mgG_lt_Om1 (c : Ordinal.{0}) : mgG c < Om1 := glG_lt_Om1 _ (Ordinal.mod_lt c mg_G0_ne)

theorem mgG_zero : mgG 0 = 0 := by rw [mgG_low gl_G0_E.pos, glG_zero]

theorem mgG_E : mgG gfE = 0 := by rw [mgG_low gfE_lt_G0, glG_E]

theorem mgG_lowE {c : Ordinal.{0}} (hc : c < gfE) : mgG c = gtc c := by
  rw [mgG_low (hc.trans gfE_lt_G0), glG_low hc]

theorem mg_succ_split (k : ℕ) {c : Ordinal.{0}} (hc : c < gcG 0) :
    gcG 0 * k + c + 1 = gcG 0 * k + (c + 1) ∧ c + 1 < gcG 0 :=
  ⟨by rw [add_assoc], gl_G0_lim.add_one_lt hc⟩

theorem mgR_succ (b x : Ordinal.{0}) : mgR (b + 1) x = mgR b x + 1 := by
  unfold mgR
  have hb : b % gcG 0 < gcG 0 := Ordinal.mod_lt b mg_G0_ne
  have e : b + 1 = gcG 0 * (b / gcG 0) + (b % gcG 0 + 1) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  have e1 : (b + 1) / gcG 0 = b / gcG 0 := by
    rw [e, Ordinal.mul_add_div _ mg_G0_ne, Ordinal.div_eq_zero_of_lt (gl_G0_lim.add_one_lt hb), add_zero]
  have e2 : (b + 1) % gcG 0 = b % gcG 0 + 1 := by
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (gl_G0_lim.add_one_lt hb)]
  rw [e1, e2, glR_succ_all, add_assoc]

theorem mgG_le_succ (b : Ordinal.{0}) : mgG b ≤ mgG (b + 1) := by
  unfold mgG
  have hb : b % gcG 0 < gcG 0 := Ordinal.mod_lt b mg_G0_ne
  have e : b + 1 = gcG 0 * (b / gcG 0) + (b % gcG 0 + 1) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  have e2 : (b + 1) % gcG 0 = b % gcG 0 + 1 := by
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (gl_G0_lim.add_one_lt hb)]
  rw [e2]; exact glG_le_succ_all _

theorem mgG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (b : Ordinal.{0}) (hg : mgG b < Z) : mgG (b + 1) < Z := by
  unfold mgG at hg ⊢
  have hb : b % gcG 0 < gcG 0 := Ordinal.mod_lt b mg_G0_ne
  have e : b + 1 = gcG 0 * (b / gcG 0) + (b % gcG 0 + 1) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  have e2 : (b + 1) % gcG 0 = b % gcG 0 + 1 := by
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (gl_G0_lim.add_one_lt hb)]
  rw [e2]; exact glG_succ hZ _ (gl_G0_lim.add_one_lt hb) hg

theorem mgR_E (x : Ordinal.{0}) : mgR gfE x = eN x := by rw [mgR_low gfE_lt_G0, glR_E]

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem mg_gq0 : lgG x = gq 0 x := (gu_gq0_eq hx hx1).symm

theorem mg_lgG_lt_G1 : lgG x < gq 1 x := by rw [mg_gq0 hx hx1]; exact gm_G0_lt_G1 hx hx1

theorem mg_lgG_w_lt : lgG x * ω < gq 1 x :=
  InE.mul_lt (gm1_facts hx hx1).2.2.2 (mg_lgG_lt_G1 hx hx1) (omega0_lt_inE (gm1_facts hx hx1).2.2.2)

theorem mg_lt_next (k : ℕ) {c : Ordinal.{0}} (hc : c < gcG 0) (hg : glG c < x) :
    lgG x * k + glR c x < lgG x * ((k + 1 : ℕ) : Ordinal.{0}) := by
  rw [Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).2 (glR_lt_G hx hx1 hc hg)

/-- **Every reading is below `Γ_{x+2}`.** -/
theorem mgR_lt1 {c : Ordinal.{0}} (hc : c < mgB) (hg : mgG c < x) : mgR c x < gq 1 x := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  rw [mgG_split k hc'] at hg
  rw [mgR_split k hc' x]
  refine (mg_lt_next hx hx1 k hc' hg).trans ?_
  refine lt_of_le_of_lt ?_ (mg_lgG_w_lt hx hx1)
  exact mul_le_mul_left' (natCast_lt_omega0 _).le _

/-- **The reading is strictly increasing** on the codes with gate below `x`. -/
theorem mgR_mono {b c : Ordinal.{0}} (hc : c < mgB) (hbc : b < c) (hgb : mgG b < x) (hgc : mgG c < x) :
    mgR b x < mgR c x := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  obtain ⟨j, b', hb', rfl⟩ := mg_split (hbc.trans hc)
  rw [mgG_split k hc'] at hgc
  rw [mgG_split j hb'] at hgb
  rw [mgR_split k hc' x, mgR_split j hb' x]
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · refine (mg_lt_next hx hx1 j hb' hgb).trans_le ?_
    refine le_trans ?_ le_self_add
    exact mul_le_mul_left' (by exact_mod_cast hjk) _
  · have hbc' : b' < c' := (add_lt_add_iff_left _).1 hbc
    exact (add_lt_add_iff_left _).2 (glR_mono hx hx1 hc' hbc' hgc hgb)
  · exfalso
    have h1 : gcG 0 * k + c' < gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hc'
    have h2 : gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}) ≤ gcG 0 * j + b' :=
      (mul_le_mul_left' (by exact_mod_cast hkj) _).trans le_self_add
    exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)

/-- **The codes `c_n` read `gT n x`** (`c_0 = ε_{Ω₁+1}`, `c_{n+1} = φ(c_n, 0)`). -/
theorem mgC_read : ∀ n : ℕ, glR (gmC n) x = gT n x
  | 0 => by
    show glR (glPsi ((0 + 1 : ℕ) : Ordinal.{0}) 0) x = eN x
    rw [Nat.cast_succ, Nat.cast_zero, zero_add, gl_E_eq, glR_E]
  | n + 1 => by
    have hO : Om1 < gmC n := Om1_lt_eW.trans_le (gmC_spec n).1
    rw [gmC_succ, gl_veb0_psi hO (gmC_lt_G0 n),
      glR_psi (one_le_iff_pos.2 (lt_of_le_of_lt zero_le hO)) (gmC_lt_G0 n) gl_G0_E.pos, glR_zero,
      glBA_eq hx hx1, mgC_read n]
    show vt x (Om1 * gT n x + 0) = vt x (Om1 * gT n x)
    rw [add_zero]

/-- **The readings of the codes below `Γ_{Ω₁+1}` are cofinal in `Γ_{x+1}`.** -/
theorem mg_cof_G {ν : Ordinal.{0}} (hν : ν < lgG x) :
    ∃ b, gfE ≤ b ∧ b < gcG 0 ∧ glG b = 0 ∧ ν < glR b x := by
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 hν
  exact ⟨gmC n, (gmC_spec n).1, gmC_lt_G0 n, (gmC_spec n).2.2, by rw [mgC_read hx hx1 n]; exact hn⟩

/-- **Cofinality**: every `ν` below the reading of a code `c ∈ (ε_{Ω₁+1}, Γ_{Ω₁+1}·ω)` is at most the reading of a
code `b ∈ [ε_{Ω₁+1}, c)` with gate below `x`. -/
theorem mgR_cofE {c : Ordinal.{0}} (hc : c < mgB) (hEc : gfE < c) (hg : mgG c < x) {ν : Ordinal.{0}}
    (hν : ν < mgR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ mgG b < x ∧ ν ≤ mgR b x := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  rw [mgG_split k hc'] at hg
  rw [mgR_split k hc' x] at hν
  rcases k with _ | k
  · rw [Nat.cast_zero, mul_zero, zero_add] at hν hEc ⊢
    obtain ⟨b, h1, h2, h3, h4⟩ := glR_cofE hx hx1 hc' hEc hg hν
    refine ⟨b, h1, h2, by rw [mgG_low (h2.trans hc')]; exact h3, by rw [mgR_low (h2.trans hc')]; exact h4⟩
  · have hG0c : gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}) = gcG 0 * k + gcG 0 := by rw [Nat.cast_succ, mul_add_one]
    have hlG : lgG x * ((k + 1 : ℕ) : Ordinal.{0}) = lgG x * k + lgG x := by rw [Nat.cast_succ, mul_add_one]
    have hEG : gfE ≤ gcG 0 * k + gcG 0 := gfE_lt_G0.le.trans le_add_self
    rcases lt_or_ge ν (lgG x * ((k + 1 : ℕ) : Ordinal.{0})) with hνk | hνk
    · -- below `Γ_{x+1}·(k+1)`
      rw [hlG] at hνk
      rcases lt_or_ge ν (lgG x * k) with hνk' | hνk'
      · rcases k with _ | k
        · simp at hνk'
        · refine ⟨gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}), ?_, ?_, ?_, ?_⟩
          · rw [Nat.cast_succ, mul_add_one]; exact gfE_lt_G0.le.trans le_add_self
          · refine lt_of_lt_of_le ?_ le_self_add
            exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (k + 1))
          · have := mgG_split (k + 1) gl_G0_E.pos
            rw [add_zero] at this; rw [this, glG_zero]; exact hx.pos
          · have := mgR_split (k + 1) gl_G0_E.pos x
            rw [add_zero] at this; rw [this, glR_zero, add_zero]; exact hνk'.le
      · obtain ⟨ν', rfl⟩ : ∃ ν', ν = lgG x * k + ν' := ⟨_, (Ordinal.add_sub_cancel_of_le hνk').symm⟩
        have hν' : ν' < lgG x := (add_lt_add_iff_left _).1 hνk
        obtain ⟨b, hb1, hb2, hb3, hb4⟩ := mg_cof_G hx hx1 hν'
        refine ⟨gcG 0 * k + b, hb1.trans le_add_self, ?_, ?_, ?_⟩
        · rw [hG0c]; exact ((add_lt_add_iff_left _).2 hb2).trans_le le_self_add
        · rw [mgG_split k hb2, hb3]; exact hx.pos
        · rw [mgR_split k hb2 x]; exact add_le_add_right hb4.le _
    · -- above `Γ_{x+1}·(k+1)`: `c' ≠ 0`
      obtain ⟨ν', rfl⟩ : ∃ ν', ν = lgG x * ((k + 1 : ℕ) : Ordinal.{0}) + ν' :=
        ⟨_, (Ordinal.add_sub_cancel_of_le hνk).symm⟩
      have hν' : ν' < glR c' x := (add_lt_add_iff_left _).1 hν
      have hc'0 : c' ≠ 0 := by rintro rfl; rw [glR_zero] at hν'; exact absurd hν' (not_lt.2 zero_le)
      rcases lt_or_ge gfE c' with hEc' | hc'E
      · obtain ⟨b, -, hb2, hb3, hb4⟩ := glR_cofE hx hx1 hc' hEc' hg hν'
        refine ⟨gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}) + b, hEG.trans (by rw [hG0c]) |>.trans le_self_add,
          (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
        · rw [mgG_split (k + 1) (hb2.trans hc')]; exact hb3
        · rw [mgR_split (k + 1) (hb2.trans hc') x]; exact add_le_add_right hb4 _
      · obtain ⟨b, hb2, hb3, hb4⟩ := glR_cof hx hx1 c' hc' hg ν' hν'
        refine ⟨gcG 0 * ((k + 1 : ℕ) : Ordinal.{0}) + b, hEG.trans (by rw [hG0c]) |>.trans le_self_add,
          (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
        · rw [mgG_split (k + 1) (hb2.trans hc')]; exact hb3
        · rw [mgR_split (k + 1) (hb2.trans hc') x]; exact add_le_add_right hb4 _

end Base

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem mg_lgG_pi : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := by
  have h := gq_pi hB hB.1.pos
  rw [mg_gq0 hB.2.1 hB.2.2.2, mg_gq0 hB.1 (hB.2.2.1.trans hB.2.2.2)]
  exact h

/-- **`π(Γ_{ρ+1}·k) = Γ_{σ+1}·k`.** -/
theorem mg_lgGk_pi : ∀ k : ℕ, lgG ρ * k ∈ TB ρ σ ∧ pi σ ρ (lgG ρ * k) = lgG σ * k
  | 0 => by
    rw [Nat.cast_zero, mul_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := mg_lgGk_pi k
    obtain ⟨h3, h4⟩ := mg_lgG_pi hB
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-- **Lemma EXACT for every code below `Γ_{Ω₁+1}·ω`** at every pair of bases above the gate. -/
theorem mgR_pi {c : Ordinal.{0}} (hc : c < mgB) (hg : mgG c < σ) :
    mgR c ρ ∈ TB ρ σ ∧ pi σ ρ (mgR c ρ) = mgR c σ := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  rw [mgG_split k hc'] at hg
  rw [mgR_split k hc' ρ, mgR_split k hc' σ]
  obtain ⟨h1, h2⟩ := mg_lgGk_pi hB k
  obtain ⟨h3, h4⟩ := gl_pi hB c' hc' hg
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [h6, h2, h4]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gm
