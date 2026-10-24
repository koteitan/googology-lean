import Googology.Trans.PoR.InaccPsi.R2.GnHI

/-!
# THE CODES `ε_{Γ_{Ω₁+1}+1}·k + c'` (`k < ω`, `c' < ε_{Γ_{Ω₁+1}+1}`): reading, gate, order, cofinality, Lemma EXACT

The first `φ`-code above `Γ_{Ω₁+1}`: `E₁ = ε_{Γ_{Ω₁+1}+1} = gnB` (the bound of `R2.GnHC`).  Every `c < E₁·ω` is
`E₁·k + c'` (`k = c / E₁` finite, `c' = c mod E₁` a hereditary code of `R2.GnHC`).  The reading replaces `E₁` by
`ε_{Γ_{x+1}+1}` and reads `c'` with `gnR`: `neR c x = ε_{Γ_{x+1}+1}·k + c'(x)`; the gate is that of `c'`.  This is
`R2.GmG0` one level up (base `Γ_{Ω₁+1}` there, `ε_{Γ_{Ω₁+1}+1}` here).

* `neB` (`ε_{G+1}·ω`), `neR`, `neG`, `ne_split`, `neR_split`, `neG_split`, `neR_low`, `neG_low`, `neR_succ`,
  `neG_le_succ`, `neG_succ`;
* `neR_lt1` (**below `Γ_{x+2}`**), `neR_mono` (**strictly increasing**), `gnTw_read`, `ne_cof_E` (**the readings of
  the towers `G, G^G, …` are cofinal in `ε_{Γ_{x+1}+1}`**), `neR_cofE` (**cofinality**);
* `ne_eNk_pi` (**`π(ε_{Γ_{ρ+1}+1}·k) = ε_{Γ_{σ+1}+1}·k`**), `neR_pi` (**Lemma EXACT for every code below
  `ε_{G+1}·ω`** at every pair of bases above the gate).

No new axiom.  New definitions: `neB`, `neR`, `neG`.
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

/-! ## The codes, the reading and the gate -/

/-- **The bound** `ε_{Γ_{Ω₁+1}+1}·ω`. -/
noncomputable def neB : Ordinal.{0} := gnB * ω

/-- **The reading** `ε_{Γ_{x+1}+1}·k + c'(x)` of `c = ε_{Γ_{Ω₁+1}+1}·k + c'`. -/
noncomputable def neR (c x : Ordinal.{0}) : Ordinal.{0} := eN (lgG x) * (c / gnB) + gnR (c % gnB) x

/-- **The gate**: the gate of `c'`. -/
noncomputable def neG (c : Ordinal.{0}) : Ordinal.{0} := gnG (c % gnB)

theorem gnB_ne : gnB ≠ 0 := gnB_E.pos.ne'

theorem ne_split_eq (k : ℕ) {c : Ordinal.{0}} (hc : c < gnB) :
    (gnB * k + c) / gnB = k ∧ (gnB * k + c) % gnB = c := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ gnB_ne, Ordinal.div_eq_zero_of_lt hc, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

/-- **Every code below `ε_{G+1}·ω` is `ε_{G+1}·k + c'`.** -/
theorem ne_split {c : Ordinal.{0}} (hc : c < neB) : ∃ k : ℕ, ∃ c', c' < gnB ∧ c = gnB * k + c' := by
  have hk : c / gnB < ω := (Ordinal.div_lt gnB_ne).2 hc
  obtain ⟨k, hk'⟩ := lt_omega0.1 hk
  refine ⟨k, c % gnB, Ordinal.mod_lt c gnB_ne, ?_⟩
  rw [← hk']; exact (Ordinal.div_add_mod c gnB).symm

theorem neR_split (k : ℕ) {c : Ordinal.{0}} (hc : c < gnB) (x : Ordinal.{0}) :
    neR (gnB * k + c) x = eN (lgG x) * k + gnR c x := by
  unfold neR; rw [(ne_split_eq k hc).1, (ne_split_eq k hc).2]

theorem neG_split (k : ℕ) {c : Ordinal.{0}} (hc : c < gnB) : neG (gnB * k + c) = gnG c := by
  unfold neG; rw [(ne_split_eq k hc).2]

theorem ne_low_eq {c : Ordinal.{0}} (hc : c < gnB) : gnB * ((0 : ℕ) : Ordinal.{0}) + c = c := by simp

theorem neR_low {c : Ordinal.{0}} (hc : c < gnB) (x : Ordinal.{0}) : neR c x = gnR c x := by
  have := neR_split 0 hc x
  rwa [ne_low_eq hc, Nat.cast_zero, mul_zero, zero_add] at this

theorem neG_low {c : Ordinal.{0}} (hc : c < gnB) : neG c = gnG c := by
  have := neG_split 0 hc
  rwa [ne_low_eq hc] at this

theorem ne_E1_lt_B : gnB < neB := by
  unfold neB
  conv_lhs => rw [← mul_one gnB]
  exact (mul_lt_mul_iff_right₀ gnB_E.pos).2 one_lt_omega0

theorem neB_eq : neB = ω ^ (gnB + 1) := by unfold neB; rw [opow_add, opow_one, show ω ^ gnB = gnB from gnB_E]

theorem neB_lim : IsSuccLimit neB := by rw [neB_eq]; exact Ph.ph_opow_lim (by simp)

theorem ne_E_lt_B : gfE < neB := (gfE_lt_G0.trans gn_G0_lt_B).trans ne_E1_lt_B

theorem neG_lt_Om1 (c : Ordinal.{0}) : neG c < Om1 := gnG_lt_Om1 _ (Ordinal.mod_lt c gnB_ne)

theorem neG_zero : neG 0 = 0 := by rw [neG_low gnB_E.pos, gnG_zero]

theorem neG_E : neG gfE = 0 := by rw [neG_low (gfE_lt_G0.trans gn_G0_lt_B), gnG_low gfE_lt_G0, glG_E]

theorem neG_lowE {c : Ordinal.{0}} (hc : c < gfE) : neG c = gtc c := by
  rw [neG_low ((hc.trans gfE_lt_G0).trans gn_G0_lt_B), gnG_low (hc.trans gfE_lt_G0), glG_low hc]

theorem neR_E (x : Ordinal.{0}) : neR gfE x = eN x := by
  rw [neR_low (gfE_lt_G0.trans gn_G0_lt_B), gnR_low gfE_lt_G0, glR_E]

theorem ne_succ_parts (b : Ordinal.{0}) :
    (b + 1) / gnB = b / gnB ∧ (b + 1) % gnB = b % gnB + 1 ∧ b % gnB + 1 < gnB := by
  have hb : b % gnB < gnB := Ordinal.mod_lt b gnB_ne
  have e : b + 1 = gnB * (b / gnB) + (b % gnB + 1) := by rw [← add_assoc, Ordinal.div_add_mod]
  have h1 := gnB_lim.add_one_lt hb
  refine ⟨?_, ?_, h1⟩
  · rw [e, Ordinal.mul_add_div _ gnB_ne, Ordinal.div_eq_zero_of_lt h1, add_zero]
  · rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt h1]

theorem neR_succ (b x : Ordinal.{0}) : neR (b + 1) x = neR b x + 1 := by
  obtain ⟨e1, e2, -⟩ := ne_succ_parts b
  unfold neR; rw [e1, e2, gnR_succ_all, add_assoc]

theorem neG_le_succ (b : Ordinal.{0}) : neG b ≤ neG (b + 1) := by
  obtain ⟨-, e2, -⟩ := ne_succ_parts b
  unfold neG; rw [e2]; exact gnG_le_succ_all _

theorem neG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (b : Ordinal.{0}) (hg : neG b < Z) : neG (b + 1) < Z := by
  obtain ⟨-, e2, h1⟩ := ne_succ_parts b
  unfold neG at hg ⊢; rw [e2]; exact gnG_succ hZ _ h1 hg

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem ne_eNG_w_lt : eN (lgG x) * ω < gq 1 x :=
  InE.mul_lt (gm1_facts hx hx1).2.2.2 (gn_eNG_lt1 hx hx1) (omega0_lt_inE (gm1_facts hx hx1).2.2.2)

theorem ne_lt_next (k : ℕ) {c : Ordinal.{0}} (hc : c < gnB) (hg : gnG c < x) :
    eN (lgG x) * k + gnR c x < eN (lgG x) * ((k + 1 : ℕ) : Ordinal.{0}) := by
  rw [Nat.cast_succ, mul_add_one]
  exact (add_lt_add_iff_left _).2 (gnR_lt_eNG hx hx1 hc hg)

/-- **Every reading is below `Γ_{x+2}`.** -/
theorem neR_lt1 {c : Ordinal.{0}} (hc : c < neB) (hg : neG c < x) : neR c x < gq 1 x := by
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  rw [neG_split k hc'] at hg
  rw [neR_split k hc' x]
  refine (ne_lt_next hx hx1 k hc' hg).trans ?_
  refine lt_of_le_of_lt ?_ (ne_eNG_w_lt hx hx1)
  exact mul_le_mul_left' (natCast_lt_omega0 _).le _

/-- **The reading is strictly increasing** on the codes with gate below `x`. -/
theorem neR_mono {b c : Ordinal.{0}} (hc : c < neB) (hbc : b < c) (hgb : neG b < x) (hgc : neG c < x) :
    neR b x < neR c x := by
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  obtain ⟨j, b', hb', rfl⟩ := ne_split (hbc.trans hc)
  rw [neG_split k hc'] at hgc
  rw [neG_split j hb'] at hgb
  rw [neR_split k hc' x, neR_split j hb' x]
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · refine (ne_lt_next hx hx1 j hb' hgb).trans_le ?_
    refine le_trans ?_ le_self_add
    exact mul_le_mul_left' (by exact_mod_cast hjk) _
  · have hbc' : b' < c' := (add_lt_add_iff_left _).1 hbc
    exact (add_lt_add_iff_left _).2 (gnR_mono hx hx1 c' hc' b' hbc' hgc hgb)
  · exfalso
    have h1 : gnB * k + c' < gnB * ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_succ, mul_add_one]; exact (add_lt_add_iff_left _).2 hc'
    have h2 : gnB * ((k + 1 : ℕ) : Ordinal.{0}) ≤ gnB * j + b' :=
      (mul_le_mul_left' (by exact_mod_cast hkj) _).trans le_self_add
    exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)

/-- The readings of the towers: `(ω^·)^[n](Γ_{x+1} + 1) ≤ (G^{⋯})(x)`. -/
theorem gnTw_read : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (lgG x + 1) ≤ gnR (gnTw (n + 1)) x := by
  have hGE := (lgG_facts hx hx1).2.2.2.1
  have h1G : (1 : Ordinal.{0}) < lgG x := one_lt_omega0.trans (omega0_lt_inE hGE)
  intro n
  induction n with
  | zero =>
    show lgG x + 1 ≤ gnR (gcG 0 ^ gcG 0) x
    rw [gnR_pow mg_G0_ne gn_G0_lt_B, gnR_G]
    have : lgG x ^ (1 : Ordinal.{0}) < lgG x ^ lgG x := (opow_lt_opow_iff_right h1G).2 h1G
    rw [opow_one] at this
    exact Order.add_one_le_of_lt this
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (lgG x + 1)) ≤ gnR (gcG 0 ^ gnTw (n + 1)) x
    have h0 : gnTw (n + 1) ≠ 0 := (gl_G0_E.pos.trans_le (gnTw_ge _)).ne'
    rw [gnR_pow h0 (gnTw_lt _)]
    calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (lgG x + 1)) ≤ ω ^ gnR (gnTw (n + 1)) x :=
          opow_le_opow_right omega0_pos ih
      _ ≤ lgG x ^ gnR (gnTw (n + 1)) x := opow_le_opow_left _ (omega0_lt_inE hGE).le

/-- **The readings of the codes below `ε_{G+1}` are cofinal in `ε_{Γ_{x+1}+1}`** (the towers, gate `0`). -/
theorem ne_cof_E {ν : Ordinal.{0}} (hν : ν < eN (lgG x)) :
    ∃ b, gfE ≤ b ∧ b < gnB ∧ gnG b = 0 ∧ ν < gnR b x := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hν
  exact ⟨gnTw (n + 1), gfE_lt_G0.le.trans (gnTw_ge _), gnTw_lt _, gnTw_g _, hn.trans_le (gnTw_read hx hx1 n)⟩

/-- **Cofinality**: every `ν` below the reading of a code `c ∈ (ε_{Ω₁+1}, ε_{G+1}·ω)` is at most the reading of a
code `b ∈ [ε_{Ω₁+1}, c)` with gate below `x`. -/
theorem neR_cofE {c : Ordinal.{0}} (hc : c < neB) (hEc : gfE < c) (hg : neG c < x) {ν : Ordinal.{0}}
    (hν : ν < neR c x) : ∃ b, gfE ≤ b ∧ b < c ∧ neG b < x ∧ ν ≤ neR b x := by
  have hEB : gfE < gnB := gfE_lt_G0.trans gn_G0_lt_B
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  rw [neG_split k hc'] at hg
  rw [neR_split k hc' x] at hν
  rcases k with _ | k
  · rw [Nat.cast_zero, mul_zero, zero_add] at hν hEc ⊢
    obtain ⟨b, h1, h2, h3, h4⟩ := gnR_cofE hx hx1 hc' hEc hg hν
    refine ⟨b, h1, h2, by rw [neG_low (h2.trans hc')]; exact h3, by rw [neR_low (h2.trans hc')]; exact h4⟩
  · have hG0c : gnB * ((k + 1 : ℕ) : Ordinal.{0}) = gnB * k + gnB := by rw [Nat.cast_succ, mul_add_one]
    have hlG : eN (lgG x) * ((k + 1 : ℕ) : Ordinal.{0}) = eN (lgG x) * k + eN (lgG x) := by
      rw [Nat.cast_succ, mul_add_one]
    have hEG : gfE ≤ gnB * k + gnB := hEB.le.trans le_add_self
    rcases lt_or_ge ν (eN (lgG x) * ((k + 1 : ℕ) : Ordinal.{0})) with hνk | hνk
    · rw [hlG] at hνk
      rcases lt_or_ge ν (eN (lgG x) * k) with hνk' | hνk'
      · rcases k with _ | k
        · simp at hνk'
        · refine ⟨gnB * ((k + 1 : ℕ) : Ordinal.{0}), ?_, ?_, ?_, ?_⟩
          · rw [Nat.cast_succ, mul_add_one]; exact hEB.le.trans le_add_self
          · refine lt_of_lt_of_le ?_ le_self_add
            exact (mul_lt_mul_iff_right₀ gnB_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (k + 1))
          · have := neG_split (k + 1) gnB_E.pos
            rw [add_zero] at this; rw [this, gnG_zero]; exact hx.pos
          · have := neR_split (k + 1) gnB_E.pos x
            rw [add_zero] at this; rw [this, gnR_zero, add_zero]; exact hνk'.le
      · obtain ⟨ν', rfl⟩ : ∃ ν', ν = eN (lgG x) * k + ν' := ⟨_, (Ordinal.add_sub_cancel_of_le hνk').symm⟩
        have hν' : ν' < eN (lgG x) := (add_lt_add_iff_left _).1 hνk
        obtain ⟨b, hb1, hb2, hb3, hb4⟩ := ne_cof_E hx hx1 hν'
        refine ⟨gnB * k + b, hb1.trans le_add_self, ?_, ?_, ?_⟩
        · rw [hG0c]; exact ((add_lt_add_iff_left _).2 hb2).trans_le le_self_add
        · rw [neG_split k hb2, hb3]; exact hx.pos
        · rw [neR_split k hb2 x]; exact add_le_add_right hb4.le _
    · obtain ⟨ν', rfl⟩ : ∃ ν', ν = eN (lgG x) * ((k + 1 : ℕ) : Ordinal.{0}) + ν' :=
        ⟨_, (Ordinal.add_sub_cancel_of_le hνk).symm⟩
      have hν' : ν' < gnR c' x := (add_lt_add_iff_left _).1 hν
      rcases lt_or_ge gfE c' with hEc' | hc'E
      · obtain ⟨b, -, hb2, hb3, hb4⟩ := gnR_cofE hx hx1 hc' hEc' hg hν'
        refine ⟨gnB * ((k + 1 : ℕ) : Ordinal.{0}) + b, (hEG.trans (by rw [hG0c])).trans le_self_add,
          (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
        · rw [neG_split (k + 1) (hb2.trans hc')]; exact hb3
        · rw [neR_split (k + 1) (hb2.trans hc') x]; exact add_le_add_right hb4 _
      · obtain ⟨b, hb2, hb3, hb4⟩ := gnR_cof hx hx1 c' hc' hg ν' hν'
        refine ⟨gnB * ((k + 1 : ℕ) : Ordinal.{0}) + b, (hEG.trans (by rw [hG0c])).trans le_self_add,
          (add_lt_add_iff_left _).2 hb2, ?_, ?_⟩
        · rw [neG_split (k + 1) (hb2.trans hc')]; exact hb3
        · rw [neR_split (k + 1) (hb2.trans hc') x]; exact add_le_add_right hb4 _

end Base

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(ε_{Γ_{ρ+1}+1}·k) = ε_{Γ_{σ+1}+1}·k`.** -/
theorem ne_eNk_pi : ∀ k : ℕ, eN (lgG ρ) * k ∈ TB ρ σ ∧ pi σ ρ (eN (lgG ρ) * k) = eN (lgG σ) * k
  | 0 => by
    rw [Nat.cast_zero, mul_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := ne_eNk_pi k
    obtain ⟨h3, h4⟩ := gn_eNG_pi hB
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h5, by rw [h6, h2, h4]⟩

/-- **Lemma EXACT for every code below `ε_{G+1}·ω`** at every pair of bases above the gate. -/
theorem neR_pi {c : Ordinal.{0}} (hc : c < neB) (hg : neG c < σ) :
    neR c ρ ∈ TB ρ σ ∧ pi σ ρ (neR c ρ) = neR c σ := by
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  rw [neG_split k hc'] at hg
  rw [neR_split k hc' ρ, neR_split k hc' σ]
  obtain ⟨h1, h2⟩ := ne_eNk_pi hB k
  obtain ⟨h3, h4⟩ := gnR_pi hB c' hc' hg
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [h6, h2, h4]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gn
