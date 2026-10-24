import Googology.Trans.PoR.InaccPsi.R2.GoRS

/-!
# THE GENERIC HEREDITARY STEP: a digit system at `B` gives a digit system at `ε_{B+1}`

**ONE GENERIC HEREDITARY STEP** (`GoD.step`): from a digit system `D : GoD` at the `ε`-number base `B`
(`R2.GoD`: reading, gate, EXACT, the digit rule, the last terms, the bounds) the hereditary codes
`c = B^k·d + r < ε_{B+1}` (`k` any code below `ε_{B+1}`, `d < B` a digit, `r < B^k`), read
`c(x) = b(x)^{k(x)}·d(x) + r(x)`, form a digit system at the base `ε_{B+1}`, with the base read `ε_{b(x)+1}`
(`= ϑˣ(Ω₁ + ba(x) + 1)`), the gate `D.hG`, Lemma EXACT (`GoD.hR_pi`), the digit rule (`GoD.hdig`), the last terms
(`GoD.hld`), the hulls (`GoD.hmem`, `GoD.h_code_gate`) and the towers `B, B^B, …` as cofinal codes.  So the bases
`ε_{Γ+1}, ε_{ε_{Γ+1}+1}, …` are instances of one theorem (`R2.GoIt`), and with `R2.GoRS` every step is a reading
system with its layers, frontiers and road.

* `GoD.hG_pow`, `GoD.hR_pow`, `GoD.hTw_g`, `GoD.hTw_read`, `GoD.NB_cof` (the readings of the towers are cofinal in
  `ε_{b(x)+1}`), `GoD.hR_succ_all`, `GoD.hG_le_succ_all`;
* `GoD.step` (**THE STEP**), `GoD.step_B`, `GoD.step_R`, `GoD.step_g`, `GoD.step_b`, `GoD.step_R_low`,
  `GoD.step_g_low`.

No new axiom.  New definition: `GoD.step`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GoD

variable (D : GoD)

theorem hR_succ_all (b x : Ordinal.{0}) : D.hR (b + 1) x = D.hR b x + 1 := by
  rcases lt_or_ge (b + 1) D.NB with h | h
  · exact D.hR_succ b h x
  · have hb : D.NB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (D.NB_lim.add_one_lt hb) (not_lt.2 h)
    rw [D.hR_high h, D.hR_high hb, D.R_succ]

theorem hG_le_succ_all (b : Ordinal.{0}) : D.hG b ≤ D.hG (b + 1) := by
  rcases lt_or_ge (b + 1) D.NB with h | h
  · exact D.hG_le_succ b h
  · have hb : D.NB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (D.NB_lim.add_one_lt hb) (not_lt.2 h)
    rw [D.hG_high h, D.hG_high hb]; exact D.g_le_succ b

/-- The gate of a power `B^k` (`1 ≤ k < ε_{B+1}`) is the gate of its exponent (`0` when finite). -/
theorem hG_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) : D.hG (D.B ^ k) = D.hQ k := by
  have e : D.B ^ k = D.B ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, D.hG_cnf hk one_ne_zero D.one_lt_B (opow_pos _ D.B_pos) (by rw [← e]; exact D.NB_gt_pow hkB), D.Q_one,
    D.hG_zero, max_eq_left zero_le, max_eq_left zero_le]

theorem hR_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) (x : Ordinal.{0}) :
    D.hR (D.B ^ k) x = D.b x ^ D.hR k x := by
  have e : D.B ^ k = D.B ^ k * 1 + 0 := by rw [mul_one, add_zero]
  rw [e, D.hR_cnf hk one_ne_zero D.one_lt_B (opow_pos _ D.B_pos) (by rw [← e]; exact D.NB_gt_pow hkB),
    D.R_one, mul_one, D.hR_zero, add_zero]

theorem hTw_g : ∀ n : ℕ, D.hG (D.hTw n) = 0
  | 0 => D.hG_G
  | n + 1 => by
    show D.hG (D.B ^ D.hTw n) = 0
    have h0 : D.hTw n ≠ 0 := (D.B_pos.trans_le (D.hTw_ge n)).ne'
    rw [D.hG_pow h0 (D.hTw_lt n)]
    unfold GoD.hQ
    rw [if_neg (not_lt.2 (D.omega_lt_B.le.trans (D.hTw_ge n))), hTw_g n]

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The readings of the towers: `(ω^·)^[n](b(x) + 1) ≤ (B^{⋯})(x)`. -/
theorem hTw_read : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1) ≤ D.hR (D.hTw (n + 1)) x := by
  have hGE := D.b_E x hx hx1
  have h1G : (1 : Ordinal.{0}) < D.b x := one_lt_omega0.trans (omega0_lt_inE hGE)
  intro n
  induction n with
  | zero =>
    show D.b x + 1 ≤ D.hR (D.B ^ D.B) x
    rw [D.hR_pow D.B_ne D.B_lt_NB, D.hR_G]
    have : D.b x ^ (1 : Ordinal.{0}) < D.b x ^ D.b x := (opow_lt_opow_iff_right h1G).2 h1G
    rw [opow_one] at this
    exact Order.add_one_le_of_lt this
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1)) ≤ D.hR (D.B ^ D.hTw (n + 1)) x
    have h0 : D.hTw (n + 1) ≠ 0 := (D.B_pos.trans_le (D.hTw_ge _)).ne'
    rw [D.hR_pow h0 (D.hTw_lt _)]
    calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.b x + 1)) ≤ ω ^ D.hR (D.hTw (n + 1)) x :=
          opow_le_opow_right omega0_pos ih
      _ ≤ D.b x ^ D.hR (D.hTw (n + 1)) x := opow_le_opow_left _ (omega0_lt_inE hGE).le

/-- **The readings of the codes below `ε_{B+1}` are cofinal in `ε_{b(x)+1}`** (the towers, gate `0`). -/
theorem NB_cof {ν : Ordinal.{0}} (hν : ν < eN (D.b x)) : ∃ c, c < D.NB ∧ D.hG c < x ∧ ν < D.hR c x := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hν
  exact ⟨D.hTw (n + 1), D.hTw_lt _, by rw [D.hTw_g]; exact hx.pos, hn.trans_le (D.hTw_read hx hx1 n)⟩

end Base

/-- **THE GENERIC HEREDITARY STEP**: the hereditary codes `B^k·d + r < ε_{B+1}` over a digit system `D` at the base
`B` form a digit system at the base `ε_{B+1}`. -/
noncomputable def step : GoD where
  B := D.NB
  R := D.hR
  g := D.hG
  b := fun x => eN (D.b x)
  ba := fun x => D.ba x + 1
  ix := D.ix + 1
  B_E := D.NB_E
  G_le := D.G_le.trans D.B_lt_NB.le
  B_lt1 := D.NB_lt1
  B_ix := D.NB_eq
  ix_mem := fun S a b ha => CSet.succ_mem (D.ix_mem S a b ha)
  g_lt := D.hG_lt_Om1
  g_zero := D.hG_zero
  g_nat := fun n => by rw [D.hG_nat]; exact D.g_nat n
  g_E := by rw [D.hG_low D.E_lt_B]; exact D.g_E
  g_lowE := fun c hc => by rw [D.hG_low (hc.trans D.E_lt_B)]; exact D.g_lowE c hc
  g_G0 := fun _ => by
    rcases D.G_le.lt_or_eq with hlt | heq
    · rw [D.hG_low hlt, D.g_G0 hlt]
    · rw [heq, D.hG_G]
  g_add := fun _ hZ hωZ => D.h_add hZ hωZ
  g_opow := fun _ hZw hωZ => D.h_opow hZw hωZ (omega0_pos.trans hωZ)
  code_gate := fun _ hZ1 hZ0 hZa hZp _ hAt _ hc hcB => D.h_code_gate hZ1 hZ0 hZa hZp hAt hc hcB
  g_succ := fun _ hZ c hc hg => D.hG_succ hZ c hc hg
  g_le_succ := D.hG_le_succ_all
  mem := fun _ _ _ ha c hc hg => D.hmem ha c hc hg
  R_zero := D.hR_zero
  R_nat := D.hR_nat
  R_E := fun x => by rw [D.hR_low D.E_lt_B]; exact D.R_E x
  R_succ := D.hR_succ_all
  R_pos := fun _ hx hx1 _ hc0 hcB hg => D.hR_pos hx hx1 hc0 hcB hg
  R_omega := fun _ hx hx1 _ ha haB hg => D.omega_le_hR hx hx1 ha haB hg
  R_lt_b := fun _ hx hx1 _ hc hg => D.hR_lt_eNb hx hx1 hc hg
  mono := fun _ hx hx1 c hc d hdc hgc hgd => D.hR_mono hx hx1 c hc d hdc hgc hgd
  cof := fun _ hx hx1 c hc hg ν hν => D.hR_cof hx hx1 c hc hg ν hν
  b_cof := fun _ hx hx1 _ hν => D.NB_cof hx hx1 hν
  b_E := fun _ _ _ => eN_E _
  x_lt_b := fun x hx hx1 => (D.x_lt_b x hx hx1).trans (lt_eN _)
  b_eN := fun x hx hx1 => by
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (D.ba_lt x hx hx1)
    rw [D.b_eN x hx hx1]; exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (D.ba_lt x hx hx1)
  b_Z := fun x hx hx1 => go_eN_lt_evZ (D.b_Z x hx hx1)
  b_pi := fun _ _ hB => D.eN_b_pi hB
  ba_pi := fun σ ρ hB => by
    obtain ⟨g1, g2⟩ := D.ba_pi σ ρ hB
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 o1
    exact ⟨s1, by rw [s2, g2, o2]⟩
  ex := fun _ _ hB c hc hg => D.hR_pi hB c hc hg
  dig := fun _ _ hB d hd hg P P' hat => D.hdig hB d hd hg P P' hat
  ld := D.hld
  cf := D.hTw
  cf_ge := fun k => D.E_lt_B.le.trans (D.hTw_ge k)
  cf_lt := D.hTw_lt
  cf_g := fun k => by rw [D.hTw_g k]; exact epsilon_pos 0
  cf_mono := D.hTw_strict
  cf_cof := fun _ hc => D.hTw_cof hc

theorem step_B : D.step.B = eN D.B := rfl

theorem step_R : D.step.R = D.hR := rfl

theorem step_g : D.step.g = D.hG := rfl

theorem step_b (x : Ordinal.{0}) : D.step.b x = eN (D.b x) := rfl

/-- The step keeps the readings and the gates of the digits. -/
theorem step_R_low {c : Ordinal.{0}} (hc : c < D.B) (x : Ordinal.{0}) : D.step.R c x = D.R c x := D.hR_low hc x

theorem step_g_low {c : Ordinal.{0}} (hc : c < D.B) : D.step.g c = D.g c := D.hG_low hc

/-- Above the old bound the step keeps the readings and the gates (they are those of the digit system). -/
theorem step_R_high {c : Ordinal.{0}} (hc : eN D.B ≤ c) (x : Ordinal.{0}) : D.step.R c x = D.R c x :=
  D.hR_high hc x

theorem step_g_high {c : Ordinal.{0}} (hc : eN D.B ≤ c) : D.step.g c = D.g c := D.hG_high hc

end GoD

end Googology.Trans.PoR.InaccPsi.R2.Go
