import Googology.Trans.PoR.InaccPsi.R2.GnZ

/-!
# A DIGIT SYSTEM AT AN `ε`-NUMBER BASE: the input of one generic hereditary step

The rounds built hereditary code systems base by base (`R2.Gf`, `R2.Gj`, `R2.Gk`, `R2.Gn`).  A digit system
`D : GoD` packages, for codes `c < D.B` below an `ε`-number bound `D.B` (`Γ_{Ω₁+1} ≤ D.B < Γ_{Ω₁+2}`), exactly the facts
one hereditary step `c = B^k·d + r` uses: the reading `D.R c x` (`Ω₁ ↦ x`), the gate `D.g c`, the reading `D.b x` of
the base `B` itself (an `ε`-number, the supremum of the digit readings, with `ε_{b(x)+1} = ϑˣ(Ω₁ + D.ba x)`), and

* gates: below `Ω₁`, of sums, of powers `ω^y`, of codes over `Z` with atoms (`code_gate`), along `+1`;
* readings: `0`, `n`, `+1`, positive, infinite, strictly increasing, cofinal, below `b(x)`, cofinal in `b(x)`;
* hulls: `c ∈ Cl(a, b)` and `ω^e·c ∈ Cl(a, b)` when `e ∈ Cl(a, b)`; `B = φ(1, ix)` with `ix` in every hull;
* Lemma EXACT for the readings, for `b` and for `ba`; **the digit rule** `dig`: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` once the
  atoms `ω^{P+β}` (`β < b(ρ)`) are exact; the last term of every limit code with Lemma EXACT for its logend (`ld`);
* the bounds `ba(x) < Γ_{x+2}` and `ε_{b(x)+1} < ζ_{Γ_{x+1}+1}` (so Lemma IMG of `R2.GnZ` applies to every logend);
* a cofinal sequence of codes with gates below `ε₀`.

* `GoD`, `GoD.Q` (the gate of an exponent), the derived facts `B_pos`, `B_lim`, `omega_lt_B`, `nat_lt_B`, `one_lt_B`,
  `g_of_Q`, `Q_le`, `Q_nat`, `Q_one_add`, `R_one`, `R_one_add`, `b_lt_Om1`, `eN_b_lt1`, `eN_b_pi`, `R_lt_eNb`;
* `go_eN_lt_SC` (`ε_{u+1} < s` for a strongly critical `s > u`), `go_eN_lt_evZ` (`ε_{u+1} < ζ_{g+1}` for `u < ζ_{g+1}`),
  `go_eN_veb` (`ε_{φ(1,i)+1} = φ(1, i+1)`), `go_noAt` (a code below `m` over atoms `≥ m` has no atom).

No new axiom.  New definitions: `GoD`, `GoD.Q`.
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

/-- **A digit system at an `ε`-number base `B`**: the facts of the codes `c < B` that one hereditary step uses. -/
structure GoD where
  B : Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  g : Ordinal.{0} → Ordinal.{0}
  b : Ordinal.{0} → Ordinal.{0}
  ba : Ordinal.{0} → Ordinal.{0}
  ix : Ordinal.{0}
  B_E : InE B
  G_le : gcG 0 ≤ B
  B_lt1 : B < gcG 1
  B_ix : B = veblen 1 ix
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ix ∈ S.CSet a b
  g_lt : ∀ c, c < B → g c < Om1
  g_zero : g 0 = 0
  g_nat : ∀ n : ℕ, g n < ω
  g_E : g gfE = 0
  g_lowE : ∀ c, c < gfE → g c = gtc c
  g_G0 : gcG 0 < B → g (gcG 0) = 0
  g_add : ∀ Z : Ordinal.{0}, (∀ u v, u < Z → v < Z → u + v < Z) → ω < Z →
    ∀ x y, x + y < B → g x < Z → g y < Z → g (x + y) < Z
  g_opow : ∀ Z : Ordinal.{0}, (∀ u, u < Z → ω ^ u < Z) → ω < Z → ∀ y, ω ^ y < B → g y < Z → g (ω ^ y) < Z
  code_gate : ∀ Z : Ordinal.{0}, Z ≤ Om1 → 0 < Z → (∀ u v, u < Z → v < Z → u + v < Z) →
    (∀ u v, u < Z → v < Z → veblen u v < Z) → ∀ At : Set Ordinal.{0}, (∀ s ∈ At, s = gcG 0 ∨ B ≤ s) →
    ∀ c, GxCl Z At c → c < B → g c < Z
  g_succ : ∀ Z : Ordinal.{0}, IsSuccLimit Z → ∀ c, c + 1 < B → g c < Z → g (c + 1) < Z
  g_le_succ : ∀ c, g c ≤ g (c + 1)
  mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ∀ c, c < B → g c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b
  R_zero : ∀ x, R 0 x = 0
  R_nat : ∀ (n : ℕ) x, R n x = n
  R_E : ∀ x, R gfE x = eN x
  R_succ : ∀ c x, R (c + 1) x = R c x + 1
  R_pos : ∀ x, InE x → x < Om1 → ∀ c, c ≠ 0 → c < B → g c < x → 0 < R c x
  R_omega : ∀ x, InE x → x < Om1 → ∀ c, ω ≤ c → c < B → g c < x → ω ≤ R c x
  R_lt_b : ∀ x, InE x → x < Om1 → ∀ c, c < B → g c < x → R c x < b x
  mono : ∀ x, InE x → x < Om1 → ∀ c, c < B → ∀ d, d < c → g c < x → g d < x → R d x < R c x
  cof : ∀ x, InE x → x < Om1 → ∀ c, c < B → g c < x → ∀ ν, ν < R c x → ∃ d, d < c ∧ g d < x ∧ ν ≤ R d x
  b_cof : ∀ x, InE x → x < Om1 → ∀ ν, ν < b x → ∃ d, d < B ∧ g d < x ∧ ν < R d x
  b_E : ∀ x, InE x → x < Om1 → InE (b x)
  x_lt_b : ∀ x, InE x → x < Om1 → x < b x
  b_eN : ∀ x, InE x → x < Om1 → eN (b x) = glA 1 (ba x) x
  ba_lt : ∀ x, InE x → x < Om1 → ba x < gq 1 x
  b_Z : ∀ x, InE x → x < Om1 → eN (b x) < evZ (lgG x)
  b_pi : ∀ σ ρ, Bases σ ρ → b ρ ∈ TB ρ σ ∧ pi σ ρ (b ρ) = b σ
  ba_pi : ∀ σ ρ, Bases σ ρ → ba ρ ∈ TB ρ σ ∧ pi σ ρ (ba ρ) = ba σ
  ex : ∀ σ ρ, Bases σ ρ → ∀ c, c < B → g c < σ → R c ρ ∈ TB ρ σ ∧ pi σ ρ (R c ρ) = R c σ
  dig : ∀ σ ρ, Bases σ ρ → ∀ d, d < B → g d < σ → ∀ P P' : Ordinal.{0},
    (∀ β, β ∈ TB ρ σ → β < b ρ → ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
    ω ^ P * R d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * R d ρ) = ω ^ P' * R d σ
  ld : ∀ c, IsSuccLimit c → c < B → ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ g cp ≤ g c ∧
    (∀ x, InE x → x < Om1 → g c < x →
      R c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ R cp x) ∧
    ∀ σ ρ, Bases σ ρ → g c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ
  cf : ℕ → Ordinal.{0}
  cf_ge : ∀ k, gfE ≤ cf k
  cf_lt : ∀ k, cf k < B
  cf_g : ∀ k, g (cf k) < ε₀
  cf_mono : ∀ k, cf k < cf (k + 1)
  cf_cof : ∀ c, c < B → ∃ k, c < cf k

/-! ## General facts -/

/-- `ε_{u+1} < s` for a strongly critical `s > u`. -/
theorem go_eN_lt_SC {u s : Ordinal.{0}} (hs : SC s) (hu : u < s) : eN u < s := by
  have hE : InE s := Low.opow_eq_self_of_SC hs
  have hu1 : u + 1 < s := (ev_isSuccLimit_of_inE hE).add_one_lt hu
  have h1s : (1 : Ordinal.{0}) < s := one_lt_omega0.trans (omega0_lt_inE hE)
  have he : veblen 1 (u + 1) < s := hs.2 1 h1s (u + 1) hu1
  have h1 : eN u ≤ veblen 1 (u + 1) :=
    eN_le ((lt_add_one u).trans_le (right_le_veblen 1 (u + 1))) (omega0_opow_epsilon (u + 1))
  exact h1.trans_lt he

/-- `ε_{u+1} < ζ_{g+1}` for every `u < ζ_{g+1}` (`evZ g` is a fixed point of `ε`). -/
theorem go_eN_lt_evZ {u g : Ordinal.{0}} (hu : u < evZ g) : eN u < evZ g := by
  have hu1 : u + 1 < evZ g := (ev_isSuccLimit_of_inE (evZ_E g)).add_one_lt hu
  have he : veblen 1 (u + 1) < evZ g := by
    have := (isNormal_veblen 1).strictMono hu1
    rwa [show veblen 1 (evZ g) = evZ g from epsilon_evZ g] at this
  have h1 : eN u ≤ veblen 1 (u + 1) :=
    eN_le ((lt_add_one u).trans_le (right_le_veblen 1 (u + 1))) (omega0_opow_epsilon (u + 1))
  exact h1.trans_lt he

/-- `ε_{φ(1, i)+1} = φ(1, i+1)`. -/
theorem go_eN_veb (i : Ordinal.{0}) : eN (veblen 1 i) = veblen 1 (i + 1) := by
  have hE : InE (veblen 1 i) := omega0_opow_epsilon i
  have h := evA_add_one (veblen 1 i) 0
  rw [evA_zero hE, zero_add] at h
  rw [← h, evA]
  exact congrArg (fun t => veblen 1 (t + 1)) (evIx_epsilon i)

/-- A code below `m` over atoms `≥ m` uses no atom. -/
theorem go_noAt {Z m : Ordinal.{0}} {At : Set Ordinal.{0}} (hAt : ∀ s ∈ At, m ≤ s) {v : Ordinal.{0}}
    (hv : GxCl Z At v) : v < m → GxCl Z ∅ v := mg_noAt hAt hv

namespace GoD

variable (D : GoD)

/-- **The gate of an exponent**: `0` when finite. -/
noncomputable def Q (k : Ordinal.{0}) : Ordinal.{0} := if k < ω then 0 else D.g k

theorem B_pos : 0 < D.B := D.B_E.pos

theorem B_ne : D.B ≠ 0 := D.B_pos.ne'

theorem B_lim : IsSuccLimit D.B := ev_isSuccLimit_of_inE D.B_E

theorem omega_lt_B : ω < D.B := omega0_lt_inE D.B_E

theorem nat_lt_B (n : ℕ) : (n : Ordinal.{0}) < D.B := (natCast_lt_omega0 n).trans D.omega_lt_B

theorem one_lt_B : (1 : Ordinal.{0}) < D.B := one_lt_omega0.trans D.omega_lt_B

theorem E_lt_B : gfE < D.B := gfE_lt_G0.trans_le D.G_le

theorem Q_le (k : Ordinal.{0}) : D.Q k ≤ D.g k := by
  unfold Q; split_ifs
  · exact zero_le
  · exact le_rfl

theorem Q_nat (n : ℕ) : D.Q n = 0 := by unfold Q; rw [if_pos (natCast_lt_omega0 n)]

theorem Q_one : D.Q 1 = 0 := by exact_mod_cast D.Q_nat 1

theorem Q_zero : D.Q 0 = 0 := by exact_mod_cast D.Q_nat 0

theorem Q_inf {k : Ordinal.{0}} (hk : ω ≤ k) : D.Q k = D.g k := by unfold Q; rw [if_neg (not_lt.2 hk)]

theorem g_of_Q {k Z : Ordinal.{0}} (hωZ : ω < Z) (h : D.Q k < Z) : D.g k < Z := by
  unfold Q at h
  split_ifs at h with hk
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    exact (D.g_nat n).trans hωZ
  · exact h

theorem Q_one_add (a : Ordinal.{0}) : D.Q (1 + a) = D.Q a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, Q_nat, Q_nat]
  · rw [one_add_of_omega0_le ha]

theorem Q_le_succ (c : Ordinal.{0}) : D.Q c ≤ D.Q (c + 1) := by
  unfold Q
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact zero_le
  · exact absurd ((lt_add_one c).trans h2) h1
  · exact D.g_le_succ c

theorem R_one (x : Ordinal.{0}) : D.R 1 x = 1 := by exact_mod_cast D.R_nat 1 x

theorem g_one : D.g 1 < ω := by exact_mod_cast D.g_nat 1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem R_one_add {a : Ordinal.{0}} (haB : a < D.B) (hg : D.g a < x) : D.R (1 + a) x = 1 + D.R a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, D.R_nat, D.R_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (D.R_omega x hx hx1 a haω haB hg)]

theorem eN_b_lt1 : eN (D.b x) < gq 1 x := by
  rw [D.b_eN x hx hx1]
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have hn := D.ba_lt x hx hx1
  have hnT := gm1_T hx hx1 hn
  exact lgVt_lt_low hx hx1 h1T h11 hnT.1 hnT.2 h1T h11 (one_lt_omega0.trans (omega0_lt_inE hq)) hn

theorem b_lt1 : D.b x < gq 1 x := (lt_eN _).trans (D.eN_b_lt1 hx hx1)

theorem eN_b_lt_Om1 : eN (D.b x) < Om1 := (D.eN_b_lt1 hx hx1).trans (gm1_facts hx hx1).2.2.1

theorem b_lt_Om1 : D.b x < Om1 := (lt_eN _).trans (D.eN_b_lt_Om1 hx hx1)

theorem b_T : D.b x ∈ Tset x := (gm1_T hx hx1 (D.b_lt1 hx hx1)).1

theorem R_lt_eNb {c : Ordinal.{0}} (hc : c < D.B) (hg : D.g c < x) : D.R c x < eN (D.b x) :=
  (D.R_lt_b x hx hx1 c hc hg).trans (lt_eN _)

end Base

/-- **Lemma EXACT for `ε_{b(ρ)+1}`** at every pair of bases. -/
theorem eN_b_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : eN (D.b ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (D.b ρ)) = eN (D.b σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := D.ba_pi σ ρ hB
  have hs1 : D.ba ρ < Om1 := (gm1_T hB.2.1 hρ1 (D.ba_lt ρ hB.2.1 hρ1)).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 g1 hs1
  rw [o2, g2, ← D.b_eN ρ hB.2.1 hρ1, ← D.b_eN σ hB.1 hσ1] at h
  exact h

theorem pi_lt_eNb {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β ∈ TB ρ σ) (hβe : β < eN (D.b ρ)) :
    pi σ ρ β < eN (D.b σ) := by
  obtain ⟨e1, e2⟩ := D.eN_b_pi hB
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

theorem pi_lt_b {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β ∈ TB ρ σ) (hβe : β < D.b ρ) :
    pi σ ρ β < D.b σ := by
  obtain ⟨e1, e2⟩ := D.b_pi σ ρ hB
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

end GoD

end Googology.Trans.PoR.InaccPsi.R2.Go
