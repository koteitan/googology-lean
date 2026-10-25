import Googology.Trans.PoR.InaccPsi.R2.HcLInd

/-!
# HcVD: A GATED DIGIT SYSTEM WITH A BOUND FIELD `Z(x) ≤ B_x(x)` (readings may pass `B_ω(x)`)

`Hb.HbVD` bounds its readings by a field `Z(x) ≤ B_ω(x)` (`Hb.hbBw`), so no `Hb.HbVD` extending the chain `Hb.hbTG`
reads the code `φ(ω, G+1)` (`Hb.hb_wall_Tw`).  `HcVD` is `Hb.HbVD` with the bound `Z(x) ≤ B_x(x)`
(`Hc.hcBR = φ(x, Γ_{x+1}+1)`); Lemma IMG holds below it (`Hc.hc_pkg_BR`).  The rest of the module is a textual
copy of `Hb.HbVD`.

* `HcVD`, `HcVD.ofHb` (**every `Hb.HbVD` is an `HcVD`**), `HcVD.Q`, the derived facts, `HcVD.R_lt_gq`,
  `HcVD.eN_b_pi`, `HcVD.pi_lt_b` (copies of the `Hb.HbVD` lemmas).

No new axiom.  New definitions: `HcVD`, `HcVD.ofHb`, `HcVD.Q`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A gated digit system with readings below a bound field `Z(x)`** (an `ε`-fixed point `≤ B_x(x)` at every
base): the fields of `Gz.GzVD` with `Z_BR` (`Z(x) ≤ B_x(x)`) in place of `Z_B3`. -/
structure HcVD where
  B : Ordinal.{0}
  γ : Ordinal.{0}
  γ_lt : γ < Om1
  γ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} B → γ < Z
  γ_G : B = gcG 0 → γ = 0
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  g : Ordinal.{0} → Ordinal.{0}
  b : Ordinal.{0} → Ordinal.{0}
  ba : Ordinal.{0} → Ordinal.{0}
  ix : Ordinal.{0}
  Z : Ordinal.{0} → Ordinal.{0}
  B_E : InE B
  G_le : gcG 0 ≤ B
  B_lt1 : B < gcG 1
  B_ix : B = veblen 1 ix
  Z_fix : ∀ x, InE x → x < Om1 → veblen 1 (Z x) = Z x
  Z_BR : ∀ x, InE x → x < Om1 → Z x ≤ hcBR x
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → γ < b → ix ∈ S.CSet a b
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
  R_lt_b : ∀ x, InE x → x < Om1 → γ < x → ∀ c, c < B → g c < x → R c x < b x
  R_lt_Z : ∀ x, InE x → x < Om1 → ∀ c, c < B → g c < x → R c x < Z x
  mono : ∀ x, InE x → x < Om1 → ∀ c, c < B → ∀ d, d < c → g c < x → g d < x → R d x < R c x
  cof : ∀ x, InE x → x < Om1 → ∀ c, c < B → g c < x → ∀ ν, ν < R c x → ∃ d, d < c ∧ g d < x ∧ ν ≤ R d x
  b_cof : ∀ x, InE x → x < Om1 → γ < x → ∀ ν, ν < b x → ∃ d, d < B ∧ g d < x ∧ ν < R d x
  b_E : ∀ x, InE x → x < Om1 → γ < x → InE (b x)
  x_lt_b : ∀ x, InE x → x < Om1 → γ < x → x < b x
  b_eN : ∀ x, InE x → x < Om1 → γ < x → eN (b x) = glA 1 (ba x) x
  ba_lt : ∀ x, InE x → x < Om1 → γ < x → ba x < gq 1 x
  b_Z : ∀ x, InE x → x < Om1 → γ < x → eN (b x) < Z x
  b_pi : ∀ σ ρ, Bases σ ρ → γ < σ → b ρ ∈ TB ρ σ ∧ pi σ ρ (b ρ) = b σ
  ba_pi : ∀ σ ρ, Bases σ ρ → γ < σ → ba ρ ∈ TB ρ σ ∧ pi σ ρ (ba ρ) = ba σ
  ex : ∀ σ ρ, Bases σ ρ → ∀ c, c < B → g c < σ → R c ρ ∈ TB ρ σ ∧ pi σ ρ (R c ρ) = R c σ
  dig : ∀ σ ρ, Bases σ ρ → γ < σ → ∀ d, d < B → g d < σ → ∀ P P' : Ordinal.{0},
    (∀ β, β ∈ TB ρ σ → β < b ρ → ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
    ω ^ P * R d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * R d ρ) = ω ^ P' * R d σ
  ld : ∀ c, IsSuccLimit c → c < B → ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ g cp ≤ g c ∧
    (∀ x, InE x → x < Om1 → g c < x →
      R c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ R cp x) ∧
    ∀ σ ρ, Bases σ ρ → g c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ


/-- **Every `Hb.HbVD` is an `HcVD`** (`Z(x) ≤ B_ω(x) < B_x(x)`). -/
noncomputable def HcVD.ofHb (D : HbVD) : HcVD where
  B := D.B
  γ := D.γ
  γ_lt := D.γ_lt
  γ_cl := D.γ_cl
  γ_G := D.γ_G
  R := D.R
  g := D.g
  b := D.b
  ba := D.ba
  ix := D.ix
  Z := D.Z
  B_E := D.B_E
  G_le := D.G_le
  B_lt1 := D.B_lt1
  B_ix := D.B_ix
  Z_fix := D.Z_fix
  Z_BR := fun x hx hx1 => (D.Z_Bw x hx hx1).trans (hc_Bw_le_BR hx hx1)
  ix_mem := D.ix_mem
  g_lt := D.g_lt
  g_zero := D.g_zero
  g_nat := D.g_nat
  g_E := D.g_E
  g_lowE := D.g_lowE
  g_G0 := D.g_G0
  g_add := D.g_add
  g_opow := D.g_opow
  code_gate := D.code_gate
  g_succ := D.g_succ
  g_le_succ := D.g_le_succ
  mem := D.mem
  R_zero := D.R_zero
  R_nat := D.R_nat
  R_E := D.R_E
  R_succ := D.R_succ
  R_pos := D.R_pos
  R_omega := D.R_omega
  R_lt_b := D.R_lt_b
  R_lt_Z := D.R_lt_Z
  mono := D.mono
  cof := D.cof
  b_cof := D.b_cof
  b_E := D.b_E
  x_lt_b := D.x_lt_b
  b_eN := D.b_eN
  ba_lt := D.ba_lt
  b_Z := D.b_Z
  b_pi := D.b_pi
  ba_pi := D.ba_pi
  ex := D.ex
  dig := D.dig
  ld := D.ld

namespace HcVD

variable (D : HcVD)

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
  unfold HcVD.Q; split_ifs
  · exact zero_le
  · exact le_rfl

theorem Q_nat (n : ℕ) : D.Q n = 0 := by unfold HcVD.Q; rw [if_pos (natCast_lt_omega0 n)]

theorem Q_one : D.Q 1 = 0 := by exact_mod_cast D.Q_nat 1

theorem Q_zero : D.Q 0 = 0 := by exact_mod_cast D.Q_nat 0

theorem Q_inf {k : Ordinal.{0}} (hk : ω ≤ k) : D.Q k = D.g k := by unfold HcVD.Q; rw [if_neg (not_lt.2 hk)]

theorem g_of_Q {k Z : Ordinal.{0}} (hωZ : ω < Z) (h : D.Q k < Z) : D.g k < Z := by
  unfold HcVD.Q at h
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
  unfold HcVD.Q
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact zero_le
  · exact absurd ((lt_add_one c).trans h2) h1
  · exact D.g_le_succ c

theorem R_one (x : Ordinal.{0}) : D.R 1 x = 1 := by exact_mod_cast D.R_nat 1 x

theorem g_one : D.g 1 < ω := by exact_mod_cast D.g_nat 1

section Base0

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem R_one_add {a : Ordinal.{0}} (haB : a < D.B) (hg : D.g a < x) : D.R (1 + a) x = 1 + D.R a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, D.R_nat, D.R_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (D.R_omega x hx hx1 a haω haB hg)]

/-- **The readings lie below `Γ_{x+2}` at every base** (also at or below the base gate). -/
theorem R_lt_gq {c : Ordinal.{0}} (hc : c < D.B) (hg : D.g c < x) : D.R c x < gq 1 x :=
  ((D.R_lt_Z x hx hx1 c hc hg).trans_le (D.Z_BR x hx hx1)).trans (hcBR_lt1 hx hx1)

end Base0

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : D.γ < x)
include hx hx1 hγx

theorem eN_b_lt1 : eN (D.b x) < gq 1 x := by
  rw [D.b_eN x hx hx1 hγx]
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have hn := D.ba_lt x hx hx1 hγx
  have hnT := gm1_T hx hx1 hn
  exact lgVt_lt_low hx hx1 h1T h11 hnT.1 hnT.2 h1T h11 (one_lt_omega0.trans (omega0_lt_inE hq)) hn

theorem b_lt1 : D.b x < gq 1 x := (lt_eN _).trans (D.eN_b_lt1 hx hx1 hγx)

theorem eN_b_lt_Om1 : eN (D.b x) < Om1 := (D.eN_b_lt1 hx hx1 hγx).trans (gm1_facts hx hx1).2.2.1

theorem b_lt_Om1 : D.b x < Om1 := (lt_eN _).trans (D.eN_b_lt_Om1 hx hx1 hγx)

theorem b_T : D.b x ∈ Tset x := (gm1_T hx hx1 (D.b_lt1 hx hx1 hγx)).1

theorem R_lt_eNb {c : Ordinal.{0}} (hc : c < D.B) (hg : D.g c < x) : D.R c x < eN (D.b x) :=
  (D.R_lt_b x hx hx1 hγx c hc hg).trans (lt_eN _)

end Base

/-- **Lemma EXACT for `ε_{b(ρ)+1}`** at every pair of bases. -/
theorem eN_b_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : D.γ < σ) :
    eN (D.b ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (D.b ρ)) = eN (D.b σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := D.ba_pi σ ρ hB hγ
  have hs1 : D.ba ρ < Om1 := (gm1_T hB.2.1 hρ1 (D.ba_lt ρ hB.2.1 hρ1 (hγ.trans hB.2.2.1))).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 g1 hs1
  rw [o2, g2, ← D.b_eN ρ hB.2.1 hρ1 (hγ.trans hB.2.2.1), ← D.b_eN σ hB.1 hσ1 hγ] at h
  exact h

theorem pi_lt_eNb {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hγ : D.γ < σ) (hβ : β ∈ TB ρ σ)
    (hβe : β < eN (D.b ρ)) : pi σ ρ β < eN (D.b σ) := by
  obtain ⟨e1, e2⟩ := D.eN_b_pi hB hγ
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

theorem pi_lt_b {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hγ : D.γ < σ) (hβ : β ∈ TB ρ σ)
    (hβe : β < D.b ρ) : pi σ ρ β < D.b σ := by
  obtain ⟨e1, e2⟩ := D.b_pi σ ρ hB hγ
  rw [← e2]; exact (pi_bijOn hB).2 hβ e1 hβe

end HcVD

end Googology.Trans.PoR.InaccPsi.R2.Hc
