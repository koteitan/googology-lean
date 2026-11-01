import Googology.Trans.PoR.InaccPsi.R2.YcEmpty

/-!
# YcVD: THE REPAIRED INTERFACES OVER THE BASE ATOM `Γ(k)` AND THE REPAIRED LAYER STATEMENTS

`Xk.XkVD k` and `Xk.XkC k` copied the hull fields of `Hg.HgVD` / `Ws.WsC` (`ix_mem`, `mem`, `L_mem`: membership in
EVERY hull `Cl(a, b)` with `0 < a`).  Over `Γ(k) = ψ_{Ω₂}(k)` the atoms `Γ(k')`, `k' ≤ k`, enter `Cl(a, b)` only for
`k' < a`, so these fields make the interfaces empty (`Yc.ycVD_empty`, `Yc.ycC_empty`).  The repair asks `k < a`
in the three hull fields and nothing else changes:

* `YcVD k` (**`Xk.XkVD k` with `ix_mem`, `mem` asked for `k < a`**), `YcC k` (**`Xk.XkC k` with `L_mem` asked for
  `k < a`**), `YcCG` (the facts of `Γ(k)` as a base, `Xk.XkCG` for `YcC`);
* `YcVD.ofXk`, `YcC.ofXk` (every old object is a repaired one), `YcVD.toXk0`, `YcC.toXk0` and the round trips at
  `k = 0` (`ycVD_round0`, `ycVD_round0'`, `ycC_round0`, `ycC_round0'`: at `k = 0` the repaired interfaces ARE the
  old ones, `0 < a`), `YcVD.ofHg`, `YcC.ofWs`, `ycVD_zero_ne`, `ycC_zero_ne`, `ycCG_zero_ne`;
* `YcLaySys S k`, `YcLayFront S k` (**the repaired statements of `skLaySys`, `skLayFront`**), `ycLayLo_of`
  (**THE REDUCTION, one proof for every `k`**, the argument of `Xk.xkLayLo_of`), `ycLaySys_zero`,
  `ycLayFront_zero`, `ycLayLo_zero` (non-vacuity at `k = 0`: region (A2) again).

No new axiom.  New definitions: `YcVD`, `YcC`, `YcCG`, `YcVD.ofXk`, `YcVD.toXk0`, `YcVD.ofHg`, `YcC.ofXk`,
`YcC.toXk0`, `YcC.ofWs`, `YcLaySys`, `YcLayFront`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hg Googology.Trans.PoR.InaccPsi.R2.Ws
open Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha
open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Xk

/-- **THE REPAIRED SYSTEM INTERFACE OVER `Γ(k)`**: `Xk.XkVD k` with the hull fields `ix_mem`, `mem` asked for `k < a`
(the atoms `Γ(k') = ψ_{Ω₂}(k')`, `k' ≤ k`, lie in `Cl(a, b)` for `k' < a`). -/
structure YcVD (k : Ordinal.{0}) where
  B : Ordinal.{0}
  γ : Ordinal.{0}
  γ_lt : γ < Om1
  γ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z (XkAt k) B → γ < Z
  γ_G : B = gcG k → γ = 0
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  g : Ordinal.{0} → Ordinal.{0}
  b : Ordinal.{0} → Ordinal.{0}
  ba : Ordinal.{0} → Ordinal.{0}
  ix : Ordinal.{0}
  Z : Ordinal.{0} → Ordinal.{0}
  B_E : InE B
  G_le : gcG k ≤ B
  B_lt1 : B < gcG (k + 1)
  B_ix : B = veblen 1 ix
  Z_fix : ∀ x, InE x → x < Om1 → veblen 1 (Z x) = Z x
  Z_G1 : ∀ x, InE x → x < Om1 → Z x < gq (k + 1) x
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), k < a → γ < b → ix ∈ S.CSet a b
  g_lt : ∀ c, c < B → g c < Om1
  g_zero : g 0 = 0
  g_nat : ∀ n : ℕ, g n < ω
  g_E : g gfE = 0
  g_lowE : ∀ c, c < gfE → g c = gtc c
  g_G0 : ∀ k', k' ≤ k → gcG k' < B → g (gcG k') = 0
  g_add : ∀ Z : Ordinal.{0}, (∀ u v, u < Z → v < Z → u + v < Z) → ω < Z →
    ∀ x y, x + y < B → g x < Z → g y < Z → g (x + y) < Z
  g_opow : ∀ Z : Ordinal.{0}, (∀ u, u < Z → ω ^ u < Z) → ω < Z → ∀ y, ω ^ y < B → g y < Z → g (ω ^ y) < Z
  code_gate : ∀ Z : Ordinal.{0}, Z ≤ Om1 → 0 < Z → (∀ u v, u < Z → v < Z → u + v < Z) →
    (∀ u v, u < Z → v < Z → veblen u v < Z) → ∀ At : Set Ordinal.{0}, (∀ s ∈ At, s ∈ XkAt k ∨ B ≤ s) →
    ∀ c, GxCl Z At c → c < B → g c < Z
  g_succ : ∀ Z : Ordinal.{0}, IsSuccLimit Z → ∀ c, c + 1 < B → g c < Z → g (c + 1) < Z
  g_le_succ : ∀ c, g c ≤ g (c + 1)
  mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), k < a → ∀ c, c < B → g c < b →
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
  ba_lt : ∀ x, InE x → x < Om1 → γ < x → ba x < gq (k + 1) x
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

/-- **THE REPAIRED CODE INTERFACE OVER `Γ(k)`**: `Xk.XkC k` with the hull field `L_mem` asked for `k < a`. -/
structure YcC (k : Ordinal.{0}) where
  Bd : Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  g : Ordinal.{0} → Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  Om1_lt : Om1 < Bd
  Bd_lt1 : Bd < gcG (k + 1)
  add_lt : ∀ a b, a < Bd → b < Bd → a + b < Bd
  g_lt : ∀ a, a < Bd → g a < Om1
  R_Om1 : ∀ x, R Om1 x = x
  g_Om1 : g Om1 = 1
  succ_R : ∀ a, a < Bd → Om1 ∣ a → ∀ x, R (a + Om1) x = R a x + x
  succ_g : ∀ a, a < Bd → Om1 ∣ a → g a ≤ g (a + Om1)
  succ_g_lt : ∀ {x a : Ordinal.{0}}, InE x → a < Bd → Om1 ∣ a → g a < x → g (a + Om1) < x
  g_succ1 : ∀ {x t : Ordinal.{0}}, InE x → t < Bd → g t < x → g (t + 1) < x
  le_R : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → Om1 ≤ ℓ → ℓ < Bd → g ℓ < x → x ≤ R ℓ x
  R_lt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → ℓ < Bd → g ℓ < x → R ℓ x < gq (k + 1) x
  R_mono : ∀ {x b c : Ordinal.{0}}, InE x → x < Om1 → c < Bd → b < c → g c < x → g b < x → R b x < R c x
  R_cof : ∀ {x c : Ordinal.{0}}, InE x → x < Om1 → c < Bd → g c < x → ∀ ν, ν < R c x →
    ∃ b, b < c ∧ g b < x ∧ ν ≤ R b x
  R_pi : ∀ {σ ρ a : Ordinal.{0}}, Bases σ ρ → a < Bd → g a < σ → R a ρ ∈ TB ρ σ ∧ pi σ ρ (R a ρ) = R a σ
  g_cl : ∀ ℓ, Om1 ≤ ℓ → Om1 ∣ ℓ → ℓ < Bd → ∀ Z y : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z (XkAt k) y → ℓ ≤ y →
    y < Om 1 * (Om1 * (ℓ / (Om1 * Om1))) + Om 1 * Om 1 → g ℓ < Z
  L_mem : ∀ ℓ, ℓ < Bd → ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), k < a → g ℓ < b → ℓ ∈ S.CSet a b
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq (k + 1) x


noncomputable def YcVD.ofXk {k : Ordinal.{0}} (D : Xk.XkVD k) : YcVD k where
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
  Z_G1 := D.Z_G1
  ix_mem := fun S a b ha hb => D.ix_mem S a b (lt_of_le_of_lt zero_le ha) hb
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
  mem := fun S a b ha => D.mem S a b (lt_of_le_of_lt zero_le ha)
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

noncomputable def YcVD.toXk0 (D : YcVD 0) : Xk.XkVD 0 where
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
  Z_G1 := D.Z_G1
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

noncomputable def YcC.ofXk {k : Ordinal.{0}} (D : Xk.XkC k) : YcC k where
  Bd := D.Bd
  R := D.R
  g := D.g
  Zo := D.Zo
  Om1_lt := D.Om1_lt
  Bd_lt1 := D.Bd_lt1
  add_lt := D.add_lt
  g_lt := D.g_lt
  R_Om1 := D.R_Om1
  g_Om1 := D.g_Om1
  succ_R := D.succ_R
  succ_g := D.succ_g
  succ_g_lt := D.succ_g_lt
  g_succ1 := D.g_succ1
  le_R := D.le_R
  R_lt := D.R_lt
  R_mono := D.R_mono
  R_cof := D.R_cof
  R_pi := D.R_pi
  g_cl := D.g_cl
  L_mem := fun ℓ hℓ S a b ha => D.L_mem ℓ hℓ S a b (lt_of_le_of_lt zero_le ha)
  Zo_fix := D.Zo_fix
  Zo_G1 := D.Zo_G1

noncomputable def YcC.toXk0 (D : YcC 0) : Xk.XkC 0 where
  Bd := D.Bd
  R := D.R
  g := D.g
  Zo := D.Zo
  Om1_lt := D.Om1_lt
  Bd_lt1 := D.Bd_lt1
  add_lt := D.add_lt
  g_lt := D.g_lt
  R_Om1 := D.R_Om1
  g_Om1 := D.g_Om1
  succ_R := D.succ_R
  succ_g := D.succ_g
  succ_g_lt := D.succ_g_lt
  g_succ1 := D.g_succ1
  le_R := D.le_R
  R_lt := D.R_lt
  R_mono := D.R_mono
  R_cof := D.R_cof
  R_pi := D.R_pi
  g_cl := D.g_cl
  L_mem := D.L_mem
  Zo_fix := D.Zo_fix
  Zo_G1 := D.Zo_G1

/-- `Hg.HgVD` as a repaired system over `G` (`k = 0`). -/
noncomputable def YcVD.ofHg (V : Hg.HgVD) : YcVD 0 := YcVD.ofXk (XkVD.ofHg V)

/-- `Ws.WsC` as a repaired code interface over `G` (`k = 0`). -/
noncomputable def YcC.ofWs (C : Ws.WsC) : YcC 0 := YcC.ofXk (XkC.ofWs C)

theorem ycVD_round0 (D : YcVD 0) : YcVD.ofXk (YcVD.toXk0 D) = D := rfl

theorem ycVD_round0' (D : XkVD 0) : YcVD.toXk0 (YcVD.ofXk D) = D := rfl

theorem ycC_round0 (D : YcC 0) : YcC.ofXk (YcC.toXk0 D) = D := rfl

theorem ycC_round0' (D : XkC 0) : YcC.toXk0 (YcC.ofXk D) = D := rfl

/-- **The facts of `Γ(k)` as a base** for a repaired code interface (`Xk.XkCG`). -/
structure YcCG {k : Ordinal.{0}} (C : YcC k) : Prop where
  Bd_le : C.Bd ≤ gcG k
  R_lt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → ℓ < C.Bd → C.g ℓ < x → C.R ℓ x < gq k x
  Zo_gt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → Om1 ≤ ℓ → ℓ < C.Bd → C.g ℓ < x →
    hdNx (C.R ℓ x) (gq k x) < C.Zo x

theorem ycVD_zero_ne : Nonempty (YcVD 0) := ⟨YcVD.ofHg Wo.woVE⟩

theorem ycC_zero_ne : Nonempty (YcC 0) := ⟨YcC.ofWs wsA1⟩

theorem ycCG_zero_ne : YcCG (YcC.ofWs wsA1) :=
  ⟨xkCG_zero_ne.Bd_le, xkCG_zero_ne.R_lt, xkCG_zero_ne.Zo_gt⟩

/-- **THE REPAIRED `skLaySys`**: for every level `ℓ < Γ(k)` a repaired system over `Γ(k)` with bound at least
`φ(ℓ, Γ(k)+1)` and gate below `K`. -/
def YcLaySys (S : InaccSeq.{0}) (k : Ordinal.{0}) : Prop :=
  ∀ ℓ, ℓ < gcG k → ∃ D : YcVD k, veblen ℓ (gcG k + 1) ≤ D.B ∧ D.γ < Td.tdK S

/-- **THE REPAIRED `skLayFront`**: UPPER, LOWER and CapV at every range restart below `ι(Γ(B)·ω)` for every repaired
system over `Γ(k)` with gate below `K`. -/
def YcLayFront (S : InaccSeq.{0}) (k : Ordinal.{0}) : Prop :=
  ∀ D : YcVD k, D.γ < Td.tdK S → ∀ l, Cd.CdRange S l → l < Bt.iota S (gcG D.B * ω) →
    Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l

/-- **THE REDUCTION** (every `k`): the repaired systems and frontier lemma give UPPER, LOWER and CapV below
`ι(Γ(φ(ℓ, Γ(k)+1))·ω)` for some `ℓ < Γ(k)`. -/
theorem ycLayLo_of {S : InaccSeq.{0}} {k : Ordinal.{0}} (hS : YcLaySys S k) (hF : YcLayFront S k) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG k ∧ l < Bt.iota S (gcG (veblen ℓ (gcG k + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  obtain ⟨D, hB, hγ⟩ := hS ℓ hℓ
  refine hF D hγ l hr (hl.trans_le (Bt.iota_mono (S := S) _ _ ?_))
  exact mul_le_mul_left (gcG_le hB) ω

/-- **The repaired systems over `G`** (`k = 0`, region (A2): `Xk.xkLaySys_zero`). -/
theorem ycLaySys_zero (S : InaccSeq.{0}) : YcLaySys S 0 := fun ℓ hℓ => by
  obtain ⟨D, hB, hγ⟩ := xkLaySys_zero S ℓ hℓ
  exact ⟨YcVD.ofXk D, hB, hγ⟩

/-- **The repaired frontier lemma over `G`** (`k = 0`: `Xk.xkLayFront_zero`). -/
theorem ycLayFront_zero (S : InaccSeq.{0}) : YcLayFront S 0 := fun D hγ l hr hl =>
  xkLayFront_zero S (YcVD.toXk0 D) hγ l hr hl

/-- **Non-vacuity of the repaired reduction**: region (A2) at `k = 0`. -/
theorem ycLayLo_zero (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG 0 ∧ l < Bt.iota S (gcG (veblen ℓ (gcG 0 + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l :=
  ycLayLo_of (ycLaySys_zero S) (ycLayFront_zero S)

end Googology.Trans.PoR.InaccPsi.R2.Yc
