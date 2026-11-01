import Googology.Trans.PoR.InaccPsi.R2.WsA1
import Googology.Trans.PoR.InaccPsi.R2.XkImg

/-!
# XkCode: THE INTERFACES OF REGION (A) OVER THE BASE ATOM `Γ(k)` OF THE LAYER `k`

The layer `k ≥ 1` of region (B-lo) (`Xh.XhLay`) is region (A) again over the base atom `Γ(k) = Γ_{Ω₁+1+k}`, read
`gq k x = Γ_{x+1+k}` (`Xk.XkBase`).  The interfaces of the region-(A) development are fixed to the base `G = Γ(0)`
(`Hg.HgVD`: codes in `[G, Γ(1))`, atom `G`, readings below `Γ_{x+2}`; `Ws.WsC`: levels below `Γ(1)`, readings below
`Γ_{x+2}`, atom `G`; `Ws.WsCG`: the facts of `G` as a base; `Gs.GsRS`: readings below `Γ_{x+2}`).  Here each takes the
base atom index `k` (a constant: the atoms `Γ(k')`, `k' ≤ k`, have gate `0`), and its instance `k = 0` IS the old
interface (both directions, field by field, no field copied as a new axiom or statement):

* `XkAt k = {Γ(k') : k' ≤ k}` (the atoms of the layer), `xkAt_zero` (`XkAt 0 = {G}`);
* `XkVD k` (`Hg.HgVD` over `Γ(k)`: `G_le : Γ(k) ≤ B`, `B < Γ(k+1)`, `Z x < gq (k+1) x`, `ba x < gq (k+1) x`, the atoms
  `XkAt k` in `γ_cl` and `code_gate`, gate `0` at every atom), `XkVD.ofHg`, `XkVD.toHg`, `xkVD_round`;
* `XkC k` (`Ws.WsC` over `Γ(k)`: `Bd < Γ(k+1)`, `R ℓ x < gq (k+1) x`, `Zo x < gq (k+1) x`, the atoms `XkAt k` in
  `g_cl`), `XkC.ofWs`, `XkC.toWs`, `xkC_round`; `XkCG C` (the facts of `Γ(k)` as a base: `Bd ≤ Γ(k)`, `R ℓ x < gq k x`,
  `hdNx (R ℓ x) (gq k x) < Zo x`; `Ws.WsCG` at `k = 0`, `xkCG_zero_iff`);
* `XkRS k` (`Gs.GsRS` with readings below `gq (k+1) x`), `XkRS.ofGs`, `XkRS.toGs`, `xkRS_round`;
* `XkVD.img` (**LEMMA IMG FOR EVERY READING OF AN `XkVD k`**, `k + 1 < ε₀`: from `Xk.xkImg_cst`; at `k = 0` this is
  the use of `He.he_pkg_G1` in `Hg.HgVD.toLD`), `XkVD.pkg` (the gated form for a specified function);
* non-vacuity at `k = 0`: `xkVD_zero_ne` (`Wo.woVE`), `xkC_zero_ne` (`Ws.wsA1`), `xkCG_zero_ne` (`Ws.wsA1_G`),
  `xkRS_zero_ne`.

No new axiom.  New definitions: `XkAt`, `XkVD`, `XkVD.ofHg`, `XkVD.toHg`, `XkC`, `XkC.ofWs`, `XkC.toWs`, `XkCG`,
`XkRS`, `XkRS.ofGs`, `XkRS.toGs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xk

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

/-- **The atoms of the layer `k`**: `Γ(k') = Γ_{Ω₁+1+k'}` for `k' ≤ k`. -/
def XkAt (k : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ k', k' ≤ k ∧ s = gcG k'}

theorem xkAt_zero : XkAt 0 = {gcG 0} := by
  ext s
  constructor
  · rintro ⟨k', hk', rfl⟩
    rw [nonpos_iff_eq_zero.1 hk']; rfl
  · intro hs
    exact ⟨0, le_rfl, hs⟩

theorem xkAt_mono {k k' : Ordinal.{0}} (h : k ≤ k') : XkAt k ⊆ XkAt k' := by
  rintro s ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans h, rfl⟩

/-- **A gated digit system over the base atom `Γ(k)`** (`Hg.HgVD` with the base `G` replaced by `Γ(k)`): codes in `[Γ(k), Γ(k+1))` bound `B`, the atoms `Γ(k')`, `k' ≤ k` (`XkAt k`) in the gate and code-gate fields, gate `0` at the atoms, readings and the bound field below `Γ_{x+2+k} = gq (k+1) x`.  `k = 0` is `Hg.HgVD` (`XkVD.ofHg`, `XkVD.toHg`). -/
structure XkVD (k : Ordinal.{0}) where
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
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → γ < b → ix ∈ S.CSet a b
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

noncomputable def XkVD.ofHg (D : Hg.HgVD) : XkVD 0 where
  B := D.B
  γ := D.γ
  γ_lt := D.γ_lt
  γ_cl := fun Z hZ hZ1 hB => D.γ_cl Z hZ hZ1 (xkAt_zero ▸ hB)
  γ_G := D.γ_G
  R := D.R
  g := D.g
  b := D.b
  ba := D.ba
  ix := D.ix
  Z := D.Z
  B_E := D.B_E
  G_le := D.G_le
  B_lt1 := by rw [zero_add]; exact D.B_lt1
  B_ix := D.B_ix
  Z_fix := D.Z_fix
  Z_G1 := fun x hx hx1 => by rw [zero_add]; exact D.Z_G1 x hx hx1
  ix_mem := D.ix_mem
  g_lt := D.g_lt
  g_zero := D.g_zero
  g_nat := D.g_nat
  g_E := D.g_E
  g_lowE := D.g_lowE
  g_G0 := fun k' hk' h => by obtain rfl := nonpos_iff_eq_zero.1 hk'; exact D.g_G0 h
  g_add := D.g_add
  g_opow := D.g_opow
  code_gate := fun Z hZ1 hZ0 hZa hZv At hAt => D.code_gate Z hZ1 hZ0 hZa hZv At fun s hs => (hAt s hs).imp_left fun h => by rw [xkAt_zero] at h; exact h
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
  ba_lt := fun x hx hx1 hγ => by rw [zero_add]; exact D.ba_lt x hx hx1 hγ
  b_Z := D.b_Z
  b_pi := D.b_pi
  ba_pi := D.ba_pi
  ex := D.ex
  dig := D.dig
  ld := D.ld

noncomputable def XkVD.toHg (D : XkVD 0) : Hg.HgVD where
  B := D.B
  γ := D.γ
  γ_lt := D.γ_lt
  γ_cl := fun Z hZ hZ1 hB => D.γ_cl Z hZ hZ1 (xkAt_zero ▸ hB)
  γ_G := D.γ_G
  R := D.R
  g := D.g
  b := D.b
  ba := D.ba
  ix := D.ix
  Z := D.Z
  B_E := D.B_E
  G_le := D.G_le
  B_lt1 := by have := D.B_lt1; rwa [zero_add] at this
  B_ix := D.B_ix
  Z_fix := D.Z_fix
  Z_G1 := fun x hx hx1 => by have := D.Z_G1 x hx hx1; rwa [zero_add] at this
  ix_mem := D.ix_mem
  g_lt := D.g_lt
  g_zero := D.g_zero
  g_nat := D.g_nat
  g_E := D.g_E
  g_lowE := D.g_lowE
  g_G0 := fun h => D.g_G0 0 le_rfl h
  g_add := D.g_add
  g_opow := D.g_opow
  code_gate := fun Z hZ1 hZ0 hZa hZv At hAt => D.code_gate Z hZ1 hZ0 hZa hZv At fun s hs => (hAt s hs).imp_left fun h => by rw [xkAt_zero]; exact h
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
  ba_lt := fun x hx hx1 hγ => by have := D.ba_lt x hx hx1 hγ; rwa [zero_add] at this
  b_Z := D.b_Z
  b_pi := D.b_pi
  ba_pi := D.ba_pi
  ex := D.ex
  dig := D.dig
  ld := D.ld

/-- **The code interface over the base atom `Γ(k)`** (`Ws.WsC` with `Γ(1)`, `Γ_{x+2}`, the atom `G` replaced by `Γ(k+1)`, `Γ_{x+2+k}`, the atoms `XkAt k`).  `k = 0` is `Ws.WsC` (`XkC.ofWs`, `XkC.toWs`). -/
structure XkC (k : Ordinal.{0}) where
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
  L_mem : ∀ ℓ, ℓ < Bd → ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → g ℓ < b → ℓ ∈ S.CSet a b
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq (k + 1) x

noncomputable def XkC.ofWs (C : Ws.WsC) : XkC 0 where
  Bd := C.Bd
  R := C.R
  g := C.g
  Zo := C.Zo
  Om1_lt := C.Om1_lt
  Bd_lt1 := by rw [zero_add]; exact C.Bd_lt1
  add_lt := C.add_lt
  g_lt := C.g_lt
  R_Om1 := C.R_Om1
  g_Om1 := C.g_Om1
  succ_R := C.succ_R
  succ_g := C.succ_g
  succ_g_lt := C.succ_g_lt
  g_succ1 := C.g_succ1
  le_R := C.le_R
  R_lt := fun hx hx1 hℓ hg => by rw [zero_add]; exact C.R_lt hx hx1 hℓ hg
  R_mono := C.R_mono
  R_cof := C.R_cof
  R_pi := C.R_pi
  g_cl := fun ℓ h1 h2 h3 Z y hZ hZ1 hy => C.g_cl ℓ h1 h2 h3 Z y hZ hZ1 (xkAt_zero ▸ hy)
  L_mem := C.L_mem
  Zo_fix := C.Zo_fix
  Zo_G1 := fun x hx hx1 => by rw [zero_add]; exact C.Zo_G1 x hx hx1

noncomputable def XkC.toWs (C : XkC 0) : Ws.WsC where
  Bd := C.Bd
  R := C.R
  g := C.g
  Zo := C.Zo
  Om1_lt := C.Om1_lt
  Bd_lt1 := by have := C.Bd_lt1; rwa [zero_add] at this
  add_lt := C.add_lt
  g_lt := C.g_lt
  R_Om1 := C.R_Om1
  g_Om1 := C.g_Om1
  succ_R := C.succ_R
  succ_g := C.succ_g
  succ_g_lt := C.succ_g_lt
  g_succ1 := C.g_succ1
  le_R := C.le_R
  R_lt := fun hx hx1 hℓ hg => by have := C.R_lt hx hx1 hℓ hg; rwa [zero_add] at this
  R_mono := C.R_mono
  R_cof := C.R_cof
  R_pi := C.R_pi
  g_cl := fun ℓ h1 h2 h3 Z y hZ hZ1 hy => C.g_cl ℓ h1 h2 h3 Z y hZ hZ1 (xkAt_zero ▸ hy)
  L_mem := C.L_mem
  Zo_fix := C.Zo_fix
  Zo_G1 := fun x hx hx1 => by have := C.Zo_G1 x hx hx1; rwa [zero_add] at this

/-- **A reading system with readings below `Γ_{x+2+k} = gq (k+1) x`** (`Gs.GsRS` with `lt0` widened).  `k = 0` is `Gs.GsRS` (`XkRS.ofGs`, `XkRS.toGs`). -/
structure XkRS (k : Ordinal.{0}) where
  K : GsCS
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  E_lt : gfE < K.B
  B_lim : IsSuccLimit K.B
  gt_E : K.gt gfE = 0
  gt_lowE : ∀ c, c < gfE → K.gt c = gtc c
  R_E : ∀ x, InE x → x < Om1 → R gfE x = eN x
  lt0 : ∀ c x, InE x → x < Om1 → c < K.B → K.gt c < x → R c x < gq (k + 1) x
  mono : ∀ b c x, InE x → x < Om1 → c < K.B → b < c → K.gt b < x → K.gt c < x → R b x < R c x
  succ : ∀ b x, x < Om1 → R (b + 1) x = R b x + 1
  gt_le_succ : ∀ b, K.gt b ≤ K.gt (b + 1)
  cof : ∀ c x, InE x → x < Om1 → c < K.B → gfE < c → K.gt c < x → ∀ ν < R c x,
    ∃ b, gfE ≤ b ∧ b < c ∧ K.gt b < x ∧ ν ≤ R b x
  ex : ∀ σ ρ c, Bases σ ρ → c < K.B → K.gt c < σ →
    R c ρ ∈ TB ρ σ ∧ Googology.Trans.PoR.InaccPsi.R2.pi σ ρ (R c ρ) = R c σ
  ld : ∀ c, IsSuccLimit c → gfE < c → c < K.B → Nonempty (GsmLD K R c)

noncomputable def XkRS.ofGs (RS : GsRS) : XkRS 0 where
  K := RS.K
  R := RS.R
  E_lt := RS.E_lt
  B_lim := RS.B_lim
  gt_E := RS.gt_E
  gt_lowE := RS.gt_lowE
  R_E := RS.R_E
  lt0 := fun c x hx hx1 hc hg => by rw [zero_add]; exact RS.lt0 c x hx hx1 hc hg
  mono := RS.mono
  succ := RS.succ
  gt_le_succ := RS.gt_le_succ
  cof := RS.cof
  ex := RS.ex
  ld := RS.ld

noncomputable def XkRS.toGs (RS : XkRS 0) : GsRS where
  K := RS.K
  R := RS.R
  E_lt := RS.E_lt
  B_lim := RS.B_lim
  gt_E := RS.gt_E
  gt_lowE := RS.gt_lowE
  R_E := RS.R_E
  lt0 := fun c x hx hx1 hc hg => by have := RS.lt0 c x hx hx1 hc hg; rwa [zero_add] at this
  mono := RS.mono
  succ := RS.succ
  gt_le_succ := RS.gt_le_succ
  cof := RS.cof
  ex := RS.ex
  ld := RS.ld


theorem xkVD_round (D : HgVD) : XkVD.toHg (XkVD.ofHg D) = D := rfl

theorem xkC_round (C : WsC) : XkC.toWs (XkC.ofWs C) = C := rfl

theorem xkRS_round (RS : GsRS) : XkRS.toGs (XkRS.ofGs RS) = RS := rfl

/-- **The facts of `Γ(k)` as a base** for a code interface over `Γ(k)` (`Ws.WsCG` at `k = 0`). -/
structure XkCG {k : Ordinal.{0}} (C : XkC k) : Prop where
  Bd_le : C.Bd ≤ gcG k
  R_lt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → ℓ < C.Bd → C.g ℓ < x → C.R ℓ x < gq k x
  Zo_gt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → Om1 ≤ ℓ → ℓ < C.Bd → C.g ℓ < x →
    hdNx (C.R ℓ x) (gq k x) < C.Zo x

/-- **`XkCG` at `k = 0` is `Ws.WsCG`** (`Γ_{x+1} = gq 0 x`, `Gm.mg_gq0`). -/
theorem xkCG_zero_iff (C : WsC) : XkCG (XkC.ofWs C) ↔ WsCG C := by
  constructor
  · intro h
    refine ⟨h.Bd_le, fun hx hx1 hℓ hg => ?_, fun hx hx1 h1 hℓ hg => ?_⟩
    · rw [mg_gq0 hx hx1]; exact h.R_lt hx hx1 hℓ hg
    · rw [mg_gq0 hx hx1]; exact h.Zo_gt hx hx1 h1 hℓ hg
  · intro h
    refine ⟨h.Bd_le, fun hx hx1 hℓ hg => ?_, fun hx hx1 h1 hℓ hg => ?_⟩
    · rw [← mg_gq0 hx hx1]; exact h.R_lt hx hx1 hℓ hg
    · rw [← mg_gq0 hx hx1]; exact h.Zo_gt hx hx1 h1 hℓ hg

/-- **LEMMA IMG FOR EVERY READING OF AN `XkVD k`** (`k + 1 < ε₀`): at a restart `ρ` every value up to a reading
`R c ρ` (gate below `ρ`) has Lemma IMG.  At `k = 0` this is the bound used through `He.he_pkg_G1` in
`Hg.HgVD.toLD`. -/
theorem XkVD.img {k : Ordinal.{0}} (D : XkVD k) (hk : k + 1 < ε₀) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
    {c : Ordinal.{0}} (hc : c < D.B) (hg : D.g c < ρ) : ∀ v, v ≤ D.R c ρ → GnI ρ δ v := fun v hv =>
  xkImg_cst h (k + 1) le_add_self hk v
    (hv.trans_lt ((D.R_lt_Z ρ h.ρE h.ρ1 c hc hg).trans (D.Z_G1 ρ h.ρE h.ρ1)))

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW THE BOUND FIELD OF AN `XkVD k`** (`k + 1 < ε₀`). -/
theorem XkVD.pkg {k : Ordinal.{0}} (D : XkVD k) (hk : k + 1 < ε₀) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
    {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ ≤ D.Z ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  xkPkg_cst h le_add_self hk hgρ hC (hT.trans_lt (D.Z_G1 ρ h.ρE h.ρ1)) hex

/-- Non-vacuity at `k = 0`. -/
theorem xkVD_zero_ne : Nonempty (XkVD 0) := ⟨XkVD.ofHg Wo.woVE⟩

theorem xkC_zero_ne : Nonempty (XkC 0) := ⟨XkC.ofWs wsA1⟩

theorem xkCG_zero_ne : XkCG (XkC.ofWs wsA1) := (xkCG_zero_iff wsA1).2 wsA1_G

theorem xkRS_zero_ne : Nonempty (XkRS 0) := ⟨XkRS.ofGs Wo.woVE.toRS⟩

end Googology.Trans.PoR.InaccPsi.R2.Xk
