import Googology.Trans.PoR.InaccPsi.R2.HkFr

/-!
# HlLv: A GATED LEVEL DATUM `(L, ℓ, g)`, AND THE READINGS AT THE LEVEL `L + ν`

PORT of `Hj.HjLv` to GATED level data.  A gated level datum (`HlLv`) is a multiple `L = Ω₁·q` (`q < Ω₁`) read as
`ℓ(x)` with a LEVEL GATE `g < Ω₁`: Lemma EXACT `π(ℓ(ρ)) = ℓ(σ)` only at base pairs with `g < σ`, `L ∈ C(a, b)` only
for `0 < a`, `g < b`, the code gate `g < Z` only for a strongly critical `Z` over which a code in `[L, Ω₁²)` exists
(`g_cl`), and `ℓ(x) + x < x·x` above the gate (`l_lt2`, used for the outer low field of `G`).  `Hj.HjLv` has no gate,
asks `L` a code over every `Z` and the membership in every hull.

* `hl_lt_sq`, `hl_sq_indec`, `hl_add_lt_sq` (`x + x < x·x`);
* `HlLv`, `hlL1` (`L = Ω₁`, `ℓ(x) = x`, gate `0`), `HlLv.succ` (`L + Ω₁`, `ℓ(x) + x`, same gate), `HlLv.L_add_lt`;
* `hlv_cl_gate`, `hlv_cl_g` (**THE LEVEL GATE `g < Z` FROM A CODE AT THE LEVEL**), `hlv_L_mem` (gated), and the
  readings at the level `ℓ(x) + ν` (ports of the `Hj.hjv_*` lemmas to `HlLv`; `hlv_glA_pi`, `hlv_lev1_pi` ask `g < σ`).
  The `Λ`-free lemmas `Hj.hj_cl_mod`, `Hj.hj_opow_mul`, `Hj.hj_absorb_mul`, `Hj.hj_mod_eq`, `Hj.hj_Om_E` are imported.

No new axiom.  New definitions: `HlLv`, `hlL1`, `HlLv.succ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The level datum -/

/-! ## Squares of `ε`-numbers -/

theorem hl_lt_sq {x : Ordinal.{0}} (hx : InE x) : x < x * x :=
  lt_mul_of_one_lt_right hx.pos (one_lt_omega0.trans (omega0_lt_inE hx))

/-- **`x·x` is additively principal** at an `ε`-number `x`. -/
theorem hl_sq_indec {x : Ordinal.{0}} (hx : InE x) : Indec (x * x) := by
  have e : x * x = ω ^ (x + x) := by
    conv_lhs => rw [← show ω ^ x = x from hx]
    rw [← opow_add]
  rw [e]; exact indec_opow _

/-- **`x + x < x·x`** at an `ε`-number `x`. -/
theorem hl_add_lt_sq {x : Ordinal.{0}} (hx : InE x) : x + x < x * x :=
  (hl_sq_indec hx).add_lt (hl_lt_sq hx) (hl_lt_sq hx)

/-- **A GATED level datum**: a multiple `L = Ω₁·q` (`q < Ω₁`), `Ω₁ ≤ L < G`, read as `ℓ(x)` with `x ≤ ℓ(x)`,
`ℓ(x) < Γ_{x+1}`; the LEVEL GATE `g < Ω₁` is below every strongly critical `Z ≤ Ω₁` over which some code in
`[L, Ω₁²)` exists (`g_cl`); `L` lies in every hull `C(a, b)` with `0 < a`, `g < b`; and Lemma EXACT for `ℓ` holds at
the base pairs `(σ, ρ)` with `g < σ`.  (`Hj.HjLv` asks Lemma EXACT at every base pair, the hull membership at every
`a`, `b`, and `L` a code over every `Z`.) -/
structure HlLv where
  L : Ordinal.{0}
  l : Ordinal.{0} → Ordinal.{0}
  q : Ordinal.{0}
  g : Ordinal.{0}
  g_lt : g < Om1
  q_lt : q < Om1
  OL : (Om1 : Ordinal.{0}) ≤ L
  L_G : L < gcG 0
  L_eq : L = Om 1 * q
  g_cl : ∀ Z y : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} y → L ≤ y → y < Om 1 * Om 1 → g < Z
  L_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → g < b → L ∈ S.CSet a b
  l_ge : ∀ x, x ≤ l x
  l_lt : ∀ x, InE x → x < Om1 → l x < lgG x
  l_lt2 : ∀ x, InE x → x < Om1 → g < x → l x + x < x * x
  l_pi : ∀ σ ρ, Bases σ ρ → g < σ → l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

/-- **The level datum `Ω₁`, read as `x`** (gate `0`). -/
noncomputable def hlL1 : HlLv where
  L := Om1
  l := fun x => x
  q := 1
  g := 0
  g_lt := gv_Om1_pos
  q_lt := hg_one_lt_Om1
  OL := le_rfl
  L_G := hg_Om1_lt_G 0
  L_eq := by rw [mul_one, Br.Om1_eq]
  g_cl := fun _ _ hZ _ _ _ _ => hZ.1
  L_mem := fun _ _ _ _ _ => by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  l_ge := fun _ => le_rfl
  l_lt := fun _ hx hx1 => (lgG_facts hx hx1).2.1
  l_lt2 := fun _ hx _ _ => hl_add_lt_sq hx
  l_pi := fun _ _ hB _ => pi_base hB

namespace HlLv

variable (Λ : HlLv)

theorem L_lt (α : Ordinal.{0}) : Λ.L < gcG α := by
  rcases eq_or_ne α 0 with h | h
  · rw [h]; exact Λ.L_G
  · exact Λ.L_G.trans (gcG_lt (pos_iff_ne_zero.2 h))

/-- **The next level datum `L + Ω₁`, read as `ℓ(x) + x`.** -/
noncomputable def succ : HlLv where
  L := Λ.L + Om1
  l := fun x => Λ.l x + x
  q := Λ.q + 1
  g := Λ.g
  g_lt := Λ.g_lt
  q_lt := gl_Om1_lim.add_one_lt Λ.q_lt
  OL := Λ.OL.trans le_self_add
  L_G := (inE_indec gr_G_inE).add_lt Λ.L_G (hg_Om1_lt_G 0)
  L_eq := by rw [mul_add, mul_one, ← Λ.L_eq, Br.Om1_eq]
  g_cl := fun Z y hZ hZ1 hy hLy hy2 => Λ.g_cl Z y hZ hZ1 hy (le_self_add.trans hLy) hy2
  L_mem := fun S a b ha hb => CSet.add_mem (Λ.L_mem S a b ha hb)
    (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))
  l_ge := fun x => (Λ.l_ge x).trans le_self_add
  l_lt := fun x hx hx1 => (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (Λ.l_lt x hx hx1) (lgG_facts hx hx1).2.1
  l_lt2 := fun x hx hx1 hg => (hl_sq_indec hx).add_lt (Λ.l_lt2 x hx hx1 hg) (hl_lt_sq hx)
  l_pi := fun σ ρ hB hg => by
    obtain ⟨l1, l2⟩ := Λ.l_pi σ ρ hB hg
    obtain ⟨r1, r2⟩ := pi_base hB
    obtain ⟨u1, u2⟩ := pi_add hB l1 r1
    rw [l2, r2] at u2
    exact ⟨u1, u2⟩

theorem succ_L : Λ.succ.L = Λ.L + Om1 := rfl

theorem succ_l (x : Ordinal.{0}) : Λ.succ.l x = Λ.l x + x := rfl

theorem succ_g : Λ.succ.g = Λ.g := rfl

theorem gq_lt : Λ.q < Om 1 := by have := Λ.q_lt; rwa [Br.Om1_eq] at this

/-- **`L + ν < Ω₁²`** for `ν < Ω₁`. -/
theorem L_add_lt {ν : Ordinal.{0}} (hν : ν < Om 1) : Λ.L + ν < Om 1 * Om 1 := by
  rw [Λ.L_eq]
  calc Om 1 * Λ.q + ν < Om 1 * Λ.q + Om 1 := (add_lt_add_iff_left _).2 hν
  _ = Om 1 * (Λ.q + 1) := by rw [mul_add_one]
  _ ≤ Om 1 * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt Λ.gq_lt) _

end HlLv

/-! ## The level gate at `L + ν` -/

theorem hlv_L1 (Λ : HlLv) (ν : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ Λ.L + ν :=
  (hg_one_lt_Om1.le.trans Λ.OL).trans le_self_add

theorem hlv_L0 (Λ : HlLv) (ν : Ordinal.{0}) : Λ.L + ν ≠ 0 := (zero_lt_one.trans_le (hlv_L1 Λ ν)).ne'

theorem hlv_ωL (Λ : HlLv) (ν : Ordinal.{0}) : ω < Λ.L + ν :=
  ((omega0_lt_inE gl_Om1_E).trans_le Λ.OL).trans_le le_self_add

/-- **THE LEVEL GATE**: a code over a strongly critical `Z ≤ Ω₁` in `[φ(L+ν, j), φ(L+ν, j+1))` (`ν < Ω₁`, `j` not a
fixed point, `G < φ(L+ν, j)`) has `ν < Z`. -/
theorem hlv_cl_gate (Λ : HlLv) {ν : Ordinal.{0}} (hν : ν < Om1) {Z j : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : j < veblen (Λ.L + ν) j) (hGQ : gcG 0 < veblen (Λ.L + ν) j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen (Λ.L + ν) j ≤ y) (hyZ : y < veblen (Λ.L + ν) (j + 1)) : ν < Z := by
  have h := hi_cl_lvl (hlv_L1 Λ ν) hZ1 hj hGQ hy hQy hyZ
  obtain ⟨q, r, he, hr⟩ := hj_cl_mod hZ hZ1 h
  rw [Λ.L_eq] at he
  rw [Br.Om1_eq] at hν
  rw [← hj_mod_eq (hr.trans_le hZ1) hν he.symm]
  exact hr

/-- **THE LEVEL GATE `g` OF THE DATUM**: a code over a strongly critical `Z ≤ Ω₁` in `[φ(L+ν, j), φ(L+ν, j+1))`
(`ν < Ω₁`, `j` not a fixed point, `G < φ(L+ν, j)`) has `g < Z`. -/
theorem hlv_cl_g (Λ : HlLv) {ν : Ordinal.{0}} (hν : ν < Om1) {Z j : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : j < veblen (Λ.L + ν) j) (hGQ : gcG 0 < veblen (Λ.L + ν) j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen (Λ.L + ν) j ≤ y) (hyZ : y < veblen (Λ.L + ν) (j + 1)) : Λ.g < Z := by
  have h := hi_cl_lvl (hlv_L1 Λ ν) hZ1 hj hGQ hy hQy hyZ
  rw [Br.Om1_eq] at hν
  exact Λ.g_cl Z _ hZ hZ1 h le_self_add (Λ.L_add_lt hν)

theorem hlv_L_mem (Λ : HlLv) (S : InaccSeq.{0}) {ν a b : Ordinal.{0}} (ha : 0 < a) (hg : Λ.g < b)
    (hνb : ν < b) : Λ.L + ν ∈ S.CSet a b :=
  CSet.add_mem (Λ.L_mem S a b ha hg) (CSet.of_lt hνb)

theorem hlv_fixk (Λ : HlLv) {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) (k : ℕ) :
    veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (hlv_ωL Λ ν)) a

theorem hlv_Lω (Λ : HlLv) {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (hlv_ωL Λ ν) a

/-! ## The readings at the level `ℓ(x) + ν` -/

section Base

variable (Λ : HlLv) {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hlv_ωl : ω < Λ.l x + ν := ((omega0_lt_inE hx).trans_le (Λ.l_ge x)).trans_le le_self_add

theorem hlv_xl : x ≤ Λ.l x + ν := (Λ.l_ge x).trans le_self_add

theorem hlv_rfixk {v : Ordinal.{0}} (hv : LuP (Λ.l x + ν) v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (hlv_ωl Λ hx hx1)) a

theorem hlv_rfixω {v : Ordinal.{0}} (hv : LuP (Λ.l x + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (hlv_ωl Λ hx hx1) a

variable (hνx : ν < x)
include hνx

theorem hlv_G : Λ.l x + ν < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (Λ.l_lt x hx hx1) (hνx.trans (lgG_facts hx hx1).2.1)

theorem hlv_G1 : Λ.l x + ν + 1 < lgG x :=
  (ev_isSuccLimit_of_inE (lgG_facts hx hx1).2.2.2.1).add_one_lt (hlv_G Λ hx hx1 hνx)

theorem hlv_q : Λ.l x + ν < gq 1 x := (hlv_G Λ hx hx1 hνx).trans (mg_lgG_lt_G1 hx hx1)

theorem hlv_T : Λ.l x + ν ∈ Tset x ∧ Λ.l x + ν < Om1 := gm1_T hx hx1 (hlv_q Λ hx hx1 hνx)

theorem hlv_one : (1 : Ordinal.{0}) ≤ Λ.l x + ν := (hi_one_le hx hx1).trans (hlv_xl Λ hx hx1)

theorem hlv_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP (Λ.l x + ν) (glA (Λ.l x + ν) t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hlv_T Λ hx hx1 hνx
  exact glA_P hx hx1 (hlv_one Λ hx hx1 hνx) hT h1 htT ht1

theorem hlv_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    Λ.l x + ν < glA (Λ.l x + ν) t x ∧ glA (Λ.l x + ν) t x < Om1 ∧ t < glA (Λ.l x + ν) t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hlv_T Λ hx hx1 hνx
  obtain ⟨-, -, ha1, -, hβa, hta⟩ := glA_facts hx hx1 (hlv_one Λ hx hx1 hνx) hT h1 htT ht1
  exact ⟨hβa, ha1, hta⟩

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + t + 1) = hdNx (ℓ(x)+ν) (ϑˣ(Ω₁·(ℓ(x)+ν) + t))`.** -/
theorem hlv_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) :
    glA (Λ.l x + ν) (t + 1) x = hdNx (Λ.l x + ν) (glA (Λ.l x + ν) t x) := by
  obtain ⟨i, hi⟩ := hlv_glA_P Λ hx hx1 hνx ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 (hlv_one Λ hx hx1 hνx) (hlv_q Λ hx hx1 hνx) ht hi.symm, ← hdNx_veb, hi]

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + P) = hdNx (ℓ(x)+ν) P`** at a fixed point `P ∈ (ℓ(x)+ν, Γ_{x+2})` of `φ(ℓ(x)+ν, ·)`. -/
theorem hlv_glA_fixP {P : Ordinal.{0}} (hP : veblen (Λ.l x + ν) P = P) (hxP : Λ.l x + ν < P) (hPq : P < gq 1 x) :
    glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P := by
  rw [hdNx_fixP hP]
  exact hc_glA_fixG hx hx1 (hlv_one Λ hx hx1 hνx) (hlv_q Λ hx hx1 hνx) hP hxP ((hlv_xl Λ hx hx1).trans_lt hxP) hPq

/-- **THE CLOSED FORM BELOW `N_{ℓ(x)+ν}(P)`**. -/
theorem hlv_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (Λ.l x + ν) P < gq 1 x) (hi0 : veblen (Λ.l x + ν) i0 = hdNx (Λ.l x + ν) P)
    (hr : r < hcN (Λ.l x + ν) P) : glA (Λ.l x + ν) (P + r) x = veblen (Λ.l x + ν) (i0 + r) := by
  have hNE := hcN_E (Λ.l x + ν) P
  have hSN : hdNx (Λ.l x + ν) P < hcN (Λ.l x + ν) P := hdNx_lt_N (hcN_gt (Λ.l x + ν) P)
  have hi0H : i0 < hcN (Λ.l x + ν) P := (right_le_veblen (Λ.l x + ν) i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcN (Λ.l x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen (Λ.l x + ν) (i0 + r) < hcN (Λ.l x + ν) P := by
    have := (isNormal_veblen (Λ.l x + ν)).strictMono hir; rwa [hcN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen (Λ.l x + ν) i0 := by rw [hi0]; exact hdNx_gt (Λ.l x + ν) P
  exact hc_glAV hx hx1 (hlv_one Λ hx hx1 hνx) (hlv_q Λ hx hx1 hνx) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixG hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + P + r) < N_{ℓ(x)+ν}(P)`** for `r < N_{ℓ(x)+ν}(P)`. -/
theorem hlv_glA_lt {P r : Ordinal.{0}} (hP0 : glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (Λ.l x + ν) P < gq 1 x) (hr : r < hcN (Λ.l x + ν) P) :
    glA (Λ.l x + ν) (P + r) x < hcN (Λ.l x + ν) P := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (Λ.l x + ν) P
  rw [hlv_lvglAV Λ hx hx1 hνx hP0 hPq hNq hi0 hr]
  have hNE := hcN_E (Λ.l x + ν) P
  have hi0H : i0 < hcN (Λ.l x + ν) P :=
    (right_le_veblen (Λ.l x + ν) i0).trans_lt (by rw [hi0]; exact hdNx_lt_N (hcN_gt (Λ.l x + ν) P))
  have hir : i0 + r < hcN (Λ.l x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen (Λ.l x + ν)).strictMono hir; rwa [hcN_fix] at this

/-- **`N_{ℓ(x)+ν}(P) = ϑˣ(Ω₁·(ℓ(x)+ν+1) + P)`** at a fixed point `P ∈ (ℓ(x)+ν, Γ_{x+2})` of `φ(ℓ(x)+ν+1, ·)`. -/
theorem hlv_N_glA {P : Ordinal.{0}} (hP : veblen (Λ.l x + ν + 1) P = P) (hxP : Λ.l x + ν + 1 < P)
    (hPq : P < gq 1 x) : hcN (Λ.l x + ν) P = glA (Λ.l x + ν + 1) P x := by
  have hq1 : Λ.l x + ν + 1 < gq 1 x :=
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hlv_q Λ hx hx1 hνx)
  have e : hcN (Λ.l x + ν) P = veblen (Λ.l x + ν + 1) (P + 1) := by
    have := hcN_veb (Λ.l x + ν) P; rwa [hP] at this
  rw [e, hc_glA_fixG hx hx1 ((hlv_one Λ hx hx1 hνx).trans le_self_add) hq1 hP hxP
    (((hlv_xl Λ hx hx1).trans le_self_add).trans_lt hxP) hPq]

end Base

/-- **Lemma EXACT for `ϑᵖ(Ω₁·(ℓ(ρ)+ν) + t)`**: `π(ϑᵖ(Ω₁·(ℓ(ρ)+ν) + t)) = ϑ^σ(Ω₁·(ℓ(σ)+ν) + π(t))` (`ν < σ`). -/
theorem hlv_glA_pi (Λ : HlLv) {ν σ ρ t : Ordinal.{0}} (hB : Bases σ ρ) (hg : Λ.g < σ) (hνσ : ν < σ) (ht : t ∈ TB ρ σ)
    (htq : t < gq 1 ρ) :
    glA (Λ.l ρ + ν) t ρ ∈ TB ρ σ ∧ pi σ ρ (glA (Λ.l ρ + ν) t ρ) = glA (Λ.l σ + ν) (pi σ ρ t) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨r1, r2⟩ := Λ.l_pi σ ρ hB hg
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h := glA_pi hB u1 (hlv_T Λ hB.2.1 hρ1 (hνσ.trans hB.2.2.1)).2 ht (gm1_T hB.2.1 hρ1 htq).2
  rw [u2] at h
  exact h

/-- **Lemma EXACT for `ℓ(ρ) + ν + 1`**. -/
theorem hlv_lev1_pi (Λ : HlLv) {ν σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hg : Λ.g < σ) (hνσ : ν < σ) :
    Λ.l ρ + ν + 1 ∈ TB ρ σ ∧ pi σ ρ (Λ.l ρ + ν + 1) = Λ.l σ + ν + 1 := by
  obtain ⟨r1, r2⟩ := Λ.l_pi σ ρ hB hg
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h1σ : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  obtain ⟨w1, w2⟩ := pi_add hB u1 (mem_TB_of_lt hB h1σ)
  rw [u2, pi_lt hB h1σ] at w2
  exact ⟨w1, w2⟩

end Googology.Trans.PoR.InaccPsi.R2.Hl
