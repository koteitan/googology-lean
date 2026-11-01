import Googology.Trans.PoR.InaccPsi.R2.HeG1

/-!
# XkBase: the base atom `Γ_{x+1+c}` of the layer `c` and the readings below `Γ_{x+2+c}`, for every index `c`

Region (B-lo) splits into layers `c ≥ 1` (`Xh.XhLay`); the layer `c` is region (A) again over the base atom
`Γ(c) = Γ_{Ω₁+1+c}`, read `gq c x = ϑˣ(Ω₁·Ω₁ + c) = Γ_{x+1+c}`, with readings below `gq (c+1) x`.  The facts of the
base `G` (`c = 0`) used by the region-(A) development are `Gm.gm1_T`, `Hc.hc_G_fix`, `He.he_G_sc`, `He.he_rep`,
`He.he_noSC`; here they are proved ONCE for every index `c ∈ Tˣ ∩ Ω₁` (in particular for every constant `c < x`):

* `xkT` (**every ordinal below `gq c x` lies in `Tˣ ∩ Ω₁`**; `c = 1` is `Gm.gm1_T`);
* `xkA_lt` (**`ϑˣ(Ω₁·β + t) < gq c x` for `β, t < gq c x`**), `xk_fix` (**`φ(β, gq c x) = gq c x` for
  `1 ≤ β < gq c x`**; `c = 0` is `Hc.hc_G_fix`), `xk_sc` (**`gq c x` is strongly critical**; `c = 0` is
  `He.he_G_sc`: `xk_sc_zero`);
* `xk_rep_all` (**every `ε`-number `v ∈ (x, gq (c+1) x)` with `c < v` is a base atom `gq c' x`, `c' ≤ c`, or
  `ϑˣ(Ω₁·q + r)` with `1 ≤ q`, `q, r ∈ Tˣ ∩ Ω₁`**), `xk_rep` (the open interval `(gq c x, gq (c+1) x)`; `c = 0` is
  `He.he_rep` above `Γ_{x+1}`);
* `xk_noSC` (**no strongly critical number in `(gq c x, gq (c+1) x)`**; `c = 0` is `He.he_noSC`), `xk_sc_iff` (**the
  strongly critical numbers `v ∈ (x, gq (c+1) x)` with `c < v` are exactly the base atoms `gq c' x`, `c' ≤ c`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xk

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.He
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Every ordinal below `gq c x` lies in `Tˣ ∩ Ω₁`** (`c ∈ Tˣ ∩ Ω₁`). -/
theorem xkT {c v : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hv : v < gq c x) : v ∈ Tset x ∧ v < Om1 := by
  obtain ⟨h1, -, h3, -, -⟩ := geq_facts hx hx1 hcT hc1
  exact ⟨vz_T_down hx hx1 h1 h3 hv.le, hv.trans h3⟩

/-- **`ϑˣ(Ω₁·β + t) < gq c x`** for `β, t < gq c x`. -/
theorem xkA_lt {c β t : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hβ : β < gq c x) (ht : t < gq c x) :
    glA β t x < gq c x := by
  obtain ⟨hβT, hβ1⟩ := xkT hx hx1 hcT hc1 hβ
  obtain ⟨htT, ht1⟩ := xkT hx hx1 hcT hc1 ht
  exact lgVt_lt_low hx hx1 hβT hβ1 htT ht1 hcT hc1 hβ ht

/-- **`φ(β, gq c x) = gq c x`** for every `1 ≤ β < gq c x`. -/
theorem xk_fix {c β : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hβ1 : 1 ≤ β) (hβ : β < gq c x) :
    veblen β (gq c x) = gq c x := by
  obtain ⟨hβT, hβΩ⟩ := xkT hx hx1 hcT hc1 hβ
  obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hcT hc1
  refine le_antisymm (((isNormal_veblen β).le_iff_forall_le (ev_isSuccLimit_of_inE hGE)).2 fun j hj => ?_)
    (right_le_veblen _ _)
  obtain ⟨hjT, hj1⟩ := xkT hx hx1 hcT hc1 hj
  exact ((glA_veb_le hx hx1 hβ1 hβT hβΩ hjT hj1).trans_lt (xkA_lt hx hx1 hcT hc1 hβ hj)).le

/-- **`gq c x` is strongly critical**: `φ(gq c x, 0) = gq c x`. -/
theorem xk_sc {c : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) : veblen (gq c x) 0 = gq c x := by
  obtain ⟨-, hxG, -, hGE, -⟩ := geq_facts hx hx1 hcT hc1
  have hG0 : gq c x ≠ 0 := (hx.pos.trans hxG).ne'
  have hmem : gq c x ∈ range (veblen (gq c x)) := by
    refine (mem_range_veblen hG0).2 (fun b hb => ?_)
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [veblen_zero_apply]; exact hGE
    · exact xk_fix hx hx1 hcT hc1 (one_le_iff_ne_zero.2 hb0) hb
  obtain ⟨a, ha⟩ := hmem
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ha
  · exfalso
    have h1 := (isNormal_veblen (gq c x)).strictMono (pos_iff_ne_zero.2 ha0)
    rw [ha] at h1
    exact absurd ((left_le_veblen (gq c x) 0).trans_lt h1) (lt_irrefl _)

/-- **The instance `c = 0` is `He.he_G_sc`.** -/
theorem xk_sc_zero : veblen (lgG x) 0 = lgG x := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  rw [mg_gq0 hx hx1]
  exact xk_sc hx hx1 h0T (hx.pos.trans hx1)

theorem xk_sc_zero_eq : xk_sc_zero hx hx1 = he_G_sc hx hx1 := rfl

/-- **EVERY `ε`-NUMBER `v ∈ (x, gq (c+1) x)` WITH `c < v` IS A BASE ATOM `gq c' x` (`c' ≤ c`) OR `ϑˣ(Ω₁·q + r)`**
with `1 ≤ q`, `q, r ∈ Tˣ ∩ Ω₁`. -/
theorem xk_rep_all {c v : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hvE : InE v) (hxv : x < v)
    (hcv : c < v) (hv : v < gq (c + 1) x) :
    (∃ c', c' ≤ c ∧ gq c' x = v) ∨
      ∃ q r, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ r ∈ Tset x ∧ r < Om1 ∧ glA q r x = v := by
  have hc1' : c + 1 < Om1 := gl_Om1_lim.add_one_lt hc1
  have h1x : (1 : Ordinal.{0}) < x := lu_one_lt_E hx
  have hc1T : c + 1 ∈ Tset x := by
    obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hcT hc1
    exact vz_T_down hx hx1 hGT hG1 (Order.add_one_le_of_lt (gmq_gt hx hx1 hcT hc1))
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hc1T hc1'
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE⟩
  have hcv' : c + 1 < v := (ev_isSuccLimit_of_inE hvE).add_one_lt hcv
  have hξk : ξ < Om1 * Om1 + (c + 1) :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hc1T hc1' (by rw [hξv]; exact hcv') (by rw [hξv]; exact hv)
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · right
    obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    refine ⟨ξ / Om1, ξ % Om1, hq1, hqT, hqΩ, hrT, hr1, ?_⟩
    show vt x (Om1 * (ξ / Om1) + ξ % Om1) = v
    rw [hdec, hξv]
  · left
    obtain ⟨c', hc'⟩ : ∃ c', ξ = Om1 * Om1 + c' := ⟨ξ - Om1 * Om1, (Ordinal.add_sub_cancel_of_le hξs).symm⟩
    have hc'c : c' < c + 1 := by rw [hc'] at hξk; exact (add_lt_add_iff_left _).1 hξk
    refine ⟨c', Order.lt_add_one_iff.1 hc'c, ?_⟩
    show vt x (Om1 * Om1 + c') = v
    rw [← hc', hξv]

/-- **EVERY `ε`-NUMBER `v ∈ (gq c x, gq (c+1) x)` IS `ϑˣ(Ω₁·q + r)`** with `1 ≤ q`, `q, r ∈ Tˣ ∩ Ω₁`. -/
theorem xk_rep {c v : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hvE : InE v) (hGv : gq c x < v)
    (hv : v < gq (c + 1) x) :
    ∃ q r, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ r ∈ Tset x ∧ r < Om1 ∧ glA q r x = v := by
  obtain ⟨-, hxG, -, -, -⟩ := geq_facts hx hx1 hcT hc1
  rcases xk_rep_all hx hx1 hcT hc1 hvE (hxG.trans hGv) ((gmq_gt hx hx1 hcT hc1).trans hGv) hv with
    ⟨c', hc'c, he⟩ | h
  · exfalso
    have := gmq_mono hx hx1 hcT hc1 hc'c
    rw [he] at this
    exact absurd hGv (not_lt.2 this)
  · exact h

/-- **NO STRONGLY CRITICAL NUMBER IN `(gq c x, gq (c+1) x)`**: `φ(v, 0) > v` there (`v` an `ε`-number). -/
theorem xk_noSC {c v : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hvE : InE v) (hGv : gq c x < v)
    (hv : v < gq (c + 1) x) : v < veblen v 0 := by
  obtain ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hev⟩ := xk_rep hx hx1 hcT hc1 hvE hGv hv
  obtain ⟨-, -, -, -, hqv, -⟩ := glA_facts hx hx1 hq1 hqT hqΩ hrT hr1
  rw [hev] at hqv
  rcases (left_le_veblen v 0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hq1v : q + 1 < v := (ev_isSuccLimit_of_inE hvE).add_one_lt hqv
    have hP : LuP (q + 1) v := by
      refine ⟨veblen v 0, ?_⟩
      rw [veblen_veblen_of_lt hq1v, ← h]
    have hn := glA_notP hx hx1 hq1 hqT hqΩ hrT hr1
    rw [hev] at hn
    exact hn hP

/-- **THE STRONGLY CRITICAL NUMBERS `v ∈ (x, gq (c+1) x)` WITH `c < v` ARE EXACTLY THE BASE ATOMS `gq c' x`,
`c' ≤ c`.** -/
theorem xk_sc_iff {c v : Ordinal.{0}} (hcT : c ∈ Tset x) (hc1 : c < Om1) (hxv : x < v) (hcv : c < v)
    (hv : v < gq (c + 1) x) : veblen v 0 = v ↔ ∃ c', c' ≤ c ∧ gq c' x = v := by
  constructor
  · intro hsc
    have hvE : InE v := by
      have h := veblen_veblen_of_lt (o₁ := 0) (o₂ := v) (hx.pos.trans hxv) 0
      rw [veblen_zero_apply, hsc] at h
      exact h
    rcases xk_rep_all hx hx1 hcT hc1 hvE hxv hcv hv with h | ⟨q, r, hq1, hqT, hqΩ, hrT, hr1, hev⟩
    · exact h
    · exfalso
      obtain ⟨-, -, -, -, hqv, -⟩ := glA_facts hx hx1 hq1 hqT hqΩ hrT hr1
      rw [hev] at hqv
      have hq1v : q + 1 < v := (ev_isSuccLimit_of_inE hvE).add_one_lt hqv
      have hP : LuP (q + 1) v := ⟨veblen v 0, by rw [veblen_veblen_of_lt hq1v, hsc]⟩
      have hn := glA_notP hx hx1 hq1 hqT hqΩ hrT hr1
      rw [hev] at hn
      exact hn hP
  · rintro ⟨c', hc'c, rfl⟩
    have hc'T : c' ∈ Tset x := vz_T_down hx hx1 hcT hc1 hc'c
    exact xk_sc hx hx1 hc'T (hc'c.trans_lt hc1)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Xk
