import Googology.Trans.PoR.InaccPsi.R2.LtNTh

/-!
# The nested terms `ϑˣ(Ω₁·ω + t)`: values below `c_K(x)`

`LnW`: an embedded term `lz a` of `R2.LzW` (values below `y_ω(x)`), `tw t` (value `ϑˣ(Ω₁·ω + t(x))`, `t` a term of
`LnW`), `th n t` (value `ϑˣ(Ω₁·n + t(x))`), a sum, a power; `dp t` is the nesting depth of `tw`.  For a base
`x ∈ E ∩ Ω₁` (`c_0 = y_ω`, `c_{K+1} = ϑˣ(Ω₁·ω + c_K)`, `R2.LtNTh`):

* `ln_T`, `ltC_th_lt`, `ln_lt_top` (**every value of a term of depth `≤ K` is below `c_K(x)`**), `ltC_lt_next`,
  `ln_lt_ups`, `ln_zero`;
* `ln_pi` (**Lemma EXACT**), `ln_uni_le`, `ln_uni_lt`, `ln_uni_eq`; `LnWC`, `lnWC_const`, `lnWC_ge`, `ln_small`;
* `lnCt K` (the term `tw(⋯tw(ω)⋯)` with value `c_K(x)`, depth `K + 1`), `lnCt_val`;
* `ln_th_form` (**an `ε`-number `v ∈ (c_K(ρ), c_{K+1}(ρ))` is `ϑᵖ(Ω₁·q + r)` (`r < v`) or `ϑᵖ(Ω₁·ω + j)` with
  `j < c_K(ρ)`**), `ltC_locate`, `ln_rep` (**representation below `c_K(ρ)` by terms of depth `≤ K`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lz

/-- **The nested terms `ϑˣ(Ω₁·ω + t)`.** -/
inductive LnW : Type 1
  | lz : LzW → LnW
  | tw : LnW → LnW
  | th : ℕ → LnW → LnW
  | sm : LnW → LnW → LnW
  | pw : LnW → LnW

namespace LnW

/-- The value at the base `x`. -/
noncomputable def val : LnW → Ordinal.{0} → Ordinal.{0}
  | lz a, x => LzW.val a x
  | tw t, x => vt x (Om1 * ω + val t x)
  | th n t, x => vt x (Om1 * (n : Ordinal.{0}) + val t x)
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`, all finite levels `≥ 1`. -/
def CBt : LnW → Ordinal.{0} → Prop
  | lz a, s => LzW.CBt a s
  | tw t, s => CBt t s
  | th n t, s => 1 ≤ n ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LnW → List Ordinal.{0}
  | lz a => LzW.cs a
  | tw t => cs t
  | th _ t => cs t
  | sm a b => cs a ++ cs b
  | pw a => cs a

/-- The nesting depth of `tw`. -/
def dp : LnW → ℕ
  | lz _ => 0
  | tw t => dp t + 1
  | th _ t => dp t
  | sm a b => max (dp a) (dp b)
  | pw a => dp a

@[simp] theorem val_lz (a : LzW) (x : Ordinal.{0}) : val (lz a) x = LzW.val a x := rfl
@[simp] theorem val_tw (t : LnW) (x : Ordinal.{0}) : val (tw t) x = vt x (Om1 * ω + val t x) := rfl
@[simp] theorem val_th (n : ℕ) (t : LnW) (x : Ordinal.{0}) :
    val (th n t) x = vt x (Om1 * (n : Ordinal.{0}) + val t x) := rfl
@[simp] theorem val_sm (a b : LnW) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LnW) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LnW) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | lz a, s, s', h, h' => LzW.cbt_iff a s s' h h'
  | tw t, s, s', h, h' => cbt_iff t s s' h h'
  | th _ t, s, s', h, h' => ⟨h.1, cbt_iff t s s' h.2 h'⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LnW) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | lz a, s, h, c, hc => LzW.cbt_cst a s h c hc
  | tw t, s, h, c, hc => cbt_cst t s h c hc
  | th _ t, s, h, c, hc => cbt_cst t s h.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LnW} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LnW

open LnW

/-- The term `tw(⋯tw(ω)⋯)` with value `c_K`. -/
noncomputable def lnCt : ℕ → LnW
  | 0 => tw (lz (LzW.vz (VzTm.cst ω)))
  | K + 1 => tw (lnCt K)

theorem lnCt_dp : ∀ K : ℕ, dp (lnCt K) = K + 1
  | 0 => rfl
  | K + 1 => by simp only [lnCt, dp, lnCt_dp K]

theorem lnCt_cs : ∀ K : ℕ, cs (lnCt K) = [ω]
  | 0 => rfl
  | K + 1 => by simp only [lnCt, cs, lnCt_cs K]

theorem lnCt_cbt {x : Ordinal.{0}} (hx : (ω : Ordinal.{0}) < x) : ∀ K : ℕ, CBt (lnCt K) x
  | 0 => hx
  | K + 1 => lnCt_cbt hx K

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lnCt_val : ∀ K : ℕ, val (lnCt K) x = ltC x K
  | 0 => (ltYw_eq hx hx1).symm
  | K + 1 => by
    show vt x (Om1 * ω + val (lnCt K) x) = vt x (Om1 * ω + ltC x K)
    rw [lnCt_val K]

/-- **`t(x) ∈ Tˣ ∩ Ω₁`.** -/
theorem ln_T : ∀ t : LnW, CBt t x → val t x ∈ Tset x ∧ val t x < Om1
  | lz a, h => lzw_T hx hx1 a h
  | tw t, h => by
    obtain ⟨h1, h2⟩ := ln_T t h
    obtain ⟨hvT, -, hv1, -, -⟩ := lt_w_facts hx hx1 h1 h2
    exact ⟨hvT, hv1⟩
  | th n t, h => by
    obtain ⟨h1, h2⟩ := ln_T t h.2
    obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 h.1 h1 h2
    exact ⟨hvT, hv1⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := ln_T a h.1
    obtain ⟨h3, h4⟩ := ln_T b h.2
    exact ⟨vzT_add hx hx1 h1 h3, Om1_add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := ln_T t h
    obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
    have hw : ω ^ val t x < m := hmE.opow_lt ((hTm _ h2).1 h1)
    exact ⟨(hTm _ (hw.trans hm1)).2 hw, hw.trans hm1⟩

/-- `ϑˣ(Ω₁·n + v) < c_K(x)` for `v ∈ Tˣ`, `v < c_K(x)`. -/
theorem ltC_th_lt (n : ℕ) {K : ℕ} {v : Ordinal.{0}} (hvT : v ∈ Tset x) (hv1 : v < Om1) (hv : v < ltC x K) :
    vt x (Om1 * (n : Ordinal.{0}) + v) < ltC x K := by
  rcases K with _ | K
  · obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hv
    exact (lzY_th_lt hx hx1 n hvT hk).trans (lzY_lt_w hx hx1 k)
  · obtain ⟨hcT, hc1, -, -⟩ := ltC_facts hx hx1 K
    exact lzVt_lt_w hx hx1 hvT hv1 hcT hc1 hv

/-- **Every value of a term of depth `≤ K` is below `c_K(x)`.** -/
theorem ln_lt_top : ∀ (t : LnW) {K : ℕ}, CBt t x → dp t ≤ K → val t x < ltC x K
  | lz a, K, h, _ => (lzw_lt_top hx hx1 (K := LzW.lv a) a h le_rfl).trans
      ((lzY_lt_w hx hx1 _).trans_le (ltC_mono hx hx1 (Nat.zero_le K)))
  | tw t, K, h, hl => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by simp only [dp] at hl; omega⟩
    have ht := ln_lt_top t (K := K') h (by simp only [dp] at hl; omega)
    obtain ⟨hcT, hc1, -, -⟩ := ltC_facts hx hx1 K'
    exact lzVt_lt_ww hx hx1 (ln_T hx hx1 t h).1 hcT hc1 ht (ht.trans (ltC_step hx hx1 K').1)
  | th n t, K, h, hl => ltC_th_lt hx hx1 n (ln_T hx hx1 t h.2).1 (ln_T hx hx1 t h.2).2 (ln_lt_top t h.2 hl)
  | sm a b, K, h, hl => (inE_indec (ltC_facts hx hx1 K).2.2.2).add_lt
      (ln_lt_top a h.1 ((le_max_left _ _).trans hl)) (ln_lt_top b h.2 ((le_max_right _ _).trans hl))
  | pw a, K, h, hl => (ltC_facts hx hx1 K).2.2.2.opow_lt (ln_lt_top a h hl)

/-- `c_K(x)` lies below every `<₁ ∞`-point above `x`. -/
theorem ltC_lt_next (K : ℕ) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : ltC x K < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hyT, hy1, -, -⟩ := ltC_facts hx hx1 K
  exact ((hTm _ hy1).1 hyT).trans_le (hmin u hxu hu)

theorem ln_lt_ups {t : LnW} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  (ln_lt_top hx hx1 t (K := dp t) ht le_rfl).trans (ltC_lt_next hx hx1 _ hxu hu.2)

/-- **A value `0` is the value `0` everywhere.** -/
theorem ln_zero : ∀ t : LnW, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | lz a, h, h0 => lzw_zero hx hx1 a h h0
  | tw t, h, h0 => by
    obtain ⟨h1, h2⟩ := ln_T hx hx1 t h
    exact absurd h0 (lt_w_facts hx hx1 h1 h2).2.2.2.1.pos.ne'
  | th n t, h, h0 => by
    obtain ⟨h1, h2⟩ := ln_T hx hx1 t h.2
    exact absurd h0 (vz_th_facts hx hx1 h.1 h1 h2).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, ln_zero a h.1 this.1 y, ln_zero b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Facts

/-! ## Lemma EXACT and the comparison -/

/-- **Lemma EXACT for `LnW`.** -/
theorem ln_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LnW, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | lz a, h => lzw_pi hσ hρ hB a h
  | tw t, h => by
    have hρE := hB.2.1
    have hρ1 := hB.2.2.2
    obtain ⟨h1, h2⟩ := ln_pi hσ hρ hB t h
    obtain ⟨hO, hpO⟩ := xtOm1w_TB hB
    obtain ⟨h3, h4⟩ := pi_add hB hO h1
    rw [hpO, h2] at h4
    have ha1 : val t ρ < Om1 := (ln_T hρE hρ1 t (cbt_mono h hB.2.2.1.le)).2
    have hγ2 := lz_Om1w_add_lt ha1
    obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h3.1 hγ2
    simp only [val_tw]
    refine ⟨⟨hvT, by rw [hvP]; exact h3.2⟩, ?_⟩
    rw [pi_vt_two hB h3 hγ2, h4]
  | th n t, h => by
    obtain ⟨h1, h2⟩ := ln_pi hσ hρ hB t h.2
    have ht1 : val t ρ < Om1 := (ln_T hB.2.1 hB.2.2.2 t (cbt_mono h.2 hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := vz_pi_th hB h1 ht1 n
    simp only [val_th]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := ln_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := ln_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := ln_pi hσ hρ hB a h
    have hb := (ln_T hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem ln_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LnW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := ln_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := ln_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem ln_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LnW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, ln_uni_le hσ hρ hB hu ht]

theorem ln_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LnW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, ln_uni_le hσ hρ hB ht hu, ln_uni_le hσ hρ hB hu ht]

/-! ## Constant terms -/

/-- A term without the base, atoms and `ϑ`-terms. -/
def LnWC : LnW → Prop
  | lz a => LzWC a
  | tw _ => False
  | th _ _ => False
  | sm a b => LnWC a ∧ LnWC b
  | pw a => LnWC a

theorem lnWC_const : ∀ t : LnW, LnWC t → ∀ x y, val t x = val t y
  | lz a, h, x, y => lzWC_const a h x y
  | tw _, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, lnWC_const a h.1 x y, lnWC_const b h.2 x y]
  | pw a, h, x, y => by simp only [val_pw, lnWC_const a h x y]

theorem lnWC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LnW, CBt t x → ¬ LnWC t → x ≤ val t x
  | lz a, hc, h => lzWC_ge hx hx1 a hc h
  | tw t, hc, _ => by
    obtain ⟨h1, h2⟩ := ln_T hx hx1 t hc
    exact (lt_w_facts hx hx1 h1 h2).2.1.le
  | th n t, hc, _ => by
    obtain ⟨h1, h2⟩ := ln_T hx hx1 t hc.2
    exact (vz_th_facts hx hx1 hc.1 h1 h2).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [LnWC, not_and_or] at h
    rcases h with h | h
    · exact (lnWC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (lnWC_ge hx hx1 b hc.2 h).trans le_add_self
  | pw a, hc, h => (lnWC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem ln_small (t : LnW) :
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x) := by
  by_cases h : LnWC t
  · exact Or.inl (lnWC_const t h)
  · exact Or.inr fun x hx hx1 hc => lnWC_ge hx hx1 t hc h

/-! ## The representation -/

/-- **An `ε`-number `v ∈ (c_K(ρ), c_{K+1}(ρ))` is `ϑᵖ(Ω₁·q + r)` (`1 ≤ q < ω`, `r < v`) or `ϑᵖ(Ω₁·ω + j)` with
`j < c_K(ρ)`.** -/
theorem ln_th_form {ρ v : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {K : ℕ} (hvE : InE v)
    (hKv : ltC ρ K < v) (hv : v < ltC ρ (K + 1)) : (∃ q : ℕ, 1 ≤ q ∧ ∃ r, r ∈ Tset ρ ∧ r < Om1 ∧ r < v ∧
      vt ρ (Om1 * (q : Ordinal.{0}) + r) = v) ∨ ∃ j, j ∈ Tset ρ ∧ j < ltC ρ K ∧ vt ρ (Om1 * ω + j) = v := by
  obtain ⟨hKT, hK1, -, -⟩ := ltC_facts hρ hρ1 (K + 1)
  obtain ⟨hcT, hc1, hρc, -⟩ := ltC_facts hρ hρ1 K
  have hv1 : v < Om1 := hv.trans hK1
  have hvT : v ∈ Tset ρ := vz_T_down hρ hρ1 hKT hK1 hv.le
  have hρv : ρ < v := hρc.trans hKv
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv, by rw [hξv]; exact hvE⟩
  have hξlt : ξ < Om1 * ω + ltC ρ K :=
    lzLt_of_vt_lt_ww hρ hρ1 hξT hξ2 hcT hc1 (by rw [hξv]; exact hKv) (by rw [hξv]; exact hv)
  rcases lt_or_ge ξ (Om1 * ω) with hξw | hwξ
  · left
    obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hqw : q < ω := by
      have h1 : Om1 * q < Om1 * ω := lt_of_le_of_lt (hdec ▸ le_self_add) hξw
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    obtain ⟨q', hq'⟩ := lt_omega0.1 hqw
    have hq'1 : 1 ≤ q' := by
      rcases Nat.eq_zero_or_pos q' with h0 | h0
      · exfalso
        rw [h0, Nat.cast_zero] at hq'
        rw [hq', mul_zero, zero_add] at hdec
        exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
      · exact h0
    have hrT : r ∈ Tset ρ := vzRem_T hρ hρ1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1
    have e : Om1 * (q' : Ordinal.{0}) + r = ξ := by rw [← hq']; exact hdec
    have hrv : r < v := by
      have := (vz_th_facts hρ hρ1 hq'1 hrT hr1).2.2.2.2.2.2.2
      rwa [e, hξv] at this
    exact ⟨q', hq'1, r, hrT, hr1, hrv, by rw [e, hξv]⟩
  · right
    have hξe : Om1 * ω + (ξ - Om1 * ω) = ξ := Ordinal.add_sub_cancel_of_le hwξ
    have hjK : ξ - Om1 * ω < ltC ρ K := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    exact ⟨_, vz_T_down hρ hρ1 hcT hc1 hjK.le, hjK, by rw [hξe, hξv]⟩

/-- **Locating `v` between two bounds**: `c_0 ≤ v < c_K` gives `c_j ≤ v < c_{j+1}` for some `j < K`. -/
theorem ltC_locate {ρ v : Ordinal.{0}} : ∀ K : ℕ, ltC ρ 0 ≤ v → v < ltC ρ K →
    ∃ j, j < K ∧ ltC ρ j ≤ v ∧ v < ltC ρ (j + 1)
  | 0, h0, hK => absurd hK (not_lt.2 h0)
  | K + 1, h0, hK => by
    rcases lt_or_ge v (ltC ρ K) with h | h
    · obtain ⟨j, hj, h1, h2⟩ := ltC_locate K h0 h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨K, by omega, h, hK⟩

/-- **Representation below `c_K(ρ)`** by terms of depth `≤ K`. -/
theorem ln_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) :
    ∀ K : ℕ, ∀ v, v < ltC ρ K → ∃ t : LnW, CBt t ρ ∧ dp t ≤ K ∧ val t ρ = v := by
  intro K
  induction K with
  | zero =>
    intro v hv
    obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hv
    obtain ⟨a, ha, -, hav⟩ := lzw_rep hρ hρ1 v hk
    exact ⟨lz a, ha, le_rfl, hav⟩
  | succ K IHK =>
    intro v
    induction v using WellFoundedLT.induction with
    | ind v IH =>
    intro hv
    rcases lt_trichotomy v (ltC ρ K) with hvK | rfl | hKv
    · obtain ⟨t, ht, hl, htv⟩ := IHK v hvK
      exact ⟨t, ht, hl.trans (Nat.le_succ K), htv⟩
    · exact ⟨lnCt K, lnCt_cbt (omega0_lt_inE hρ) K, (lnCt_dp K).le, lnCt_val hρ hρ1 K⟩
    by_cases hvE : InE v
    · rcases ln_th_form hρ hρ1 hvE hKv hv with ⟨q, hq, r, -, -, hrv, he⟩ | ⟨j, -, hjK, he⟩
      · obtain ⟨t, ht, hl, htv⟩ := IH r hrv (hrv.trans hv)
        exact ⟨th q t, ⟨hq, ht⟩, hl, by rw [val_th, htv, he]⟩
      · obtain ⟨t, ht, hl, htv⟩ := IHK j hjK
        exact ⟨tw t, ht, by simp only [dp]; omega, by rw [val_tw, htv, he]⟩
    have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hKv).ne'
    obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
    rcases eq_or_ne v' 0 with h0' | h0'
    · rw [h0', zero_add] at hvs
      have hzv : lg v < v := by
        have hz : lg v ≤ ω ^ lg v := right_le_opow _ one_lt_omega0
        refine lt_of_le_of_ne (hz.trans_eq hvs.symm) fun e => hvE ?_
        show ω ^ v = v
        calc ω ^ v = ω ^ lg v := by rw [e]
          _ = v := hvs.symm
      obtain ⟨t, ht, hl, htv⟩ := IH _ hzv (hzv.trans hv)
      exact ⟨pw t, ht, hl, by rw [val_pw, htv, ← hvs]⟩
    · have hwv' : ω ^ lg v < v := by
        have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
        calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
          _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
          _ = v := hvs.symm
      obtain ⟨t1, ht1, hl1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
      obtain ⟨t2, ht2, hl2, hv2⟩ := IH _ hwv' (hwv'.trans hv)
      exact ⟨sm t1 t2, ⟨ht1, ht2⟩, max_le hl1 hl2, by rw [val_sm, hv1, hv2, ← hvs]⟩

end Googology.Trans.PoR.InaccPsi.R2.Lt
