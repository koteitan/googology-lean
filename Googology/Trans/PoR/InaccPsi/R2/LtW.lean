import Googology.Trans.PoR.InaccPsi.R2.LtTh

/-!
# The terms `ϑˣ(Ω₁·ω + a)` with `a` a term of `LzW`: values below `T_K(x) = ϑˣ(Ω₁·ω + y_K(x))`

`LtW`: an embedded term `lz a` of `R2.LzW` (values below `y_ω(x)`), `tw a` (value `ϑˣ(Ω₁·ω + a(x))`, `a` a term of
`LzW`), `th n t` (value `ϑˣ(Ω₁·n + t(x))`), a sum `sm a b`, a power `pw a`; `ltwLv t` is the largest level `lv a`
of an argument `a` of `tw` in `t`.  For a base `x ∈ E ∩ Ω₁` and `T_K(x) := ϑˣ(Ω₁·ω + y_K(x))` (`ltT`):

* `ltw_T`, `ltYw_lt_T` (`y_ω(x) < T_K(x)`), `ltT_facts`, `ltw_lt_top` (**every value of a term of level `≤ K` is
  below `T_K(x)`**: [W07a] Lemma 3.30 at `Ω₁·ω + y_K(x)`), `ltT_lt_next`, `ltw_lt_ups`, `ltw_zero`;
* `ltw_pi` (**Lemma EXACT**: `lzw_pi`, `xtOm1w_TB`, `pi_add`, `pi_vt_two`, `vz_pi_th`, `pi_opowZ`), `ltw_uni_le`,
  `ltw_uni_lt`, `ltw_uni_eq`;
* `LtWC`, `ltWC_const`, `ltWC_ge`, `ltw_small`;
* `ltw_th_form` (**an `ε`-number `v ∈ (y_ω(ρ), T_K(ρ))` is `ϑᵖ(Ω₁·q + r)` (`1 ≤ q < ω`, `r < v`) or
  `ϑᵖ(Ω₁·ω + j)` with `j < y_K(ρ)`**), `ltw_rep` (**representation below `T_K(ρ)` by terms of level `≤ K`**).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Lz

/-- The top `T_K(x) = ϑˣ(Ω₁·ω + y_K(x))`. -/
noncomputable def ltT (x : Ordinal.{0}) (K : ℕ) : Ordinal.{0} := vt x (Om1 * ω + lzY x K)

/-- **The terms `ϑˣ(Ω₁·ω + a)`** over the terms `a` of `LzW`. -/
inductive LtW : Type 1
  | lz : LzW → LtW
  | tw : LzW → LtW
  | th : ℕ → LtW → LtW
  | sm : LtW → LtW → LtW
  | pw : LtW → LtW

namespace LtW

/-- The value at the base `x`. -/
noncomputable def val : LtW → Ordinal.{0} → Ordinal.{0}
  | lz a, x => LzW.val a x
  | tw a, x => vt x (Om1 * ω + LzW.val a x)
  | th n t, x => vt x (Om1 * (n : Ordinal.{0}) + val t x)
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`, all finite levels `≥ 1`. -/
def CBt : LtW → Ordinal.{0} → Prop
  | lz a, s => LzW.CBt a s
  | tw a, s => LzW.CBt a s
  | th n t, s => 1 ≤ n ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LtW → List Ordinal.{0}
  | lz a => LzW.cs a
  | tw a => LzW.cs a
  | th _ t => cs t
  | sm a b => cs a ++ cs b
  | pw a => cs a

/-- The level: the largest level of an argument of `tw`. -/
def lw : LtW → ℕ
  | lz _ => 0
  | tw a => LzW.lv a
  | th _ t => lw t
  | sm a b => max (lw a) (lw b)
  | pw a => lw a

@[simp] theorem val_lz (a : LzW) (x : Ordinal.{0}) : val (lz a) x = LzW.val a x := rfl
@[simp] theorem val_tw (a : LzW) (x : Ordinal.{0}) : val (tw a) x = vt x (Om1 * ω + LzW.val a x) := rfl
@[simp] theorem val_th (n : ℕ) (t : LtW) (x : Ordinal.{0}) :
    val (th n t) x = vt x (Om1 * (n : Ordinal.{0}) + val t x) := rfl
@[simp] theorem val_sm (a b : LtW) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LtW) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LtW) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | lz a, s, s', h, h' => LzW.cbt_iff a s s' h h'
  | tw a, s, s', h, h' => LzW.cbt_iff a s s' h h'
  | th _ t, s, s', h, h' => ⟨h.1, cbt_iff t s s' h.2 h'⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LtW) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | lz a, s, h, c, hc => LzW.cbt_cst a s h c hc
  | tw a, s, h, c, hc => LzW.cbt_cst a s h c hc
  | th _ t, s, h, c, hc => cbt_cst t s h.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LtW} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LtW

open LtW

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`t(x) ∈ Tˣ ∩ Ω₁`.** -/
theorem ltw_T : ∀ t : LtW, CBt t x → val t x ∈ Tset x ∧ val t x < Om1
  | lz a, h => lzw_T hx hx1 a h
  | tw a, h => by
    obtain ⟨h1, h2⟩ := lzw_T hx hx1 a h
    obtain ⟨hvT, -, hv1, -, -⟩ := lt_w_facts hx hx1 h1 h2
    exact ⟨hvT, hv1⟩
  | th n t, h => by
    obtain ⟨h1, h2⟩ := ltw_T t h.2
    obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 h.1 h1 h2
    exact ⟨hvT, hv1⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := ltw_T a h.1
    obtain ⟨h3, h4⟩ := ltw_T b h.2
    exact ⟨vzT_add hx hx1 h1 h3, Om1_add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := ltw_T t h
    obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
    have hw : ω ^ val t x < m := hmE.opow_lt ((hTm _ h2).1 h1)
    exact ⟨(hTm _ (hw.trans hm1)).2 hw, hw.trans hm1⟩

theorem lzY_T (K : ℕ) : lzY x K ∈ Tset x ∧ lzY x K < Om1 :=
  ⟨(lzY_facts hx hx1 K).1, (lzY_facts hx hx1 K).2.2.1⟩

/-- The facts on the top `T_K(x)`. -/
theorem ltT_facts (K : ℕ) :
    ltT x K ∈ Tset x ∧ x < ltT x K ∧ ltT x K < Om1 ∧ InE (ltT x K) ∧ Indec (ltT x K) :=
  lt_w_facts hx hx1 (lzY_T hx hx1 K).1 (lzY_T hx hx1 K).2

/-- **`y_ω(x) < T_K(x)`.** -/
theorem ltYw_lt_T (K : ℕ) : lzYw x < ltT x K := by
  rw [ltYw_eq hx hx1]
  have hω := lt_omega_T hx hx1
  have hωK : (ω : Ordinal.{0}) < lzY x K := omega0_lt_inE (lzY_facts hx hx1 K).2.2.2.1
  exact lt_w_mono hx hx1 hω.1 (lzY_T hx hx1 K).1 (lzY_T hx hx1 K).2 (lzY_lt_w hx hx1 K) hωK

theorem ltT_strict {K K' : ℕ} (h : K < K') : ltT x K < ltT x K' :=
  lt_w_mono hx hx1 (lzY_T hx hx1 K).1 (lzY_T hx hx1 K').1 (lzY_T hx hx1 K').2 (lzY_lt_w hx hx1 K')
    (lzY_strict hx hx1 h)

theorem ltT_mono {K K' : ℕ} (h : K ≤ K') : ltT x K ≤ ltT x K' := by
  rcases h.lt_or_eq with h | rfl
  · exact (ltT_strict hx hx1 h).le
  · exact le_rfl

/-- **Every value of a term of level `≤ K` is below `T_K(x)`.** -/
theorem ltw_lt_top {K : ℕ} : ∀ t : LtW, CBt t x → lw t ≤ K → val t x < ltT x K
  | lz a, h, _ => (lzw_lt_top hx hx1 (K := LzW.lv a) a h le_rfl).trans
      ((lzY_lt_w hx hx1 _).trans (ltYw_lt_T hx hx1 K))
  | tw a, h, hl => lt_w_mono hx hx1 (lzw_T hx hx1 a h).1 (lzY_T hx hx1 K).1 (lzY_T hx hx1 K).2
      (lzY_lt_w hx hx1 K) (lzw_lt_top hx hx1 a h hl)
  | th _ t, h, hl => lzVt_lt_w hx hx1 (ltw_T hx hx1 t h.2).1 (ltw_T hx hx1 t h.2).2 (lzY_T hx hx1 K).1
      (lzY_T hx hx1 K).2 (ltw_lt_top t h.2 hl)
  | sm a b, h, hl => (inE_indec (ltT_facts hx hx1 K).2.2.2.1).add_lt
      (ltw_lt_top a h.1 ((le_max_left _ _).trans hl)) (ltw_lt_top b h.2 ((le_max_right _ _).trans hl))
  | pw a, h, hl => (ltT_facts hx hx1 K).2.2.2.1.opow_lt (ltw_lt_top a h hl)

/-- `T_K(x)` lies below every `<₁ ∞`-point above `x`. -/
theorem ltT_lt_next (K : ℕ) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : ltT x K < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hyT, -, hy1, -, -⟩ := ltT_facts hx hx1 K
  exact ((hTm _ hy1).1 hyT).trans_le (hmin u hxu hu)

theorem ltw_lt_ups {t : LtW} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  (ltw_lt_top hx hx1 (K := lw t) t ht le_rfl).trans (ltT_lt_next hx hx1 _ hxu hu.2)

/-- **A value `0` is the value `0` everywhere.** -/
theorem ltw_zero : ∀ t : LtW, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | lz a, h, h0 => lzw_zero hx hx1 a h h0
  | tw a, h, h0 => by
    obtain ⟨h1, h2⟩ := lzw_T hx hx1 a h
    exact absurd h0 (lt_w_facts hx hx1 h1 h2).2.2.2.1.pos.ne'
  | th n t, h, h0 => by
    obtain ⟨h1, h2⟩ := ltw_T hx hx1 t h.2
    exact absurd h0 (vz_th_facts hx hx1 h.1 h1 h2).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, ltw_zero a h.1 this.1 y, ltw_zero b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Facts

/-! ## Lemma EXACT and the comparison -/

/-- **Lemma EXACT for `ϑ(Ω₁·ω + a)`.** -/
theorem lt_tw_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {a : LzW}
    (h : LzW.CBt a σ) :
    vt ρ (Om1 * ω + LzW.val a ρ) ∈ TB ρ σ ∧ pi σ ρ (vt ρ (Om1 * ω + LzW.val a ρ)) =
      vt σ (Om1 * ω + LzW.val a σ) := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨h1, h2⟩ := lzw_pi hσ hρ hB a h
  obtain ⟨hO, hpO⟩ := xtOm1w_TB hB
  obtain ⟨h3, h4⟩ := pi_add hB hO h1
  rw [hpO, h2] at h4
  have ha1 : LzW.val a ρ < Om1 := (lzw_T hρE hρ1 a (LzW.cbt_mono h hB.2.2.1.le)).2
  have hγ2 := lz_Om1w_add_lt ha1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 h3.1 hγ2
  refine ⟨⟨hvT, by rw [hvP]; exact h3.2⟩, ?_⟩
  rw [pi_vt_two hB h3 hγ2, h4]

/-- **Lemma EXACT for `LtW`.** -/
theorem ltw_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LtW, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | lz a, h => lzw_pi hσ hρ hB a h
  | tw a, h => lt_tw_pi hσ hρ hB h
  | th n t, h => by
    obtain ⟨h1, h2⟩ := ltw_pi hσ hρ hB t h.2
    have ht1 : val t ρ < Om1 := (ltw_T hB.2.1 hB.2.2.2 t (cbt_mono h.2 hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := vz_pi_th hB h1 ht1 n
    simp only [val_th]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := ltw_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := ltw_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := ltw_pi hσ hρ hB a h
    have hb := (ltw_T hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem ltw_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LtW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := ltw_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := ltw_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem ltw_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LtW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, ltw_uni_le hσ hρ hB hu ht]

theorem ltw_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LtW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, ltw_uni_le hσ hρ hB ht hu, ltw_uni_le hσ hρ hB hu ht]

/-! ## Constant terms -/

/-- A term without the base, atoms and `ϑ`-terms. -/
def LtWC : LtW → Prop
  | lz a => LzWC a
  | tw _ => False
  | th _ _ => False
  | sm a b => LtWC a ∧ LtWC b
  | pw a => LtWC a

theorem ltWC_const : ∀ t : LtW, LtWC t → ∀ x y, val t x = val t y
  | lz a, h, x, y => lzWC_const a h x y
  | tw _, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, ltWC_const a h.1 x y, ltWC_const b h.2 x y]
  | pw a, h, x, y => by simp only [val_pw, ltWC_const a h x y]

theorem ltWC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LtW, CBt t x → ¬ LtWC t → x ≤ val t x
  | lz a, hc, h => lzWC_ge hx hx1 a hc h
  | tw a, hc, _ => by
    obtain ⟨h1, h2⟩ := lzw_T hx hx1 a hc
    exact (lt_w_facts hx hx1 h1 h2).2.1.le
  | th n t, hc, _ => by
    obtain ⟨h1, h2⟩ := ltw_T hx hx1 t hc.2
    exact (vz_th_facts hx hx1 hc.1 h1 h2).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [LtWC, not_and_or] at h
    rcases h with h | h
    · exact (ltWC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (ltWC_ge hx hx1 b hc.2 h).trans le_add_self
  | pw a, hc, h => (ltWC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem ltw_small (t : LtW) :
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x) := by
  by_cases h : LtWC t
  · exact Or.inl (ltWC_const t h)
  · exact Or.inr fun x hx hx1 hc => ltWC_ge hx hx1 t hc h

/-! ## The representation -/

/-- **An `ε`-number `v ∈ (y_ω(ρ), T_K(ρ))` is `ϑᵖ(Ω₁·q + r)` (`1 ≤ q < ω`, `r ∈ Tᵖ ∩ Ω₁`, `r < v`) or
`ϑᵖ(Ω₁·ω + j)` with `j < y_K(ρ)`.** -/
theorem ltw_th_form {ρ v : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {K : ℕ} (hvE : InE v)
    (hwv : lzYw ρ < v) (hv : v < ltT ρ K) : (∃ q : ℕ, 1 ≤ q ∧ ∃ r, r ∈ Tset ρ ∧ r < Om1 ∧ r < v ∧
      vt ρ (Om1 * (q : Ordinal.{0}) + r) = v) ∨ ∃ j, j ∈ Tset ρ ∧ j < lzY ρ K ∧ vt ρ (Om1 * ω + j) = v := by
  obtain ⟨hKT, -, hK1, -, -⟩ := ltT_facts hρ hρ1 K
  have hv1 : v < Om1 := hv.trans hK1
  have hvT : v ∈ Tset ρ := vz_T_down hρ hρ1 hKT hK1 hv.le
  have hρv : ρ < v := ((lzY_facts hρ hρ1 0).2.1.trans_le (lzY_le_w ρ 0)).trans hwv
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv, by rw [hξv]; exact hvE⟩
  have hk := lzY_T hρ hρ1 K
  have hξlt : ξ < Om1 * ω + lzY ρ K :=
    lzLt_of_vt_lt_ww hρ hρ1 hξT hξ2 hk.1 hk.2
      (by rw [hξv]; exact (lzY_lt_w hρ hρ1 K).trans hwv) (by rw [hξv]; exact hv)
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
    have hjK : ξ - Om1 * ω < lzY ρ K := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    exact ⟨_, vz_T_down hρ hρ1 hk.1 hk.2 hjK.le, hjK, by rw [hξe, hξv]⟩

/-- **Representation below `T_K(ρ)`** by terms of level `≤ K`. -/
theorem ltw_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {K : ℕ} :
    ∀ v, v < ltT ρ K → ∃ t : LtW, CBt t ρ ∧ lw t ≤ K ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (lzYw ρ) with hvw | rfl | hwv
  · obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hvw
    obtain ⟨a, ha, -, hav⟩ := lzw_rep hρ hρ1 v hk
    exact ⟨lz a, ha, Nat.zero_le K, hav⟩
  · refine ⟨tw (LzW.vz (VzTm.cst ω)), omega0_lt_inE hρ, Nat.zero_le K, ?_⟩
    rw [ltYw_eq hρ hρ1]; rfl
  by_cases hvE : InE v
  · rcases ltw_th_form hρ hρ1 hvE hwv hv with ⟨q, hq, r, -, -, hrv, he⟩ | ⟨j, -, hjK, he⟩
    · obtain ⟨t, ht, hl, htv⟩ := IH r hrv (hrv.trans hv)
      exact ⟨th q t, ⟨hq, ht⟩, hl, by rw [val_th, htv, he]⟩
    · obtain ⟨a, ha, hl, hav⟩ := lzw_rep hρ hρ1 j hjK
      exact ⟨tw a, ha, hl, by rw [val_tw, hav, he]⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hwv).ne'
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
