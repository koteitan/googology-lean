import Googology.Trans.PoR.InaccPsi.R2.LzY

/-!
# The terms `ϑˣ(Ω₁·n + t)` over the atoms `y_k(x) = ϑˣ(Ω₁·ω + k)`: values below `y_K(x)`

`LzW`: a term `vz t` of `R2.VzT` (values below `B(x) = y_0(x)`), an atom `yk k` (value `y_k(x)`, `R2.LzY`),
`th n t` (value `ϑˣ(Ω₁·n + t(x))`), a sum `sm a b`, a power `pw a`; `lzwLv t` is the least `K` with all atoms
`yk k` of `t` at `k < K`.  For a base `x ∈ E ∩ Ω₁`:

* `lzw_T`, `lzw_lt_top` (**every value of a term of level `≤ K` is below `y_K(x)`**: [W07a] Lemma 3.30 at `Ω₁·ω + K`,
  `lzY_th_lt`), `lzw_lt_ups`;
* `lzw_pi` (**Lemma EXACT**: `vzv_pi`, `lzY_pi`, `vz_pi_th`, `pi_add`, `pi_opowZ`), `lzw_uni_le`, `lzw_uni_lt`,
  `lzw_uni_eq`;
* `lzw_th_form` (**an `ε`-number `v ∈ (B(ρ), y_K(ρ))` is `ϑᵖ(Ω₁·q + r)`, `1 ≤ q < ω`, `r < v`, or an atom `y_j(ρ)`,
  `j < K`**: `vt_rep`, `vt_E_iff`, `lzLt_of_vt_lt_ww`, `vzRem_T`), `lzw_rep` (**representation below `y_K(ρ)` by terms of
  level `≤ K`**);
* `lzw_zero`, `LzWC`, `lzw_small`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **The terms `ϑˣ(Ω₁·n + t)` over the atoms `y_k`.** -/
inductive LzW : Type 1
  | vz : VzTm → LzW
  | yk : ℕ → LzW
  | th : ℕ → LzW → LzW
  | sm : LzW → LzW → LzW
  | pw : LzW → LzW

namespace LzW

/-- The value at the base `x`. -/
noncomputable def val : LzW → Ordinal.{0} → Ordinal.{0}
  | vz t, x => t.val x
  | yk k, x => lzY x k
  | th n t, x => vt x (Om1 * (n : Ordinal.{0}) + val t x)
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`, all levels `≥ 1`. -/
def CBt : LzW → Ordinal.{0} → Prop
  | vz t, s => t.CBt s
  | yk _, _ => True
  | th n t, s => 1 ≤ n ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LzW → List Ordinal.{0}
  | vz t => t.cst'
  | yk _ => []
  | th _ t => cs t
  | sm a b => cs a ++ cs b
  | pw a => cs a

/-- The level: one more than the largest atom index (`0` without atoms). -/
def lv : LzW → ℕ
  | vz _ => 0
  | yk k => k + 1
  | th _ t => lv t
  | sm a b => max (lv a) (lv b)
  | pw a => lv a

@[simp] theorem val_vz (t : VzTm) (x : Ordinal.{0}) : val (vz t) x = t.val x := rfl
@[simp] theorem val_yk (k : ℕ) (x : Ordinal.{0}) : val (yk k) x = lzY x k := rfl
@[simp] theorem val_th (n : ℕ) (t : LzW) (x : Ordinal.{0}) :
    val (th n t) x = vt x (Om1 * (n : Ordinal.{0}) + val t x) := rfl
@[simp] theorem val_sm (a b : LzW) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LzW) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LzW) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | vz t, s, s', h, h' => VzTm.cbt_iff t s s' h h'
  | yk _, _, _, _, _ => trivial
  | th _ t, s, s', h, h' => ⟨h.1, cbt_iff t s s' h.2 h'⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LzW) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | vz t, s, h, c, hc => VzTm.cbt_cst t s h c hc
  | yk _, _, _, c, hc => by simp [cs] at hc
  | th _ t, s, h, c, hc => cbt_cst t s h.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LzW} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LzW

open LzW

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`t(x) ∈ Tˣ ∩ Ω₁`.** -/
theorem lzw_T : ∀ t : LzW, CBt t x → val t x ∈ Tset x ∧ val t x < Om1
  | vz t, h => vzv_T hx hx1 t h
  | yk k, _ => ⟨(lzY_facts hx hx1 k).1, (lzY_facts hx hx1 k).2.2.1⟩
  | th n t, h => by
    obtain ⟨h1, h2⟩ := lzw_T t h.2
    obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 h.1 h1 h2
    exact ⟨hvT, hv1⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lzw_T a h.1
    obtain ⟨h3, h4⟩ := lzw_T b h.2
    exact ⟨vzT_add hx hx1 h1 h3, Om1_add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := lzw_T t h
    obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
    have hw : ω ^ val t x < m := hmE.opow_lt ((hTm _ h2).1 h1)
    exact ⟨(hTm _ (hw.trans hm1)).2 hw, hw.trans hm1⟩

/-- **Every value of a term of level `≤ K` is below `y_K(x)`.** -/
theorem lzw_lt_top {K : ℕ} : ∀ t : LzW, CBt t x → lv t ≤ K → val t x < lzY x K
  | vz t, h, _ => (vzv_lt_B hx hx1 h).trans_le (by rw [← lzY_zero hx hx1]; exact lzY_mono hx hx1 (Nat.zero_le K))
  | yk k, _, hl => lzY_strict hx hx1 (by simp only [lv] at hl; omega)
  | th n t, h, hl => lzY_th_lt hx hx1 n (lzw_T hx hx1 t h.2).1 (lzw_lt_top t h.2 hl)
  | sm a b, h, hl => (inE_indec (lzY_facts hx hx1 K).2.2.2.1).add_lt
      (lzw_lt_top a h.1 ((le_max_left _ _).trans hl)) (lzw_lt_top b h.2 ((le_max_right _ _).trans hl))
  | pw a, h, hl => (lzY_facts hx hx1 K).2.2.2.1.opow_lt (lzw_lt_top a h hl)

theorem lzw_lt_ups {t : LzW} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  (lzw_lt_top hx hx1 (K := lv t) t ht le_rfl).trans (lzY_lt_next hx hx1 _ hxu hu.2)

/-- **A value `0` is the value `0` everywhere.** -/
theorem lzw_zero : ∀ t : LzW, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | vz t, h, h0 => Ly.lb_zero_const hx hx1 h h0
  | yk k, _, h0 => absurd h0 (lzY_facts hx hx1 k).2.2.2.1.pos.ne'
  | th n t, h, h0 => by
    obtain ⟨h1, h2⟩ := lzw_T hx hx1 t h.2
    exact absurd h0 (vz_th_facts hx hx1 h.1 h1 h2).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lzw_zero a h.1 this.1 y, lzw_zero b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Facts

/-! ## Lemma EXACT and the comparison -/

/-- **Lemma EXACT for `LzW`.** -/
theorem lzw_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LzW, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | vz t, h => vzv_pi hσ hρ hB t h
  | yk k, _ => lzY_pi hB k
  | th n t, h => by
    obtain ⟨h1, h2⟩ := lzw_pi hσ hρ hB t h.2
    have ht1 : val t ρ < Om1 := (lzw_T hB.2.1 hB.2.2.2 t (cbt_mono h.2 hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := vz_pi_th hB h1 ht1 n
    simp only [val_th]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lzw_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lzw_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lzw_pi hσ hρ hB a h
    have hb := (lzw_T hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lzw_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lzw_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lzw_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lzw_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lzw_uni_le hσ hρ hB hu ht]

theorem lzw_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzW}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lzw_uni_le hσ hρ hB ht hu, lzw_uni_le hσ hρ hB hu ht]

/-! ## Constant terms -/

/-- A term without the base, atoms and `ϑ`-terms. -/
def LzWC : LzW → Prop
  | vz t => VzTm.noB t
  | yk _ => False
  | th _ _ => False
  | sm a b => LzWC a ∧ LzWC b
  | pw a => LzWC a

theorem lzWC_const : ∀ t : LzW, LzWC t → ∀ x y, val t x = val t y
  | vz t, h, x, y => vzv_noB t h x y
  | yk _, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, lzWC_const a h.1 x y, lzWC_const b h.2 x y]
  | pw a, h, x, y => by simp only [val_pw, lzWC_const a h x y]

theorem lzWC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LzW, CBt t x → ¬ LzWC t → x ≤ val t x
  | vz t, hc, h => le_vzv_of_not_noB hx hx1 t hc h
  | yk k, _, _ => (lzY_facts hx hx1 k).2.1.le
  | th n t, hc, _ => by
    obtain ⟨h1, h2⟩ := lzw_T hx hx1 t hc.2
    exact (vz_th_facts hx hx1 hc.1 h1 h2).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [LzWC, not_and_or] at h
    rcases h with h | h
    · exact (lzWC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (lzWC_ge hx hx1 b hc.2 h).trans le_add_self
  | pw a, hc, h => (lzWC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem lzw_small (t : LzW) :
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x) := by
  by_cases h : LzWC t
  · exact Or.inl (lzWC_const t h)
  · exact Or.inr fun x hx hx1 hc => lzWC_ge hx hx1 t hc h

/-! ## The representation -/

/-- **An `ε`-number `v ∈ (B(ρ), y_K(ρ))` is `ϑᵖ(Ω₁·q + r)` (`1 ≤ q < ω`, `r ∈ Tᵖ ∩ Ω₁`, `r < v`) or an atom
`y_j(ρ)`, `j < K`.** -/
theorem lzw_th_form {ρ v : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {K : ℕ} (hvE : InE v) (hBv : VzB ρ < v)
    (hv : v < lzY ρ K) : (∃ q : ℕ, 1 ≤ q ∧ ∃ r, r ∈ Tset ρ ∧ r < Om1 ∧ r < v ∧
      vt ρ (Om1 * (q : Ordinal.{0}) + r) = v) ∨ ∃ j : ℕ, j < K ∧ v = lzY ρ j := by
  obtain ⟨hKT, -, hK1, -, -⟩ := lzY_facts hρ hρ1 K
  have hv1 : v < Om1 := hv.trans hK1
  have hvT : v ∈ Tset ρ := vz_T_down hρ hρ1 hKT hK1 hv.le
  have hρB := (vzB_omega hρ hρ1).2.1
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv, by rw [hξv]; exact hvE⟩
  have hk := lz_natT hρ hρ1 K
  have hξlt : ξ < Om1 * ω + (K : Ordinal.{0}) :=
    lzLt_of_vt_lt_ww hρ hρ1 hξT hξ2 hk.1 hk.2
      (by rw [hξv]; exact (natCast_lt_omega0 _).trans (omega0_lt_inE hvE)) (by rw [hξv]; exact hv)
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
    set j := ξ - Om1 * ω with hj
    have hξe : Om1 * ω + j = ξ := Ordinal.add_sub_cancel_of_le hwξ
    have hjK : j < (K : Ordinal.{0}) := (add_lt_add_iff_left _).1 (by rw [hξe]; exact hξlt)
    obtain ⟨j', hj'⟩ := lt_omega0.1 (hjK.trans (natCast_lt_omega0 _))
    refine ⟨j', by rw [hj'] at hjK; exact_mod_cast hjK, ?_⟩
    rw [← hξv, ← hξe, hj']
    rfl

/-- **Representation below `y_K(ρ)`** by terms of level `≤ K`. -/
theorem lzw_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {K : ℕ} :
    ∀ v, v < lzY ρ K → ∃ t : LzW, CBt t ρ ∧ lv t ≤ K ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (VzB ρ) with hvB | rfl | hBv
  · obtain ⟨t, ht, htv⟩ := vzv_repB hρ hρ1 hvB
    exact ⟨vz t, ht, Nat.zero_le K, htv⟩
  · have hK : 0 < K := by
      by_contra h0
      push Not at h0
      have : K = 0 := by omega
      subst this
      rw [lzY_zero hρ hρ1] at hv
      exact lt_irrefl _ hv
    exact ⟨yk 0, trivial, by simp only [lv]; omega, lzY_zero hρ hρ1⟩
  by_cases hvE : InE v
  · rcases lzw_th_form hρ hρ1 hvE hBv hv with ⟨q, hq, r, -, -, hrv, he⟩ | ⟨j, hj, rfl⟩
    · obtain ⟨t, ht, hl, htv⟩ := IH r hrv (hrv.trans hv)
      exact ⟨th q t, ⟨hq, ht⟩, hl, by rw [val_th, htv, he]⟩
    · exact ⟨yk j, trivial, by simp only [lv]; omega, rfl⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
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
  · have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨t1, ht1, hl1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨t2, ht2, hl2, hv2⟩ := IH _ hwv (hwv.trans hv)
    exact ⟨sm t1 t2, ⟨ht1, ht2⟩, max_le hl1 hl2, by rw [val_sm, hv1, hv2, ← hvs]⟩

end Googology.Trans.PoR.InaccPsi.R2.Lz
