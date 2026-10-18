import Googology.Trans.PoR.InaccPsi.R2.LzSys

/-!
# The terms `ϑˣ(Ω₁·n + t)` over `B`: values below `B₁(x) = sup_N ϑˣ(Ω₁·N + B(x) + 1)`

`LzV`: a term `vz t` of `R2.VzT` (values below `B(x)`), the atom `bB` (value `B(x)`), `th n t` (value
`ϑˣ(Ω₁·n + t(x))`, `1 ≤ n < ω`; the argument may lie above `B(x)`), a sum `sm a b`, a power `pw a`.  `VzB1 x :=
sup_N ϑˣ(Ω₁·N + (B(x) + 1))`.  For every base `x` (an `ε`-number below `Ω₁`), from the cited facts of `R2.CitedVz`,
`R2.CitedEv`, `R2.CitedXt` ([W07a] Def 3.22, Lemma 3.30, Convention 4.1, Def 5.1; no new axiom):

* `lzv_T` (`t(x) ∈ Tˣ ∩ Ω₁`), `lzv_bound` (**`t(x) < ϑˣ(Ω₁·N + B(x) + 1)` for some `N ≥ 1`**), `lzv_lt_top`
  (**every value is below `B₁(x)`**), `lzB1_le_next`, `lzv_lt_ups` (`B₁(x)` and the values lie below every `<₁ ∞`-point
  above `x`);
* `lzv_pi` (**Lemma EXACT**: `vzv_pi`, `xtPiB`, `vz_pi_th`, `pi_add`, `pi_opowZ`), `lzv_uni_le`, `lzv_uni_lt`,
  `lzv_uni_eq`;
* `lzv_rep` (**representation below `B₁(ρ)`**: an `ε`-number `v ∈ (B(ρ), B₁(ρ))` is `ϑᵖ(ξ)` with
  `Ω₁ ≤ ξ < Ω₁·N + B(ρ) + 1`, so `ξ = Ω₁·q + r`, `1 ≤ q ≤ N`, `r < v`: [W07a] Lemma 3.30 at `Ω₁·N + η` with
  `η = B(ρ) + 1 ≥ B(ρ)` through the axiom `vzLt_of_vt_lt`, Convention 4.1 through `vzRem_T`);
* `lzv_zero`, `LzVC`, `lzv_small`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **The terms `ϑˣ(Ω₁·n + t)` over `B`.** -/
inductive LzV : Type 1
  | vz : VzTm → LzV
  | bB : LzV
  | th : ℕ → LzV → LzV
  | sm : LzV → LzV → LzV
  | pw : LzV → LzV

namespace LzV

/-- The value at the base `x`. -/
noncomputable def val : LzV → Ordinal.{0} → Ordinal.{0}
  | vz t, x => t.val x
  | bB, x => VzB x
  | th n t, x => vt x (Om1 * (n : Ordinal.{0}) + val t x)
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`, all levels `≥ 1`. -/
def CBt : LzV → Ordinal.{0} → Prop
  | vz t, s => t.CBt s
  | bB, _ => True
  | th n t, s => 1 ≤ n ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LzV → List Ordinal.{0}
  | vz t => t.cst'
  | bB => []
  | th _ t => cs t
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_vz (t : VzTm) (x : Ordinal.{0}) : val (vz t) x = t.val x := rfl
@[simp] theorem val_bB (x : Ordinal.{0}) : val bB x = VzB x := rfl
@[simp] theorem val_th (n : ℕ) (t : LzV) (x : Ordinal.{0}) :
    val (th n t) x = vt x (Om1 * (n : Ordinal.{0}) + val t x) := rfl
@[simp] theorem val_sm (a b : LzV) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LzV) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LzV) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | vz t, s, s', h, h' => VzTm.cbt_iff t s s' h h'
  | bB, _, _, _, _ => trivial
  | th _ t, s, s', h, h' => ⟨h.1, cbt_iff t s s' h.2 h'⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LzV) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | vz t, s, h, c, hc => VzTm.cbt_cst t s h c hc
  | bB, _, _, c, hc => by simp [cs] at hc
  | th _ t, s, h, c, hc => cbt_cst t s h.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LzV} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LzV

open LzV

/-- `B₁(x) = sup_N ϑˣ(Ω₁·N + (B(x) + 1))`. -/
noncomputable def VzB1 (x : Ordinal.{0}) : Ordinal.{0} := ⨆ N : ℕ, vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1))

theorem lzN1_le_B1 (x : Ordinal.{0}) (N : ℕ) : vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1)) ≤ VzB1 x :=
  Ordinal.le_iSup _ N

theorem lzB1_lt_iff {x v : Ordinal.{0}} : v < VzB1 x ↔ ∃ N : ℕ, v < vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1)) :=
  Ordinal.lt_iSup_iff

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lz_B1T : VzB x + 1 ∈ Tset x ∧ VzB x + 1 < Om1 :=
  ⟨vzT_add hx hx1 (lz_BT hx hx1) (mem_T_of_le hx hx1 (one_le_iff_pos.2 hx.pos)),
    Om1_add_lt (xt_B_lt_Om1 hx hx1) (one_lt_omega0.trans omega0_lt_omega_one)⟩

/-- `N ↦ ϑˣ(Ω₁·N + η)` is increasing. -/
theorem lz_vtN_mono {η : Ordinal.{0}} (hηT : η ∈ Tset x) (hη1 : η < Om1) {N M : ℕ} (hNM : N < M) :
    vt x (Om1 * (N : Ordinal.{0}) + η) < vt x (Om1 * (M : Ordinal.{0}) + η) := by
  have hM1 : 1 ≤ M := by omega
  refine vzVt_lt hx hx1 hηT hη1 hηT hη1 ?_ (vz_th_facts hx hx1 hM1 hηT hη1).2.2.2.2.2.2.2
  calc Om1 * (N : Ordinal.{0}) + η < Om1 * (N : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * ((N + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
    _ ≤ Om1 * (M : Ordinal.{0}) := mul_le_mul_right (by exact_mod_cast hNM) Om1
    _ ≤ Om1 * (M : Ordinal.{0}) + η := le_self_add

theorem lz_vtN_le {η : Ordinal.{0}} (hηT : η ∈ Tset x) (hη1 : η < Om1) {N M : ℕ} (hNM : N ≤ M) :
    vt x (Om1 * (N : Ordinal.{0}) + η) ≤ vt x (Om1 * (M : Ordinal.{0}) + η) := by
  rcases hNM.lt_or_eq with h | rfl
  · exact (lz_vtN_mono hx hx1 hηT hη1 h).le
  · exact le_rfl

theorem lz_B_lt_N1 {N : ℕ} (hN : 1 ≤ N) : VzB x + 1 < vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1)) := by
  obtain ⟨hT, h1⟩ := lz_B1T hx hx1
  exact (vz_th_facts hx hx1 hN hT h1).2.2.2.2.2.2.2

theorem lz_B_lt_B1 : VzB x < VzB1 x :=
  (lt_add_one _).trans ((lz_B_lt_N1 hx hx1 (N := 1) le_rfl).trans_le (lzN1_le_B1 x 1))

/-- **`t(x) ∈ Tˣ ∩ Ω₁`.** -/
theorem lzv_T : ∀ t : LzV, CBt t x → val t x ∈ Tset x ∧ val t x < Om1
  | vz t, h => vzv_T hx hx1 t h
  | bB, _ => ⟨lz_BT hx hx1, xt_B_lt_Om1 hx hx1⟩
  | th n t, h => by
    obtain ⟨h1, h2⟩ := lzv_T t h.2
    obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 h.1 h1 h2
    exact ⟨hvT, hv1⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lzv_T a h.1
    obtain ⟨h3, h4⟩ := lzv_T b h.2
    exact ⟨vzT_add hx hx1 h1 h3, Om1_add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := lzv_T t h
    obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
    have hw : ω ^ val t x < m := hmE.opow_lt ((hTm _ h2).1 h1)
    exact ⟨(hTm _ (hw.trans hm1)).2 hw, hw.trans hm1⟩

/-- **`t(x) < ϑˣ(Ω₁·N + B(x) + 1)`** for some `N ≥ 1`. -/
theorem lzv_bound : ∀ t : LzV, CBt t x →
    ∃ N : ℕ, 1 ≤ N ∧ val t x < vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1)) := by
  obtain ⟨hηT, hη1⟩ := lz_B1T hx hx1
  have hfa : ∀ N : ℕ, 1 ≤ N → InE (vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1))) := fun N hN =>
    (vz_th_facts hx hx1 hN hηT hη1).2.2.2.2.2.1
  have hB : VzB x < vt x (Om1 * ((1 : ℕ) : Ordinal.{0}) + (VzB x + 1)) :=
    (lt_add_one _).trans (lz_B_lt_N1 hx hx1 le_rfl)
  intro t
  induction t with
  | vz t => exact fun h => ⟨1, le_rfl, (vzv_lt_B hx hx1 h).trans hB⟩
  | bB => exact fun _ => ⟨1, le_rfl, hB⟩
  | th n t ih =>
    intro h
    obtain ⟨N, hN, hlt⟩ := ih h.2
    obtain ⟨h1, h2⟩ := lzv_T hx hx1 t h.2
    refine ⟨max N (n + 1), le_max_of_le_left hN, ?_⟩
    have hN' := lz_vtN_le hx hx1 hηT hη1 (le_max_left N (n + 1))
    refine vzVt_lt hx hx1 h1 h2 hηT hη1 ?_ (hlt.trans_le hN')
    calc Om1 * (n : Ordinal.{0}) + val t x < Om1 * (n : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 h2
      _ = Om1 * ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
      _ ≤ Om1 * ((max N (n + 1) : ℕ) : Ordinal.{0}) :=
        mul_le_mul_right (by exact_mod_cast le_max_right N (n + 1)) Om1
      _ ≤ _ := le_self_add
  | sm a b iha ihb =>
    intro h
    obtain ⟨N1, hN1, h1⟩ := iha h.1
    obtain ⟨N2, hN2, h2⟩ := ihb h.2
    refine ⟨max N1 N2, le_max_of_le_left hN1, ?_⟩
    have hE := hfa (max N1 N2) (le_max_of_le_left hN1)
    exact (inE_indec hE).add_lt (h1.trans_le (lz_vtN_le hx hx1 hηT hη1 (le_max_left _ _)))
      (h2.trans_le (lz_vtN_le hx hx1 hηT hη1 (le_max_right _ _)))
  | pw t ih =>
    intro h
    obtain ⟨N, hN, h1⟩ := ih h
    exact ⟨N, hN, (hfa N hN).opow_lt h1⟩

/-- **Every value is below `B₁(x)`.** -/
theorem lzv_lt_top (t : LzV) (h : CBt t x) : val t x < VzB1 x := by
  obtain ⟨N, -, hN⟩ := lzv_bound hx hx1 t h
  exact hN.trans_le (lzN1_le_B1 x N)

/-- `B₁(x)` lies below or at every `<₁ ∞`-point above `x`. -/
theorem lzB1_le_next {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : VzB1 x ≤ u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hηT, hη1⟩ := lz_B1T hx hx1
  refine Ordinal.iSup_le (fun N => (lz_vtN_le hx hx1 hηT hη1 (Nat.le_succ N)).trans ?_)
  obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 (Nat.succ_pos N) hηT hη1
  exact (((hTm _ hv1).1 hvT).trans_le (hmin u hxu hu)).le

theorem lzv_lt_ups {t : LzV} (ht : CBt t x) {u : Ordinal.{0}} (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  (lzv_lt_top hx hx1 t ht).trans_le (lzB1_le_next hx hx1 hxu hu.2)

theorem lzB1_lt_Om1 : VzB1 x < Om1 := by
  obtain ⟨m, hxm, hm, -, -, hm1⟩ := T_next (Or.inr hx) hx1
  exact (lzB1_le_next hx hx1 hxm hm).trans_lt hm1

/-- **A value `0` is the value `0` everywhere.** -/
theorem lzv_zero : ∀ t : LzV, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | vz t, h, h0 => Ly.lb_zero_const hx hx1 h h0
  | bB, _, h0 => absurd h0 (xt_B_E hx hx1).pos.ne'
  | th n t, h, h0 => by
    obtain ⟨h1, h2⟩ := lzv_T hx hx1 t h.2
    exact absurd h0 (vz_th_facts hx hx1 h.1 h1 h2).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lzv_zero a h.1 this.1 y, lzv_zero b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Facts

/-! ## Lemma EXACT and the comparison -/

/-- **Lemma EXACT for `LzV`.** -/
theorem lzv_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LzV, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | vz t, h => vzv_pi hσ hρ hB t h
  | bB, _ => xtPiB hB
  | th n t, h => by
    obtain ⟨h1, h2⟩ := lzv_pi hσ hρ hB t h.2
    have ht1 : val t ρ < Om1 := (lzv_T hB.2.1 hB.2.2.2 t (cbt_mono h.2 hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := vz_pi_th hB h1 ht1 n
    simp only [val_th]
    exact ⟨h3, by rw [h4, h2]⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lzv_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lzv_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lzv_pi hσ hρ hB a h
    have hb := (lzv_T hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lzv_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzV}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lzv_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lzv_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lzv_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzV}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lzv_uni_le hσ hρ hB hu ht]

theorem lzv_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzV}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lzv_uni_le hσ hρ hB ht hu, lzv_uni_le hσ hρ hB hu ht]

/-! ## Constant terms -/

/-- A term without the base, `B` and `ϑ`-terms. -/
def LzVC : LzV → Prop
  | vz t => VzTm.noB t
  | bB => False
  | th _ _ => False
  | sm a b => LzVC a ∧ LzVC b
  | pw a => LzVC a

theorem lzVC_const : ∀ t : LzV, LzVC t → ∀ x y, val t x = val t y
  | vz t, h, x, y => vzv_noB t h x y
  | bB, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, lzVC_const a h.1 x y, lzVC_const b h.2 x y]
  | pw a, h, x, y => by simp only [val_pw, lzVC_const a h x y]

theorem lzVC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LzV, CBt t x → ¬ LzVC t → x ≤ val t x
  | vz t, hc, h => le_vzv_of_not_noB hx hx1 t hc h
  | bB, _, _ => (vzB_omega hx hx1).2.1.le
  | th n t, hc, _ => by
    obtain ⟨h1, h2⟩ := lzv_T hx hx1 t hc.2
    exact (vz_th_facts hx hx1 hc.1 h1 h2).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [LzVC, not_and_or] at h
    rcases h with h | h
    · exact (lzVC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (lzVC_ge hx hx1 b hc.2 h).trans le_add_self
  | pw a, hc, h => (lzVC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem lzv_small (t : LzV) :
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x) := by
  by_cases h : LzVC t
  · exact Or.inl (lzVC_const t h)
  · exact Or.inr fun x hx hx1 hc => lzVC_ge hx hx1 t hc h

/-! ## The representation -/

/-- **An `ε`-number `v ∈ (B(ρ), B₁(ρ))` is `ϑᵖ(Ω₁·q + r)`** with `1 ≤ q`, `r ∈ Tᵖ ∩ Ω₁`, `r < v`. -/
theorem lzv_th_form {ρ v : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) (hvE : InE v) (hBv : VzB ρ < v)
    (hv : v < VzB1 ρ) : ∃ q : ℕ, 1 ≤ q ∧ ∃ r, r ∈ Tset ρ ∧ r < Om1 ∧ r < v ∧
      vt ρ (Om1 * (q : Ordinal.{0}) + r) = v := by
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hρ) hρ1
  obtain ⟨hηT, hη1⟩ := lz_B1T hρ hρ1
  obtain ⟨N, hN⟩ := lzB1_lt_iff.1 hv
  set M := max N 1 with hM
  have hvM : v < vt ρ (Om1 * (M : Ordinal.{0}) + (VzB ρ + 1)) :=
    hN.trans_le (lz_vtN_le hρ hρ1 hηT hη1 (le_max_left N 1))
  obtain ⟨-, -, hMT, -, hM1, -, -, -⟩ := vz_th_facts hρ hρ1 (le_max_right N 1) hηT hη1
  have hv1 : v < Om1 := hvM.trans hM1
  have hvT : v ∈ Tset ρ := (hTm v hv1).2 (hvM.trans ((hTm _ hM1).1 hMT))
  have hρB := (vzB_omega hρ hρ1).2.1
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv.le hv1 (inE_indec hvE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv, by rw [hξv]; exact hvE⟩
  have hB1v : VzB ρ + 1 < v := (inE_indec hvE).add_lt hBv (one_lt_omega0.trans (omega0_lt_inE hvE))
  have hξN : ξ < Om1 * (M : Ordinal.{0}) + (VzB ρ + 1) :=
    vzLt_of_vt_lt hρ hρ1 hξT hξ2 hηT hη1 (by rw [hξv]; exact hB1v) (by rw [hξv]; exact hvM)
  obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
  set q := ξ / Om1 with hq
  set r := ξ % Om1 with hr
  have hqN : q < ((M + 1 : ℕ) : Ordinal.{0}) := by
    have h1 : Om1 * q < Om1 * ((M + 1 : ℕ) : Ordinal.{0}) := by
      calc Om1 * q ≤ ξ := hdec ▸ le_self_add
        _ < Om1 * (M : Ordinal.{0}) + (VzB ρ + 1) := hξN
        _ < Om1 * (M : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hη1
        _ = Om1 * ((M + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
    exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
  obtain ⟨q', hq'⟩ := lt_omega0.1 (hqN.trans (natCast_lt_omega0 _))
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

/-- **Representation below `B₁(ρ)`.** -/
theorem lzv_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) :
    ∀ v, v < VzB1 ρ → ∃ t : LzV, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (VzB ρ) with hvB | rfl | hBv
  · obtain ⟨t, ht, htv⟩ := vzv_repB hρ hρ1 hvB
    exact ⟨vz t, ht, htv⟩
  · exact ⟨bB, trivial, rfl⟩
  by_cases hvE : InE v
  · obtain ⟨q, hq, r, -, -, hrv, he⟩ := lzv_th_form hρ hρ1 hvE hBv hv
    obtain ⟨t, ht, htv⟩ := IH r hrv (hrv.trans hv)
    exact ⟨th q t, ⟨hq, ht⟩, by rw [val_th, htv, he]⟩
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
    obtain ⟨t, ht, htv⟩ := IH _ hzv (hzv.trans hv)
    exact ⟨pw t, ht, by rw [val_pw, htv, ← hvs]⟩
  · have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨t1, ht1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨t2, ht2, hv2⟩ := IH _ hwv (hwv.trans hv)
    exact ⟨sm t1 t2, ⟨ht1, ht2⟩, by rw [val_sm, hv1, hv2, ← hvs]⟩

end Googology.Trans.PoR.InaccPsi.R2.Lz
