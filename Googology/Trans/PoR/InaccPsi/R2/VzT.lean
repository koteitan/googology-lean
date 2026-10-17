import Googology.Trans.PoR.InaccPsi.R2.VzL
import Googology.Trans.PoR.InaccPsi.R2.EvTZ

/-!
# The terms `φ(n, ·)` in `x` for `1 ≤ n < ω`: values, Lemma EXACT, the representation, Lemma RS

The terms `VzTm`: a constant (`cst a`), the base `x` (`bs`), `ϑˣ(Ω₁·n + t)` for `1 ≤ n < ω` and a term `t` (`th n t`;
by `R2.VzL` its value is the `t`-th ordinal of `(x, Ω₁)` of fixed-point level exactly `n`, a value of `φ_n` that is
not a fixed point of `φ_n`), a sum (`sm`), and `ω^t` (`pw t`).  The term functions are Wilken's `ϑˣ` themselves, so
the base change is [W07a] Def 5.1 (`pi_vt_two`, `pi_add`, `pi_Om1`).

* `VzTm`, `VzTm.val`, `VzTm.CBt`, `VzTm.cst'`, `VzTm.noB`; `vzv_T` (**`t(x) ∈ Tˣ ∩ Ω₁`**), `vzv_lt_next` (below every
  `<₁ ∞`-point above `x`), `vzv_bound` (`t(x) < ϑˣ(Ω₁·N)` for some `N`), `vzN_mono`, `VzB` (`sup_N ϑˣ(Ω₁·N)`),
  `vzv_lt_B`;
* `vz_pi_Om1_mul`, `vzv_pi` (**Lemma EXACT**: `t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`), `uniVz_le`, `uniVz_lt`,
  `uniVz_eq`;
* `vzv_rep` (**representation**: every ordinal below `ϑᵖ(Ω₁·N)` is a value at `ρ`; an `ε`-number `v > ρ` there is
  `ϑᵖ(Ω₁·q + r)` with `1 ≤ q < N`, `r ∈ Tᵖ`, `r < v`, by [W07a] Lemma 3.30 and Convention 4.1);
* `rs_rstVz`, `rsStep_Vz` (**Lemma RS for every term**).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The terms `φ(n, ·)` in `x`: a constant, the base, `ϑˣ(Ω₁·n + t)`, a sum, or `ω^t`. -/
inductive VzTm : Type 1
  | cst : Ordinal.{0} → VzTm
  | bs : VzTm
  | th : ℕ → VzTm → VzTm
  | sm : VzTm → VzTm → VzTm
  | pw : VzTm → VzTm

namespace VzTm

/-- The value of a term at the base `x`. -/
noncomputable def val : VzTm → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th n t, x => vt x (Om1 * (n : Ordinal.{0}) + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- All constants below `s`, all levels `≥ 1`. -/
def CBt : VzTm → Ordinal.{0} → Prop
  | cst a, s => a < s
  | bs, _ => True
  | th n t, s => 1 ≤ n ∧ CBt t s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw t, s => CBt t s

/-- The constants. -/
def cst' : VzTm → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th _ t => cst' t
  | sm a b => cst' a ++ cst' b
  | pw t => cst' t

/-- No `bs` and no `th` occurs (a constant term). -/
def noB : VzTm → Prop
  | cst _ => True
  | bs => False
  | th _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th (n : ℕ) (t : VzTm) (x : Ordinal.{0}) :
    val (th n t) x = vt x (Om1 * (n : Ordinal.{0}) + val t x) := rfl
@[simp] theorem val_sm (a b : VzTm) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : VzTm) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

theorem cbt_iff : ∀ (t : VzTm) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cst' t, c < s') → CBt t s'
  | cst a, s, s', _, h => h a (by simp [cst'])
  | bs, _, _, _, _ => trivial
  | th n t, s, s', h, h' => ⟨h.1, cbt_iff t s s' h.2 h'⟩
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cst', hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cst', hc]))⟩
  | pw t, s, s', h, h' => cbt_iff t s s' h h'

theorem cbt_cst : ∀ (t : VzTm) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cst' t, c < s
  | cst a, s, h, c, hc => by simp [cst'] at hc; rw [hc]; exact h
  | bs, _, _, c, hc => by simp [cst'] at hc
  | th _ t, s, h, c, hc => cbt_cst t s h.2 c hc
  | sm a b, s, h, c, hc => by
    simp only [cst', List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw t, s, h, c, hc => cbt_cst t s h c hc

theorem CBt_mono {t : VzTm} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => lt_of_lt_of_le (cbt_cst t s h c hc) hs)

end VzTm

open VzTm

/-! ## Values -/

/-- The first `<₁ ∞`-point `m` above `x` is an `ε`-number, and `Tˣ ∩ Ω₁ = m`. -/
theorem vz_next {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∃ m, x < m ∧ LtInf1 m ∧ (∀ a, x < a → LtInf1 a → m ≤ a) ∧ (∀ a, a < Om1 → (a ∈ Tset x ↔ a < m)) ∧
      m < Om1 ∧ InE m := by
  obtain ⟨m, hxm, hm, hmin, hTm, hm1⟩ := T_next (Or.inr hx) hx1
  have hm0 : 0 < m := lt_of_le_of_lt zero_le hxm
  exact ⟨m, hxm, hm, hmin, hTm, hm1, (le1R_two_iff hm0).1 (hm _ (by rw [mul_two_eq]; exact le_self_add))⟩

/-- **`t(x) ∈ Tˣ ∩ Ω₁`** for an `ε`-number `x < Ω₁` and a term with constants below `x`. -/
theorem vzv_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : VzTm, CBt t x → val t x ∈ Tset x ∧ val t x < Om1
  | cst a, h => ⟨mem_T_of_le hx hx1 h.le, h.trans hx1⟩
  | bs, _ => ⟨mem_T_of_le hx hx1 le_rfl, hx1⟩
  | th n t, h => by
    obtain ⟨h1, h2⟩ := vzv_T hx hx1 t h.2
    obtain ⟨-, -, hvT, -, hv1, -⟩ := vz_th_facts hx hx1 h.1 h1 h2
    exact ⟨hvT, hv1⟩
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := vzv_T hx hx1 a h.1
    obtain ⟨h3, h4⟩ := vzv_T hx hx1 b h.2
    exact ⟨vzT_add hx hx1 h1 h3, Om1_add_lt h2 h4⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := vzv_T hx hx1 t h
    obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
    have hw : ω ^ val t x < m := hmE.opow_lt ((hTm _ h2).1 h1)
    exact ⟨(hTm _ (hw.trans hm1)).2 hw, hw.trans hm1⟩

/-- Term values lie below every `<₁ ∞`-point above the base. -/
theorem vzv_lt_next {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : VzTm} (ht : CBt t x) {u : Ordinal.{0}}
    (hxu : x < u) (hu : LtInf1 u) : val t x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨h1, h2⟩ := vzv_T hx hx1 t ht
  exact lt_of_lt_of_le ((hTm _ h2).1 h1) (hmin u hxu hu)

theorem vzv_lt_ups {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : VzTm} (ht : CBt t x) {u : Ordinal.{0}}
    (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  vzv_lt_next hx hx1 ht hxu hu.2

/-- `N ↦ ϑˣ(Ω₁·N)` is increasing. -/
theorem vzN_mono {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {N N' : ℕ} (hN : N < N') :
    vt x (Om1 * (N : Ordinal.{0}) + 0) < vt x (Om1 * (N' : Ordinal.{0}) + 0) := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine vzVt_lt hx hx1 h0T (Ordinal.omega_pos 1) h0T (Ordinal.omega_pos 1) ?_ ?_
  · rw [add_zero, add_zero]
    exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).2 (by exact_mod_cast hN)
  · exact lt_of_le_of_lt zero_le (vz_th_facts hx hx1 (by omega : 1 ≤ N') h0T (Ordinal.omega_pos 1)).2.2.2.1

theorem vzN_le {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {N N' : ℕ} (hN : N ≤ N') :
    vt x (Om1 * (N : Ordinal.{0}) + 0) ≤ vt x (Om1 * (N' : Ordinal.{0}) + 0) := by
  rcases hN.lt_or_eq with h | rfl
  · exact (vzN_mono hx hx1 h).le
  · exact le_rfl

/-- **`t(x) < ϑˣ(Ω₁·N)`** for some `N ≥ 1`. -/
theorem vzv_bound {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : VzTm, CBt t x → ∃ N : ℕ, 1 ≤ N ∧ val t x < vt x (Om1 * (N : Ordinal.{0}) + 0) := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hfa : ∀ N : ℕ, 1 ≤ N → x < vt x (Om1 * (N : Ordinal.{0}) + 0) ∧ InE (vt x (Om1 * (N : Ordinal.{0}) + 0)) :=
    fun N hN => by
      obtain ⟨-, -, -, h1, -, h2, -⟩ := vz_th_facts hx hx1 hN h0T (Ordinal.omega_pos 1)
      exact ⟨h1, h2⟩
  intro t
  induction t with
  | cst a => exact fun h => ⟨1, le_rfl, h.trans (hfa 1 le_rfl).1⟩
  | bs => exact fun _ => ⟨1, le_rfl, (hfa 1 le_rfl).1⟩
  | th n t ih =>
    intro h
    obtain ⟨N, hN, hlt⟩ := ih h.2
    obtain ⟨h1, h2⟩ := vzv_T hx hx1 t h.2
    refine ⟨max N (n + 1), le_max_of_le_left hN, ?_⟩
    have hN' : vt x (Om1 * (N : Ordinal.{0}) + 0) ≤ vt x (Om1 * ((max N (n + 1) : ℕ) : Ordinal.{0}) + 0) :=
      vzN_le hx hx1 (le_max_left _ _)
    refine vzVt_lt hx hx1 h1 h2 h0T (Ordinal.omega_pos 1) ?_ (hlt.trans_le hN')
    rw [add_zero]
    calc Om1 * (n : Ordinal.{0}) + val t x < Om1 * (n : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 h2
      _ = Om1 * ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
      _ ≤ Om1 * ((max N (n + 1) : ℕ) : Ordinal.{0}) :=
        mul_le_mul_right (by exact_mod_cast le_max_right N (n + 1)) Om1
  | sm a b iha ihb =>
    intro h
    obtain ⟨N1, hN1, h1⟩ := iha h.1
    obtain ⟨N2, hN2, h2⟩ := ihb h.2
    refine ⟨max N1 N2, le_max_of_le_left hN1, ?_⟩
    have hE := (hfa (max N1 N2) (le_max_of_le_left hN1)).2
    exact (inE_indec hE).add_lt (h1.trans_le (vzN_le hx hx1 (le_max_left _ _)))
      (h2.trans_le (vzN_le hx hx1 (le_max_right _ _)))
  | pw t ih =>
    intro h
    obtain ⟨N, hN, h1⟩ := ih h
    exact ⟨N, hN, (hfa N hN).2.opow_lt h1⟩

/-- `VzB x = sup_N ϑˣ(Ω₁·N)`. -/
noncomputable def VzB (x : Ordinal.{0}) : Ordinal.{0} := ⨆ N : ℕ, vt x (Om1 * (N : Ordinal.{0}) + 0)

theorem vzN_le_B (x : Ordinal.{0}) (N : ℕ) : vt x (Om1 * (N : Ordinal.{0}) + 0) ≤ VzB x :=
  Ordinal.le_iSup _ N

theorem vzv_lt_B {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : VzTm} (ht : CBt t x) : val t x < VzB x := by
  obtain ⟨N, -, h⟩ := vzv_bound hx hx1 t ht
  exact h.trans_le (vzN_le_B x N)

theorem vzB_lt_iff {x v : Ordinal.{0}} : v < VzB x ↔ ∃ N : ℕ, v < vt x (Om1 * (N : Ordinal.{0}) + 0) :=
  Ordinal.lt_iSup_iff

/-- `VzB x` lies below every `<₁ ∞`-point above `x`, up to `≤`. -/
theorem vzB_le_next {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {u : Ordinal.{0}} (hxu : x < u)
    (hu : LtInf1 u) : VzB x ≤ u := by
  refine Ordinal.iSup_le (fun N => ?_)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Nat.cast_zero, mul_zero, add_zero]
    obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hx hx1 h0T (lt_of_le_of_lt zero_le Om1_lt_OmTwo)
    exact (lt_of_lt_of_le ((hTm _ hv1).1 hvT) (hmin u hxu hu)).le
  · have := vzv_lt_next (t := th N (cst 0)) hx hx1 ⟨hN, hx.pos⟩ hxu hu
    exact this.le

/-! ## Lemma EXACT -/

/-- `Ω₁·n + γ ∈ Tᵖ[σ]` and `π_{σ,ρ}(Ω₁·n + γ) = Ω₁·n + π_{σ,ρ}(γ)`. -/
theorem vz_pi_Om1_mul {σ ρ γ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : γ ∈ TB ρ σ) :
    ∀ n : ℕ, Om1 * (n : Ordinal.{0}) + γ ∈ TB ρ σ ∧
      pi σ ρ (Om1 * (n : Ordinal.{0}) + γ) = Om1 * (n : Ordinal.{0}) + pi σ ρ γ
  | 0 => by rw [Nat.cast_zero, mul_zero, zero_add, zero_add]; exact ⟨hγ, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := vz_pi_Om1_mul hB hγ n
    obtain ⟨hOT, hpO⟩ := pi_Om1 hB
    obtain ⟨h3, h4⟩ := pi_add hB hOT h1
    have e : ∀ y : Ordinal.{0}, Om1 + (Om1 * (n : Ordinal.{0}) + y) = Om1 * ((n + 1 : ℕ) : Ordinal.{0}) + y :=
      fun y => by rw [← add_assoc, ← mul_one_add, ← Nat.cast_one, ← Nat.cast_add, add_comm 1 n]
    rw [e] at h3 h4
    rw [h4, hpO, h2, e]
    exact ⟨h3, rfl⟩

/-- **Lemma EXACT for `VzTm`**: for `υ`-points `σ < ρ` (`Bases σ ρ`) and a term with constants below `σ`,
`t(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(t(ρ)) = t(σ)`. -/
theorem vzv_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : VzTm, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | bs, _ => pi_base hB
  | th n t, h => by
    obtain ⟨h1, h2⟩ := vzv_pi hσ hρ hB t h.2
    have hρ1 := hB.2.2.2
    have ht1 : val t ρ < Om1 := (vzv_T hB.2.1 hρ1 t (CBt_mono h.2 hB.2.2.1.le)).2
    obtain ⟨hγTB, hpγ⟩ := vz_pi_Om1_mul hB h1 n
    have hγ2 := vzOm1_mul_lt ht1 n
    obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hρ1 hγTB.1 hγ2
    simp only [val_th]
    refine ⟨⟨hvT, by rw [hvP]; exact hγTB.2⟩, ?_⟩
    rw [pi_vt_two hB hγTB hγ2, hpγ, h2]
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := vzv_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := vzv_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw t, h => by
    obtain ⟨h1, h2⟩ := vzv_pi hσ hρ hB t h
    have hb := (vzv_T hB.2.1 hB.2.2.2 t (CBt_mono h hB.2.2.1.le)).2
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem uniVz_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : VzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := vzv_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := vzv_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uniVz_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : VzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uniVz_le hσ hρ hB hu ht]

theorem uniVz_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : VzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uniVz_le hσ hρ hB ht hu, uniVz_le hσ hρ hB hu ht]

/-! ## The representation -/

/-- **Representation**: every ordinal below `ϑᵖ(Ω₁·N)` is the value at `ρ` of a term with constants below `ρ`. -/
theorem vzv_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {N : ℕ} (hN : 1 ≤ N) :
    ∀ v, v < vt ρ (Om1 * (N : Ordinal.{0}) + 0) → ∃ t : VzTm, CBt t ρ ∧ val t ρ = v := by
  have h0T := mem_T_of_le hρ hρ1 (zero_le : (0 : Ordinal.{0}) ≤ ρ)
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hρ) hρ1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  obtain ⟨-, -, hNT, -, hN1, -, -, -⟩ := vz_th_facts hρ hρ1 hN h0T (Ordinal.omega_pos 1)
  have hv1 : v < Om1 := hv.trans hN1
  have hvT : v ∈ Tset ρ := (hTm v hv1).2 (hv.trans ((hTm _ hN1).1 hNT))
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨cst v, hvρ, rfl⟩
  by_cases hI : Indec v
  · by_cases hE : InE v
    · rcases eq_or_lt_of_le hρv with rfl | hρv'
      · exact ⟨bs, trivial, rfl⟩
      obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρ hρ1 hvT hρv hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hρ hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv', by rw [hξv]; exact hE⟩
      have hξN : ξ < Om1 * (N : Ordinal.{0}) + 0 :=
        vzLt_of_vt_lt hρ hρ1 hξT hξ2 h0T (Ordinal.omega_pos 1) (by rw [hξv]; exact hE.pos)
          (by rw [hξv]; exact hv)
      obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
      set q := ξ / Om1 with hq
      set r := ξ % Om1 with hr
      have hqN : q < (N : Ordinal.{0}) := by
        have h1 : Om1 * q < Om1 * (N : Ordinal.{0}) := by
          calc Om1 * q ≤ ξ := hdec ▸ le_self_add
            _ < Om1 * (N : Ordinal.{0}) := by rw [add_zero] at hξN; exact hξN
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
      obtain ⟨t, ht, et⟩ := IH r hrv (hrv.trans hv)
      exact ⟨th q' t, ⟨hq'1, ht⟩, by rw [val_th, et, e, hξv]⟩
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨t, ht, e⟩ := IH L hL (hL.trans hv)
      exact ⟨pw t, ht, by rw [val_pw, e]⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρ.pos hρv).ne'
    obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
    exact ⟨sm s1 s2, ⟨h1, h2⟩, by rw [val_sm, e1, e2, hsum]⟩

/-! ## Lemma RS -/

/-- A term without `bs` and `th` has a constant value. -/
theorem vzv_noB : ∀ t : VzTm, noB t → ∀ x y, val t x = val t y
  | cst _, _, _, _ => rfl
  | bs, h, _, _ => absurd h id
  | th _ _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, vzv_noB a h.1 x y, vzv_noB b h.2 x y]
  | pw t, h, x, y => by simp only [val_pw, vzv_noB t h x y]

/-- A term with `bs` or `th` has value `≥ x`. -/
theorem le_vzv_of_not_noB {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : VzTm, CBt t x → ¬ noB t → x ≤ val t x
  | cst _, _, h => absurd trivial h
  | bs, _, _ => le_rfl
  | th n t, hc, _ => by
    obtain ⟨h1, h2⟩ := vzv_T hx hx1 t hc.2
    exact (vz_th_facts hx hx1 hc.1 h1 h2).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [noB, not_and_or] at h
    rcases h with h | h
    · exact (le_vzv_of_not_noB hx hx1 a hc.1 h).trans le_self_add
    · exact (le_vzv_of_not_noB hx hx1 b hc.2 h).trans le_add_self
  | pw t, hc, h => (le_vzv_of_not_noB hx hx1 t hc h).trans (right_le_opow _ one_lt_omega0)

/-- **Lemma RS with the target `t(ρ)`** (`t(ρ) ≥ ρ`, constants below `ρ`). -/
theorem rs_rstVz {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {s : VzTm} (hs : CBt s (upsilon r)) (hρs : upsilon r ≤ val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ (cst' s).toFinset, c < σ) → CBt s σ := fun σ hσ =>
    cbt_iff s _ σ hs (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := val s) (C := (cst' s).toFinset) h
    (fun c hc => cbt_cst s _ hs c (List.mem_toFinset.1 hc)) hρs
    (vzv_lt_ups h.ρE h.ρ1 hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (vzv_pi hσ h.ρU hB s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact vzv_lt_next hσE (hσρ.trans h.ρ1) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `VzTm`** with constants below `ρ_λ`. -/
theorem rsStep_Vz {l : Ordinal.{0}} {s : VzTm} (hs : CBt s (upsilon l)) : RsStep l (val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ val s (upsilon l)
  · exact rs_rstVz R hs hρs htg
  · have hn : noB s := by
      by_contra hn
      exact hρs (le_vzv_of_not_noB R.ρE R.ρ1 s hs hn)
    set c := val s (upsilon l) with hc
    have e : val s = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, vzv_noB s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have := rs_rstT R hcb htg
    rwa [OT.ev_k] at this

end Googology.Trans.PoR.InaccPsi.R2
