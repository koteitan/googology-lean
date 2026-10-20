import Googology.Trans.PoR.InaccPsi.R2.LvLoc

/-!
# The term system of the levels `x·(k+1) + b` (`k < ω`, `b < x`): grammar, top `ϑˣ(Ω₁·(x·ω))`, EXACT

`LvWT`: constants, the base, `ϑˣ(Ω₁·b + t)` for a constant level `1 ≤ b < x` (`th0`), `ϑˣ(Ω₁·(x·(k+1) + b) + t)` for
`k < ω`, `b < x` (`th k b`), sums, `ω^t`; top `lvwTop x = ϑˣ(Ω₁·(x·ω))`.  From the axioms of `R2.CitedLu` and
`R2.CitedLv`:

* `LvWT.lvw_T` (a term with constants below `x` denotes a member of `Tˣ` below the top), `LvWT.lvw_rep` (every
  ordinal below the top is such a term), `LvWT.pi` (**Lemma EXACT**: the base change `π_{σ,ρ}` maps the value at `ρ`
  to the value at `σ`), `LvWT.uni_le`, `lvw_small`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The new top, at the level `x·ω`. -/
noncomputable def lvwTop (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * (x * ω))

/-- The level `x·(k+1) + b`. -/
noncomputable def lvwL (x : Ordinal.{0}) (k : ℕ) (b : Ordinal.{0}) : Ordinal.{0} :=
  x * ((k : Ordinal.{0}) + 1) + b

/-- Terms at the levels `x·(k+1) + b`. -/
inductive LvWT : Type 1
  | cst : Ordinal.{0} → LvWT
  | bs : LvWT
  | th0 : Ordinal.{0} → LvWT → LvWT
  | th : ℕ → Ordinal.{0} → LvWT → LvWT
  | sm : LvWT → LvWT → LvWT
  | pw : LvWT → LvWT

namespace LvWT

/-- Value of a term at base `x`. -/
noncomputable def val : LvWT → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | th k b t, x => vt x (Om1 * lvwL x k b + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- Constants in the term, including the parameters `b` of the levels. -/
def cs : LvWT → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th0 b t => b :: cs t
  | th _ b t => b :: cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- The side condition: all constants and level parameters below the base. -/
def CBt : LvWT → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | th _ b t, x => b < x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- A term is base-independent only when it contains no theta or base constructor. -/
def noB : LvWT → Prop
  | cst _ => True
  | bs => False
  | th0 _ _ => False
  | th _ _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : LvWT) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_th (k : ℕ) (b : Ordinal.{0}) (t : LvWT) (x : Ordinal.{0}) :
    val (th k b t) x = vt x (Om1 * lvwL x k b + val t x) := rfl
@[simp] theorem val_sm (a b : LvWT) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LvWT) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

end LvWT

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `x·ω = ω^{x+1}` lies in `Tˣ ∩ Ω₁`. -/
theorem lvw_xw : x * ω ∈ Tset x ∧ x * ω < Om1 := by
  obtain ⟨m, hxm, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
  have e : x * ω = ω ^ (x + 1) := by rw [opow_add, opow_one, show ω ^ x = x from hx]
  have hlt : x * ω < m := by rw [e]; exact hmE.opow_lt ((inE_indec hmE).add_lt hxm (Lu.lu_one_lt_E hmE))
  exact ⟨(hTm _ (hlt.trans hm1)).2 hlt, hlt.trans hm1⟩

/-- The facts on a level `x·(k+1) + b`, `b < x`. -/
theorem lvwL_facts {k : ℕ} {b : Ordinal.{0}} (hb : b < x) :
    lvwL x k b ∈ Tset x ∧ x ≤ lvwL x k b ∧ lvwL x k b < x * ω ∧ lvwL x k b < Om1 := by
  obtain ⟨hwT, hw1⟩ := lvw_xw hx hx1
  have hlt : lvwL x k b < x * ω := by
    unfold lvwL
    calc x * ((k : Ordinal.{0}) + 1) + b < x * ((k : Ordinal.{0}) + 1) + x := (add_lt_add_iff_left _).2 hb
      _ = x * ((k : Ordinal.{0}) + 1 + 1) := (mul_add_one x _).symm
      _ < x * ω := by
        refine (mul_lt_mul_iff_right₀ hx.pos).2 ?_
        exact_mod_cast natCast_lt_omega0 (k + 1 + 1)
  have hge : x ≤ lvwL x k b := by
    unfold lvwL
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * ((k : Ordinal.{0}) + 1) := mul_le_mul_right (le_add_self) x
      _ ≤ _ := le_self_add
  exact ⟨vz_T_down hx hx1 hwT hw1 hlt.le, hge, hlt, hlt.trans hw1⟩

theorem lvwTop_facts :
    Om1 * (x * ω) ∈ Tset x ∧ Om1 * (x * ω) < OmTwo ∧ lvwTop x ∈ Tset x ∧
      x < lvwTop x ∧ lvwTop x < Om1 ∧ InE (lvwTop x) ∧ x * ω < lvwTop x := by
  obtain ⟨hwT, hw1⟩ := lvw_xw hx hx1
  have hxw : x ≤ x * ω := Ordinal.le_mul_left x omega0_pos
  obtain ⟨a, b, c, d, e, f, -, g, -⟩ :=
    Lv.gen_facts hx hx1 hwT hxw hw1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  simp only [add_zero] at a b c d e f g
  exact ⟨a, b, c, d, e, f, g⟩

/-- Below the top: `ϑˣ(Ω₁·β + η) < ϑˣ(Ω₁·(x·ω))` for a level `β ∈ Tˣ`, `β < x·ω`, and `η < ϑˣ(Ω₁·(x·ω))`. -/
theorem lvw_lt_top {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβ : β < x * ω) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : η < lvwTop x) : vt x (Om1 * β + η) < lvwTop x := by
  obtain ⟨hwT, hw1⟩ := lvw_xw hx hx1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := lvwTop_facts hx hx1
  have e : lvwTop x = vt x (Om1 * (x * ω) + 0) := by rw [add_zero]; rfl
  rw [e] at h hwt ⊢
  refine lvVt_lt_gen hx hx1 hβT (hβ.trans hw1) hwT (Ordinal.le_mul_left x omega0_pos) hw1 hη hη1
    (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1) ?_ (hβ.trans hwt) h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * (x * ω) := mul_le_mul_right (add_one_le_of_lt hβ) Om1

/-- An `ε`-number `ϑˣ(ξ) ∈ (x, ϑˣ(Ω₁·(x·ω)))` has the argument quotient `ξ / Ω₁ < x·ω`. -/
theorem lvw_quot_top {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hxξ : x < vt x ξ)
    (hE : InE (vt x ξ)) (h : vt x ξ < lvwTop x) : ξ / Om1 < x * ω := by
  obtain ⟨hwT, hw1⟩ := lvw_xw hx hx1
  have hwξ : x * ω < vt x ξ := by
    have e : x * ω = ω ^ (x + 1) := by rw [opow_add, opow_one, show ω ^ x = x from hx]
    rw [e]; exact hE.opow_lt ((inE_indec hE).add_lt hxξ (Lu.lu_one_lt_E hE))
  have hlt : ξ < Om1 * (x * ω) + 0 :=
    lvLt_of_vt_lt hx hx1 hξT hξ2 hwT (Ordinal.le_mul_left x omega0_pos) hw1 (mem_T_of_le hx hx1 zero_le)
      (Ordinal.omega_pos 1) (hx.pos.trans hxξ) hwξ (by rw [add_zero]; exact h)
  have h1 : Om1 * (ξ / Om1) < Om1 * (x * ω) := by
    calc Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
      _ < Om1 * (x * ω) := by simpa using hlt
  exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1

/-- A level `x ≤ q < x·ω` is `x·(k+1) + b` with `b < x`. -/
theorem lvw_split {q : Ordinal.{0}} (hxq : x ≤ q) (hq : q < x * ω) : ∃ k : ℕ, ∃ b, b < x ∧ lvwL x k b = q := by
  have hx0 : x ≠ 0 := hx.pos.ne'
  have hdm : x * (q / x) + q % x = q := div_add_mod q x
  have hr : q % x < x := mod_lt q hx0
  have hqω : q / x < ω := by
    have h0 : x * (q / x) ≤ q := by
      calc x * (q / x) ≤ x * (q / x) + q % x := le_self_add
        _ = q := hdm
    have h1 : x * (q / x) < x * ω := lt_of_le_of_lt h0 hq
    exact (mul_lt_mul_iff_right₀ hx.pos).1 h1
  have hq1 : 1 ≤ q / x := by
    rcases eq_or_ne (q / x) 0 with h0 | h0
    · rw [h0, mul_zero, zero_add] at hdm
      exact absurd (hdm ▸ hr) (not_lt.2 hxq)
    · exact one_le_iff_ne_zero.2 h0
  obtain ⟨n, hn⟩ := lt_omega0.1 hqω
  have hn1 : 1 ≤ n := by
    have h : (1 : Ordinal.{0}) ≤ (n : Ordinal.{0}) := hn ▸ hq1
    exact_mod_cast h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨k, q % x, hr, ?_⟩
  unfold lvwL
  rw [← Nat.cast_succ, ← hn, hdm]

end Base

namespace LvWT

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The terms denote members of `Tˣ` below the top. -/
theorem lvw_T : ∀ t : LvWT, CBt t x → val t x ∈ Tset x ∧ val t x < lvwTop x
  | .cst a, h => by
      obtain ⟨-, -, hTopT, hxt, hTop1, -, -⟩ := lvwTop_facts hx hx1
      exact ⟨vz_T_down hx hx1 hTopT hTop1 (h.trans hxt).le, h.trans hxt⟩
  | .bs, _ => by
      obtain ⟨-, -, -, hxt, -, -, -⟩ := lvwTop_facts hx hx1
      exact ⟨mem_T_of_le hx hx1 le_rfl, hxt⟩
  | .th0 b t, h => by
      obtain ⟨htT, htLt⟩ := lvw_T t h.2.2
      obtain ⟨-, -, -, -, hTop1, -, -⟩ := lvwTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt (h.2.1.trans hx1) ht1
      have hb : b < x * ω := h.2.1.trans_le (Ordinal.le_mul_left x omega0_pos)
      exact ⟨(vt_memTwo hx hx1 hargT harg2).1,
        lvw_lt_top hx hx1 (mem_T_of_le hx hx1 h.2.1.le) hb htT ht1 htLt⟩
  | .th k b t, h => by
      obtain ⟨htT, htLt⟩ := lvw_T t h.2
      obtain ⟨-, -, -, -, hTop1, -, -⟩ := lvwTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      obtain ⟨hLT, hxL, hLw, hL1⟩ := lvwL_facts hx hx1 (k := k) h.1
      have hargT := lvArg_mem hx hx1 hLT hxL hL1 htT ht1
      have harg2 := Lu.luOm1_mul_lt hL1 ht1
      exact ⟨(vt_memTwo hx hx1 hargT harg2).1, lvw_lt_top hx hx1 hLT hLw htT ht1 htLt⟩
  | .sm a b, h => by
      obtain ⟨haT, haLt⟩ := lvw_T a h.1
      obtain ⟨hbT, hbLt⟩ := lvw_T b h.2
      obtain ⟨-, -, -, -, -, hTopE, -⟩ := lvwTop_facts hx hx1
      exact ⟨vzT_add hx hx1 haT hbT, (inE_indec hTopE).add_lt haLt hbLt⟩
  | .pw t, h => by
      obtain ⟨htT, htLt⟩ := lvw_T t h
      obtain ⟨-, -, hTopT, -, hTop1, hTopE, -⟩ := lvwTop_facts hx hx1
      have hw : ω ^ val t x < lvwTop x := hTopE.opow_lt htLt
      exact ⟨vz_T_down hx hx1 hTopT hTop1 hw.le, hw⟩

/-- **Representation**: every ordinal below the top is the value of a term with constants below the base. -/
theorem lvw_rep : ∀ v, v < lvwTop x → ∃ t : LvWT, CBt t x ∧ val t x = v := by
  obtain ⟨-, -, hTopT, -, hTop1, -, -⟩ := lvwTop_facts hx hx1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
    intro hv
    have hv1 : v < Om1 := hv.trans hTop1
    have hvT : v ∈ Tset x := vz_T_down hx hx1 hTopT hTop1 hv.le
    rcases lt_or_ge v x with hvx | hxv
    · exact ⟨.cst v, hvx, rfl⟩
    by_cases hI : Indec v
    · by_cases hE : InE v
      · rcases eq_or_lt_of_le hxv with rfl | hxv'
        · exact ⟨.bs, trivial, rfl⟩
        obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv hv1 (inE_indec hE)
        have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv', by rw [hξv]; exact hE⟩
        obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hx hx1 hξT hξ2 hΩξ
        have hqw : ξ / Om1 < x * ω :=
          lvw_quot_top hx hx1 hξT hξ2 (by rw [hξv]; exact hxv') (by rw [hξv]; exact hE) (by rw [hξv]; exact hv)
        rcases lt_or_ge (ξ / Om1) x with hqx | hqx
        · have hrv : ξ % Om1 < v := by
            have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th0 (ξ / Om1) t, ⟨hq1, hqx, ht⟩, by rw [val_th0, he, hdec, hξv]⟩
        · obtain ⟨k, b, hbx, hkb⟩ := lvw_split hx hx1 hqx hqw
          have hqT : ξ / Om1 ∈ Tset x := by rw [← hkb]; exact (lvwL_facts hx hx1 hbx).1
          have hrv : ξ % Om1 < v := by
            have h := (lvLevel_lt_vt hx hx1 hqT hqx ((lvw_xw hx hx1).2.trans' hqw) hrT hr1).2
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th k b t, ⟨hbx, ht⟩, by rw [val_th, he, hkb, hdec, hξv]⟩
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
          (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
        obtain ⟨t, ht, e⟩ := IH L hL (hL.trans hv)
        exact ⟨.pw t, ht, by rw [val_pw, e]⟩
    · have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hx.pos hxv).ne'
      obtain ⟨s1, h1, e1⟩ := IH u1 hu1 (hu1.trans hv)
      obtain ⟨s2, h2, e2⟩ := IH u2 hu2 (hu2.trans hv)
      exact ⟨.sm s1 s2, ⟨h1, h2⟩, by rw [val_sm, e1, e2, hsum]⟩

omit hx hx1 in
/-- A term without a base or theta constructor has constant value. -/
theorem noB_val : ∀ t : LvWT, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .th _ _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

omit hx hx1 in
/-- The side condition depends only on the listed constants. -/
theorem cbt_iff {t : LvWT} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
  | th0 b t ih =>
      refine ⟨h.1, hy b (by simp [cs]), ?_⟩
      exact ih h.2.2 (fun c hc => hy c (by simp [cs, hc]))
  | th k b t ih =>
      refine ⟨hy b (by simp [cs]), ?_⟩
      exact ih h.2 (fun c hc => hy c (by simp [cs, hc]))
  | sm a b iha ihb =>
      exact ⟨iha h.1 (fun c hc => hy c (by simp [cs, hc])),
        ihb h.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | pw t ih => exact ih h (fun c hc => hy c (by simpa [cs] using hc))

end Base

/-- All explicit constants and level parameters are below the base. -/
theorem cbt_cst {ρ : Ordinal.{0}} {s : LvWT} (hs : CBt s ρ) : ∀ c ∈ cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [cs] at hc
  | th0 b t ih =>
      intro c hc
      simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.2.1
      · exact ih hs.2.2 c hc
  | th k b t ih =>
      intro c hc
      simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.1
      · exact ih hs.2 c hc
  | sm a b iha ihb =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hs.1 c hc
      · exact ihb hs.2 c hc
  | pw t ih => intro c hc; exact ih hs c (by simpa [cs] using hc)

/-- The side condition is monotone in the base. -/
theorem CBt.mono {s : LvWT} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y :=
  cbt_iff hs (fun c hc => (cbt_cst hs c hc).trans_le hxy)

/-- A term containing a base-dependent constructor has value at least its base. -/
theorem le_of_not_noB {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LvWT, CBt t x → ¬ noB t → x ≤ val t x
  | .cst _, _, h => absurd trivial h
  | .bs, _, _ => le_rfl
  | .th0 b t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lvw_T hx hx1 t hc.2.2
      have ht1 : val t x < Om1 := htLt.trans (lvwTop_facts hx hx1).2.2.2.2.1
      exact (Lu.lu_th_facts hx hx1 hc.1 hc.2.1 htT ht1).2.2.2.1.le
  | .th k b t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lvw_T hx hx1 t hc.2
      have ht1 : val t x < Om1 := htLt.trans (lvwTop_facts hx hx1).2.2.2.2.1
      obtain ⟨hLT, hxL, -, hL1⟩ := lvwL_facts hx hx1 (k := k) hc.1
      exact (Lv.gen_facts hx hx1 hLT hxL hL1 htT ht1).2.2.2.1.le
  | .sm a b, hc, hn => by
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (le_of_not_noB hx hx1 a hc.1 hn).trans le_self_add
      · exact (le_of_not_noB hx hx1 b hc.2 hn).trans le_add_self
  | .pw t, hc, hn =>
      (le_of_not_noB hx hx1 t hc hn).trans (right_le_opow _ one_lt_omega0)

/-- The top lies below every next point above the base. -/
theorem lvw_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u)
    (hu : LtInf1 u) : lvwTop x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, hT, -, htop1, -, -⟩ := lvwTop_facts hx hx1
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

theorem lvw_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvWT}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (lvw_T hx hx1 t ht).2.trans (lvw_top_lt_next hx hx1 hxu hu)

theorem lvw_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvWT}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lvw_lt_next hx hx1 ht hxu hu.2

/-- The level `ρ·(k+1) + b` under the base map: `π(ρ·(k+1) + b) = σ·(k+1) + b`. -/
theorem pi_lvwL {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (k : ℕ) {b : Ordinal.{0}} (hb : b < σ) :
    lvwL ρ k b ∈ TB ρ σ ∧ pi σ ρ (lvwL ρ k b) = lvwL σ k b := by
  obtain ⟨h1, h2⟩ := pi_mul_nat hB (pi_base hB).1 (pi_base hB).2 (k + 1)
  rw [Nat.cast_succ] at h1 h2
  have hbTB := mem_TB_of_lt hB hb
  obtain ⟨h3, h4⟩ := pi_add hB h1 hbTB
  exact ⟨h3, by unfold lvwL; rw [h4, h2, pi_lt hB hb]⟩

/-- The theta term at the level `ρ·(k+1) + b` commutes with `π`. -/
theorem pi_vt_lvw {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (k : ℕ) {b η : Ordinal.{0}} (hb : b < σ)
    (hη : η ∈ TB ρ σ) (hη1 : η < Om1) :
    vt ρ (Om1 * lvwL ρ k b + η) ∈ TB ρ σ ∧
      pi σ ρ (vt ρ (Om1 * lvwL ρ k b + η)) = vt σ (Om1 * lvwL σ k b + pi σ ρ η) := by
  obtain ⟨hLTB, hLpi⟩ := pi_lvwL hB k hb
  obtain ⟨-, hρL, -, hL1⟩ := lvwL_facts hB.2.1 hB.2.2.2 (k := k) (hb.trans hB.2.2.1)
  have hmul := lvPi_mul hB hLTB hρL hL1
  have hadd := pi_add hB hmul.1 hη
  have harg2 := Lu.luOm1_mul_lt hL1 hη1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 hadd.1.1 harg2
  exact ⟨⟨hvT, by rw [hvP]; exact hadd.1.2⟩,
    by rw [pi_vt_two hB hadd.1 harg2, hadd.2, hmul.2, hLpi]⟩

/-- **Lemma EXACT** for `LvWT`: the value maps to the same term at the smaller base. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LvWT, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have ht1 : val t ρ < Om1 :=
        (lvw_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)).2.trans
          (lvwTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := LvT.pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .th k b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2
      have ht1 : val t ρ < Om1 :=
        (lvw_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2)).2.trans
          (lvwTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := pi_vt_lvw hB k h.1 h1 ht1
      simp only [val_th]
      exact ⟨h3, by rw [h4, h2]⟩
  | .sm a b, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB a h.1
      obtain ⟨h3, h4⟩ := pi hσ hρ hB b h.2
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      simp only [val_sm]
      exact ⟨h5, by rw [h6, h2, h4]⟩
  | .pw t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h
      have ht1 : val t ρ < Om1 :=
        (lvw_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h)).2.trans
          (lvwTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvWT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvWT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB ht hu, uni_le hσ hρ hB hu ht]

end LvWT

/-- The `small` field: a term is base-independent or at least the base. -/
theorem lvw_small : ∀ t : LvWT,
    (∀ x y, LvWT.val t x = LvWT.val t y) ∨
      (∀ x, InE x → x < Om1 → LvWT.CBt t x → x ≤ LvWT.val t x) := by
  intro t
  by_cases h : LvWT.noB t
  · exact Or.inl (LvWT.noB_val t h)
  · exact Or.inr (fun x hx hx1 hc => LvWT.le_of_not_noB hx hx1 t hc h)

end Googology.Trans.PoR.InaccPsi.R2
