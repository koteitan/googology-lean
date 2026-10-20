import Googology.Trans.PoR.InaccPsi.R2.LvTh
import Googology.Trans.PoR.InaccPsi.R2.CitedVz
import Googology.Trans.PoR.InaccPsi.R2.VzL
import Googology.Trans.PoR.InaccPsi.R2.LamLt
import Googology.Trans.PoR.InaccPsi.R2.LuTh
import Googology.Trans.PoR.InaccPsi.R2.LuTm

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-- The new top, at the level `x+x`. -/
noncomputable def lvTop (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * (x + x))

/-- Terms at the first level depending on the base: `ϑˣ(Ω₁·(x+b)+t)` for `b<x`. -/
inductive LvT : Type 1
  | cst : Ordinal.{0} → LvT
  | bs : LvT
  | th0 : Ordinal.{0} → LvT → LvT
  | th : Ordinal.{0} → LvT → LvT
  | sm : LvT → LvT → LvT
  | pw : LvT → LvT

namespace LvT

/-- Value of a family term at base `x`. -/
noncomputable def val : LvT → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | th b t, x => vt x (Om1 * (x + b) + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- Constants in the term, including the parameter `b` in a base-dependent level. -/
def cs : LvT → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th0 b t => b :: cs t
  | th b t => b :: cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- The side condition that all constants and level parameters are below the base. -/
def CBt : LvT → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | th b t, x => b < x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- A term is base-independent only when it contains no theta or base constructor. -/
def noB : LvT → Prop
  | cst _ => True
  | bs => False
  | th0 _ _ => False
  | th _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : LvT) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_th (b : Ordinal.{0}) (t : LvT) (x : Ordinal.{0}) :
    val (th b t) x = vt x (Om1 * (x + b) + val t x) := rfl
@[simp] theorem val_sm (a b : LvT) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LvT) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

end LvT

namespace LvT

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lvTop_facts :
    Om1 * (x + x) ∈ Tset x ∧ Om1 * (x + x) < OmTwo ∧ lvTop x ∈ Tset x ∧
      x < lvTop x ∧ lvTop x < Om1 ∧ InE (lvTop x) := by
  have hxxT : x ∈ Tset x := mem_T_of_le hx hx1 le_rfl
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have hβT : x + x ∈ Tset x := vzT_add hx hx1 hxxT hxxT
  have hβ : x ≤ x + x := le_self_add
  have hβ1 : 1 ≤ x + x := (Lu.lu_one_lt_E hx).le.trans hβ
  have hβ1O : x + x < Om1 := Om1_add_lt hx1 hx1
  have hargT0 := lvArg_mem hx hx1 hβT hβ hβ1O h0T (Ordinal.omega_pos 1)
  have hargT : Om1 * (x + x) ∈ Tset x := by simpa using hargT0
  have harg2 : Om1 * (x + x) < OmTwo := by
    simpa using Lu.luOm1_mul_lt hβ1O (Ordinal.omega_pos 1)
  have hOm : Om1 ≤ Om1 * (x + x) := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * (x + x) := mul_le_mul_right hβ1 Om1
  have hE := (vt_E_iff hx hx1 hargT harg2).2 hOm
  obtain ⟨hvT, hxv, hv1, hvE⟩ := vt_memTwo hx hx1 hargT harg2
  exact ⟨hargT, harg2, hvT, hE.1, hv1, hE.2⟩

/-- The new top lies below every `<₁ ∞`-point above the base. -/
theorem lvTop_lt_next {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : lvTop x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, hTopT, -, hTop1, -⟩ := lvTop_facts hx hx1
  have hTopm : lvTop x < m := (hTm _ hTop1).1 hTopT
  exact lt_of_lt_of_le hTopm (hmin u hxu hu)

/-- The first family grammar stays below `lvTop` and denotes members of `Tˣ`. -/
theorem lv_T : ∀ t : LvT, CBt t x → val t x ∈ Tset x ∧ val t x < lvTop x
  | .cst a, h => by
      obtain ⟨-, -, hTopT, -, hTop1, -⟩ := lvTop_facts hx hx1
      have hTop := (lvTop_facts hx hx1).2.2.2.1
      exact ⟨vz_T_down hx hx1 hTopT hTop1 (h.trans hTop).le, (h.trans hTop)⟩
  | .bs, _ => by
      obtain ⟨-, -, -, hxt, -, -⟩ := lvTop_facts hx hx1
      exact ⟨mem_T_of_le hx hx1 le_rfl, hxt⟩
  | .th0 b t, h => by
      obtain ⟨htT, htLt⟩ := lv_T t h.2.2
      obtain ⟨-, -, -, hxTop, hTop1, -⟩ := lvTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      have hb1 : b < Om1 := h.2.1.trans hx1
      have hbT : b ∈ Tset x := mem_T_of_le hx hx1 h.2.1.le
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt hb1 ht1
      obtain ⟨hvT, -, -, -, -⟩ := vt_memTwo hx hx1 hargT harg2
      have hTopT : x + x ∈ Tset x := vzT_add hx hx1
        (mem_T_of_le hx hx1 le_rfl) (mem_T_of_le hx hx1 le_rfl)
      have hTop1 : x + x < Om1 := Om1_add_lt hx1 hx1
      have hTopArgT := lvArg_mem hx hx1 hTopT le_self_add hTop1
        (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
      have hTopArg2 : Om1 * (x + x) + 0 < OmTwo := by
        simpa using Lu.luOm1_mul_lt hTop1 (Ordinal.omega_pos 1)
      have hxTop : x < lvTop x := (lvTop_facts hx hx1).2.2.2.1
      have hηTop : val t x < lvTop x := htLt
      have hββ : b < x + x := h.2.1.trans (lt_add_of_pos_right x hx.pos)
      have hvLt := lvVt_lt hx hx1 hbT hb1 hTopT le_self_add hTop1
        htT ht1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
        hββ
        (by
          have hh : Om1 * b + val t x < Om1 * (x + x) + 0 := by
            rw [add_zero]
            calc
              Om1 * b + val t x < Om1 * b + Om1 := (add_lt_add_iff_left _).2 ht1
              _ = Om1 * (b + 1) := by rw [mul_add_one]
              _ ≤ Om1 * (x + x) := mul_le_mul_right (Order.add_one_le_of_lt hββ) Om1
          simpa using hh) (by simpa [lvTop, add_zero] using (h.2.1.trans hxTop))
        (by simpa [lvTop, add_zero] using hηTop)
      exact ⟨hvT, by simpa [lvTop] using hvLt⟩
  | .th b t, h => by
      obtain ⟨htT, htLt⟩ := lv_T t h.2
      obtain ⟨hTopArgT, hTopArg2, hTopT, hxt, hTop1, hTopE⟩ := lvTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      have hb1 : b < Om1 := h.1.trans hx1
      have hβT : x + b ∈ Tset x := vzT_add hx hx1 (mem_T_of_le hx hx1 le_rfl)
        (mem_T_of_le hx hx1 h.1.le)
      have hβx : x ≤ x + b := le_self_add
      have hβ1 : 1 ≤ x + b := (Lu.lu_one_lt_E hx).le.trans hβx
      have hβ1O : x + b < Om1 := Om1_add_lt hx1 hb1
      have hargT := lvArg_mem hx hx1 hβT hβx hβ1O htT ht1
      have harg2 : Om1 * (x + b) + val t x < OmTwo :=
        Lu.luOm1_mul_lt hβ1O ht1
      have hββ : x + b < x + x := add_lt_add_right h.1 x
      have hβTargetT : x + x ∈ Tset x := vzT_add hx hx1 (mem_T_of_le hx hx1 le_rfl)
        (mem_T_of_le hx hx1 le_rfl)
      have hβTargetx : x ≤ x + x := le_self_add
      have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
      have hβTop : x + b < lvTop x := hTopE.add_lt hxt (h.1.trans hxt)
      have hηTop : val t x < lvTop x := htLt
      have hargLt : Om1 * (x + b) + val t x < Om1 * (x + x) := by
        have h1 : Om1 * (x + b) + val t x < Om1 * ((x + b) + 1) := by
          calc
            Om1 * (x + b) + val t x < Om1 * (x + b) + Om1 :=
              (add_lt_add_iff_left (Om1 * (x + b))).2 ht1
            _ = Om1 * (x + b) + Om1 * 1 := by rw [mul_one]
            _ = Om1 * ((x + b) + 1) := (mul_add _ _ _).symm
        have h2 : (x + b) + 1 ≤ x + x := Order.add_one_le_of_lt hββ
        exact h1.trans_le (mul_le_mul_right h2 Om1)
      have hTargetBeta1O : x + x < Om1 := Om1_add_lt hx1 hx1
      have hv := lvVt_lt hx hx1 hβT hβ1O hβTargetT hβTargetx hTargetBeta1O
        htT ht1 h0T (Ordinal.omega_pos 1) hββ (by simpa using hargLt)
        (by simpa [lvTop] using hβTop) (by simpa [lvTop] using hηTop)
      have hvT := (vt_memTwo hx hx1 hargT harg2).1
      exact ⟨hvT, by simpa [lvTop] using hv⟩
  | .sm a b, h => by
      obtain ⟨haT, haLt⟩ := lv_T a h.1
      obtain ⟨hbT, hbLt⟩ := lv_T b h.2
      obtain ⟨-, -, hTopT, -, hTop1, hTopE⟩ := lvTop_facts hx hx1
      exact ⟨vzT_add hx hx1 haT hbT, hTopE.add_lt haLt hbLt⟩
  | .pw t, h => by
      obtain ⟨htT, htLt⟩ := lv_T t h
      obtain ⟨-, -, hTopT, -, hTop1, hTopE⟩ := lvTop_facts hx hx1
      have hw : ω ^ val t x < lvTop x := hTopE.opow_lt htLt
      exact ⟨vz_T_down hx hx1 hTopT hTop1 hw.le, hw⟩

/-- Every ordinal below the new top is represented by a base-dependent or lower-level term. -/
theorem lv_rep : ∀ v, v < lvTop x → ∃ t : LvT, CBt t x ∧ val t x = v := by
  obtain ⟨hTopArgT, hTopArg2, hTopT, hxTop, hTop1, hTopE⟩ := lvTop_facts hx hx1
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
        set q := ξ / Om1 with hq
        set r := ξ % Om1 with hr
        have hxxT : x + x ∈ Tset x := vzT_add hx hx1
          (mem_T_of_le hx hx1 le_rfl) (mem_T_of_le hx hx1 le_rfl)
        have hxx1 : x + x < Om1 := Om1_add_lt hx1 hx1
        have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
        have hxxv : x + x < v := (inE_indec hE).add_lt hxv' hxv'
        have hξlt : ξ < Om1 * (x + x) + 0 :=
          lvLt_of_vt_lt hx hx1 hξT hξ2 hxxT le_self_add hxx1 h0T (Ordinal.omega_pos 1)
            (by rw [hξv]; exact hx.pos.trans hxv') (by rw [hξv]; exact hxxv)
            (by rw [hξv, add_zero]; exact hv)
        have hqLt : q < x + x := by
          have h1 : Om1 * q < Om1 * (x + x) := by
            calc Om1 * q ≤ ξ := mul_div_le ξ Om1
              _ < Om1 * (x + x) := by simpa using hξlt
          exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
        have hqT : q ∈ Tset x := vz_T_down hx hx1 hxxT hxx1 hqLt.le
        have hq1Om : q < Om1 := hqLt.trans hxx1
        have hqTlow : q ∈ Tset x := vz_T_down hx hx1 hxxT hxx1 hqLt.le
        have hr_lt_v : r < v := by
          rcases lt_or_ge q x with hqx | hqx
          · have hθ := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [← hξv, ← hdec, hq, hr]
            simpa [q, r] using hθ
          · let b := q - x
            have hqb : x + b = q := Ordinal.add_sub_cancel_of_le hqx
            have hbx : b < x := by
              by_contra h
              push Not at h
              have hxxq : x + x ≤ x + b := add_le_add_right h x
              rw [hqb] at hxxq
              exact (not_le_of_gt hqLt) hxxq
            have hθ := lvLt_vt_self_tau_add hx hx1 hbx hrT hr1
            rw [← hξv, ← hdec, hq, hr]
            simpa [q, r, hqb] using hθ
        obtain ⟨t, ht, he⟩ := IH r hr_lt_v (hr_lt_v.trans hv)
        rcases lt_or_ge q x with hqx | hqx
        · exact ⟨.th0 q t, ⟨hq1, hqx, ht⟩, by rw [val_th0, he, ← hξv, ← hdec]⟩
        · let b := q - x
          have hqb : x + b = q := Ordinal.add_sub_cancel_of_le hqx
          have hbx : b < x := by
            by_contra h
            push Not at h
            have hxxq : x + x ≤ x + b := add_le_add_right h x
            rw [hqb] at hxxq
            exact (not_le_of_gt hqLt) hxxq
          exact ⟨.th b t, ⟨hbx, ht⟩, by rw [val_th, he, hqb, ← hξv, ← hdec]⟩
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
theorem noB_val : ∀ t : LvT, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .th _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

omit hx hx1 in
/-- Re-establish the side condition at a larger base. -/
theorem cbt_mono {t : LvT} {x y : Ordinal.{0}} (ht : CBt t x) (hxy : x ≤ y) : CBt t y := by
  induction t with
  | cst a => exact ht.trans_le hxy
  | bs => trivial
  | th0 b t ih => exact ⟨ht.1, ht.2.1.trans_le hxy, ih ht.2.2⟩
  | th b t ih => exact ⟨ht.1.trans_le hxy, ih ht.2⟩
  | sm a b iha ihb => exact ⟨iha ht.1, ihb ht.2⟩
  | pw t ih => exact ih ht

omit hx hx1 in
/-- The side condition depends only on the listed constants and the positivity of level parameters. -/
theorem cbt_iff {t : LvT} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
  | th0 b t ih =>
      refine ⟨h.1, hy b (by simp [cs]), ?_⟩
      exact ih h.2.2 (fun c hc => hy c (by simp [cs, hc]))
  | th b t ih =>
      refine ⟨hy b (by simp [cs]), ?_⟩
      exact ih h.2 (fun c hc => hy c (by simp [cs, hc]))
  | sm a b iha ihb =>
      exact ⟨iha h.1 (fun c hc => hy c (by simp [cs, hc])),
        ihb h.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | pw t ih => exact ih h (fun c hc => hy c (by simpa [cs] using hc))

end Base

/-- A term containing a base-dependent constructor has value at least its base. -/
theorem le_of_not_noB {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LvT, CBt t x → ¬ noB t → x ≤ val t x
  | .cst _, _, h => absurd trivial h
  | .bs, _, _ => le_rfl
  | .th0 b t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lv_T hx hx1 t hc.2.2
      have ht1 : val t x < Om1 := htLt.trans (LvT.lvTop_facts hx hx1).2.2.2.2.1
      exact (Lu.lu_th_facts hx hx1 hc.1 hc.2.1 htT ht1).2.2.2.1.le
  | .th b t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lv_T hx hx1 t hc.2
      have ht1 : val t x < Om1 := htLt.trans (LvT.lvTop_facts hx hx1).2.2.2.2.1
      have hβT : x + b ∈ Tset x := vzT_add hx hx1 (mem_T_of_le hx hx1 le_rfl)
        (mem_T_of_le hx hx1 hc.1.le)
      have hβ1 : 1 ≤ x + b := (Lu.lu_one_lt_E hx).le.trans le_self_add
      have hβO : x + b < Om1 := Om1_add_lt hx1 (hc.1.trans hx1)
      have hargT := lvArg_mem hx hx1 hβT le_self_add hβO htT ht1
      have harg2 := Lu.luOm1_mul_lt hβO ht1
      have hOm : Om1 ≤ Om1 * (x + b) + val t x := by
        calc Om1 = Om1 * 1 := (mul_one _).symm
          _ ≤ Om1 * (x + b) := mul_le_mul_right hβ1 Om1
          _ ≤ _ := le_self_add
      exact ((vt_E_iff hx hx1 hargT harg2).2 hOm).1.le
  | .sm a b, hc, hn => by
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (le_of_not_noB hx hx1 a hc.1 hn).trans le_self_add
      · exact (le_of_not_noB hx hx1 b hc.2 hn).trans le_add_self
  | .pw t, hc, hn =>
      (le_of_not_noB hx hx1 t hc hn).trans (right_le_opow _ one_lt_omega0)

/-- The new top lies below every next point above the base. -/
theorem lv_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u)
    (hu : LtInf1 u) : lvTop x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, hT, -, htop1, -⟩ := LvT.lvTop_facts hx hx1
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

/-- Every term lies below the next point above the base. -/
theorem lv_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvT}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (LvT.lv_T hx hx1 t ht).2.trans (lv_top_lt_next hx hx1 hxu hu)

theorem lv_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvT}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lv_lt_next hx hx1 ht hxu hu.2

/-- The base-change map is monotone on term side conditions. -/
theorem CBt.mono {s : LvT} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y := by
  induction s with
  | cst a => exact hs.trans_le hxy
  | bs => trivial
  | th0 b t ih => exact ⟨hs.1, hs.2.1.trans_le hxy, ih hs.2.2⟩
  | th b t ih => exact ⟨hs.1.trans_le hxy, ih hs.2⟩
  | sm a b iha ihb => exact ⟨iha hs.1, ihb hs.2⟩
  | pw t ih => exact ih hs

/-- The higher-level argument transforms under the base map `π`. -/
theorem pi_th_high {σ ρ b η : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < σ)
    (hη : η ∈ TB ρ σ) (hη1 : η < Om1) :
    Om1 * (ρ + b) + η ∈ TB ρ σ ∧
      pi σ ρ (Om1 * (ρ + b) + η) = Om1 * (σ + b) + pi σ ρ η := by
  have hbase := pi_base hB
  have hbTB := mem_TB_of_lt hB hb
  have hβTB := (pi_add hB hbase.1 hbTB).1
  have hβpi : pi σ ρ (ρ + b) = σ + b := by
    rw [(pi_add hB hbase.1 hbTB).2, hbase.2, pi_lt hB hb]
  have hbOm : b < Om1 := lt_trans hb (lt_trans hB.2.2.1 hB.2.2.2)
  have hβ1 : ρ + b < Om1 := Om1_add_lt hB.2.2.2 hbOm
  have hmul := lvPi_mul hB hβTB le_self_add hβ1
  have hadd := pi_add hB hmul.1 hη
  exact ⟨hadd.1, by rw [hadd.2, hmul.2, hβpi]⟩

/-- The higher-level theta term commutes with `π` under the base-dependent parameter. -/
theorem pi_vt_high {σ ρ b η : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < σ)
    (hη : η ∈ TB ρ σ) (hη1 : η < Om1) :
    vt ρ (Om1 * (ρ + b) + η) ∈ TB ρ σ ∧
      pi σ ρ (vt ρ (Om1 * (ρ + b) + η)) = vt σ (Om1 * (σ + b) + pi σ ρ η) := by
  have harg := pi_th_high hB hb hη hη1
  have hbOm : b < Om1 := lt_trans hb (lt_trans hB.2.2.1 hB.2.2.2)
  have harg2 := Lu.luOm1_mul_lt (Om1_add_lt hB.2.2.2 hbOm) hη1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 harg.1.1 harg2
  exact ⟨⟨hvT, by rw [hvP]; exact harg.1.2⟩,
    by rw [pi_vt_two hB harg.1 harg2, harg.2]⟩

theorem pi_vt_low {σ ρ b η : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < σ)
    (hη : η ∈ TB ρ σ) (hη1 : η < Om1) :
    vt ρ (Om1 * b + η) ∈ TB ρ σ ∧
      pi σ ρ (vt ρ (Om1 * b + η)) = vt σ (Om1 * b + pi σ ρ η) := by
  have harg := Googology.Trans.PoR.InaccPsi.R2.Lu.lu_pi_Om1_mul_add hB hb hη
  have harg2 := Lu.luOm1_mul_lt ((hb.trans hB.2.2.1).trans hB.2.2.2) hη1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 harg.1.1 harg2
  exact ⟨⟨hvT, by rw [hvP]; exact harg.1.2⟩,
    by rw [pi_vt_two hB harg.1 harg2, harg.2]⟩

/-- **Lemma EXACT** for `LvT`: the value maps to the same term at the smaller base. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LvT, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have ht1 : val t ρ < Om1 := by
        obtain ⟨-, -, -, -, htop1, -⟩ := lvTop_facts hB.2.1 hB.2.2.2
        exact (lv_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)).2.trans htop1
      obtain ⟨h3, h4⟩ := pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .th b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2
      have ht1 : val t ρ < Om1 := by
        obtain ⟨-, -, -, -, htop1, -⟩ := lvTop_facts hB.2.1 hB.2.2.2
        exact (lv_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2)).2.trans htop1
      obtain ⟨h3, h4⟩ := pi_vt_high hB h.1 h1 ht1
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
      have ht1 : val t ρ < Om1 := by
        obtain ⟨-, -, -, -, htop1, -⟩ := lvTop_facts hB.2.1 hB.2.2.2
        exact (lv_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h)).2.trans htop1
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uni_le hσ hρ hB hu ht]

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvT} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB ht hu, uni_le hσ hρ hB hu ht]

end LvT

/-- Embed the old constant-level grammar into `LvT`. -/
def ofLu : Lu.LuT → LvT
  | .cst a => .cst a
  | .bs => .bs
  | .th b t => .th0 b (ofLu t)
  | .sm a b => .sm (ofLu a) (ofLu b)
  | .pw t => .pw (ofLu t)

theorem ofLu_cb {t : Lu.LuT} {x : Ordinal.{0}} (ht : Lu.LuT.CBt t x) :
    LvT.CBt (ofLu t) x := by
  induction t with
  | cst a => exact ht
  | bs => trivial
  | th b t ih => exact ⟨ht.1, ht.2.1, ih ht.2.2⟩
  | sm a b iha ihb => exact ⟨iha ht.1, ihb ht.2⟩
  | pw t ih => exact ih ht

theorem ofLu_cs (t : Lu.LuT) : LvT.cs (ofLu t) = Lu.LuT.cs t := by
  induction t <;> simp [ofLu, LvT.cs, Lu.LuT.cs, *]

theorem ofLu_val (t : Lu.LuT) (x : Ordinal.{0}) :
    LvT.val (ofLu t) x = Lu.LuT.val t x := by
  induction t <;> simp [ofLu, LvT.val, Lu.LuT.val, *]

end Googology.Trans.PoR.InaccPsi.R2
