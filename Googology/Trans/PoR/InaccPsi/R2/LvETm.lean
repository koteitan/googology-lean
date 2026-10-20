import Googology.Trans.PoR.InaccPsi.R2.LvWLoc

/-!
# The term system of all levels below `ε_{x+1}`: grammar, top `ϑˣ(Ω₁·ε_{x+1})`, EXACT

`LvET`: constants, the base, `ϑˣ(Ω₁·b + t)` for a constant level `1 ≤ b < x` (`th0`), `ϑˣ(Ω₁·l(x) + t)` for a
**level term** `l` (`tl l t`: `l` built from constants, the base, sums and `ω`-powers only (`isLev`), containing the
base (`hasB`), so `x ≤ l(x) < ε_{x+1}`), sums, `ω^t`; top `lveTop x = ϑˣ(Ω₁·ε_{x+1})` (`eN x = ε_{x+1}`).  From the
axioms of `R2.CitedLu` and `R2.CitedLv`:

* `lve_eN_T` (`ε_{x+1} = ϑˣ(Ω₁) ∈ Tˣ`), `LvET.lev_lt_eN`, `LvET.lev_ge`, `LvET.lev_rep` (every ordinal below
  `ε_{x+1}` is the value of a level term, with the base when it is `≥ x`);
* `LvET.lve_T`, `LvET.lve_rep` (the representation below the top), `LvET.pi` (**Lemma EXACT**), `LvET.uni_le`,
  `lve_small`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The new top, at the level `ε_{x+1}`. -/
noncomputable def lveTop (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * eN x)

/-- Terms with levels given by theta-free terms. -/
inductive LvET : Type 1
  | cst : Ordinal.{0} → LvET
  | bs : LvET
  | th0 : Ordinal.{0} → LvET → LvET
  | tl : LvET → LvET → LvET
  | sm : LvET → LvET → LvET
  | pw : LvET → LvET

namespace LvET

/-- Value of a term at base `x`. -/
noncomputable def val : LvET → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | tl l t, x => vt x (Om1 * val l x + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- Constants in the term. -/
def cs : LvET → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | th0 b t => b :: cs t
  | tl l t => cs l ++ cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- A level term: built from constants, the base, sums and `ω`-powers only. -/
def isLev : LvET → Prop
  | cst _ => True
  | bs => True
  | th0 _ _ => False
  | tl _ _ => False
  | sm a b => isLev a ∧ isLev b
  | pw t => isLev t

/-- The term contains the base. -/
def hasB : LvET → Prop
  | cst _ => False
  | bs => True
  | th0 _ t => hasB t
  | tl l t => hasB l ∨ hasB t
  | sm a b => hasB a ∨ hasB b
  | pw t => hasB t

/-- The side condition: constants below the base, constant levels at least `1`, level terms with the base. -/
def CBt : LvET → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | tl l t, x => isLev l ∧ hasB l ∧ CBt l x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- A term is base-independent only when it contains no theta or base constructor. -/
def noB : LvET → Prop
  | cst _ => True
  | bs => False
  | th0 _ _ => False
  | tl _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val bs x = x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : LvET) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_tl (l t : LvET) (x : Ordinal.{0}) :
    val (tl l t) x = vt x (Om1 * val l x + val t x) := rfl
@[simp] theorem val_sm (a b : LvET) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : LvET) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

/-- A level term with constants below an `ε`-number `x` has value below `ε_{x+1}`. -/
theorem lev_lt_eN {x : Ordinal.{0}} (hx : InE x) : ∀ l : LvET, isLev l → CBt l x → val l x < eN x
  | .cst a, _, h => h.trans (lt_eN x)
  | .bs, _, _ => lt_eN x
  | .sm a b, hl, h => (inE_indec (eN_E x)).add_lt (lev_lt_eN hx a hl.1 h.1) (lev_lt_eN hx b hl.2 h.2)
  | .pw t, hl, h => (eN_E x).opow_lt (lev_lt_eN hx t hl h)

/-- A level term with the base has value at least the base. -/
theorem lev_ge {x : Ordinal.{0}} (hx : InE x) : ∀ l : LvET, isLev l → hasB l → CBt l x → x ≤ val l x
  | .bs, _, _, _ => le_rfl
  | .sm a b, hl, hb, h => by
      rcases hb with hb | hb
      · exact (lev_ge hx a hl.1 hb h.1).trans le_self_add
      · exact (lev_ge hx b hl.2 hb h.2).trans le_add_self
  | .pw t, hl, hb, h => (lev_ge hx t hl hb h).trans (right_le_opow _ one_lt_omega0)

/-- A level term without the base has value below the base. -/
theorem lev_lt_of_not_hasB {x : Ordinal.{0}} (hx : InE x) :
    ∀ l : LvET, isLev l → ¬ hasB l → CBt l x → val l x < x
  | .cst _, _, _, h => h
  | .bs, _, hb, _ => absurd trivial hb
  | .sm a b, hl, hb, h => by
      simp only [hasB, not_or] at hb
      exact (inE_indec hx).add_lt (lev_lt_of_not_hasB hx a hl.1 hb.1 h.1) (lev_lt_of_not_hasB hx b hl.2 hb.2 h.2)
  | .pw t, hl, hb, h => hx.opow_lt (lev_lt_of_not_hasB hx t hl hb h)

/-- **Every ordinal below `ε_{x+1}` is the value of a level term**, with the base when it is `≥ x`. -/
theorem lev_rep {x : Ordinal.{0}} (hx : InE x) :
    ∀ q, q < eN x → ∃ l : LvET, isLev l ∧ CBt l x ∧ val l x = q ∧ (x ≤ q → hasB l) := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases lt_or_ge q x with hqx | hxq
  · exact ⟨.cst q, trivial, hqx, rfl, fun h => absurd h (not_le.2 hqx)⟩
  by_cases hI : Indec q
  · rcases eq_or_lt_of_le hxq with rfl | hxq'
    · exact ⟨.bs, trivial, trivial, rfl, fun _ => trivial⟩
    obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hnE : ¬ InE (ω ^ L) := fun hE => absurd (eN_le hxq' hE) (not_le.2 hq)
    have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
      (fun h => hnE (by unfold InE; rw [← h]; exact h.symm))
    have hxL : x ≤ L := by
      by_contra hlt
      push Not at hlt
      have : ω ^ L < ω ^ x := (opow_lt_opow_iff_right one_lt_omega0).2 hlt
      rw [show ω ^ x = x from hx] at this
      exact absurd hxq (not_le.2 this)
    obtain ⟨l, hl, hc, he, hb⟩ := IH L hL (hL.trans hq)
    exact ⟨.pw l, hl, hc, by rw [val_pw, he], fun _ => hb hxL⟩
  · have hD : DecompR0 q := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hx.pos hxq).ne'
    obtain ⟨l1, h1, c1, e1, b1⟩ := IH u1 hu1 (hu1.trans hq)
    obtain ⟨l2, h2, c2, e2, b2⟩ := IH u2 hu2 (hu2.trans hq)
    refine ⟨.sm l1 l2, ⟨h1, h2⟩, ⟨c1, c2⟩, by rw [val_sm, e1, e2, hsum], fun hxq => ?_⟩
    by_contra hn
    simp only [hasB, not_or] at hn
    have hl1 : u1 < x := by
      by_contra h; exact hn.1 (b1 (not_lt.1 h))
    have hl2 : u2 < x := by
      by_contra h; exact hn.2 (b2 (not_lt.1 h))
    exact absurd ((inE_indec hx).add_lt hl1 hl2) (not_lt.2 (hsum ▸ hxq))

end LvET

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `ε_{x+1} = ϑˣ(Ω₁)` lies in `Tˣ ∩ Ω₁`. -/
theorem lve_eN_T : eN x ∈ Tset x ∧ eN x < Om1 := by
  obtain ⟨-, -, haT, hxa, ha1, haE, -, -⟩ :=
    Lu.lu_th_facts hx hx1 le_rfl (Lu.lu_one_lt_E hx) (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  have hle : eN x ≤ vt x (Om1 * 1 + 0) := eN_le hxa haE
  exact ⟨vz_T_down hx hx1 haT ha1 hle, hle.trans_lt ha1⟩

/-- The facts on a level term value. -/
theorem lve_lev_facts {l : LvET} (hl : LvET.isLev l) (hlB : LvET.hasB l) (hc : LvET.CBt l x) :
    LvET.val l x ∈ Tset x ∧ x ≤ LvET.val l x ∧ LvET.val l x < eN x ∧ LvET.val l x < Om1 := by
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
  have hlt := LvET.lev_lt_eN hx l hl hc
  exact ⟨vz_T_down hx hx1 heT he1 hlt.le, LvET.lev_ge hx l hl hlB hc, hlt, hlt.trans he1⟩

theorem lveTop_facts :
    Om1 * eN x ∈ Tset x ∧ Om1 * eN x < OmTwo ∧ lveTop x ∈ Tset x ∧
      x < lveTop x ∧ lveTop x < Om1 ∧ InE (lveTop x) ∧ eN x < lveTop x := by
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
  obtain ⟨a, b, c, d, e, f, -, g, -⟩ :=
    Lv.gen_facts hx hx1 heT (lt_eN x).le he1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
  simp only [add_zero] at a b c d e f g
  exact ⟨a, b, c, d, e, f, g⟩

/-- Below the top: `ϑˣ(Ω₁·β + η) < ϑˣ(Ω₁·ε_{x+1})` for `β ∈ Tˣ`, `β < ε_{x+1}`, `η < ϑˣ(Ω₁·ε_{x+1})`. -/
theorem lve_lt_top {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβ : β < eN x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : η < lveTop x) : vt x (Om1 * β + η) < lveTop x := by
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
  obtain ⟨-, -, -, -, -, -, het⟩ := lveTop_facts hx hx1
  have e : lveTop x = vt x (Om1 * eN x + 0) := by rw [add_zero]; rfl
  rw [e] at h het ⊢
  refine lvVt_lt_gen hx hx1 hβT (hβ.trans he1) heT (lt_eN x).le he1 hη hη1
    (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1) ?_ (hβ.trans het) h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * eN x := mul_le_mul_right (add_one_le_of_lt hβ) Om1

/-- An `ε`-number `ϑˣ(ξ) ∈ (x, ϑˣ(Ω₁·ε_{x+1}))` has the argument quotient `ξ / Ω₁ < ε_{x+1}`. -/
theorem lve_quot_top {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hxξ : x < vt x ξ)
    (hE : InE (vt x ξ)) (h : vt x ξ < lveTop x) : ξ / Om1 < eN x := by
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hle : eN x ≤ vt x ξ := eN_le hxξ hE
  have hlt : ξ < Om1 * eN x := by
    rcases hle.lt_or_eq with hlt' | heq
    · have := lvLt_of_vt_lt hx hx1 hξT hξ2 heT (lt_eN x).le he1 h0T (Ordinal.omega_pos 1)
        (hx.pos.trans hxξ) hlt' (by rw [add_zero]; exact h)
      simpa using this
    · have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
      have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h1x.le
      have h11 : (1 : Ordinal.{0}) < Om1 := h1x.trans hx1
      obtain ⟨-, -, -, hxa, -, haE, -, -⟩ :=
        Lu.lu_th_facts hx hx1 le_rfl h1x h0T (Ordinal.omega_pos 1)
      have hea : eN x ≤ vt x (Om1 * 1 + 0) := eN_le hxa haE
      have h2 : vt x (Om1 * 1 + 0) < vt x (Om1 * 1 + 1) :=
        Lu.lu_th_lt hx hx1 le_rfl h1x h0T h1T h11 zero_lt_one
      have h3 : ξ < Om1 * 1 + 1 :=
        luLt_of_vt_lt hx hx1 hξT hξ2 h1x h1T h11 (by rw [← heq]; exact Lu.lu_one_lt_E (eN_E x))
          (by rw [← heq]; exact hea.trans_lt h2)
      have h2e : (1 : Ordinal.{0}) + 1 ≤ eN x := Order.add_one_le_of_lt (h1x.trans (lt_eN x))
      calc ξ < Om1 * 1 + 1 := h3
        _ ≤ Om1 * 1 + Om1 := add_le_add_right h11.le _
        _ = Om1 * (1 + 1) := by rw [mul_add_one]
        _ ≤ Om1 * eN x := mul_le_mul_right h2e Om1
  have h1 : Om1 * (ξ / Om1) < Om1 * eN x := lt_of_le_of_lt (mul_div_le ξ Om1) hlt
  exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1

end Base

namespace LvET

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- The terms denote members of `Tˣ` below the top. -/
theorem lve_T : ∀ t : LvET, CBt t x → val t x ∈ Tset x ∧ val t x < lveTop x
  | .cst a, h => by
      obtain ⟨-, -, hTopT, hxt, hTop1, -, -⟩ := lveTop_facts hx hx1
      exact ⟨vz_T_down hx hx1 hTopT hTop1 (h.trans hxt).le, h.trans hxt⟩
  | .bs, _ => by
      obtain ⟨-, -, -, hxt, -, -, -⟩ := lveTop_facts hx hx1
      exact ⟨mem_T_of_le hx hx1 le_rfl, hxt⟩
  | .th0 b t, h => by
      obtain ⟨htT, htLt⟩ := lve_T t h.2.2
      obtain ⟨-, -, -, -, hTop1, -, -⟩ := lveTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt (h.2.1.trans hx1) ht1
      have hb : b < eN x := h.2.1.trans (lt_eN x)
      exact ⟨(vt_memTwo hx hx1 hargT harg2).1,
        lve_lt_top hx hx1 (mem_T_of_le hx hx1 h.2.1.le) hb htT ht1 htLt⟩
  | .tl l t, h => by
      obtain ⟨htT, htLt⟩ := lve_T t h.2.2.2
      obtain ⟨-, -, -, -, hTop1, -, -⟩ := lveTop_facts hx hx1
      have ht1 : val t x < Om1 := htLt.trans hTop1
      obtain ⟨hLT, hxL, hLe, hL1⟩ := lve_lev_facts hx hx1 h.1 h.2.1 h.2.2.1
      have hargT := lvArg_mem hx hx1 hLT hxL hL1 htT ht1
      have harg2 := Lu.luOm1_mul_lt hL1 ht1
      exact ⟨(vt_memTwo hx hx1 hargT harg2).1, lve_lt_top hx hx1 hLT hLe htT ht1 htLt⟩
  | .sm a b, h => by
      obtain ⟨haT, haLt⟩ := lve_T a h.1
      obtain ⟨hbT, hbLt⟩ := lve_T b h.2
      obtain ⟨-, -, -, -, -, hTopE, -⟩ := lveTop_facts hx hx1
      exact ⟨vzT_add hx hx1 haT hbT, (inE_indec hTopE).add_lt haLt hbLt⟩
  | .pw t, h => by
      obtain ⟨htT, htLt⟩ := lve_T t h
      obtain ⟨-, -, hTopT, -, hTop1, hTopE, -⟩ := lveTop_facts hx hx1
      have hw : ω ^ val t x < lveTop x := hTopE.opow_lt htLt
      exact ⟨vz_T_down hx hx1 hTopT hTop1 hw.le, hw⟩

/-- **Representation**: every ordinal below the top is the value of a term with constants below the base. -/
theorem lve_rep : ∀ v, v < lveTop x → ∃ t : LvET, CBt t x ∧ val t x = v := by
  obtain ⟨-, -, hTopT, -, hTop1, -, -⟩ := lveTop_facts hx hx1
  obtain ⟨heT, he1⟩ := lve_eN_T hx hx1
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
        have hqe : ξ / Om1 < eN x :=
          lve_quot_top hx hx1 hξT hξ2 (by rw [hξv]; exact hxv') (by rw [hξv]; exact hE) (by rw [hξv]; exact hv)
        rcases lt_or_ge (ξ / Om1) x with hqx | hqx
        · have hrv : ξ % Om1 < v := by
            have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th0 (ξ / Om1) t, ⟨hq1, hqx, ht⟩, by rw [val_th0, he, hdec, hξv]⟩
        · obtain ⟨l, hl, hlc, hle, hlB⟩ := lev_rep hx (ξ / Om1) hqe
          have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 heT he1 hqe.le
          have hrv : ξ % Om1 < v := by
            have h := (lvLevel_lt_vt hx hx1 hqT hqx (hqe.trans he1) hrT hr1).2
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.tl l t, ⟨hl, hlB hqx, hlc, ht⟩, by rw [val_tl, he, hle, hdec, hξv]⟩
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
theorem noB_val : ∀ t : LvET, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .tl _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

omit hx hx1 in
/-- The side condition depends only on the listed constants. -/
theorem cbt_iff {t : LvET} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
  | th0 b t ih =>
      refine ⟨h.1, hy b (by simp [cs]), ?_⟩
      exact ih h.2.2 (fun c hc => hy c (by simp [cs, hc]))
  | tl l t ihl iht =>
      exact ⟨h.1, h.2.1, ihl h.2.2.1 (fun c hc => hy c (by simp [cs, hc])),
        iht h.2.2.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | sm a b iha ihb =>
      exact ⟨iha h.1 (fun c hc => hy c (by simp [cs, hc])),
        ihb h.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | pw t ih => exact ih h (fun c hc => hy c (by simpa [cs] using hc))

end Base

/-- All explicit constants and level parameters are below the base. -/
theorem cbt_cst {ρ : Ordinal.{0}} {s : LvET} (hs : CBt s ρ) : ∀ c ∈ cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [cs] at hc
  | th0 b t ih =>
      intro c hc
      simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.2.1
      · exact ih hs.2.2 c hc
  | tl l t ihl iht =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihl hs.2.2.1 c hc
      · exact iht hs.2.2.2 c hc
  | sm a b iha ihb =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hs.1 c hc
      · exact ihb hs.2 c hc
  | pw t ih => intro c hc; exact ih hs c (by simpa [cs] using hc)

/-- The side condition is monotone in the base. -/
theorem CBt.mono {s : LvET} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y :=
  cbt_iff hs (fun c hc => (cbt_cst hs c hc).trans_le hxy)

/-- A term containing a base-dependent constructor has value at least its base. -/
theorem le_of_not_noB {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LvET, CBt t x → ¬ noB t → x ≤ val t x
  | .cst _, _, h => absurd trivial h
  | .bs, _, _ => le_rfl
  | .th0 b t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lve_T hx hx1 t hc.2.2
      have ht1 : val t x < Om1 := htLt.trans (lveTop_facts hx hx1).2.2.2.2.1
      exact (Lu.lu_th_facts hx hx1 hc.1 hc.2.1 htT ht1).2.2.2.1.le
  | .tl l t, hc, _ => by
      obtain ⟨htT, htLt⟩ := lve_T hx hx1 t hc.2.2.2
      have ht1 : val t x < Om1 := htLt.trans (lveTop_facts hx hx1).2.2.2.2.1
      obtain ⟨hLT, hxL, -, hL1⟩ := lve_lev_facts hx hx1 hc.1 hc.2.1 hc.2.2.1
      exact (Lv.gen_facts hx hx1 hLT hxL hL1 htT ht1).2.2.2.1.le
  | .sm a b, hc, hn => by
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (le_of_not_noB hx hx1 a hc.1 hn).trans le_self_add
      · exact (le_of_not_noB hx hx1 b hc.2 hn).trans le_add_self
  | .pw t, hc, hn =>
      (le_of_not_noB hx hx1 t hc hn).trans (right_le_opow _ one_lt_omega0)

/-- The top lies below every next point above the base. -/
theorem lve_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u)
    (hu : LtInf1 u) : lveTop x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨-, -, hT, -, htop1, -, -⟩ := lveTop_facts hx hx1
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

theorem lve_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvET}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (lve_T hx hx1 t ht).2.trans (lve_top_lt_next hx hx1 hxu hu)

theorem lve_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {t : LvET}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  lve_lt_next hx hx1 ht hxu hu.2

/-- The theta term at a level term commutes with `π`. -/
theorem pi_vt_tl {σ ρ β η : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β ∈ TB ρ σ) (hρβ : ρ ≤ β) (hβ1 : β < Om1)
    (hη : η ∈ TB ρ σ) (hη1 : η < Om1) :
    vt ρ (Om1 * β + η) ∈ TB ρ σ ∧
      pi σ ρ (vt ρ (Om1 * β + η)) = vt σ (Om1 * pi σ ρ β + pi σ ρ η) := by
  have hmul := lvPi_mul hB hβ hρβ hβ1
  have hadd := pi_add hB hmul.1 hη
  have harg2 := Lu.luOm1_mul_lt hβ1 hη1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hB.2.1 hB.2.2.2 hadd.1.1 harg2
  exact ⟨⟨hvT, by rw [hvP]; exact hadd.1.2⟩,
    by rw [pi_vt_two hB hadd.1 harg2, hadd.2, hmul.2]⟩

/-- **Lemma EXACT** for `LvET`: the value maps to the same term at the smaller base. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LvET, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2
      have ht1 : val t ρ < Om1 :=
        (lve_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2)).2.trans
          (lveTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := LvT.pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .tl l t, h => by
      obtain ⟨hl1, hl2⟩ := pi hσ hρ hB l h.2.2.1
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h.2.2.2
      have hcρ : CBt l ρ := CBt.mono hB.2.2.1.le h.2.2.1
      obtain ⟨-, hρL, -, hL1⟩ := lve_lev_facts hB.2.1 hB.2.2.2 h.1 h.2.1 hcρ
      have ht1 : val t ρ < Om1 :=
        (lve_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h.2.2.2)).2.trans
          (lveTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := pi_vt_tl hB hl1 hρL hL1 h1 ht1
      simp only [val_tl]
      exact ⟨h3, by rw [h4, h2, hl2]⟩
  | .sm a b, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB a h.1
      obtain ⟨h3, h4⟩ := pi hσ hρ hB b h.2
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      simp only [val_sm]
      exact ⟨h5, by rw [h6, h2, h4]⟩
  | .pw t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB t h
      have ht1 : val t ρ < Om1 :=
        (lve_T hB.2.1 hB.2.2.2 t (CBt.mono hB.2.2.1.le h)).2.trans
          (lveTop_facts hB.2.1 hB.2.2.2).2.2.2.2.1
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvET} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvET} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uni_le hσ hρ hB hu ht]

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    {t u : LvET} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB ht hu, uni_le hσ hρ hB hu ht]

end LvET

/-- The `small` field: a term is base-independent or at least the base. -/
theorem lve_small : ∀ t : LvET,
    (∀ x y, LvET.val t x = LvET.val t y) ∨
      (∀ x, InE x → x < Om1 → LvET.CBt t x → x ≤ LvET.val t x) := by
  intro t
  by_cases h : LvET.noB t
  · exact Or.inl (LvET.noB_val t h)
  · exact Or.inr (fun x hx hx1 hc => LvET.le_of_not_noB hx hx1 t hc h)

end Googology.Trans.PoR.InaccPsi.R2
