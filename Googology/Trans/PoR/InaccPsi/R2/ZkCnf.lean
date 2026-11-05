import Googology.Trans.PoR.InaccPsi.R2.ZfPiG

/-!
# The leaf substitution on `Ω₁·v` for a countable `v` is the Cantor-normal-form exponent map

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

For a countable `v = ω^{c₁}·k₁ + ⋯ + ω^{cₙ}·kₙ` (Cantor normal form, base `ω`) the code `Ω₁·v = ω^{Ω₁+c₁}·k₁ + ⋯` lies
below `B₂`, and its leaves (`Vc.VcLv`) are the exponents `cᵢ ≠ 0`.  So the leaf substitution acts on `Ω₁·v` through
the exponents only:

* `zkCnf f v = ω^{f c₁}·k₁ + ⋯ + ω^{f cₙ}·kₙ` (the exponent map), `ZkEx P v` (every exponent satisfies `P`);
* `zk_vcSub_mul`: `f 0 = 0 ⇒ vcSub f (Ω₁·v) = Ω₁·zkCnf f v`, and `zk_yvSub_mul` (the same for `yvSub`);
* `zk_lv_mul`: the leaves of `Ω₁·v` are its nonzero exponents (`VcLv P (Ω₁·v) ⇒ ZkEx (c = 0 ∨ P c) v`);
* `zk_add`: **the exponent map is additive when `f` is strictly increasing on the exponents** (absorption is kept);
* `zk_pi_cnf`: for `v ∈ Tᵗ[σ] ∩ Ω₁`: `π_{σ,τ}(v) = zkCnf π_{σ,τ} v` and every exponent of `v` lies in `Tᵗ[σ]`.

No new axiom.  New definitions: `zkCnf`, `ZkEx` (a function and a predicate on ordinals).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **The exponent map** on the Cantor normal form (base `ω`): `ω^c·k + r ↦ ω^{f c}·k + zkCnf f r`. -/
noncomputable def zkCnf (f : Ordinal.{0} → Ordinal.{0}) (v : Ordinal.{0}) : Ordinal.{0} :=
  if h : v = 0 then 0 else
    have : v % ω ^ log ω v < v := mod_opow_log_lt_self ω h
    ω ^ f (log ω v) * (v / ω ^ log ω v) + zkCnf f (v % ω ^ log ω v)
termination_by v

/-- **Every exponent of the Cantor normal form satisfies `P`.** -/
def ZkEx (P : Ordinal.{0} → Prop) (v : Ordinal.{0}) : Prop :=
  if h : v = 0 then True else
    have : v % ω ^ log ω v < v := mod_opow_log_lt_self ω h
    P (log ω v) ∧ ZkEx P (v % ω ^ log ω v)
termination_by v

theorem zkCnf_zero (f : Ordinal.{0} → Ordinal.{0}) : zkCnf f 0 = 0 := by
  rw [zkCnf, dif_pos rfl]

theorem zkCnf_ne (f : Ordinal.{0} → Ordinal.{0}) {v : Ordinal.{0}} (hv : v ≠ 0) :
    zkCnf f v = ω ^ f (log ω v) * (v / ω ^ log ω v) + zkCnf f (v % ω ^ log ω v) := by
  rw [zkCnf, dif_neg hv]

theorem zkEx_zero (P : Ordinal.{0} → Prop) : ZkEx P 0 := by
  rw [ZkEx, dif_pos rfl]; trivial

theorem zkEx_ne (P : Ordinal.{0} → Prop) {v : Ordinal.{0}} (hv : v ≠ 0) :
    ZkEx P v ↔ P (log ω v) ∧ ZkEx P (v % ω ^ log ω v) := by
  rw [ZkEx, dif_neg hv]

/-! ## The Cantor normal form step -/

theorem zk_one_lt_omega : (1 : Ordinal.{0}) < ω := one_lt_omega0

theorem zk_two_lt_omega : (2 : Ordinal.{0}) < ω := by exact_mod_cast Ordinal.nat_lt_omega0 2

/-- The parts of `ω^c·k + r` (`0 < k < ω`, `r < ω^c`). -/
theorem zk_parts {c k r : Ordinal.{0}} (hk0 : k ≠ 0) (hk : k < ω) (hr : r < ω ^ c) :
    ω ^ c * k + r ≠ 0 ∧ log ω (ω ^ c * k + r) = c ∧ (ω ^ c * k + r) / ω ^ c = k ∧
      (ω ^ c * k + r) % ω ^ c = r := by
  have hc0 : (ω : Ordinal.{0}) ^ c ≠ 0 := (opow_pos c omega0_pos).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := (Ordinal.add_eq_zero_iff.1 h).1
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hc0 h1
    · exact hk0 h1
  · rw [log_opow_mul_add zk_one_lt_omega hk0 hr, log_eq_zero hk, add_zero]
  · rw [Ordinal.mul_add_div k hc0 r, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- The decomposition of a nonzero ordinal. -/
theorem zk_dec {v : Ordinal.{0}} (hv : v ≠ 0) :
    v / ω ^ log ω v ≠ 0 ∧ v / ω ^ log ω v < ω ∧ v % ω ^ log ω v < ω ^ log ω v ∧
      ω ^ log ω v * (v / ω ^ log ω v) + v % ω ^ log ω v = v :=
  ⟨(div_opow_log_pos ω hv).ne', div_opow_log_lt v zk_one_lt_omega,
    Ordinal.mod_lt v (opow_pos _ omega0_pos).ne', Ordinal.div_add_mod v _⟩

theorem zkCnf_step (f : Ordinal.{0} → Ordinal.{0}) {c k r : Ordinal.{0}} (hk0 : k ≠ 0) (hk : k < ω)
    (hr : r < ω ^ c) : zkCnf f (ω ^ c * k + r) = ω ^ f c * k + zkCnf f r := by
  obtain ⟨h0, hl, hd, hm⟩ := zk_parts hk0 hk hr
  rw [zkCnf_ne f h0, hl, hd, hm]

theorem zkEx_step (P : Ordinal.{0} → Prop) {c k r : Ordinal.{0}} (hk0 : k ≠ 0) (hk : k < ω)
    (hr : r < ω ^ c) : ZkEx P (ω ^ c * k + r) ↔ P c ∧ ZkEx P r := by
  obtain ⟨h0, hl, -, hm⟩ := zk_parts hk0 hk hr
  rw [zkEx_ne P h0, hl, hm]

/-- **Induction along the Cantor normal form.** -/
theorem zk_ind {C : Ordinal.{0} → Prop} (h0 : C 0)
    (hs : ∀ c k r : Ordinal.{0}, k ≠ 0 → k < ω → r < ω ^ c → C r → C (ω ^ c * k + r)) : ∀ v, C v := by
  intro v
  induction v using WellFoundedLT.induction with
  | _ v IH =>
    rcases eq_or_ne v 0 with rfl | hv
    · exact h0
    · obtain ⟨hk0, hk, hr, he⟩ := zk_dec hv
      rw [← he]
      exact hs _ _ _ hk0 hk hr (IH _ (mod_opow_log_lt_self ω hv))

theorem zkEx_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ x, P x → Q x) : ∀ v, ZkEx P v → ZkEx Q v := by
  refine zk_ind (fun _ => zkEx_zero Q) ?_
  intro c k r hk0 hk hr IH h
  rw [zkEx_step P hk0 hk hr] at h
  rw [zkEx_step Q hk0 hk hr]
  exact ⟨hPQ c h.1, IH h.2⟩

theorem zkEx_and {P Q : Ordinal.{0} → Prop} : ∀ v, ZkEx P v → ZkEx Q v → ZkEx (fun x => P x ∧ Q x) v := by
  refine zk_ind (fun _ _ => zkEx_zero _) ?_
  intro c k r hk0 hk hr IH hP hQ
  rw [zkEx_step _ hk0 hk hr] at hP hQ ⊢
  exact ⟨⟨hP.1, hQ.1⟩, IH hP.2 hQ.2⟩

/-- Every exponent of `v < ω^c` is below `c`. -/
theorem zkEx_lt : ∀ v c, v < ω ^ c → ZkEx (· < c) v := by
  refine zk_ind (fun _ _ => zkEx_zero _) ?_
  intro e k r hk0 hk hr IH c hv
  rw [zkEx_step _ hk0 hk hr]
  have hv0 : ω ^ e * k + r ≠ 0 := (zk_parts hk0 hk hr).1
  have hl := (lt_opow_iff_log_lt zk_one_lt_omega hv0).1 hv
  rw [(zk_parts hk0 hk hr).2.1] at hl
  exact ⟨hl, IH c (hr.trans ((opow_lt_opow_iff_right zk_one_lt_omega).2 hl))⟩

/-- **Congruence**: maps agreeing on the exponents have the same exponent map. -/
theorem zkCnf_congr {f g : Ordinal.{0} → Ordinal.{0}} : ∀ v, ZkEx (fun x => f x = g x) v →
    zkCnf f v = zkCnf g v := by
  refine zk_ind (fun _ => by rw [zkCnf_zero, zkCnf_zero]) ?_
  intro c k r hk0 hk hr IH h
  rw [zkEx_step _ hk0 hk hr] at h
  rw [zkCnf_step f hk0 hk hr, zkCnf_step g hk0 hk hr, h.1, IH h.2]

/-! ## Additivity -/

/-- **The bound**: if `f` is strictly increasing on `A`, `c ∈ A`, the exponents of `r < ω^c` lie in `A`, then
`zkCnf f r < ω^{f c}`. -/
theorem zk_bound {f : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}} (hf : StrictMonoOn f A) :
    ∀ r c, c ∈ A → ZkEx (· ∈ A) r → r < ω ^ c → zkCnf f r < ω ^ f c := by
  refine zk_ind (fun c _ _ _ => by rw [zkCnf_zero]; exact opow_pos _ omega0_pos) ?_
  intro e k r hk0 hk hr IH c hc hA hlt
  rw [zkEx_step _ hk0 hk hr] at hA
  have hv0 : ω ^ e * k + r ≠ 0 := (zk_parts hk0 hk hr).1
  have hl := (lt_opow_iff_log_lt zk_one_lt_omega hv0).1 hlt
  rw [(zk_parts hk0 hk hr).2.1] at hl
  have hfe : f e < f c := hf hA.1 hc hl
  rw [zkCnf_step f hk0 hk hr]
  have h1 : zkCnf f r < ω ^ f e := IH e hA.1 hA.2 hr
  have h2 : ω ^ f e * k + zkCnf f r < ω ^ f e * ω := opow_mul_add_lt_opow_mul h1 hk
  rw [← opow_succ] at h2
  exact h2.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hfe))

theorem zk_mul_pos {a b : Ordinal.{0}} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mul_ne_zero ha hb

/-- **The exponent map is additive** when `f` is strictly increasing on a set containing the exponents. -/
theorem zk_add {f : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}} (hf : StrictMonoOn f A) :
    ∀ v w, ZkEx (· ∈ A) v → ZkEx (· ∈ A) w →
      ZkEx (· ∈ A) (v + w) ∧ zkCnf f (v + w) = zkCnf f v + zkCnf f w := by
  refine zk_ind (fun w _ hw => by rw [zero_add, zkCnf_zero, zero_add]; exact ⟨hw, rfl⟩) ?_
  intro c k r hk0 hk hr IH w hv hw
  have hv' := hv
  rw [zkEx_step _ hk0 hk hr] at hv'
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [add_zero, zkCnf_zero, add_zero]; exact ⟨hv, rfl⟩
  obtain ⟨hm0, hm, hs, hwe⟩ := zk_dec hw0
  set d := log ω w with hd
  set m := w / ω ^ d with hmdef
  set s := w % ω ^ d with hsdef
  have hw' := hw
  rw [← hwe, zkEx_step _ hm0 hm hs] at hw'
  have hcw : zkCnf f w = ω ^ f d * m + zkCnf f s := by
    conv_lhs => rw [← hwe]
    exact zkCnf_step f hm0 hm hs
  have hcv : zkCnf f (ω ^ c * k + r) = ω ^ f c * k + zkCnf f r := zkCnf_step f hk0 hk hr
  rcases lt_trichotomy d c with hdc | hdc | hdc
  · -- `d < c`: `r + w < ω^c`
    have hwc : w < ω ^ c :=
      (lt_opow_iff_log_lt zk_one_lt_omega hw0).2 hdc
    have hrw : r + w < ω ^ c := isPrincipal_add_omega0_opow c hr hwc
    obtain ⟨hA, hE⟩ := IH w hv'.2 hw
    rw [add_assoc, zkEx_step _ hk0 hk hrw, zkCnf_step f hk0 hk hrw, hE, hcv, add_assoc]
    exact ⟨⟨hv'.1, hA⟩, rfl⟩
  · -- `d = c`: the coefficients add up
    rw [hdc] at hs hcw hw'
    have habs : r + w = w := by
      refine add_of_omega0_opow_le hr ?_
      have := opow_log_le_self ω hw0
      rwa [← hd, hdc] at this
    have hpω : IsPrincipal (· + ·) (ω : Ordinal.{0}) := by
      simpa only [opow_one] using isPrincipal_add_omega0_opow (1 : Ordinal.{0})
    have hkm : k + m < ω := hpω hk hm
    have hkm0 : k + m ≠ 0 := fun h => hk0 (Ordinal.add_eq_zero_iff.1 h).1
    have hsum : ω ^ c * k + r + w = ω ^ c * (k + m) + s := by
      rw [add_assoc, habs, ← hwe, hdc, ← add_assoc, ← mul_add]
    have hbr : zkCnf f r < ω ^ f c := zk_bound hf r c hv'.1 hv'.2 hr
    have habs2 : zkCnf f r + zkCnf f w = zkCnf f w := by
      refine add_of_omega0_opow_le hbr ?_
      rw [hcw]
      exact (le_mul_left _ (pos_iff_ne_zero.2 hm0)).trans le_self_add
    rw [hsum, zkEx_step _ hkm0 hkm hs, zkCnf_step f hkm0 hkm hs, hcv, add_assoc, habs2, hcw, ← add_assoc,
      ← mul_add]
    exact ⟨⟨hv'.1, hw'.2⟩, rfl⟩
  · -- `c < d`: `w` absorbs `v`
    have hvd : ω ^ c * k + r < ω ^ d := by
      have h1 : ω ^ c * k + r < ω ^ c * ω := opow_mul_add_lt_opow_mul hr hk
      rw [← opow_succ] at h1
      exact h1.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hdc))
    have hdw : ω ^ d ≤ w := opow_log_le_self ω hw0
    have habs : ω ^ c * k + r + w = w := add_of_omega0_opow_le hvd hdw
    have hbv : zkCnf f (ω ^ c * k + r) < ω ^ f d := zk_bound hf _ d hw'.1 hv hvd
    have habs2 : zkCnf f (ω ^ c * k + r) + zkCnf f w = zkCnf f w := by
      refine add_of_omega0_opow_le hbv ?_
      rw [hcw]
      exact (le_mul_left _ (pos_iff_ne_zero.2 hm0)).trans le_self_add
    rw [habs, habs2]
    exact ⟨hw, rfl⟩

/-! ## The leaf substitution on `Ω₁·v` -/

theorem zk_Om1_opow : ω ^ (Om1 : Ordinal.{0}) = Om1 := Rj.rj_Om1_opow

/-- `Ω₁·v` in Cantor normal form: `Ω₁·(ω^c·k + r) = ω^{Ω₁+c}·k + Ω₁·r`, with `Ω₁·r < ω^{Ω₁+c}`. -/
theorem zk_mul_cnf {c k r : Ordinal.{0}} (hr : r < ω ^ c) :
    Om1 * (ω ^ c * k + r) = ω ^ (Om1 + c) * k + Om1 * r ∧ Om1 * r < ω ^ (Om1 + c) := by
  have hO : (0 : Ordinal.{0}) < Om1 := Rj.rj_Om1_pos
  refine ⟨?_, ?_⟩
  · rw [mul_add, ← mul_assoc, opow_add, zk_Om1_opow]
  · rw [opow_add, zk_Om1_opow]; exact mul_lt_mul_of_pos_left hr hO

theorem zk_Om1_mul_lt_B {v : Ordinal.{0}} (hv : v < Om1) : Om1 * v < Uc.ucB := by
  have hE : (Om1 : Ordinal.{0}) < Gg.ggE := Rj.rj_Om1_lt_E
  -- `Ω₁·v < Ω₁·Ω₁ = ω^{Ω₁+Ω₁} < ε_{Ω₁+1} < B₂`
  have h2 : Om1 * v < ω ^ (Om1 + Om1) := by
    rw [opow_add, zk_Om1_opow]; exact mul_lt_mul_of_pos_left hv Rj.rj_Om1_pos
  have hEe : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Gg.ggE_spec.1
  have h3 : (Om1 : Ordinal.{0}) + Om1 < Gg.ggE := by
    have hp : IsPrincipal (· + ·) (Gg.ggE : Ordinal.{0}) := by
      rw [← hEe]; exact isPrincipal_add_omega0_opow _
    exact hp hE hE
  have h4 : ω ^ (Om1 + Om1) < (Gg.ggE : Ordinal.{0}) := by
    conv_rhs => rw [← hEe]
    exact (opow_lt_opow_iff_right zk_one_lt_omega).2 h3
  exact ((h2.trans h4).trans Uv.uv_E_lt_B)

/-- `Ω₁·v` is no `ε`-number for `2 ≤ v < Ω₁`. -/
theorem zk_mul_not_eps {v : Ordinal.{0}} (hv2 : 2 ≤ v) (hv : v < Om1) : ω ^ (Om1 * v) ≠ Om1 * v := by
  intro h
  have h2 : Om1 * v < ω ^ (Om1 + Om1) := by
    rw [opow_add, zk_Om1_opow]; exact mul_lt_mul_of_pos_left hv Rj.rj_Om1_pos
  rw [← h] at h2
  have h3 := (opow_lt_opow_iff_right zk_one_lt_omega).1 h2
  have h4 : Om1 * 2 ≤ Om1 * v := mul_le_mul_left' hv2 _
  rw [Ordinal.mul_two] at h4
  exact absurd (h4.trans_lt h3) (lt_irrefl _)

/-- **`vcSub f (Ω₁·v) = Ω₁·zkCnf f v`** for `v < Ω₁` and `f 0 = 0`. -/
theorem zk_vcSub_mul (f : Ordinal.{0} → Ordinal.{0}) (hf0 : f 0 = 0) :
    ∀ v, v < Om1 → Vc.vcSub f (Om1 * v) = Om1 * zkCnf f v := by
  refine zk_ind (fun _ => by rw [mul_zero, zkCnf_zero, mul_zero, Vc.vcSub_small f Rj.rj_Om1_pos, hf0]) ?_
  intro c k r hk0 hk hr IH hv
  have hO : (0 : Ordinal.{0}) < Om1 := Rj.rj_Om1_pos
  have hrv : r < Om1 := (le_add_self (a := r)).trans_lt hv
  have hcv : c < Om1 := by
    have h1 : ω ^ c ≤ ω ^ c * k + r := (le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add
    exact ((right_le_opow c zk_one_lt_omega).trans h1).trans_lt hv
  obtain ⟨hz, hzr⟩ := zk_mul_cnf (k := k) hr
  rw [zkCnf_step f hk0 hk hr]
  -- the case `v = 1`
  by_cases h1 : ω ^ c * k + r = 1
  · have hc0 : c = 0 := by
      by_contra hc
      have : ω ≤ ω ^ c * k + r :=
        ((left_le_opow ω (pos_iff_ne_zero.2 hc)).trans (le_mul_left _ (pos_iff_ne_zero.2 hk0))).trans
          le_self_add
      rw [h1] at this; exact absurd this (not_le.2 zk_one_lt_omega)
    subst hc0
    rw [opow_zero, one_mul] at h1
    have hr0 : r = 0 := by rw [opow_zero] at hr; exact Ordinal.lt_one_iff_zero.1 hr
    subst hr0
    rw [add_zero] at h1; subst h1
    rw [opow_zero, one_mul, add_zero, mul_one, hf0, opow_zero, one_mul, zkCnf_zero, add_zero, mul_one]
    exact Vc.vcSub_Om1 f
  · have hv2 : 2 ≤ ω ^ c * k + r := by
      have hne : ω ^ c * k + r ≠ 0 := (zk_parts hk0 hk hr).1
      rcases lt_or_ge (ω ^ c * k + r) 2 with h | h
      · exfalso
        have : ω ^ c * k + r < 1 + 1 := by rwa [one_add_one_eq_two]
        rcases (Order.lt_add_one_iff.1 this).lt_or_eq with h' | h'
        · exact hne (Ordinal.lt_one_iff_zero.1 h')
        · exact h1 h'
      · exact h
    set z := Om1 * (ω ^ c * k + r) with hzdef
    have hzO : Om1 < z := by
      have := mul_le_mul_left' hv2 Om1
      rw [Ordinal.mul_two] at this
      exact (lt_add_of_pos_right _ hO).trans_le this
    have hzB : z < Uc.ucB := zk_Om1_mul_lt_B hv
    have hzE : ω ^ z ≠ z := zk_mul_not_eps hv2 hv
    obtain ⟨-, hl, hd, hm⟩ := zk_parts (c := Om1 + c) hk0 hk hzr
    rw [← hz] at hl hd hm
    rw [Vc.vcSub, dif_pos ⟨hzO, hzB⟩, dif_neg hzE]
    dsimp only
    rw [hl, hd, hm, IH hrv]
    by_cases hc0 : c = 0
    · subst hc0
      rw [add_zero, zk_Om1_opow, if_pos rfl, hf0, opow_zero, one_mul]
      have hr0 : r = 0 := by rw [opow_zero] at hr; exact Ordinal.lt_one_iff_zero.1 hr
      subst hr0
      rw [Vc.vcSub_Om1, zkCnf_zero, mul_zero, add_zero, add_zero]
    · have hne : ω ^ (Om1 + c) ≠ Om1 + c := by
        intro h
        have h2 : Om1 + c < Om1 * ω ^ c := by
          have hω : (2 : Ordinal.{0}) ≤ ω ^ c :=
            zk_two_lt_omega.le.trans
              (left_le_opow ω (pos_iff_ne_zero.2 hc0))
          have := mul_le_mul_left' hω Om1
          rw [Ordinal.mul_two] at this
          exact ((add_lt_add_iff_left Om1).2 hcv).trans_le this
        rw [opow_add, zk_Om1_opow] at h
        exact absurd h h2.ne'
      rw [if_neg hne, Ordinal.add_sub_cancel, Vc.vcSub_small f hcv, mul_add, mul_assoc]

/-- **`yvSub f (Ω₁·v) = Ω₁·zkCnf f v`** for `v < Ω₁`, `f 0 = 0`. -/
theorem zk_yvSub_mul {S : InaccSeq.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hf0 : f 0 = 0) {v : Ordinal.{0}}
    (hv : v < Om1) : Yv.yvSub S f (Om1 * v) = Om1 * zkCnf f v := by
  rw [Yv.yvSub_low f (zk_Om1_mul_lt_B hv), zk_vcSub_mul f hf0 v hv]

/-- **The leaves of `Ω₁·v` are its nonzero exponents.** -/
theorem zk_vcLv_mul (P : Ordinal.{0} → Prop) :
    ∀ v, v < Om1 → Vc.VcLv P (Om1 * v) → ZkEx (fun c => c = 0 ∨ P c) v := by
  refine zk_ind (fun _ _ => zkEx_zero _) ?_
  intro c k r hk0 hk hr IH hv hL
  have hO : (0 : Ordinal.{0}) < Om1 := Rj.rj_Om1_pos
  have hrv : r < Om1 := (le_add_self (a := r)).trans_lt hv
  have hcv : c < Om1 := by
    have h1 : ω ^ c ≤ ω ^ c * k + r := (le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add
    exact ((right_le_opow c zk_one_lt_omega).trans h1).trans_lt hv
  rw [zkEx_step _ hk0 hk hr]
  obtain ⟨hz, hzr⟩ := zk_mul_cnf (k := k) hr
  by_cases hc0 : c = 0
  · subst hc0
    have hr0 : r = 0 := by rw [opow_zero] at hr; exact Ordinal.lt_one_iff_zero.1 hr
    subst hr0
    exact ⟨Or.inl rfl, zkEx_zero _⟩
  · refine ⟨?_, ?_⟩
    · right
      have hv2 : 2 ≤ ω ^ c * k + r := by
        have : ω ≤ ω ^ c * k + r :=
          ((left_le_opow ω (pos_iff_ne_zero.2 hc0)).trans (le_mul_left _ (pos_iff_ne_zero.2 hk0))).trans
            le_self_add
        exact zk_two_lt_omega.le.trans this
      set z := Om1 * (ω ^ c * k + r) with hzdef
      have hzO : Om1 < z := by
        have := mul_le_mul_left' hv2 Om1
        rw [Ordinal.mul_two] at this
        exact (lt_add_of_pos_right _ hO).trans_le this
      have hzB : z < Uc.ucB := zk_Om1_mul_lt_B hv
      have hzE : ω ^ z ≠ z := zk_mul_not_eps hv2 hv
      obtain ⟨-, hl, -, -⟩ := zk_parts (c := Om1 + c) hk0 hk hzr
      rw [← hz] at hl
      have hne : ω ^ (Om1 + c) ≠ Om1 + c := by
        intro h
        have h2 : Om1 + c < Om1 * ω ^ c := by
          have hω : (2 : Ordinal.{0}) ≤ ω ^ c :=
            zk_two_lt_omega.le.trans
              (left_le_opow ω (pos_iff_ne_zero.2 hc0))
          have := mul_le_mul_left' hω Om1
          rw [Ordinal.mul_two] at this
          exact ((add_lt_add_iff_left Om1).2 hcv).trans_le this
        rw [opow_add, zk_Om1_opow] at h
        exact absurd h h2.ne'
      rw [Vc.VcLv, dif_pos ⟨hzO, hzB⟩, dif_neg hzE] at hL
      dsimp only at hL
      rw [hl, if_neg hne, Ordinal.add_sub_cancel] at hL
      exact (Vc.VcLv_small P hcv).1 hL.1
    · by_cases h1 : ω ^ c * k + r = 1
      · exfalso
        have : ω ≤ ω ^ c * k + r :=
          ((left_le_opow ω (pos_iff_ne_zero.2 hc0)).trans (le_mul_left _ (pos_iff_ne_zero.2 hk0))).trans
            le_self_add
        rw [h1] at this; exact absurd this (not_le.2 zk_one_lt_omega)
      have hv2 : 2 ≤ ω ^ c * k + r := by
        have : ω ≤ ω ^ c * k + r :=
          ((left_le_opow ω (pos_iff_ne_zero.2 hc0)).trans (le_mul_left _ (pos_iff_ne_zero.2 hk0))).trans
            le_self_add
        exact zk_two_lt_omega.le.trans this
      set z := Om1 * (ω ^ c * k + r) with hzdef
      have hzO : Om1 < z := by
        have := mul_le_mul_left' hv2 Om1
        rw [Ordinal.mul_two] at this
        exact (lt_add_of_pos_right _ hO).trans_le this
      have hzB : z < Uc.ucB := zk_Om1_mul_lt_B hv
      have hzE : ω ^ z ≠ z := zk_mul_not_eps hv2 hv
      obtain ⟨-, hl, -, hm⟩ := zk_parts (c := Om1 + c) hk0 hk hzr
      rw [← hz] at hl hm
      rw [Vc.VcLv, dif_pos ⟨hzO, hzB⟩, dif_neg hzE] at hL
      dsimp only at hL
      rw [hl, hm] at hL
      exact IH hrv hL.2

/-- **The leaves of `Ω₁·v` (as a `Yv` code) are its nonzero exponents.** -/
theorem zk_yvLv_mul {S : InaccSeq.{0}} {P : Ordinal.{0} → Prop} {v : Ordinal.{0}} (hv : v < Om1)
    (hL : Yv.YvLv S P (Om1 * v)) : ZkEx (fun c => c = 0 ∨ P c) v := by
  have hB := zk_Om1_mul_lt_B hv
  cases hL with
  | low _ hV => exact zk_vcLv_mul P v hv hV
  | om hs _ e => exact absurd hB (not_lt.2 (e ▸ Yv.yv_Om_ge_B hs))
  | cnf _ _ _ _ hB' => exact absurd hB (not_lt.2 hB')
  | veb _ _ _ _ hB' => exact absurd hB (not_lt.2 hB')
  | atom _ _ _ _ hB' => exact absurd hB (not_lt.2 hB')

/-! ## The base change on a countable point is its exponent map -/

/-- **`π(v) = zkCnf π v`** and the exponents of `v` lie in `Tᵗ[σ]`, for `v ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem zk_pi_cnf {S : InaccSeq.{0}} {σ τ v : Ordinal.{0}} (hB : Bases σ τ) (hT : v ∈ TB τ σ) (hv : v < Om1) :
    pi σ τ v = zkCnf (pi σ τ) v ∧ ZkEx (· ∈ TB τ σ) v := by
  obtain ⟨m1, m2⟩ := Gl.gl_pi_mul hB hT hv
  have hzB := zk_Om1_mul_lt_B hv
  have hz : Om1 * v < ConjT.th S := hzB.trans Vd.vd_B_lt_th
  have hLT : Yv.YvLv S (· ∈ TB τ σ) (Om1 * v) := (Yv.yv_TB_iff hB hz).1 m1
  obtain ⟨-, hR⟩ := Yv.yv_pi_th hB hz hLT
  have h0σ : (0 : Ordinal.{0}) < σ := (omega0_pos).trans (omega0_lt_inE hB.1)
  have hp0 : pi σ τ 0 = 0 := pi_lt hB h0σ
  have e1 : Yv.yvSub S (pi σ τ) (Om1 * v) = pi σ τ (Om1 * v) := Yv.yvSub_eq hR
  rw [zk_yvSub_mul (pi σ τ) hp0 hv, m2] at e1
  refine ⟨mul_left_cancel₀ Rj.rj_Om1_pos.ne' e1.symm, ?_⟩
  refine zkEx_mono (fun c hc => ?_) v (zk_yvLv_mul hv hLT)
  rcases hc with rfl | hc
  · exact mem_TB_of_lt hB h0σ
  · exact hc

end Googology.Trans.PoR.InaccPsi.R2.Zk
