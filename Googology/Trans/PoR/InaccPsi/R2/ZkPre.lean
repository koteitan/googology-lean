import Googology.Trans.PoR.InaccPsi.R2.ZkImg3

/-!
# The leaf substitution is additive at sums with no touching terms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

For a code `a < θ` all of whose Cantor-normal-form exponents are `≥ Ω₁·2` (e.g. `a = Ω₁·U` with `Ω₁ ∣ U`) and a
`b < ω^{Ω₁·2} = Ω₁·Ω₁` (e.g. `b = Ω₁·c` with `c < Ω₁`), the canonical decomposition of `a + b` is that of `a`
followed by that of `b` (in both regimes, below `B₂` by `Vc.vcSub`, from `B₂` on by the `cnf` clause of `Yv.YvR`):

* `zk_yv_add`: `YvLv P (a + b) ⇒ YvLv P a ∧ YvLv P b` and `yvSub f (a + b) = yvSub f a + yvSub f b`
  (`f 0 = 0`, `P 0`);
* helpers `zk_not_eps`, `zk_yvSub_zero`, `zk_W2_lt_B`, `zk_vcLv_of`, `zk_yvSub_cnf`, `zkEx_opow_mul`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- A sum of two smaller ordinals is no `ε`-number. -/
theorem zk_not_eps {x y z : Ordinal.{0}} (hx : x < z) (hy : y < z) (hz : x + y = z) : ω ^ z ≠ z := by
  intro h
  have hp : IsPrincipal (· + ·) z := by rw [← h]; exact isPrincipal_add_omega0_opow _
  exact absurd (hz ▸ hp hx hy) (lt_irrefl _)

theorem zk_yvSub_zero (f : Ordinal.{0} → Ordinal.{0}) (hf0 : f 0 = 0) : yvSub S f 0 = 0 := by
  have hB0 : (0 : Ordinal.{0}) < Uc.ucB := lt_of_le_of_lt zero_le (Rj.rj_Om1_lt_E.trans Uv.uv_E_lt_B)
  rw [yvSub_low f hB0, Vc.vcSub_small f Rj.rj_Om1_pos, hf0]

theorem zk_W2_eq : ω ^ ((Om1 : Ordinal.{0}) * 2) = Om1 * Om1 := by
  rw [Ordinal.mul_two, opow_add, zk_Om1_opow]

theorem zk_W2_lt_B : ω ^ ((Om1 : Ordinal.{0}) * 2) < Uc.ucB := by
  have hEe : ω ^ (Gg.ggE : Ordinal.{0}) = Gg.ggE := Gg.ggE_spec.1
  have hE : (Om1 : Ordinal.{0}) < Gg.ggE := Rj.rj_Om1_lt_E
  have hp : IsPrincipal (· + ·) (Gg.ggE : Ordinal.{0}) := by rw [← hEe]; exact isPrincipal_add_omega0_opow _
  have h3 : (Om1 : Ordinal.{0}) * 2 < Gg.ggE := by rw [Ordinal.mul_two]; exact hp hE hE
  have h4 : ω ^ ((Om1 : Ordinal.{0}) * 2) < Gg.ggE := by
    conv_rhs => rw [← hEe]
    exact (opow_lt_opow_iff_right zk_one_lt_omega).2 h3
  exact h4.trans Uv.uv_E_lt_B

theorem zk_Om1_lt_W2 : (Om1 : Ordinal.{0}) < ω ^ ((Om1 : Ordinal.{0}) * 2) := by
  conv_lhs => rw [← zk_Om1_opow]
  refine (opow_lt_opow_iff_right zk_one_lt_omega).2 ?_
  rw [Ordinal.mul_two]; exact lt_add_of_pos_right _ Rj.rj_Om1_pos

/-- A `Yv` code below `B₂` has its `Vc` leaves. -/
theorem zk_vcLv_of {P : Ordinal.{0} → Prop} {x : Ordinal.{0}} (h : YvLv S P x) (hx : x < Uc.ucB) :
    Vc.VcLv P x := by
  cases h with
  | low _ hV => exact hV
  | om hs _ e => exact absurd hx (not_lt.2 (e ▸ yv_Om_ge_B hs))
  | cnf _ _ _ _ hB => exact absurd hx (not_lt.2 hB)
  | veb _ _ _ _ hB => exact absurd hx (not_lt.2 hB)
  | atom _ _ _ _ hB => exact absurd hx (not_lt.2 hB)

/-- **The `cnf` clause of the substitution** at a code `B₂ ≤ z < Ω₂` that is no `ε`-number. -/
theorem zk_yvSub_cnf (f : Ordinal.{0} → Ordinal.{0}) {P : Ordinal.{0} → Prop} {z : Ordinal.{0}}
    (hLv : YvLv S P z) (hB : Uc.ucB ≤ z) (hE : ω ^ z ≠ z) (hz2 : z < Om ((1 : Ordinal.{0}) + 1)) :
    YvLv S P (log ω z) ∧ YvLv S P (z % ω ^ log ω z) ∧
      yvSub S f z = (if ω ^ log ω z = log ω z then yvSub S f (log ω z) else ω ^ yvSub S f (log ω z)) *
        (z / ω ^ log ω z) + yvSub S f (z % ω ^ log ω z) := by
  cases hLv with
  | low hz _ => exact absurd hz (not_lt.2 hB)
  | om hs _ e =>
    subst e
    exact absurd (Om_lt_Om.1 hz2) (not_lt.2 (Order.add_one_le_of_lt hs))
  | cnf hs1 hs hlo hhi hB' hE' h1 h2 =>
    obtain ⟨g', R1⟩ := yvR_ex f h1
    obtain ⟨r', R2⟩ := yvR_ex f h2
    have R := YvR.cnf hs1 hs hlo hhi hB' hE' R1 R2
    refine ⟨h1, h2, ?_⟩
    rw [yvSub_eq R, yvSub_eq R1, yvSub_eq R2]
  | veb _ _ _ _ _ hE' => exact absurd hE' hE
  | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) hE

/-- The exponents of `ω^c·u` are `≥ c`. -/
theorem zkEx_opow_mul (c : Ordinal.{0}) : ∀ u, ZkEx (fun e => c ≤ e) (ω ^ c * u) := by
  refine zk_ind (by rw [mul_zero]; exact zkEx_zero _) ?_
  intro d k r hk0 hk hr IH
  have hr' : ω ^ c * r < ω ^ (c + d) := by
    rw [opow_add]; exact mul_lt_mul_of_pos_left hr (opow_pos c omega0_pos)
  have e : ω ^ c * (ω ^ d * k + r) = ω ^ (c + d) * k + ω ^ c * r := by
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e, zkEx_step _ hk0 hk hr']
  exact ⟨le_self_add, IH⟩

/-- **The leaf substitution is additive at `a + b`** (exponents of `a` all `≥ Ω₁·2`, `b < ω^{Ω₁·2}`). -/
theorem zk_yv_add (f : Ordinal.{0} → Ordinal.{0}) (hf0 : f 0 = 0) {P : Ordinal.{0} → Prop} (hP0 : P 0) :
    ∀ a, ZkEx (fun e => Om1 * 2 ≤ e) a → ∀ b, b < ω ^ ((Om1 : Ordinal.{0}) * 2) → a + b < ConjT.th S →
      YvLv S P (a + b) → YvLv S P a ∧ YvLv S P b ∧ yvSub S f (a + b) = yvSub S f a + yvSub S f b := by
  have hB0 : (0 : Ordinal.{0}) < Uc.ucB := lt_of_le_of_lt zero_le (Rj.rj_Om1_lt_E.trans Uv.uv_E_lt_B)
  have hY0 : YvLv S P 0 := YvLv.low hB0 ((Vc.VcLv_small P Rj.rj_Om1_pos).2 hP0)
  have hBE : ω ^ (Uc.ucB : Ordinal.{0}) = Uc.ucB := yv_B_eps
  have hBp : IsPrincipal (· + ·) (Uc.ucB : Ordinal.{0}) := by rw [← hBE]; exact isPrincipal_add_omega0_opow _
  have hθ2 : ConjT.th S < Om ((1 : Ordinal.{0}) + 1) := Br.th_lt_Om2
  refine zk_ind ?_ ?_
  · intro _ b _ _ hL
    rw [zero_add] at hL ⊢
    rw [zk_yvSub_zero f hf0, zero_add]
    exact ⟨hY0, hL, rfl⟩
  intro e k r hk0 hk hr IH hEx b hb hθ hL
  rw [zkEx_step _ hk0 hk hr] at hEx
  obtain ⟨he, hExr⟩ := hEx
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [add_zero] at hL ⊢
    rw [zk_yvSub_zero f hf0, add_zero]
    exact ⟨hL, hY0, rfl⟩
  set a := ω ^ e * k + r with hadef
  have hbe : b < ω ^ e := hb.trans_le (opow_le_opow_right omega0_pos he)
  have hrb : r + b < ω ^ e := isPrincipal_add_omega0_opow e hr hbe
  have hz : a + b = ω ^ e * k + (r + b) := by rw [hadef, add_assoc]
  have ha0 : a ≠ 0 := (zk_parts hk0 hk hr).1
  have haz : a < a + b := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
  have hbz : b < a + b := by
    have : b < a := hbe.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add)
    exact this.trans haz
  have hzE : ω ^ (a + b) ≠ a + b := zk_not_eps haz hbz rfl
  obtain ⟨-, hl, hd, hm⟩ := zk_parts hk0 hk hrb
  rw [← hz] at hl hd hm
  obtain ⟨-, hla, hda, hma⟩ := zk_parts hk0 hk hr
  rw [← hadef] at hla hda hma
  have hWa : ω ^ ((Om1 : Ordinal.{0}) * 2) ≤ a :=
    (opow_le_opow_right omega0_pos he).trans ((le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add)
  have hOa : Om1 < a := zk_Om1_lt_W2.trans_le hWa
  have hrθ : r + b < ConjT.th S := (hrb.trans_le
    ((le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add)).trans_le (hz ▸ hθ).le
  -- the `ε` case: `a = ω^a`, `k = 1`, `r = 0`
  have hEcase : ω ^ a = a → e = a ∧ k = 1 ∧ r = 0 := by
    intro hEa
    have hea : e = a := by
      have h1 : log ω a = a := by
        conv_lhs => rw [← hEa]
        exact log_opow zk_one_lt_omega a
      rw [← hla, h1]
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by
        rcases lt_or_ge k 2 with h | h
        · exfalso
          have : k < 1 + 1 := by rwa [one_add_one_eq_two]
          rcases (Order.lt_add_one_iff.1 this).lt_or_eq with h' | h'
          · exact hk0 (Ordinal.lt_one_iff_zero.1 h')
          · exact hk1 h'
        · exact h
      have h1 : a * 2 ≤ a := by
        calc a * 2 ≤ a * k := mul_le_mul_left' hk2 a
          _ = ω ^ e * k := by rw [hea, hEa]
          _ ≤ a := le_self_add
      rw [Ordinal.mul_two] at h1
      exact absurd h1 (not_le.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 ha0)))
    refine ⟨hea, hk1, ?_⟩
    have h1 : a = a + r := by
      conv_lhs => rw [hadef]
      rw [hk1, mul_one, hea, hEa]
    exact (left_eq_add.1 h1)
  by_cases hzB : a + b < Uc.ucB
  · -- below `B₂`: `Vc.vcSub`
    have haB : a < Uc.ucB := haz.trans hzB
    have hbB : b < Uc.ucB := hbz.trans hzB
    have hrbB : r + b < Uc.ucB :=
      (hrb.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add)).trans haB
    have hVz := zk_vcLv_of hL hzB
    rw [Vc.VcLv, dif_pos ⟨hOa.trans haz, hzB⟩, dif_neg hzE] at hVz
    dsimp only at hVz
    rw [hl, hm] at hVz
    rw [yvSub_low f hzB, yvSub_low f haB, yvSub_low f hbB, Vc.vcSub, dif_pos ⟨hOa.trans haz, hzB⟩, dif_neg hzE]
    dsimp only
    rw [hl, hd, hm]
    by_cases hEa : ω ^ a = a
    · obtain ⟨hea, hk1, hr0⟩ := hEcase hEa
      have heE : ω ^ e = e := by rw [hea]; exact hEa
      rw [if_pos heE] at hVz ⊢
      rw [hr0, zero_add] at hVz ⊢
      rw [hk1, mul_one, hea]
      exact ⟨YvLv.low haB (hea ▸ hVz.1), YvLv.low hbB hVz.2, rfl⟩
    · have hrbL : YvLv S P (r + b) := YvLv.low hrbB hVz.2
      obtain ⟨hLr, hLb, hrbe⟩ := IH hExr b hb hrθ hrbL
      have hrB : r < Uc.ucB := (le_self_add.trans_lt hrbB)
      rw [yvSub_low f hrbB, yvSub_low f hrB, yvSub_low f hbB] at hrbe
      have hVa : Vc.VcLv P a := by
        rw [Vc.VcLv, dif_pos ⟨hOa, haB⟩, dif_neg hEa]
        dsimp only
        rw [hla, hma]
        exact ⟨hVz.1, zk_vcLv_of hLr hrB⟩
      have hva : Vc.vcSub f a = (if ω ^ e = e then Vc.vcSub f e else Om1 * ω ^ Vc.vcSub f (e - Om1)) * k +
          Vc.vcSub f r := by
        rw [Vc.vcSub, dif_pos ⟨hOa, haB⟩, dif_neg hEa]
        dsimp only
        rw [hla, hda, hma]
      refine ⟨YvLv.low haB hVa, hLb, ?_⟩
      rw [hva, hrbe, add_assoc]
  · -- from `B₂` on: the `cnf` clause
    have hzB' : Uc.ucB ≤ a + b := not_lt.1 hzB
    have haB : Uc.ucB ≤ a := by
      by_contra h
      exact hzB (hBp (not_le.1 h) (hb.trans zk_W2_lt_B))
    have hz2 : a + b < Om ((1 : Ordinal.{0}) + 1) := hθ.trans hθ2
    obtain ⟨hLl, hLm, hsz⟩ := zk_yvSub_cnf f hL hzB' hzE hz2
    rw [hl] at hLl hLm hsz
    rw [hm] at hLm hsz
    rw [hd] at hsz
    by_cases hEa : ω ^ a = a
    · obtain ⟨hea, hk1, hr0⟩ := hEcase hEa
      have heE : ω ^ e = e := by rw [hea]; exact hEa
      rw [if_pos heE, hk1, mul_one, hr0, zero_add, hea] at hsz
      rw [hr0, zero_add] at hLm
      rw [hea] at hLl
      exact ⟨hLl, hLm, hsz⟩
    · obtain ⟨hLr, hLb, hrbe⟩ := IH hExr b hb hrθ hLm
      have ha2 : a < Om ((1 : Ordinal.{0}) + 1) := haz.trans hz2
      have hLa : YvLv S P a := by
        refine YvLv.cnf (s := 1) le_rfl zk_one_lt_omega (by rw [← Rj.rj_Om1]; exact hOa) ha2 haB hEa ?_ ?_
        · rw [hla]; exact hLl
        · rw [hla, hma]; exact hLr
      obtain ⟨-, -, hsa⟩ := zk_yvSub_cnf f hLa haB hEa ha2
      rw [hla, hda, hma] at hsa
      refine ⟨hLa, hLb, ?_⟩
      rw [hsz, hsa, hrbe, add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Zk
