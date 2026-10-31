import Googology.Trans.PoR.InaccPsi.R2.WzIt

/-!
# The iterates `z_{n+1} = ψ_{Ω₂}(b + z_n)` over a base `b`, and `ζ < ψ₂(b + ζ)` below `ψ₂(b + Ω₂)`

`P = Ω₂`, `z_0 = 0`, `z_{n+1} = ψ_{Ω₂}(b + z_n)` (`xdZ`), `X̂_b = ψ_{Ω₂}(b + Ω₂)`.  Hypotheses on the base:
`b ∈ Cl(b, ψ₂(b))` (normal) and `b % Ω₂ = 0`.

* `xdMod_opow`, `xdMod_SC` (a power `ω^c ≥ Ω₂` and a strongly critical `x ≥ Ω₂` are `≡ 0 mod Ω₂`), `xdMod_add`
  (`(p + q) % Ω₂ ≤ p % Ω₂ + q % Ω₂`);
* `xdZ_lt` (the iterates increase strictly; this uses the normality of `b`), `xdZ_SC`, `xdZ_bdd`;
* `xdX_le_sup` (**`X̂_b ≤ sup_n z_n`**: every `x ∈ Cl(b + Ω₂, sup z)` has `x % Ω₂ < z_n` for some `n`);
* `xdLtPsi` (**every `ζ < X̂_b` has `ζ < ψ₂(b + ζ)`**; `Wz.wzLtPsi` is `b = Ω₂`).

No new axiom.  New definition: `xdZ` (the iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- The iterates over the base `b`: `z_0 = 0`, `z_{n+1} = ψ_{Ω₂}(b + z_n)`. -/
noncomputable def xdZ (S : InaccSeq.{0}) (b : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | n + 1 => S.psi (b + xdZ S b n) (Om (1 + 1))

theorem xdZ_zero (b : Ordinal.{0}) : xdZ S b 0 = 0 := rfl

theorem xdZ_succ (b : Ordinal.{0}) (n : ℕ) : xdZ S b (n + 1) = S.psi (b + xdZ S b n) (Om (1 + 1)) := rfl

/-- A power `ω^c ≥ Ω₂` is a multiple of `Ω₂`. -/
theorem xdMod_opow {c : Ordinal.{0}} (h : Om (1 + 1) ≤ ω ^ c) : ω ^ c % Om (1 + 1) = 0 := by
  have h2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Ru.ruOm2_eps
  have hc : Om (1 + 1) ≤ c := by
    rw [← h2] at h; exact (opow_le_opow_iff_right one_lt_omega0).1 h
  rw [← Ordinal.add_sub_cancel_of_le hc, opow_add, h2]
  exact Ordinal.mul_mod _ _

/-- A strongly critical `x ≥ Ω₂` is a multiple of `Ω₂`. -/
theorem xdMod_SC {x : Ordinal.{0}} (hS : SC x) (h : Om (1 + 1) ≤ x) : x % Om (1 + 1) = 0 := by
  have e := gg_SC_eps hS
  rw [← e] at h ⊢; exact xdMod_opow h

/-- `(p + q) % Ω₂ ≤ p % Ω₂ + q % Ω₂`. -/
theorem xdMod_add (p q : Ordinal.{0}) :
    (p + q) % Om (1 + 1) ≤ p % Om (1 + 1) + q % Om (1 + 1) := by
  set P := Om (1 + 1 : Ordinal.{0}) with hP
  have hPSC : SC P := ldOm2_SC
  have hP0 : P ≠ 0 := hPSC.1.ne'
  rcases lt_or_ge q P with hq | hq
  · rw [ldModK_add_lt hPSC p hq, Ordinal.mod_eq_of_lt hq]
  · have hm : 1 ≤ q / P := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      have := Ordinal.div_add_mod q P
      rw [h0, mul_zero, zero_add] at this
      exact absurd (this ▸ Ordinal.mod_lt q hP0) (not_lt.2 hq)
    have hab : p % P + P * (q / P) = P * (q / P) := by
      have h2 : ω ^ P = P := Ru.ruOm2_eps
      refine Ordinal.add_absorp (by rw [h2]; exact Ordinal.mod_lt p hP0) ?_
      rw [h2]; exact Ordinal.le_mul_left _ (zero_lt_one.trans_le hm)
    have e : p + q = P * (p / P + q / P) + q % P := by
      conv_lhs => rw [← Ordinal.div_add_mod p P, ← Ordinal.div_add_mod q P]
      rw [mul_add, add_assoc, ← add_assoc (p % P), hab, add_assoc]
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_mod]
    exact le_add_self

section Base

variable {b : Ordinal.{0}}

theorem xdZ_lt_Om2 (n : ℕ) : xdZ S b n < Om (1 + 1) := by
  cases n with
  | zero => exact ldOm2_SC.1
  | succ n => rw [xdZ_succ]; exact psi_lt (InR_Om_succ 1) _

theorem xdZ_bdd : BddAbove (range (xdZ S b)) :=
  ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (xdZ_lt_Om2 n).le⟩

theorem xdZ_SC (n : ℕ) : SC (xdZ S b (n + 1)) := by rw [xdZ_succ]; exact SC_psi (InR_Om_succ 1) _

theorem xdZ_one_gt : Om 1 < xdZ S b 1 := by
  rw [xdZ_succ]; exact (psiS_bounds (S := S) _ 1).1

variable (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))))

include hbn

/-- **The iterates increase strictly** (`b` normal). -/
theorem xdZ_lt : ∀ n : ℕ, xdZ S b n < xdZ S b (n + 1) := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro n
  induction n with
  | zero => exact (Om_pos one_ne_zero).trans xdZ_one_gt
  | succ n ih =>
    rw [xdZ_succ b (n + 1), xdZ_succ b n]
    refine psi_lt_psi_of_mem hκ ((add_lt_add_iff_left b).2 ih) (CSet.add_mem ?_ (CSet.of_lt ?_))
    · exact (psi_mono (S := S) hκ le_self_add).2 hbn
    · exact ih.trans_le (by rw [xdZ_succ]; exact (psi_mono hκ (add_le_add le_rfl ih.le)).1)

theorem xdZ_mono : Monotone (xdZ S b) := (strictMono_nat_of_lt_succ (xdZ_lt hbn)).monotone

variable (hbm : b % Om (1 + 1) = 0)

include hbm

/-- **`ψ_{Ω₂}(b + Ω₂) ≤ sup_n z_n`.** -/
theorem xdX_le_sup : S.psi (b + Om (1 + 1)) (Om (1 + 1)) ≤ ⨆ n : ℕ, xdZ S b n := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hbdd := xdZ_bdd (S := S) (b := b)
  have hmono := xdZ_mono hbn
  have hy1 : Om 1 < xdZ S b 1 := xdZ_one_gt
  have hz1 : 0 < xdZ S b 1 := (Om_pos one_ne_zero).trans hy1
  have hΩ2 : SC (Om (1 + 1 : Ordinal.{0})) := ldOm2_SC
  have hup : ∀ i j : ℕ, ∀ x y, x < xdZ S b i → y < xdZ S b j →
      x < xdZ S b (max i j + 1) ∧ y < xdZ S b (max i j + 1) := fun i j x y hx hy =>
    ⟨hx.trans_le (hmono ((le_max_left i j).trans (Nat.le_succ _))),
      hy.trans_le (hmono ((le_max_right i j).trans (Nat.le_succ _)))⟩
  have key : ∀ x ∈ S.CSet (b + Om (1 + 1)) (⨆ n, xdZ S b n), ∃ n, x % Om (1 + 1) < xdZ S b n := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨n, (Ordinal.mod_le _ _).trans_lt hn⟩
    | zero => exact ⟨1, by rw [Ordinal.zero_mod]; exact hz1⟩
    | inacc n =>
      exact ⟨1, by rw [xdMod_SC (SC_I n) (uuOm_le_I uuTwo_lt n)]; exact hz1⟩
    | inaccW =>
      exact ⟨1, by rw [xdMod_SC SC_Iw ((uuOm_le_I uuTwo_lt 0).trans (S.I_le_Iw 0))]; exact hz1⟩
    | @add p q _ _ ihp ihq =>
      obtain ⟨i, hi⟩ := ihp
      obtain ⟨j, hj⟩ := ihq
      obtain ⟨hi', hj'⟩ := hup i j _ _ hi hj
      exact ⟨_, (xdMod_add p q).trans_lt ((xdZ_SC (max i j)).isPrincipal hi' hj')⟩
    | @phi p q _ _ ihp ihq =>
      rcases lt_or_ge (veblen p q) (Om (1 + 1)) with hlt | hge
      · obtain ⟨i, hi⟩ := ihp
        obtain ⟨j, hj⟩ := ihq
        have hp : p < Om (1 + 1) := (left_le_veblen p q).trans_lt hlt
        have hq : q < Om (1 + 1) := (right_le_veblen p q).trans_lt hlt
        rw [Ordinal.mod_eq_of_lt hp] at hi
        rw [Ordinal.mod_eq_of_lt hq] at hj
        obtain ⟨hi', hj'⟩ := hup i j _ _ hi hj
        exact ⟨_, by rw [Ordinal.mod_eq_of_lt hlt]; exact (xdZ_SC (max i j)).2 _ hi' _ hj'⟩
      · obtain ⟨c, hc⟩ := Ordinal.veblen_mem_range_opow p q
        rw [← hc] at hge ⊢
        exact ⟨1, by rw [xdMod_opow hge]; exact hz1⟩
    | @om a _ _ =>
      rcases lt_or_ge (Om a) (Om (1 + 1)) with hlt | hge
      · have ha : a ≤ 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 hlt)
        exact ⟨1, by rw [Ordinal.mod_eq_of_lt hlt]; exact (Om_le_Om.2 ha).trans_lt hy1⟩
      · have ha0 : a ≠ 0 := by
          rintro rfl
          rw [Om_zero] at hge
          exact absurd hge (not_le.2 hΩ2.1)
        exact ⟨1, by rw [xdMod_SC (SC_Om ha0) hge]; exact hz1⟩
    | @coll π e hπ _ _ _ ihe =>
      rcases lt_trichotomy π (Om (1 + 1)) with hlt | heq | hgt
      · have hx : S.psi e.1 π < xdZ S b 1 :=
          ((psi_lt hπ _).trans_le (uuInR_lt uuTwo_lt hπ hlt)).trans hy1
        exact ⟨1, (Ordinal.mod_le _ _).trans_lt hx⟩
      · subst heq
        obtain ⟨m, hm⟩ := ihe
        have hle : e.1 ≤ b + xdZ S b m := by
          rcases le_or_gt e.1 b with h1 | h1
          · exact h1.trans le_self_add
          · have hw : e.1 - b < Om (1 + 1) := Ry.rySub_lt h1.le e.2
            have ee : e.1 = b + (e.1 - b) := (Ordinal.add_sub_cancel_of_le h1.le).symm
            have hmod : e.1 % Om (1 + 1) = e.1 - b := by
              conv_lhs => rw [ee]
              rw [ldModK_add_lt hΩ2 b hw, hbm, zero_add]
            rw [hmod] at hm
            rw [ee]
            exact add_le_add le_rfl hm.le
        have hx : S.psi e.1 (Om (1 + 1)) < xdZ S b (m + 1 + 1) := by
          calc S.psi e.1 (Om (1 + 1)) ≤ S.psi (b + xdZ S b m) (Om (1 + 1)) := (psi_mono hκ hle).1
            _ = xdZ S b (m + 1) := (xdZ_succ b m).symm
            _ < xdZ S b (m + 1 + 1) := xdZ_lt hbn (m + 1)
        exact ⟨_, (Ordinal.mod_le _ _).trans_lt hx⟩
      · have hge : Om (1 + 1) ≤ S.psi e.1 π := uuInR_gt uuTwo_lt hπ hgt e.1
        exact ⟨1, by rw [xdMod_SC (SC_psi hπ e.1) hge]; exact hz1⟩
  refine psi_le_of_good (mxOm2_mem _ _) fun x hx hxκ => ?_
  obtain ⟨n, hn⟩ := key x hx
  rw [Ordinal.mod_eq_of_lt hxκ] at hn
  exact hn.trans_le (le_ciSup hbdd n)

/-- **Every `ζ < ψ_{Ω₂}(b + Ω₂)` has `ζ < ψ_{Ω₂}(b + ζ)`.** -/
theorem xdLtPsi {ζ : Ordinal.{0}} (hζ : ζ < S.psi (b + Om (1 + 1)) (Om (1 + 1))) :
    ζ < S.psi (b + ζ) (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨n, hn⟩ := (lt_ciSup_iff (xdZ_bdd (S := S) (b := b))).1 (hζ.trans_le (xdX_le_sup hbn hbm))
  induction n generalizing ζ with
  | zero => exact absurd hn (not_lt.2 zero_le)
  | succ n ih =>
    by_cases h : ζ < xdZ S b n
    · exact ih hζ h
    · push Not at h
      rw [xdZ_succ] at hn
      exact hn.trans_le (psi_mono hκ (add_le_add le_rfl h)).1

end Base

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdMod_add
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdZ_lt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdX_le_sup
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLtPsi
