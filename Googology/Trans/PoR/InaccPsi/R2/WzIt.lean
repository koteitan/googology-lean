import Googology.Trans.PoR.InaccPsi.R2.WvImg

/-!
# The iterates `z_{n+1} = ψ_{Ω₂}(Ω₂ + z_n)` and the normal arguments below `ψ_{Ω₂}(Ω₂·2)`

`z_0 = 0`, `z_{n+1} = ψ_{Ω₂}(Ω₂ + z_n)`, `X̂ = ψ_{Ω₂}(Ω₂ + Ω₂)` (the candidate image `Wv.wvX0 S λ 0 Ω₃` of the
top law at `Ω₃` over the base `Ω₃`).

* `wzZ_lt`, `wzZ_bdd`, `wzZ_mono`, `wzZ_SC`, `wzZ_lt_X` (the iterates increase, stay below `X̂`);
* `wzX_le_sup` (**`X̂ ≤ sup_n z_n`**: the closure induction of `Uu.uuY_le_sup` with the second clause
  `x < Ω₂·2 ⇒ x < Ω₂ + z_n`);
* `wzLtPsi` (**every `ζ < X̂` has `ζ < ψ_{Ω₂}(Ω₂ + ζ)`**);
* `wzZ_mem` (`z_n ∈ Cl(a, b)` for every `a ≥ Ω₂·2`), `wzZ_N` (`z_n` is a normal member over every `T`),
  `wzX_lt_th` (`X̂ < θ`).

No new axiom.  New definition: `wzZ` (the iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- The iterates `z_0 = 0`, `z_{n+1} = ψ_{Ω₂}(Ω₂ + z_n)`. -/
noncomputable def wzZ (S : InaccSeq.{0}) (n : ℕ) : Ordinal.{0} :=
  (fun x => S.psi (Om (1 + 1) + x) (Om (1 + 1)))^[n] 0

theorem wzZ_zero : wzZ S 0 = 0 := rfl

theorem wzZ_succ (n : ℕ) : wzZ S (n + 1) = S.psi (Om (1 + 1) + wzZ S n) (Om (1 + 1)) :=
  Function.iterate_succ_apply' _ n 0

theorem wzZ_lt : ∀ n : ℕ, wzZ S n < wzZ S (n + 1) := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro n
  induction n with
  | zero => rw [wzZ_succ, wzZ_zero, add_zero]; exact (SC_psi hκ _).1
  | succ n ih =>
    rw [wzZ_succ (n + 1), wzZ_succ n]
    have ih' : wzZ S n < S.psi (Om (1 + 1) + wzZ S n) (Om (1 + 1)) := by rwa [wzZ_succ] at ih
    exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left _).2 ih')
      (CSet.add_mem (mxOm2_mem _ _) (CSet.of_lt (ih'.trans_le (psi_mono hκ (add_le_add le_rfl ih'.le)).1)))

theorem wzZ_mono : Monotone (wzZ S) := (strictMono_nat_of_lt_succ wzZ_lt).monotone

theorem wzZ_strictMono : StrictMono (wzZ S) := strictMono_nat_of_lt_succ wzZ_lt

theorem wzZ_lt_Om2 (n : ℕ) : wzZ S n < Om (1 + 1) := by
  rcases n with _ | n
  · rw [wzZ_zero]; exact ldOm2_SC.1
  · rw [wzZ_succ]; exact psi_lt (InR_Om_succ 1) _

theorem wzZ_bdd : BddAbove (range (wzZ S)) :=
  ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (wzZ_lt_Om2 n).le⟩

theorem wzZ_SC (n : ℕ) : SC (wzZ S (n + 1)) := by rw [wzZ_succ]; exact SC_psi (InR_Om_succ 1) _

theorem wzZ_lt_X (n : ℕ) : wzZ S n < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
  (wzZ_lt n).trans_le (by
    rw [wzZ_succ]; exact (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (wzZ_lt_Om2 n).le)).1)

/-- `Ω₂ + Ω₂ < Ω₃`. -/
theorem wzOm22_lt_Om3 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om (1 + 1 + 1) := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  exact (SC_Om h3).isPrincipal h23 h23

/-- **`ψ_{Ω₂}(Ω₂ + Ω₂) ≤ sup_n z_n`.** -/
theorem wzX_le_sup : S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) ≤ ⨆ n : ℕ, wzZ S n := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hbdd := wzZ_bdd (S := S)
  have hmono := wzZ_mono (S := S)
  have hSC := wzZ_SC (S := S)
  have hy1 : Om 1 < wzZ S 1 := by rw [wzZ_succ, wzZ_zero, add_zero]; exact (psiS_bounds (S := S) _ 1).1
  have hz1 : 0 < wzZ S 1 := (Om_pos one_ne_zero).trans hy1
  have hΩ2 : SC (Om (1 + 1 : Ordinal.{0})) := ldOm2_SC
  have h2ε : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps hΩ2
  have h22 := wzOm22_lt_Om3
  -- a member `≤ Ω₂` with the first clause has the second
  have snd : ∀ x, (x < Om (1 + 1) → ∃ n, x < wzZ S n) → x ≤ Om (1 + 1) →
      ∃ n, x < Om (1 + 1) + wzZ S n := by
    intro x h1 h2
    rcases h2.lt_or_eq with h | h
    · obtain ⟨n, hn⟩ := h1 h; exact ⟨n, hn.trans_le le_add_self⟩
    · exact ⟨1, by rw [h]; exact lt_add_of_pos_right _ hz1⟩
  have hsum : ∀ i j : ℕ, ∀ a b, a < wzZ S i → b < wzZ S j → a + b < wzZ S (max i j + 1) := by
    intro i j a b ha hb
    exact (hSC (max i j)).isPrincipal (ha.trans_le (hmono ((le_max_left i j).trans (Nat.le_succ _))))
      (hb.trans_le (hmono ((le_max_right i j).trans (Nat.le_succ _))))
  have key : ∀ x ∈ S.CSet (Om (1 + 1) + Om (1 + 1)) (⨆ n, wzZ S n),
      (x < Om (1 + 1) → ∃ n, x < wzZ S n) ∧
        (x < Om (1 + 1) + Om (1 + 1) → ∃ n, x < Om (1 + 1) + wzZ S n) := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨fun _ => ⟨n, hn⟩, fun _ => ⟨n, hn.trans_le le_add_self⟩⟩
    | zero => exact ⟨fun _ => ⟨1, hz1⟩, fun _ => ⟨1, hz1.trans_le le_add_self⟩⟩
    | inacc n =>
      have hI : Om (1 + 1 + 1 : Ordinal.{0}) ≤ S.I n := uuOm_le_I uuThree_lt n
      exact ⟨fun h => absurd (h.trans (Om_lt_Om.2 (lt_add_one _))) (not_lt.2 hI),
        fun h => absurd (h.trans h22) (not_lt.2 hI)⟩
    | inaccW =>
      have hI : Om (1 + 1 + 1 : Ordinal.{0}) ≤ S.Iw := (uuOm_le_I uuThree_lt 0).trans (S.I_le_Iw 0)
      exact ⟨fun h => absurd (h.trans (Om_lt_Om.2 (lt_add_one _))) (not_lt.2 hI),
        fun h => absurd (h.trans h22) (not_lt.2 hI)⟩
    | @add a b _ _ iha ihb =>
      have first : a + b < Om (1 + 1) → ∃ n, a + b < wzZ S n := fun h => by
        obtain ⟨i, hi⟩ := iha.1 (le_self_add.trans_lt h)
        obtain ⟨j, hj⟩ := ihb.1 (le_add_self.trans_lt h)
        exact ⟨_, hsum i j a b hi hj⟩
      refine ⟨first, fun h => ?_⟩
      rcases lt_or_ge b (Om (1 + 1)) with hb | hb
      · obtain ⟨j, hj⟩ := ihb.1 hb
        rcases lt_or_ge a (Om (1 + 1)) with ha | ha
        · obtain ⟨n, hn⟩ := first (hΩ2.isPrincipal ha hb)
          exact ⟨n, hn.trans_le le_add_self⟩
        · obtain ⟨i, hi⟩ := iha.2 (le_self_add.trans_lt h)
          have ea : a = Om (1 + 1) + (a - Om (1 + 1)) := (Ordinal.add_sub_cancel_of_le ha).symm
          have hi' : a - Om (1 + 1) < wzZ S i := by
            rw [ea] at hi; exact (add_lt_add_iff_left _).1 hi
          refine ⟨max i j + 1, ?_⟩
          rw [ea, add_assoc]
          exact (add_lt_add_iff_left _).2 (hsum i j _ _ hi' hj)
      · have ha : a < Om (1 + 1) := by
          by_contra hc
          push Not at hc
          exact absurd ((add_le_add hc hb).trans_lt h) (lt_irrefl _)
        have e1 : a + b = b := Ordinal.add_of_omega0_opow_le (by rw [h2ε]; exact ha) (by rw [h2ε]; exact hb)
        rw [e1] at h ⊢
        exact ihb.2 h
    | @phi a b _ _ iha ihb =>
      have first : veblen a b < Om (1 + 1) → ∃ n, veblen a b < wzZ S n := fun h => by
        obtain ⟨i, hi⟩ := iha.1 ((left_le_veblen a b).trans_lt h)
        obtain ⟨j, hj⟩ := ihb.1 ((right_le_veblen a b).trans_lt h)
        exact ⟨max i j + 1, (hSC (max i j)).2 _ (hi.trans_le (hmono ((le_max_left i j).trans (Nat.le_succ _))))
          _ (hj.trans_le (hmono ((le_max_right i j).trans (Nat.le_succ _))))⟩
      refine ⟨first, fun h => snd _ first ?_⟩
      by_contra hc
      push Not at hc
      have hp : IsPrincipal (· + ·) (veblen a b) := by
        obtain ⟨c, hc⟩ := Ordinal.veblen_mem_range_opow a b
        have e : veblen a b = ω ^ c := hc.symm
        rw [e]; exact isPrincipal_add_omega0_opow c
      exact absurd (hp hc hc) (not_lt.2 h.le)
    | @om a _ _ =>
      have first : Om a < Om (1 + 1) → ∃ n, Om a < wzZ S n := fun h => by
        have ha : a ≤ 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 h)
        exact ⟨1, (Om_le_Om.2 ha).trans_lt hy1⟩
      refine ⟨first, fun h => snd _ first ?_⟩
      have ha : a < 1 + 1 + 1 := Om_lt_Om.1 (h.trans h22)
      exact Om_le_Om.2 (Order.lt_add_one_iff.1 ha)
    | @coll π e hπ _ _ _ ihe =>
      rcases lt_trichotomy π (Om (1 + 1)) with hlt | heq | hgt
      · have hx : S.psi e.1 π < wzZ S 1 :=
          ((psi_lt hπ _).trans_le (uuInR_lt uuTwo_lt hπ hlt)).trans hy1
        have first : S.psi e.1 π < Om (1 + 1) → ∃ n, S.psi e.1 π < wzZ S n := fun _ => ⟨1, hx⟩
        exact ⟨first, fun _ => snd _ first (hx.trans (wzZ_lt_Om2 1)).le⟩
      · subst heq
        obtain ⟨n, hn⟩ := ihe.2 e.2
        have hx : S.psi e.1 (Om (1 + 1)) < wzZ S (n + 1 + 1) := by
          calc S.psi e.1 (Om (1 + 1)) ≤ S.psi (Om (1 + 1) + wzZ S n) (Om (1 + 1)) := (psi_mono hκ hn.le).1
            _ = wzZ S (n + 1) := (wzZ_succ n).symm
            _ < wzZ S (n + 1 + 1) := wzZ_lt (n + 1)
        have first : S.psi e.1 (Om (1 + 1)) < Om (1 + 1) → ∃ m, S.psi e.1 (Om (1 + 1)) < wzZ S m :=
          fun _ => ⟨_, hx⟩
        exact ⟨first, fun _ => snd _ first (psi_lt hκ _).le⟩
      · have hge : Om (1 + 1) ≤ S.psi e.1 π := uuInR_gt uuTwo_lt hπ hgt e.1
        refine ⟨fun h => absurd h (not_lt.2 hge), fun h => ?_⟩
        have hle : S.psi e.1 π ≤ Om (1 + 1) := by
          by_contra hc
          push Not at hc
          exact absurd ((SC_psi hπ e.1).isPrincipal hc hc) (not_lt.2 h.le)
        exact snd _ (fun h' => absurd h' (not_lt.2 hge)) hle
  refine psi_le_of_good (mxOm2_mem _ _) fun x hx hxκ => ?_
  obtain ⟨n, hn⟩ := (key x hx).1 hxκ
  exact hn.trans_le (le_ciSup hbdd n)

/-- **Every `ζ < ψ_{Ω₂}(Ω₂ + Ω₂)` has `ζ < ψ_{Ω₂}(Ω₂ + ζ)`.** -/
theorem wzLtPsi {ζ : Ordinal.{0}} (hζ : ζ < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) :
    ζ < S.psi (Om (1 + 1) + ζ) (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨n, hn⟩ := (lt_ciSup_iff (wzZ_bdd (S := S))).1 (hζ.trans_le wzX_le_sup)
  induction n generalizing ζ with
  | zero => exact absurd hn (not_lt.2 zero_le)
  | succ n ih =>
    by_cases h : ζ < wzZ S n
    · exact ih hζ h
    · push Not at h
      rw [wzZ_succ] at hn
      exact hn.trans_le (psi_mono hκ (add_le_add le_rfl h)).1

/-- `z_n ∈ Cl(a, b)` for every `a ≥ Ω₂ + Ω₂`. -/
theorem wzZ_mem {a b : Ordinal.{0}} (ha : Om (1 + 1) + Om (1 + 1) ≤ a) : ∀ n : ℕ, wzZ S n ∈ S.CSet a b := by
  intro n
  induction n with
  | zero => exact CSet.zero_mem _ _
  | succ n ih =>
    rw [wzZ_succ]
    exact CSet.psi_mem (((add_lt_add_iff_left _).2 (wzZ_lt_Om2 n)).trans_le ha) (InR_Om_succ 1)
      (mxOm2_mem _ _) (CSet.add_mem (mxOm2_mem _ _) ih)

/-- `z_n` is a normal member over every `T`. -/
theorem wzZ_N {T : Ordinal.{0}} : ∀ n : ℕ, RxN S T (wzZ S n) := by
  have h11 : RxN S T (1 + 1 : Ordinal.{0}) := RxN.add RxN.one RxN.one
  have hO : RxN S T (Om (1 + 1 : Ordinal.{0})) := RxN.om h11
  have hne : Om (1 + 1 : Ordinal.{0}) ≠ Om 1 := (Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0}))).ne'
  intro n
  induction n with
  | zero => exact RxN.zero
  | succ n ih =>
    rw [wzZ_succ]
    refine RxN.psi (InR_Om_succ 1) hne hO (RxN.add hO ih) ?_
    rw [← wzZ_succ]
    exact CSet.add_mem (mxOm2_mem _ _) (CSet.of_lt (wzZ_lt n))

/-- `X̂ = ψ_{Ω₂}(Ω₂ + Ω₂) < θ`. -/
theorem wzX_lt_th : S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (vkOmW.1.isPrincipal vkOmW.2 vkOmW.2)
    (CSet.add_mem (mxOm2_mem _ _) (mxOm2_mem _ _))

/-- `z_n` is in the domain of the level shift over every `T`. -/
theorem wzZ_E {T : Ordinal.{0}} (n : ℕ) : RxE S T (wzZ S n) :=
  ⟨wzZ_N n, CSet.of_lt ((wzZ_lt_X n).trans wzX_lt_th),
    (wzZ_lt_Om2 n).trans vkOmW.2⟩

end Googology.Trans.PoR.InaccPsi.R2.Wz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzZ_lt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzX_le_sup
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLtPsi
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzZ_mem
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzZ_E
