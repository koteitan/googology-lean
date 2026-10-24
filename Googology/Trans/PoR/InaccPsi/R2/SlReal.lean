import Googology.Trans.PoR.InaccPsi.R2.SlShift

/-!
# Realizers along a renaming of the offsets, with the carry of the inner reaches (EQ)

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = υ_λ` a restart, `r(λ) = Cd.cdR S λ`.  `Sl.slShiftCore` moves a configuration along an offset map `f`
(`υ_{λ+d} ↦ υ_{μ+f(d)}`).  The `≤₁`-pairs whose left end is an inner restart `υ_{λ+g}` (`0 < g`, `ω² ∣ g`) are
given by its reach (UPPER at `λ + g`) and need the reach of the image restart `μ + f(g)` (LOWER there).
Here an inner reach may contain the base point itself: `r(λ+g) = υ_{λ+h} + υ_λ·j + p` (`p < υ_λ`), and
`υ_λ ↦ υ_μ` moves it to `υ_{μ+f(h)} + υ_μ·j + p`.

* `SlCarry S λ β μ f B γ Os` (**EQ for the renaming at the inner restarts of the offset set**): at every
  `g ∈ Os` with `0 < g`, `ω² ∣ g`: LOWER at `μ + f(g)`, `υ_{μ+B} ≤ r(μ+f(g))` when `υ_{λ+β} ≤ r(λ+g)`, and
  `υ_{μ+f(h)} + υ_μ·j + p ≤ r(μ+f(g))` when `r(λ+g) = υ_{λ+h} + υ_λ·j + p` (`h ∈ Os`, `0 < h`, `p < γ`);
* `slE_omega_lt`, `slE_mul_lt` (an `ε`-number is above `ω` and closed under `·`), `slE_mul_nat_lt`;
* `slReal_ren` (**`LrReal S υ_λ υ_{λ+β}` from UPPER at the inner restarts, the form of their reaches, and
  Range restarts with an offset map, the supply `υ_{μ+B} ≤ r(μ)` and the carry**): the configuration is
  enlarged by `υ_{λ+h}`, `υ_λ·i`, `υ_{λ+h} + υ_λ·i` (`i ≤ j`), `υ_{λ+h} + υ_λ·j + p` and `p`; the map keeps
  `+`, so these go to `υ_{μ+f(h)} + υ_μ·i + p`.

No new axiom.  New definition: `SlCarry`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **EQ for an offset map at the inner restarts of `Os`.** -/
def SlCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B γ : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ h ∈ Os, ∀ (j : ℕ) (p : Ordinal.{0}), 0 < h → p < γ →
      cdR S (l + g) = upsilon (l + h) + upsilon l * (j : Ordinal.{0}) + p →
      upsilon (μ + f h) + upsilon μ * (j : Ordinal.{0}) + p ≤ cdR S (μ + f g)

/-- An `ε`-number is above `ω`. -/
theorem slE_omega_lt {e : Ordinal.{0}} (he : InE e) : ω < e := by
  have h1 : 1 ≤ e := Order.one_le_iff_ne_zero.2 he.pos.ne'
  have hle : ω ≤ e := by
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ e := opow_le_opow_right omega0_pos h1
      _ = e := he
  refine lt_of_le_of_ne hle fun h => ?_
  have h3 : ω ^ e = e := he
  rw [← h] at h3
  have h2 : ω ^ (1 : Ordinal.{0}) < ω ^ ω := (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_omega0
  rw [opow_one, h3] at h2
  exact lt_irrefl _ h2

/-- An `ε`-number is closed under `·`. -/
theorem slE_mul_lt {e x y : Ordinal.{0}} (he : InE e) (hx : x < e) (hy : y < e) : x * y < e := by
  have h := isPrincipal_mul_omega0_opow_opow e
  have h3 : ω ^ e = e := he
  rw [h3, h3] at h
  exact h hx hy

theorem slE_mul_nat_lt {e x : Ordinal.{0}} (he : InE e) (hx : x < e) (n : ℕ) : x * (n : Ordinal.{0}) < e :=
  slE_mul_lt he hx ((natCast_lt_omega0 n).trans (slE_omega_lt he))

theorem slE_mul_omega_lt {e x : Ordinal.{0}} (he : InE e) (hx : x < e) : x * ω < e :=
  slE_mul_lt he hx (slE_omega_lt he)

theorem slUpsE (ζ : Ordinal.{0}) : InE (upsilon (succ ζ)) :=
  upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ζ)))

/-- **Realizer maps along an offset map, with the carry of the inner reaches.** -/
theorem slReal_ren {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨
      ∃ h, ∃ j : ℕ, ∃ p, 0 < h ∧ h < β ∧ p < upsilon l ∧
        cdR S (l + g) = upsilon (l + h) + upsilon l * (j : Ordinal.{0}) + p)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ SlOff f Os B ∧ SlCarry S l β μ f B γ Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  -- the inner restarts of `Y` whose reach has the form `υ_{λ+h} + υ_λ·j + p`
  set rp : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    ∃ h, ∃ j : ℕ, ∃ p, 0 < h ∧ h < β ∧ p < upsilon l ∧
      cdR S (l + g) = upsilon (l + h) + upsilon l * (j : Ordinal.{0}) + p with hrpdef
  have hch : ∀ y, rp y → ∃ g h, ∃ j : ℕ, ∃ p, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      0 < h ∧ h < β ∧ p < upsilon l ∧
      cdR S (l + g) = upsilon (l + h) + upsilon l * (j : Ordinal.{0}) + p := by
    rintro y ⟨g, hg, h, j, p, h0, h1, h2, h3⟩
    exact ⟨g, h, j, p, hg, h0, h1, h2, h3⟩
  choose! gf hf jf pf hgf hh0 hhf hpf hrf using hch
  set T := Y.filter rp with hTdef
  set A : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    ((Finset.range (jf y + 1)).image (fun i : ℕ => upsilon (l + hf y) + upsilon l * (i : Ordinal.{0}))) ∪
    ((Finset.range (jf y)).image (fun i : ℕ => upsilon l * ((i + 1 : ℕ) : Ordinal.{0}))) ∪
    {upsilon (l + hf y), upsilon (l + hf y) + upsilon l * (jf y : Ordinal.{0}) + pf y} with hAdef
  set Y' := Y ∪ T.biUnion A with hY'def
  set X' := X ∪ T.image pf with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact hpf y (Finset.mem_filter.1 hy).2
  -- the added points lie in `[υ_λ, υ_{λ+β})`
  have hA : ∀ y ∈ T, ∀ z ∈ A y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    have hh0' := hh0 y hr
    have hhβ := hhf y hr
    have hpl := hpf y hr
    have hlh : upsilon l < upsilon (l + hf y) := hm (lt_add_of_pos_right l hh0')
    have hEh : InE (upsilon (l + hf y)) := upsPt_inE (upsPt_upsilon
      (lt_of_le_of_lt zero_le (lt_add_of_pos_right l hh0')))
    have hEs := slUpsE (l + hf y)
    have hhs : upsilon (l + hf y) < upsilon (succ (l + hf y)) := hm (lt_succ _)
    have hsβ : upsilon (succ (l + hf y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt hhβ)
    have hmul : ∀ i : ℕ, upsilon l * (i : Ordinal.{0}) < upsilon (succ (l + hf y)) := fun i =>
      slE_mul_nat_lt hEs (hlh.trans hhs) i
    have hsum : ∀ i : ℕ, upsilon (l + hf y) + upsilon l * (i : Ordinal.{0}) < upsilon (succ (l + hf y)) :=
      fun i => hEs.add_lt hhs (hmul i)
    have hge : ∀ i : ℕ, upsilon l ≤ upsilon (l + hf y) + upsilon l * (i : Ordinal.{0}) := fun i =>
      hlh.le.trans le_self_add
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact ⟨hge i, (hsum i).trans_le hsβ⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        refine ⟨Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos i), ?_⟩
        exact ((slE_mul_nat_lt hEh hlh (i + 1)).trans hhs).trans_le hsβ
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hlh.le, hhs.trans_le hsβ⟩
      · rw [Finset.mem_singleton.1 hz]
        exact ⟨(hge (jf y)).trans le_self_add,
          (hEs.add_lt (hsum (jf y)) (hpl.trans (hlh.trans hhs))).trans_le hsβ⟩
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      exact hA u hu y hyu
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, -, hW, hres, himg⟩ :=
    slShiftCore (Q := SlCarry S l β) hl hl1 hν hνβ hsup hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ hx
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ hy
  have hsub : ∀ u ∈ X ∪ Y, u ∈ X' ∪ Y' := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Finset.mem_union_left _ (hXX u hu)
    · exact Finset.mem_union_right _ (hYY u hu)
  refine ⟨D, μ, ⟨fun x hx => hW.fix x (hXX x hx), hW.mono.mono fun u hu => hsub u hu,
    fun x hx y hy z hz => hW.add x (hsub x hx) y (hsub y hy) z (hsub z hz),
    fun y hy => hW.indec y (hYY y hy), fun y hy x hx => hW.above y (hYY y hy) x (hXX x hx),
    fun y hy => hW.below y (hYY y hy), hW.rng, fun ha => hW.base (hYY _ ha),
    fun y hy => hW.bd y (hYY y hy), ?_,
    fun y hy y' hy' => hW.pair2 y (hYY y hy) y' (hYY y' hy')⟩⟩
  intro y hy y' hy' hay hyy h1
  by_cases hr : ∃ g, 0 < g ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)
  · obtain ⟨g, hg0, hgd, rfl⟩ := hr
    have hgβ : g < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hY _ hy).2)
    have hyr : y' ≤ cdR S (l + g) := cdUpper_iff.1 (hU g hg0 hgβ hgd) y' h1
    obtain ⟨hgO, hDy⟩ := hres g (hYY _ hy)
    obtain ⟨hLow, hbig, hfrm⟩ := hQ g hgO hg0 hgd
    have hmono : ∀ u ∈ X' ∪ Y', ∀ v ∈ X' ∪ Y', u ≤ v → D u ≤ D v := fun u hu v hv huv =>
      (hW.mono.le_iff_le (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv)).2 huv
    have hle : D y' ≤ cdR S (μ + f g) := by
      rcases hform g hg0 hgβ hgd with hb | ⟨h, j, p, hh0', hh, hp, hrr⟩
      · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
      · have hrp : rp (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h, j, p, hh0', hh, hp, hrr⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrp⟩
        have hgg : gf (upsilon (l + g)) = g := by
          have e := (hgf _ hrp).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hr' := hrf _ hrp
        rw [hgg] at hr'
        set H := hf (upsilon (l + g)) with hHdef
        set J := jf (upsilon (l + g)) with hJdef
        set P := pf (upsilon (l + g)) with hPdef
        have hAY : ∀ z ∈ A (upsilon (l + g)), z ∈ Y' := fun z hz =>
          Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT, hz⟩)
        have hHm : upsilon (l + H) ∈ Y' := hAY _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
        have hSm : upsilon (l + H) + upsilon l * (J : Ordinal.{0}) + P ∈ Y' :=
          hAY _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        have hIm : ∀ i : ℕ, i ≤ J → upsilon (l + H) + upsilon l * (i : Ordinal.{0}) ∈ Y' := fun i hi =>
          hAY _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))))
        have hMm : ∀ i : ℕ, i < J → upsilon l * ((i + 1 : ℕ) : Ordinal.{0}) ∈ Y' := fun i hi =>
          hAY _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))))
        have hPm : P ∈ X' := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hT)
        have hDH : D (upsilon (l + H)) = upsilon (μ + f H) := (hres H hHm).2
        have hHO : H ∈ Os := (hres H hHm).1
        have hDP : D P = P := hW.fix P hPm
        have hYr : ∀ u ∈ Y', u ∈ X' ∪ Y' := fun u hu => Finset.mem_union_right _ hu
        -- `D(υ_λ) = υ_μ` when `J > 0`
        have hDl : 0 < J → D (upsilon l) = upsilon μ := by
          intro hJ
          have hm1 := hMm 0 hJ
          rw [zero_add, Nat.cast_one, mul_one] at hm1
          exact hW.base hm1
        -- `D(υ_λ·(i+1)) = υ_μ·(i+1)`
        have hDM : ∀ i : ℕ, i < J → D (upsilon l * ((i + 1 : ℕ) : Ordinal.{0})) =
            upsilon μ * ((i + 1 : ℕ) : Ordinal.{0}) := by
          intro i
          induction i with
          | zero =>
            intro hi
            rw [zero_add, Nat.cast_one, mul_one, mul_one]
            exact hDl hi
          | succ i ih =>
            intro hi
            have hlm : upsilon l ∈ Y' := by
              have := hMm 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
            have e : upsilon l * ((i + 1 : ℕ) : Ordinal.{0}) + upsilon l =
                upsilon l * ((i + 1 + 1 : ℕ) : Ordinal.{0}) := by
              rw [Nat.cast_succ (i + 1), mul_add_one]
            have := (hW.add _ (hYr _ (hMm i (by omega))) _ (hYr _ hlm) _
              (hYr _ (hMm (i + 1) hi))).1 e
            rw [ih (by omega), hDl (by omega)] at this
            rw [← this, Nat.cast_succ (i + 1), mul_add_one]
        -- `D(υ_{λ+h} + υ_λ·i) = υ_{μ+f(h)} + υ_μ·i`
        have hDI : ∀ i : ℕ, i ≤ J → D (upsilon (l + H) + upsilon l * (i : Ordinal.{0})) =
            upsilon (μ + f H) + upsilon μ * (i : Ordinal.{0}) := by
          intro i
          induction i with
          | zero => intro _; simp only [Nat.cast_zero, mul_zero, add_zero]; exact hDH
          | succ i ih =>
            intro hi
            have e : upsilon (l + H) + upsilon l * (i : Ordinal.{0}) + upsilon l * ((0 + 1 : ℕ) : Ordinal.{0}) =
                upsilon (l + H) + upsilon l * ((i + 1 : ℕ) : Ordinal.{0}) := by
              rw [zero_add, Nat.cast_one, mul_one, add_assoc, Nat.cast_succ, mul_add_one]
            have := (hW.add _ (hYr _ (hIm i (by omega))) _ (hYr _ (hMm 0 (by omega))) _
              (hYr _ (hIm (i + 1) hi))).1 e
            rw [ih (by omega), hDM 0 (by omega)] at this
            rw [← this, zero_add, Nat.cast_one, mul_one, add_assoc, Nat.cast_succ, mul_add_one]
        have hDS : D (upsilon (l + H) + upsilon l * (J : Ordinal.{0}) + P) =
            upsilon (μ + f H) + upsilon μ * (J : Ordinal.{0}) + P := by
          have := (hW.add _ (hYr _ (hIm J le_rfl)) _ (Finset.mem_union_left _ hPm) _ (hYr _ hSm)).1 rfl
          rw [hDI J le_rfl, hDP] at this
          exact this.symm
        have h3 : D y' ≤ D (upsilon (l + H) + upsilon l * (J : Ordinal.{0}) + P) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (hYr _ hSm) (hr' ▸ hyr)
        rw [hDS] at h3
        exact h3.trans (hfrm H hHO J P (hh0 _ hrp) (hXγ P hPm) hr')
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Sl
