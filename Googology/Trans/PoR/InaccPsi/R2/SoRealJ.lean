import Googology.Trans.PoR.InaccPsi.R2.SoShift

/-!
# Realizers along a renaming of the offsets, with inner reaches `υ_{λ+h} + υ_λ·J + p` for ordinal `J`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`a = υ_λ` a restart, `r(λ) = Cd.cdR S λ`.  `Sl.slReal_ren` carries inner reaches `υ_{λ+h} + υ_λ·j + p` with
`j < ω` only: the realizer map keeps `+` and sends `υ_λ ↦ υ_μ`, which fixes `υ_λ·j` for finite `j` but not
`υ_λ·ω`.  With `So.soShiftCore` the map is `π_{υ_μ, υ_λ}` on `seg(υ_λ)`, and `R2.pi_mul` gives
`π_{υ_μ,υ_λ}(υ_λ·J) = υ_μ·J` for every `J < υ_μ`.  So the codes `a·J + p` of the inner reaches (for instance
`a·ω`, the code of the offset `a^ω`) are carried:

* `SoCarry S λ β μ f B γ Os` (**EQ for the renaming with ordinal `J`**): as `Sl.SlCarry` with `J < γ` in place
  of `j < ω`;
* `soReal_ren` (**`LrReal S υ_λ υ_{λ+β}` from UPPER at the inner restarts, the form `υ_{λ+h} + υ_λ·J + p`
  (`J, p < υ_λ`) or `≥ υ_{λ+β}` of their reaches, and Range restarts with an offset map, the supply and
  `SoCarry`**): the configuration is enlarged by `υ_{λ+h}`, `υ_λ·J`, `υ_{λ+h} + υ_λ·J`,
  `υ_{λ+h} + υ_λ·J + p`, `J` and `p`.

No new axiom.  New definition: `SoCarry`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **EQ for an offset map at the inner restarts of `Os`, with ordinal multipliers.** -/
def SoCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B γ : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ h ∈ Os, ∀ J p : Ordinal.{0}, 0 < h → J < γ → p < γ →
      cdR S (l + g) = upsilon (l + h) + upsilon l * J + p →
      upsilon (μ + f h) + upsilon μ * J + p ≤ cdR S (μ + f g)

/-- **Realizer maps along an offset map, with the carry of the inner reaches `υ_{λ+h} + υ_λ·J + p`.** -/
theorem soReal_ren {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨
      ∃ h J p, 0 < h ∧ h < β ∧ J < upsilon l ∧ p < upsilon l ∧
        cdR S (l + g) = upsilon (l + h) + upsilon l * J + p)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ SoCarry S l β μ f B γ Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  have hlE : InE (upsilon l) := upsPt_inE ha
  -- the inner restarts of `Y` whose reach has the form `υ_{λ+h} + υ_λ·J + p`
  set rp : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    ∃ h J p, 0 < h ∧ h < β ∧ J < upsilon l ∧ p < upsilon l ∧
      cdR S (l + g) = upsilon (l + h) + upsilon l * J + p with hrpdef
  have hch : ∀ y, rp y → ∃ g h J p, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      0 < h ∧ h < β ∧ J < upsilon l ∧ p < upsilon l ∧
      cdR S (l + g) = upsilon (l + h) + upsilon l * J + p := by
    rintro y ⟨g, hg, h, J, p, h0, h1, h2, h3, h4⟩
    exact ⟨g, h, J, p, hg, h0, h1, h2, h3, h4⟩
  choose! gf hf Jf pf hgf hh0 hhf hJf hpf hrf using hch
  set T := Y.filter rp with hTdef
  set A : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    {upsilon (l + hf y), upsilon (l + hf y) + upsilon l * Jf y,
      upsilon (l + hf y) + upsilon l * Jf y + pf y} ∪
    (if Jf y = 0 then ∅ else {upsilon l * Jf y}) with hAdef
  set Y' := Y ∪ T.biUnion A with hY'def
  set X' := X ∪ T.image pf ∪ T.image Jf with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact hX x hx
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hpf y (Finset.mem_filter.1 hy).2
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact hJf y (Finset.mem_filter.1 hy).2
  -- the added points lie in `[υ_λ, υ_{λ+β})`
  have hA : ∀ y ∈ T, ∀ z ∈ A y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    have hh0' := hh0 y hr
    have hhβ := hhf y hr
    have hpl := hpf y hr
    have hJl := hJf y hr
    have hlh : upsilon l < upsilon (l + hf y) := hm (lt_add_of_pos_right l hh0')
    have hEs := Sl.slUpsE (l + hf y)
    have hhs : upsilon (l + hf y) < upsilon (succ (l + hf y)) := hm (lt_succ _)
    have hsβ : upsilon (succ (l + hf y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt hhβ)
    have hmul : upsilon l * Jf y < upsilon (succ (l + hf y)) :=
      Sl.slE_mul_lt hEs (hlh.trans hhs) (hJl.trans (hlh.trans hhs))
    have hsum : upsilon (l + hf y) + upsilon l * Jf y < upsilon (succ (l + hf y)) :=
      hEs.add_lt hhs hmul
    have hge : upsilon l ≤ upsilon (l + hf y) + upsilon l * Jf y := hlh.le.trans le_self_add
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hlh.le, hhs.trans_le hsβ⟩
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact ⟨hge, hsum.trans_le hsβ⟩
        · rw [Finset.mem_singleton.1 hz]
          exact ⟨hge.trans le_self_add,
            (hEs.add_lt hsum (hpl.trans (hlh.trans hhs))).trans_le hsβ⟩
    · by_cases hJ0 : Jf y = 0
      · rw [if_pos hJ0] at hz; exact absurd hz (Finset.notMem_empty _)
      · rw [if_neg hJ0, Finset.mem_singleton] at hz
        rw [hz]
        refine ⟨Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hJ0), ?_⟩
        have hEl := Sl.slUpsE l
        have hls : upsilon l < upsilon (succ l) := hm (lt_succ l)
        refine (Sl.slE_mul_lt hEl hls (hJl.trans hls)).trans_le (hm.monotone ?_)
        exact Order.succ_le_of_lt (lt_add_of_pos_right l (hh0'.trans hhβ))
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      exact hA u hu y hyu
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, hμl, hpi⟩ :=
    soShiftCore (Q := SoCarry S l β) hl hl1 hν hνβ hsup hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
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
      rcases hform g hg0 hgβ hgd with hb | ⟨h, J, p, hh0', hh, hJ, hp, hrr⟩
      · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
      · have hrp : rp (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h, J, p, hh0', hh, hJ, hp, hrr⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrp⟩
        have hgg : gf (upsilon (l + g)) = g := by
          have e := (hgf _ hrp).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hr' := hrf _ hrp
        rw [hgg] at hr'
        set H := hf (upsilon (l + g)) with hHdef
        set J' := Jf (upsilon (l + g)) with hJdef
        set P := pf (upsilon (l + g)) with hPdef
        have hAY : ∀ z ∈ A (upsilon (l + g)), z ∈ Y' := fun z hz =>
          Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT, hz⟩)
        have hHm : upsilon (l + H) ∈ Y' := hAY _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
        have hIm : upsilon (l + H) + upsilon l * J' ∈ Y' :=
          hAY _ (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        have hSm : upsilon (l + H) + upsilon l * J' + P ∈ Y' :=
          hAY _ (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_singleton_self _))))
        have hPm : P ∈ X' :=
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hT))
        have hJm : J' ∈ X' := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hT)
        have hDH : D (upsilon (l + H)) = upsilon (μ + f H) := (hres H hHm).2
        have hHO : H ∈ Os := (hres H hHm).1
        have hDP : D P = P := hW.fix P hPm
        have hYr : ∀ u ∈ Y', u ∈ X' ∪ Y' := fun u hu => Finset.mem_union_right _ hu
        have hJγ : J' < γ := hXγ J' hJm
        -- `D(υ_{λ+h} + υ_λ·J) = υ_{μ+f(h)} + υ_μ·J`: the map is `π_{υ_μ,υ_λ}` on `seg(υ_λ)`
        have hDI : D (upsilon (l + H) + upsilon l * J') = upsilon (μ + f H) + upsilon μ * J' := by
          by_cases hJ0 : J' = 0
          · have e0 : upsilon (l + H) + upsilon l * J' = upsilon (l + H) := by rw [hJ0, mul_zero, add_zero]
            rw [e0, hDH, hJ0, mul_zero, add_zero]
          · have hJm' : upsilon l * J' ∈ Y' := hAY _ (Finset.mem_union_right _ (by
              rw [if_neg hJ0]; exact Finset.mem_singleton_self _))
            have hμE : InE (upsilon μ) :=
              upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hW.rng.1.1))
            have hB : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
            have hls : upsilon l * J' < upsilon (succ l) := by
              have hl' : upsilon l < upsilon (succ l) := hm (lt_succ l)
              exact Sl.slE_mul_lt (Sl.slUpsE l) hl' ((hX' J' hJm).trans hl')
            have hDJ : D (upsilon l * J') = upsilon μ * J' := by
              rw [hpi _ hJm' hls]; exact (pi_mul hB J' (hJγ.trans hγμ)).2
            have := (hW.add _ (hYr _ hHm) _ (hYr _ hJm') _ (hYr _ hIm)).1 rfl
            rw [hDH, hDJ] at this
            exact this.symm
        have hDS : D (upsilon (l + H) + upsilon l * J' + P) = upsilon (μ + f H) + upsilon μ * J' + P := by
          have := (hW.add _ (hYr _ hIm) _ (Finset.mem_union_left _ hPm) _ (hYr _ hSm)).1 rfl
          rw [hDI, hDP] at this
          exact this.symm
        have h3 : D y' ≤ D (upsilon (l + H) + upsilon l * J' + P) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (hYr _ hSm) (hr' ▸ hyr)
        rw [hDS] at h3
        exact h3.trans (hfrm H hHO J' P (hh0 _ hrp) hJγ (hXγ P hPm) hr')
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.So
