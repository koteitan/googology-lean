import Googology.Trans.PoR.InaccPsi.R2.TvReal
import Googology.Trans.PoR.InaccPsi.R2.UbShift

/-!
# Realizers with a fourth form of inner reaches: non-pure countable-argument terms

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Tv.tvReal_gen` with `Ub.ubShiftCore` in place of `Tv.tvShiftCore`, and a fourth form of the reach `r(λ+g)` of an
inner restart: `r(λ+g) ∈ seg(υ_{λ+h})` is the value `t[υ_{λ+h}; p]` of a countable-argument term whose leaves are
ordinals below `υ_λ` or inner `υ`-points `υ_{λ+h'}` (`UbForm`; the parameters of `r(λ+g)` over `υ_{λ+h}` may lie in
lower segments).  The realizer map carries it to `t[υ_{μ+f(h)}; ρ p]`, `ρ = ubLf λ μ f` (fixed below `υ_λ`,
`υ_{λ+h'} ↦ υ_{μ+f(h')}`), by the hull isomorphism of `Ub.ubShiftCore`; EQ at it is `UbCarry`.

* `ubLf` (**the leaf map**), `UbForm` (**the fourth form**), `UbCarry` (**EQ at the fourth form**);
* `ubReal_gen` (**`LrReal S υ_λ υ_{λ+β}` from UPPER at the inner restarts, the four forms of their reaches, the
  supply, `Tv.TvCarry` and `UbCarry`**).

No new axiom (beyond `R2.tvSeg_pi`).  New definitions: `ubLf`, `UbForm`, `UbCarry` (statements and the leaf map).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ub

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Sr
  Googology.Trans.PoR.InaccPsi.R2.Tv

variable {S : InaccSeq.{0}}

/-- **The leaf map** of the realizer along `υ_λ ↦ υ_μ`, offsets `f`: identity below `υ_λ`,
`υ_{λ+h'} ↦ υ_{μ+f(h')}`. -/
noncomputable def ubLf (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (p : Ordinal.{0}) : Ordinal.{0} :=
  if p < upsilon l then p else upsilon (μ + f (lrIx p - l))

/-- **The fourth form of the reach of the inner restart `λ+g`**: `r(λ+g) ∈ seg(υ_{λ+h})` is `t[υ_{λ+h}; p]` for a
countable-argument term `t` with the argument bounds whose leaves are below `υ_λ` or inner `υ`-points
`υ_{λ+h'}`, `h' < β`. -/
def UbForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ h t, 0 < h ∧ h < β ∧ UbT.IsA t ∧ UbT.WF (upsilon (l + h)) t ∧
    UbT.Lv (fun p => p < upsilon l ∨ ∃ h', h' < β ∧ p = upsilon (l + h')) t ∧
    upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
    UbT.ev (upsilon (l + h)) t = cdR S (l + g)

/-- **The three forms of `Tv.tvReal_gen`** for the reach of the inner restart `λ+g`. -/
def UbF3 (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  upsilon (l + β) ≤ cdR S (l + g) ∨
    (∃ h c, 0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c) ∨
    ∃ h, 0 < h ∧ h < β ∧ TvLowAt S l g h

/-- **EQ at the fourth form**: `t[υ_{μ+f(h)}; ρ p] ≤ r(μ+f(g))` whenever `r(λ+g) = t[υ_{λ+h}; p]` (leaves below
`υ_λ` or `υ_{λ+h'}` with `h' ∈ Os`), asked only at the inner restarts whose reach has none of the three forms of
`Tv.tvReal_gen`. -/
def UbCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → g < β → ω ^ 2 ∣ g → ¬ UbF3 S l β g → ∀ h ∈ Os, 0 < h → ∀ t : UbT, UbT.IsA t →
    UbT.WF (upsilon (l + h)) t →
    UbT.Lv (fun p => p < upsilon l ∨ ∃ h' ∈ Os, p = upsilon (l + h')) t →
    upsilon (l + h) ≤ cdR S (l + g) → cdR S (l + g) < upsilon (succ (l + h)) →
    UbT.ev (upsilon (l + h)) t = cdR S (l + g) →
    UbT.ev (upsilon (μ + f h)) (t.map (ubLf l μ f)) ≤ cdR S (μ + f g)

/-- **Realizer maps along an offset map with four forms of inner reaches**: the inner reaches `υ_{λ+h} + c`
(`c < υ_{λ+1}`) carried to `υ_{μ+f(h)} + π_{υ_μ,υ_λ}(c)`, the inner reaches in `seg(υ_{λ+h})` with parameters below
`υ_λ` carried by the segment move `mv υ_{λ+h} υ_{μ+f(h)}`, and the inner reaches `t[υ_{λ+h}; p]` (`UbForm`) carried
to `t[υ_{μ+f(h)}; ρ p]` by the hull isomorphism. -/
theorem ubReal_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TvCarry S l β μ f B Os ∧ UbCarry S l β μ f Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  have hlE : InE (upsilon l) := upsPt_inE ha
  -- the inner restarts of `Y` whose reach has the form `υ_{λ+h} + c`
  set rp : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    ∃ h c, 0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c with hrpdef
  have hch : ∀ y, rp y → ∃ g h c, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c := by
    rintro y ⟨g, hg, h, c, h0, h1, h2, h3⟩
    exact ⟨g, h, c, hg, h0, h1, h2, h3⟩
  choose! gf hf cf hgf hh0 hhf hcf hrf using hch
  -- the inner restarts of `Y` whose reach is a low point of an inner segment
  set rq : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    ∃ h, 0 < h ∧ h < β ∧ TvLowAt S l g h with hrqdef
  have hcq : ∀ y, rq y → ∃ g h, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      0 < h ∧ h < β ∧ TvLowAt S l g h := by
    rintro y ⟨g, hg, h, h0, h1, h2⟩
    exact ⟨g, h, hg, h0, h1, h2⟩
  choose! gq hq hgq hq0 hqβ hqL using hcq
  -- the inner restarts of `Y` whose reach has the fourth form
  set r4 : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    UbForm S l β g with hr4def
  have hc4 : ∀ y, r4 y → ∃ g h t, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧ 0 < h ∧ h < β ∧
      UbT.IsA t ∧ UbT.WF (upsilon (l + h)) t ∧
      UbT.Lv (fun p => p < upsilon l ∨ ∃ h', h' < β ∧ p = upsilon (l + h')) t ∧
      upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
      UbT.ev (upsilon (l + h)) t = cdR S (l + g) := by
    rintro y ⟨g, hg, h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨g, h, t, hg, h0, h1, h2, h3, h4, h5, h6, h7⟩
  choose! g4 h4 t4 hg4 h40 h4β hA4 hW4 hL4 hlo4 hhi4 hev4 using hc4
  set T3 := Y.filter r4 with hT3def
  set A3 : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    insert (upsilon (l + h4 y)) (insert (cdR S (l + g4 y)) ((UbT.lvs (t4 y)).filter (upsilon l ≤ ·)))
    with hA3def
  set T2 := Y.filter rq with hT2def
  set A2 : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    {upsilon (l + hq y), cdR S (l + gq y)} with hA2def
  set T := Y.filter rp with hTdef
  set A : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    {upsilon (l + hf y), upsilon (l + hf y) + cf y} ∪
    (if upsilon l ≤ cf y then {cf y} else ∅) with hAdef
  set Y' := Y ∪ T.biUnion A ∪ T2.biUnion A2 ∪ T3.biUnion A3 with hY'def
  set X' := X ∪ (T.image cf).filter (· < upsilon l) ∪
    T3.biUnion (fun y => (UbT.lvs (t4 y)).filter (· < upsilon l)) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact hX x hx
      · exact (Finset.mem_filter.1 hx).2
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxu).2
  -- the added points lie in `[υ_λ, υ_{λ+β})`
  have hA : ∀ y ∈ T, ∀ z ∈ A y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    have hh0' := hh0 y hr
    have hhβ := hhf y hr
    have hcl := hcf y hr
    have hlh : upsilon l < upsilon (l + hf y) := hm (lt_add_of_pos_right l hh0')
    have hEs := Sl.slUpsE (l + hf y)
    have hhs : upsilon (l + hf y) < upsilon (succ (l + hf y)) := hm (lt_succ _)
    have hsβ : upsilon (succ (l + hf y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt hhβ)
    have hcs : cf y < upsilon (succ (l + hf y)) :=
      hcl.trans_le (hm.monotone (Order.succ_le_succ le_self_add))
    have hsum : upsilon (l + hf y) + cf y < upsilon (succ (l + hf y)) := hEs.add_lt hhs hcs
    rcases Finset.mem_union.1 hz with hz | hz
    · rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hlh.le, hhs.trans_le hsβ⟩
      · rw [Finset.mem_singleton.1 hz]
        exact ⟨hlh.le.trans le_self_add, hsum.trans_le hsβ⟩
    · by_cases hc : upsilon l ≤ cf y
      · rw [if_pos hc, Finset.mem_singleton] at hz
        rw [hz]
        refine ⟨hc, hcl.trans_le (hm.monotone ?_)⟩
        exact Order.succ_le_of_lt (lt_add_of_pos_right l (hh0'.trans hhβ))
      · rw [if_neg hc] at hz; exact absurd hz (Finset.notMem_empty _)
  have hA2 : ∀ y ∈ T2, ∀ z ∈ A2 y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    obtain ⟨hL1, hL2, -⟩ := hqL y hr
    have hh0' := hq0 y hr
    have hlh : upsilon l < upsilon (l + hq y) := hm (lt_add_of_pos_right l hh0')
    have hsβ : upsilon (succ (l + hq y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt (hqβ y hr))
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hlh.le, (hm (lt_succ _)).trans_le hsβ⟩
    · rw [Finset.mem_singleton.1 hz]
      exact ⟨hlh.le.trans hL1, hL2.trans_le hsβ⟩
  have hA3 : ∀ y ∈ T3, ∀ z ∈ A3 y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    have hh0' := h40 y hr
    have hlh : upsilon l < upsilon (l + h4 y) := hm (lt_add_of_pos_right l hh0')
    have hsβ : upsilon (succ (l + h4 y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt (h4β y hr))
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hlh.le, (hm (lt_succ _)).trans_le hsβ⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hlh.le.trans (hlo4 y hr), (hhi4 y hr).trans_le hsβ⟩
    obtain ⟨hzl, hlz⟩ := Finset.mem_filter.1 hz
    rcases UbT.mem_lvs (hL4 y hr) z hzl with hzl' | ⟨h', hh', rfl⟩
    · exact absurd hzl' (not_lt.2 hlz)
    · exact ⟨hlz, hm (add_lt_add_right hh' l)⟩
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 hy with hy | hy
      · rcases Finset.mem_union.1 hy with hy | hy
        · exact hY y hy
        · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
          exact hA u hu y hyu
      · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
        exact hA2 u hu y hyu
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      exact hA3 u hu y hyu
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll, hubAll⟩ :=
    ubShiftCore (Q := fun μ f B _ Os => TvCarry S l β μ f B Os ∧ UbCarry S l β μ f Os) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩) hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
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
    obtain ⟨hLow, hbig, hfrm⟩ := hQ.1.1 g hgO hg0 hgd
    have hmono : ∀ u ∈ X' ∪ Y', ∀ v ∈ X' ∪ Y', u ≤ v → D u ≤ D v := fun u hu v hv huv =>
      (hW.mono.le_iff_le (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv)).2 huv
    have hle : D y' ≤ cdR S (μ + f g) := by
      by_cases h3 : UbF3 S l β g
      · rcases h3 with hb | ⟨h, c, hh0', hh, hc, hrr⟩ | ⟨h, hh0', hh, hLw⟩
        · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
        · have hrp : rp (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h, c, hh0', hh, hc, hrr⟩
          have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrp⟩
          have hgg : gf (upsilon (l + g)) = g := by
            have e := (hgf _ hrp).2.2.2
            exact (add_left_cancel (hm.injective e)).symm
          have hr' := hrf _ hrp
          rw [hgg] at hr'
          set H := hf (upsilon (l + g)) with hHdef
          set C := cf (upsilon (l + g)) with hCdef
          have hAY : ∀ z ∈ A (upsilon (l + g)), z ∈ Y' := fun z hz =>
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, hz⟩)))
          have hHm : upsilon (l + H) ∈ Y' := hAY _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
          have hSm : upsilon (l + H) + C ∈ Y' :=
            hAY _ (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          have hDH : D (upsilon (l + H)) = upsilon (μ + f H) := (hres H hHm).2
          have hHO : H ∈ Os := (hres H hHm).1
          have hYr : ∀ u ∈ Y', u ∈ X' ∪ Y' := fun u hu => Finset.mem_union_right _ hu
          have hCl : C < upsilon (succ l) := hcf _ hrp
          have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hW.rng.1.1))
          have hB : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
          -- `D(c) = π_{υ_μ,υ_λ}(c)`, and `c` lies in the configuration
          have hCm : C ∈ X' ∪ Y' ∧ D C = pi (upsilon μ) (upsilon l) C := by
            by_cases hc : upsilon l ≤ C
            · have hCY : C ∈ Y' := hAY _ (Finset.mem_union_right _ (by
                rw [if_pos hc]; exact Finset.mem_singleton_self _))
              exact ⟨hYr _ hCY, hpi _ hCY hCl⟩
            · have hCX : C ∈ X' := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2
                ⟨Finset.mem_image_of_mem _ hT, not_le.1 hc⟩))
              refine ⟨Finset.mem_union_left _ hCX, ?_⟩
              rw [hW.fix C hCX, pi_lt hB ((hXγ C hCX).trans hγμ)]
          have hDS : D (upsilon (l + H) + C) = upsilon (μ + f H) + pi (upsilon μ) (upsilon l) C := by
            have := (hW.add _ (hYr _ hHm) _ hCm.1 _ (hYr _ hSm)).1 rfl
            rw [hDH, hCm.2] at this
            exact this.symm
          have h3 : D y' ≤ D (upsilon (l + H) + C) :=
            hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (hYr _ hSm) (hr' ▸ hyr)
          rw [hDS] at h3
          exact h3.trans (hfrm H hHO C (hh0 _ hrp) hCl hr')
        · -- a low point of the inner segment `seg(υ_{λ+h})`: the segment move
          have hrq : rq (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h, hh0', hh, hLw⟩
          have hT2 : upsilon (l + g) ∈ T2 := Finset.mem_filter.2 ⟨hy, hrq⟩
          have hgg : gq (upsilon (l + g)) = g := by
            have e := (hgq _ hrq).2.2.2
            exact (add_left_cancel (hm.injective e)).symm
          have hL := hqL _ hrq
          rw [hgg] at hL
          set H := hq (upsilon (l + g)) with hHdef
          have hAY : ∀ z ∈ A2 (upsilon (l + g)), z ∈ Y' := fun z hz =>
            Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT2, hz⟩))
          have hHm : upsilon (l + H) ∈ Y' := hAY _ (Finset.mem_insert_self _ _)
          have hRm : cdR S (l + g) ∈ Y' := hAY _ (Finset.mem_insert_of_mem (by
            rw [hgg]; exact Finset.mem_singleton_self _))
          have hHO : H ∈ Os := (hres H hHm).1
          have hDR : D (cdR S (l + g)) = mv (upsilon (l + H)) (upsilon (μ + f H)) (cdR S (l + g)) :=
            hmvAll _ hRm H hL.1 hL.2.1 hL.2.2
          have h3 : D y' ≤ D (cdR S (l + g)) :=
            hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (Finset.mem_union_right _ hRm) hyr
          rw [hDR] at h3
          exact h3.trans (hQ.1.2 g hgO hg0 hgd H hHO (hq0 _ hrq) hL)
      · -- the fourth form: the hull isomorphism on the term `t`, leaves fixed below `υ_λ` or inner `υ`-points
        have h4f : UbForm S l β g := (hform g hg0 hgβ hgd).resolve_left h3
        have hr4 : r4 (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h4f⟩
        have hT3 : upsilon (l + g) ∈ T3 := Finset.mem_filter.2 ⟨hy, hr4⟩
        have hgg : g4 (upsilon (l + g)) = g := by
          have e := (hg4 _ hr4).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hlo := hlo4 _ hr4
        have hhi := hhi4 _ hr4
        have hev := hev4 _ hr4
        rw [hgg] at hlo hhi hev
        have hAY : ∀ z ∈ A3 (upsilon (l + g)), z ∈ Y' := fun z hz =>
          Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT3, hz⟩)
        have hRm : cdR S (l + g) ∈ Y' := hAY _ (Finset.mem_insert_of_mem (by
          rw [hgg]; exact Finset.mem_insert_self _ _))
        have hleaf : ∀ p ∈ UbT.lvs (t4 (upsilon (l + g))), p ∈ X' ∪ Y' ∧ D p = ubLf l μ f p ∧
            (p < upsilon l ∨ ∃ h' ∈ Os, p = upsilon (l + h')) := by
          intro p hp
          have hLp := UbT.mem_lvs (hL4 _ hr4) p hp
          by_cases hpl : p < upsilon l
          · have hpX : p ∈ X' := Finset.mem_union_right _ (Finset.mem_biUnion.2
              ⟨_, hT3, Finset.mem_filter.2 ⟨hp, hpl⟩⟩)
            refine ⟨Finset.mem_union_left _ hpX, ?_, Or.inl hpl⟩
            rw [hW.fix p hpX]; simp only [ubLf, if_pos hpl]
          · obtain ⟨h', -, rfl⟩ := hLp.resolve_left hpl
            have hpY : upsilon (l + h') ∈ Y' := hAY _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_filter.2 ⟨hp, not_lt.1 hpl⟩)))
            obtain ⟨hO', hD'⟩ := hres h' hpY
            refine ⟨Finset.mem_union_right _ hpY, ?_, Or.inr ⟨h', hO', rfl⟩⟩
            rw [hD']; simp only [ubLf, if_neg hpl, lrIx_up, Ordinal.add_sub_cancel]
        have hHO : h4 (upsilon (l + g)) ∈ Os := (hres _ (hAY _ (Finset.mem_insert_self _ _))).1
        have hLt := UbT.Lv_lvs (t4 (upsilon (l + g)))
        obtain ⟨e1, -⟩ := hubAll _ hRm _ hlo hhi _ (hA4 _ hr4) (hW4 _ hr4)
          (UbT.Lv_mono (fun p hp => (hleaf p hp).1) _ hLt) hev
        have hmap : (t4 (upsilon (l + g))).map D = (t4 (upsilon (l + g))).map (ubLf l μ f) :=
          UbT.map_congr _ (UbT.Lv_mono (fun p hp => (hleaf p hp).2.1) _ hLt)
        rw [hmap] at e1
        have h5 : D y' ≤ D (cdR S (l + g)) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (Finset.mem_union_right _ hRm) hyr
        rw [e1] at h5
        exact h5.trans (hQ.2 g hgO hg0 hgβ hgd h3 _ hHO (h40 _ hr4) _ (hA4 _ hr4) (hW4 _ hr4)
          (UbT.Lv_mono (fun p hp => (hleaf p hp).2.2) _ hLt) hlo hhi hev)
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Ub
