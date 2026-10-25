import Googology.Trans.PoR.InaccPsi.R2.SrReal
import Googology.Trans.PoR.InaccPsi.R2.TvShift

/-!
# Realizers along an offset map with the segment move on every inner segment

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Sr.srReal_gen` with `Tv.tvShiftCore` in place of `So.soShiftCore`.  An inner restart `λ+g` of `[υ_λ, υ_{λ+β})` may
now have its reach `r(λ+g)` in any inner segment `seg(υ_{λ+h})` (`0 < h < β`) as long as the parameters of `r(λ+g)`
over `υ_{λ+h}` lie below `υ_λ` (`TvLowAt`; e.g. `r = δ + ρ²`-type reaches whose term over `υ_{λ+h}` uses only `0`):
the realizer map carries it by the segment move `mv υ_{λ+h} υ_{μ+f(h)} = π_{υ_{μ+f(h)}, υ_{λ+h}}`.

* `TvLowAt S λ g h` (**`r(λ+g) ∈ seg(υ_{λ+h})` with parameters below `υ_λ`**);
* `TvCarry` (**`Sr.SrCarry` plus EQ for the segment move: `mv υ_{λ+h} υ_{μ+f(h)} (r(λ+g)) ≤ r(μ+f(g))`**);
* `tvReal_gen` (**`LrReal S υ_λ υ_{λ+β}` from UPPER at the inner restarts, the three forms of their reaches
  (`≥ υ_{λ+β}`, `υ_{λ+h} + c` with `c < υ_{λ+1}`, `TvLowAt`), the supply and `TvCarry`**).

No new axiom (beyond `R2.tvSeg_pi`).  New definitions: `TvLowAt`, `TvCarry` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Sr

variable {S : InaccSeq.{0}}

/-- **The reach of the inner restart `λ+g` is a point of `seg(υ_{λ+h})` with parameters below `υ_λ`.** -/
def TvLowAt (S : InaccSeq.{0}) (l g h : Ordinal.{0}) : Prop :=
  upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
    ∀ p ∈ Par (upsilon (l + h)) (cdR S (l + g)), p < upsilon l

/-- **EQ for an offset map: `Sr.SrCarry` and the segment move at the low reaches of inner segments.** -/
def TvCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  SrCarry S l β μ f B Os ∧
    ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → ∀ h ∈ Os, 0 < h → TvLowAt S l g h →
      mv (upsilon (l + h)) (upsilon (μ + f h)) (cdR S (l + g)) ≤ cdR S (μ + f g)

/-- `TvCarry` gives `Sr.SrCarry`. -/
theorem tvCarry_sr {l β μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (h : TvCarry S l β μ f B Os) : SrCarry S l β μ f B Os := h.1

/-- `Sr.SrCarry` gives `TvCarry` when no inner reach is a low point of a later inner segment. -/
theorem tvCarry_of_sr {l β μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (h : SrCarry S l β μ f B Os) (hno : ∀ g ∈ Os, ∀ h ∈ Os, 0 < h → ¬ TvLowAt S l g h) :
    TvCarry S l β μ f B Os :=
  ⟨h, fun g hg _ _ h' hh' hh0 hL => absurd hL (hno g hg h' hh' hh0)⟩

/-- **Realizer maps along an offset map**: the inner reaches `υ_{λ+h} + c` (`c < υ_{λ+1}`) carried to
`υ_{μ+f(h)} + π_{υ_μ,υ_λ}(c)`, and the inner reaches in `seg(υ_{λ+h})` with parameters below `υ_λ` carried by the
segment move `mv υ_{λ+h} υ_{μ+f(h)}`. -/
theorem tvReal_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨
      (∃ h c, 0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c) ∨
      ∃ h, 0 < h ∧ h < β ∧ TvLowAt S l g h)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TvCarry S l β μ f B Os)
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
  set T2 := Y.filter rq with hT2def
  set A2 : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    {upsilon (l + hq y), cdR S (l + gq y)} with hA2def
  set T := Y.filter rp with hTdef
  set A : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    {upsilon (l + hf y), upsilon (l + hf y) + cf y} ∪
    (if upsilon l ≤ cf y then {cf y} else ∅) with hAdef
  set Y' := Y ∪ T.biUnion A ∪ T2.biUnion A2 with hY'def
  set X' := X ∪ (T.image cf).filter (· < upsilon l) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    · exact (Finset.mem_filter.1 hx).2
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
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 hy with hy | hy
      · exact hY y hy
      · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
        exact hA u hu y hyu
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      exact hA2 u hu y hyu
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll⟩ :=
    tvShiftCore (Q := fun μ f B _ Os => TvCarry S l β μ f B Os) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩) hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ hx
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ (Finset.mem_union_left _ hy)
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
    obtain ⟨hLow, hbig, hfrm⟩ := hQ.1 g hgO hg0 hgd
    have hmono : ∀ u ∈ X' ∪ Y', ∀ v ∈ X' ∪ Y', u ≤ v → D u ≤ D v := fun u hu v hv huv =>
      (hW.mono.le_iff_le (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv)).2 huv
    have hle : D y' ≤ cdR S (μ + f g) := by
      rcases hform g hg0 hgβ hgd with hb | ⟨h, c, hh0', hh, hc, hrr⟩ | ⟨h, hh0', hh, hLw⟩
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
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT, hz⟩))
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
          · have hCX : C ∈ X' := Finset.mem_union_right _ (Finset.mem_filter.2
              ⟨Finset.mem_image_of_mem _ hT, not_le.1 hc⟩)
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
          Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT2, hz⟩)
        have hHm : upsilon (l + H) ∈ Y' := hAY _ (Finset.mem_insert_self _ _)
        have hRm : cdR S (l + g) ∈ Y' := hAY _ (Finset.mem_insert_of_mem (by
          rw [hgg]; exact Finset.mem_singleton_self _))
        have hHO : H ∈ Os := (hres H hHm).1
        have hDR : D (cdR S (l + g)) = mv (upsilon (l + H)) (upsilon (μ + f H)) (cdR S (l + g)) :=
          hmvAll _ hRm H hL.1 hL.2.1 hL.2.2
        have h3 : D y' ≤ D (cdR S (l + g)) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (Finset.mem_union_right _ hRm) hyr
        rw [hDR] at h3
        exact h3.trans (hQ.2 g hgO hg0 hgd H hHO (hq0 _ hrq) hL)
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Tv
