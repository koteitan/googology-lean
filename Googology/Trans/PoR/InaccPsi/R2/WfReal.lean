import Googology.Trans.PoR.InaccPsi.R2.WfCarry

/-!
# Realizers from the restricted carry

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`Vr.vrReal_gen` with `Vr.VrCarry` replaced by `WfCarry`: the configuration handed to `Vl.vlShiftCore` contains the
low points of the chosen decompositions and their low parameters (`wfPrm`); they all lie below the base
`γ < υ_μ`, so the chosen decompositions satisfy `WfR λ μ` (`wfR_of`) and the restricted image clause applies.

* `wfReal_gen` (**realizer maps from UPPER, the forms, and the supply with `WfCarry`**), `wfReal_of_gen`;
* `wfVisI_of_gen` (**`WfVisGen ⇒ Tk.TkVisI`**), `wfVis_all` (at `m*` and every `L(n+1)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Tk

variable {S : InaccSeq.{0}}

/-- **Realizer maps from the restricted carry**: UPPER at the inner restarts, the forms
`υ_{λ+β} ≤ r(λ+g) ∨ VrForm`, and the supply with `WfCarry` give `LrReal S υ_λ υ_{λ+β}`. -/
theorem wfReal_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ Vr.VrForm S l β g)
    (hsup : WfSup S l β)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have ha : UpsPt (upsilon l) := upsPt_upsilon hl0
  have hlE : InE (upsilon l) := upsPt_inE ha
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  set rr : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    Vr.VrForm S l β g with hrrdef
  have hch : ∀ y, rr y → ∃ g, ∃ E : Vr.VrE, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      Vr.VrWF l β E ∧ Vr.vrVal l E = cdR S (l + g) := by
    rintro y ⟨g, hg, E, hW, hv⟩
    exact ⟨g, E, hg, hW, hv⟩
  choose! gE EE hgE hWE hvE using hch
  set T := Y.filter rr with hTdef
  set Y' := Y ∪ T.biUnion (fun y => (Vr.vrPts l (EE y)).filter (upsilon l ≤ ·)) with hY'def
  set X' := X ∪ (T.biUnion (fun y => (Vr.vrPts l (EE y)).filter (· < upsilon l)) ∪
    T.biUnion (fun y => wfPrm l (EE y))) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxu).2
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact wfPrm_lt l _ x hxu
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hyp, hly⟩ := Finset.mem_filter.1 hyu
      have hr := (Finset.mem_filter.1 hu).2
      exact ⟨hly, Vr.vrPts_lt ((hgE u hr).1.trans (hgE u hr).2.1) _ (hWE u hr) y hyp⟩
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll, hubAll, heAll, -, hDid, -⟩ :=
    vlShiftCore (Q := fun μ f B _ Os => WfCarry S l β μ f B Os) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩) hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ hx
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ hy
  have hsub : ∀ u ∈ X ∪ Y, u ∈ X' ∪ Y' := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Finset.mem_union_left _ (hXX u hu)
    · exact Finset.mem_union_right _ (hYY u hu)
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hW.rng.1.1))
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
  have hDE := Vr.vrD_eq (l := l) (β := β) (μ := μ) (γ := γ) (f := f) (D := D) (Os := Os) (X := X') (Y := Y')
    hl0 hb1 hX' hY' hW.fix hW.add hXγ hγμ hBμ hres hpi hmvAll hubAll heAll hDid
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
      rcases hform g hg0 hgβ hgd with hb | hF
      · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
      · have hrr : rr (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, hF⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrr⟩
        have hgg : gE (upsilon (l + g)) = g := by
          have e := (hgE _ hrr).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hv := hvE _ hrr
        rw [hgg] at hv
        set E := EE (upsilon (l + g)) with hEdef
        have hlowX : ∀ z ∈ Vr.vrPts l E, z < upsilon l → z ∈ X' := fun z hz hzl =>
          Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩))
        have hpts : ∀ z ∈ Vr.vrPts l E, z ∈ X' ∪ Y' := by
          intro z hz
          by_cases hzl : upsilon l ≤ z
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩))
          · exact Finset.mem_union_left _ (hlowX z hz (not_le.1 hzl))
        have hR : WfR l μ E := wfR_of hl0 hBμ E (hWE _ hrr)
          (fun z hz hzl => (hXγ z (hlowX z hz hzl)).trans hγμ)
          (fun q hq => (hXγ q (Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨_, hT, hq⟩)))).trans hγμ)
        obtain ⟨e1, hOs⟩ := hDE E (hWE _ hrr) hpts
        have hRm : cdR S (l + g) ∈ X' ∪ Y' := hv ▸ hpts _ (Vr.vrVal_mem l E)
        have h5 : D y' ≤ D (cdR S (l + g)) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ hRm hyr
        rw [← hv, e1] at h5
        exact h5.trans (hfrm E (hWE _ hrr) hv hOs hR)
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

/-- **`WfGen` gives the realizer.** -/
theorem wfReal_of_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S)
    (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) (h : WfGen S l β) : LrReal S (upsilon l) (upsilon (l + β)) :=
  wfReal_gen hl hl1 hν hνβ h.1 h.2.1 h.2.2 hstd hlL

/-- **`WfVisGen` gives the visible statements `Tk.TkVisI`.** -/
theorem wfVisI_of_gen (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l) (hb : b ≤ nuC)
    (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : WfVisGen S l b c) :
    TkVisI S (upsilon l) b c := by
  refine tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, wfReal_of_gen hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `WfVisGen`. -/
theorem wfVis_all (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      WfVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      WfVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
      ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hstd : Cx.CxStdPairTop S := Tp.tpStdPairTop hν
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hlt : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := fun k =>
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    have h1 : Nc.ncL S 1 ≤ Nc.ncL S (ω + 1) := by simpa using hlt 0
    have := wfVisI_of_gen hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := wfVisI_of_gen hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

end Googology.Trans.PoR.InaccPsi.R2.Wf
