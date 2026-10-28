import Googology.Trans.PoR.InaccPsi.R2.UyReal
import Googology.Trans.PoR.InaccPsi.R2.VlShift

/-!
# Realizers with inner reaches given by terms with the node `thz G r` (levels with moving leaves)

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Uy.uyReal_gen` with `Vl.vlShiftCore`: the fifth form of the reach `r(λ+g)` of an inner restart is `Uy.UyForm`
(constant levels with data below `υ_λ`) or the new `VlForm`: a term of `Un.UnT` with the node conditions `Vi.ZW`
(levels `Ω₁·q < B₂` with any countable leaves) whose parameters and level leaves are below `υ_λ` or inner `υ`-points
`υ_{λ+h'}`, `h' ≤ h` (a finite set `Lf` holds the level leaves).  The carry `VlCarry` is asked only where none of the
earlier forms holds.

* `vl_ZW_of_qsY`, `vl_ZL_of_qsY`, `vl_vmap_map` (**the terms of `Uy.QsY` are `thz`-terms with fixed level leaves**);
* `VlForm`, `VlCarry`;
* `vlReal_gen` (**realizer maps from the forms, the supply and the carries**).

New definitions: `VlForm`, `VlCarry` (statements).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Sr
  Googology.Trans.PoR.InaccPsi.R2.Tv Googology.Trans.PoR.InaccPsi.R2.Ub Googology.Trans.PoR.InaccPsi.R2.Uh
  Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Uy Googology.Trans.PoR.InaccPsi.R2.Vi

variable {S : InaccSeq.{0}}

/-! ## The terms of `Uy.QsY` are `thz`-terms -/

/-- **The constant levels of `Uy.QsY` satisfy the node conditions `Vi.ZW`** (`Uy.uy_Om1_mul_TB`, `Uy.uy_arg_T`,
`Uy.uyLt_vt_self`, `Uy.uyMem`). -/
theorem vl_ZW_of_qsY {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ {k : Bool} (t : UnT k), UnT.Lv (· ∈ Tset τ) t → WFr τ t → QsY κ t → ZW τ t
  | _, .par _, _, _, _ => trivial
  | _, .add s t, hl, hw, hq => ⟨vl_ZW_of_qsY hB s hl.1 hw.1 hq.1, vl_ZW_of_qsY hB t hl.2 hw.2 hq.2⟩
  | _, .base, _, _, _ => trivial
  | _, .th1 s, hl, hw, hq => vl_ZW_of_qsY hB s hl hw.1 hq
  | _, .thc q r, hl, hw, hq => by
    have hr := uyMem hB r hl hw.1 hq.2
    exact ⟨⟨hq.1.1, hq.1.2.1, (uy_Om1_mul_TB hB le_rfl hq.1).1.1, (uy_arg_T hB hq.1 hr hw.2).1,
      uyLt_vt_self hB hq.1 hr hw.2⟩, vl_ZW_of_qsY hB r hl hw.1 hq.2⟩
  | _, .thg _ G r, hl, hw, hq => ⟨vl_ZW_of_qsY hB G hl.1 hw.1 hq.1, vl_ZW_of_qsY hB r hl.2 hw.2.1 hq.2⟩
  | _, .lf c, hl, hw, hq => vl_ZW_of_qsY hB c hl hw.1 hq
  | _, .om b, hl, hw, hq => vl_ZW_of_qsY hB b hl hw hq
  | _, .ad x y, hl, hw, hq => ⟨vl_ZW_of_qsY hB x hl.1 hw.1 hq.1, vl_ZW_of_qsY hB y hl.2 hw.2 hq.2⟩

/-- **The level leaves of a `Uy.QsY κ`-term lie below `κ`** (`κ` an `ε`-number; `Vc.vc_dat_lt`). -/
theorem vl_ZL_of_qsY {κ : Ordinal.{0}} (hκ : InE κ) : ∀ {k : Bool} (t : UnT k), QsY κ t → ZL (· < κ) t
  | _, .par _, _ => trivial
  | _, .add s t, hq => ⟨vl_ZL_of_qsY hκ s hq.1, vl_ZL_of_qsY hκ t hq.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, hq => vl_ZL_of_qsY hκ s hq
  | _, .thc _ r, hq => ⟨(Vc.vc_dat_lt hκ _ hq.1.2.1).2 hq.1.2.2.2, vl_ZL_of_qsY hκ r hq.2⟩
  | _, .thg _ G r, hq => ⟨vl_ZL_of_qsY hκ G hq.1, vl_ZL_of_qsY hκ r hq.2⟩
  | _, .lf c, hq => vl_ZL_of_qsY hκ c hq
  | _, .om b, hq => vl_ZL_of_qsY hκ b hq
  | _, .ad x y, hq => ⟨vl_ZL_of_qsY hκ x hq.1, vl_ZL_of_qsY hκ y hq.2⟩

/-- **`vmap f = UnT.map f` when `f` fixes every level leaf** (`Vc.vcSub_fix`). -/
theorem vl_vmap_map (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ {k : Bool} (t : UnT k), ZL (fun x => f x = x) t → vmap f t = t.map f
  | _, .par _, _ => rfl
  | _, .add s t, h => by simp only [vmap, UnT.map, vl_vmap_map f s h.1, vl_vmap_map f t h.2]
  | _, .base, _ => rfl
  | _, .th1 s, h => by simp only [vmap, UnT.map, vl_vmap_map f s h]
  | _, .thc q r, h => by
    have hq : vq f q = q := by
      show Vc.vcSub f (Om1 * q) / Om1 = q
      rw [Vc.vcSub_fix _ h.1]; exact Ordinal.mul_div_cancel q Rj.rj_Om1_pos.ne'
    simp only [vmap, UnT.map, vl_vmap_map f r h.2, hq]
  | _, .thg _ G r, h => by simp only [vmap, UnT.map, vl_vmap_map f G h.1, vl_vmap_map f r h.2]
  | _, .lf c, h => by simp only [vmap, UnT.map, vl_vmap_map f c h]
  | _, .om b, h => by simp only [vmap, UnT.map, vl_vmap_map f b h]
  | _, .ad x y, h => by simp only [vmap, UnT.map, vl_vmap_map f x h.1, vl_vmap_map f y h.2]


/-- **The form with moving level leaves of the reach of the inner restart `λ+g`**: `r(λ+g) ∈ seg(υ_{λ+h})` is
`t[υ_{λ+h}; p]` for a term `t` of `Un.UnT` with the node conditions `Vi.ZW` (levels `Ω₁·q < B₂`, any countable
leaves) and the argument bounds `WFr`, whose parameters are below `υ_λ` or inner `υ`-points `υ_{λ+h'}`, `h' ≤ h`,
and whose level leaves lie in a finite set `Lf` of such points or below a bound `δ < υ_λ`. -/
def VlForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ h, ∃ t : UnC, ∃ Lf : Finset Ordinal.{0}, ∃ δ, 0 < h ∧ h < β ∧ δ < upsilon l ∧ ZW (upsilon (l + h)) t ∧
    WFr (upsilon (l + h)) t ∧ UnT.Lv (fun p => p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) t ∧
    ZL (fun p => p ∈ Lf ∨ p < δ) t ∧
    (∀ p ∈ Lf, p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) ∧
    upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
    UnT.ev (upsilon (l + h)) t = cdR S (l + g)

/-- **EQ at the form with moving level leaves**: `(vmap ρ t)[υ_{μ+f(h)}] ≤ r(μ+f(g))` whenever
`r(λ+g) = t[υ_{λ+h}; p]` (parameters and the level leaves of `Lf` below `υ_λ` or `υ_{λ+h'}` with `h' ∈ Os`, `h' ≤ h`,
the other level leaves below `δ < υ_λ`;
`ρ = Ub.ubLf λ μ f`), asked only at the inner restarts whose reach has none of the forms `Ub.UbF3`, `Ub.UbForm`,
`Uy.UyForm` (`Uy.UyForm` covers `Un.UnForm`, `Uk.UkForm`, `Ur.UrForm`). -/
def VlCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → g < β → ω ^ 2 ∣ g → ¬ UbF3 S l β g → ¬ UbForm S l β g → ¬ UyForm S l β g →
    ∀ h ∈ Os, 0 < h → ∀ t : UnC, ∀ Lf : Finset Ordinal.{0}, ∀ δ, δ < upsilon l → ZW (upsilon (l + h)) t →
    WFr (upsilon (l + h)) t → UnT.Lv (fun p => p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ h ∧ p = upsilon (l + h')) t →
    ZL (fun p => p ∈ Lf ∨ p < δ) t →
    (∀ p ∈ Lf, p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ h ∧ p = upsilon (l + h')) →
    upsilon (l + h) ≤ cdR S (l + g) → cdR S (l + g) < upsilon (succ (l + h)) →
    UnT.ev (upsilon (l + h)) t = cdR S (l + g) →
    UnT.ev (upsilon (μ + f h)) (vmap (ubLf l μ f) t) ≤ cdR S (μ + f g)

/-- **Realizer maps along an offset map with five forms of inner reaches, the fifth with moving level leaves**:
the inner reaches `υ_{λ+h} + c`
(`c < υ_{λ+1}`) carried to `υ_{μ+f(h)} + π_{υ_μ,υ_λ}(c)`, the inner reaches in `seg(υ_{λ+h})` with parameters below
`υ_λ` carried by the segment move `mv υ_{λ+h} υ_{μ+f(h)}`, and the inner reaches `t[υ_{λ+h}; p]` (`Ub.UbForm`, and
`UnForm` with nested level terms) carried to `t[υ_{μ+f(h)}; ρ p]` by the hull isomorphism. -/
theorem vlReal_gen {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → UbF3 S l β g ∨ UbForm S l β g ∨ UyForm S l β g ∨ VlForm S l β g)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ TvCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
          Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ Ur.UrCarry S l β μ f Os ∧ UyCarry S l β μ f Os ∧ VlCarry S l β μ f Os)
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
  -- the inner restarts of `Y` whose reach has the fifth form
  set r5U : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    UyForm S l β g with hr5Udef
  have hc5U : ∀ y, r5U y → ∃ g h, ∃ t : UnC, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧ 0 < h ∧ h < β ∧
      QsY (upsilon l) t ∧ WFr (upsilon (l + h)) t ∧
      UnT.Lv (fun p => p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) t ∧
      upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
      UnT.ev (upsilon (l + h)) t = cdR S (l + g) ∧
      (∀ μ f (Os : Finset Ordinal.{0}), Ue.UeCarry S l β μ f Os → Uh.UhCarry S l β μ f Os →
        Uk.UkCarry S l β μ f Os → UnCarry S l β μ f Os → Ur.UrCarry S l β μ f Os → UyCarry S l β μ f Os →
        g ∈ Os → ¬ UbF3 S l β g → ¬ UbForm S l β g → h ∈ Os →
        UnT.Lv (fun p => p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ h ∧ p = upsilon (l + h')) t →
        UnT.ev (upsilon (μ + f h)) (t.map (ubLf l μ f)) ≤ cdR S (μ + f g)) := by
    rintro y ⟨g, hg, hfm⟩
    by_cases hun : UnForm S l β g
    · -- the form of `Un`: its witnesses and carries
      by_cases huk : Uk.UkForm S l β g
      · by_cases huh : Uh.UhForm S l β g
        · by_cases hue : Ue.UeForm S l β g
          · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hue
            refine ⟨g, h, ofUk (Uk.ofUh (Uh.ofUe t)), hg, h0, h1,
              qsY_of_qs _ ((ofUk_Qs _).2 ((Uk.ofUh_Qs _).2 (Uh.ofUe_Qs hl1.le t h2))),
              ofUn_WF _ (ofUk_WF _ _ ((Uk.ofUh_WF _ _).2 ((Uh.ofUe_WF _ t).2 h3))),
              (ofUk_Lv _).2 ((Uk.ofUh_Lv _).2 ((Uh.ofUe_Lv t).2 h4)), h5, h6,
              by rw [ofUk_ev, Uk.ofUh_ev, Uh.ofUe_ev]; exact h7, fun μ f Os hUe _ _ _ _ _ hgO hn3 hn4 hhO hLv => ?_⟩
            have e := hUe g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 h hhO h0 t h2 h3
              ((Uh.ofUe_Lv t).1 ((Uk.ofUh_Lv _).1 ((ofUk_Lv _).1 hLv))) h5 h6 h7
            rw [← ofUk_map, ← Uk.ofUh_map, ← Uh.ofUe_map, ofUk_ev, Uk.ofUh_ev, Uh.ofUe_ev]; exact e
          · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := huh
            refine ⟨g, h, ofUk (Uk.ofUh t), hg, h0, h1, qsY_of_qs _ ((ofUk_Qs _).2 ((Uk.ofUh_Qs t).2 h2)),
              ofUn_WF _ (ofUk_WF _ _ ((Uk.ofUh_WF _ t).2 h3)),
              (ofUk_Lv _).2 ((Uk.ofUh_Lv t).2 h4), h5, h6,
              by rw [ofUk_ev, Uk.ofUh_ev]; exact h7, fun μ f Os _ hUh _ _ _ _ hgO hn3 hn4 hhO hLv => ?_⟩
            have e := hUh g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 hue h hhO h0 t h2 h3
              ((Uk.ofUh_Lv t).1 ((ofUk_Lv _).1 hLv)) h5 h6 h7
            rw [← ofUk_map, ← Uk.ofUh_map, ofUk_ev, Uk.ofUh_ev]; exact e
        · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := huk
          refine ⟨g, h, ofUk t, hg, h0, h1, qsY_of_qs _ ((ofUk_Qs t).2 h2), ofUn_WF _ (ofUk_WF _ t h3),
            (ofUk_Lv t).2 h4, h5, h6,
            by rw [ofUk_ev]; exact h7, fun μ f Os _ _ hUk _ _ _ hgO hn3 hn4 hhO hLv => ?_⟩
          have e := hUk g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 huh h hhO h0 t h2 h3 ((ofUk_Lv t).1 hLv) h5 h6 h7
          rw [← ofUk_map, ofUk_ev]; exact e
      · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hun
        exact ⟨g, h, t, hg, h0, h1, qsY_of_qs t h2, ofUn_WF t h3, h4, h5, h6, h7,
          fun μ f Os _ _ _ hUn _ _ hgO hn3 hn4 hhO hLv =>
          hUn g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 huk h hhO h0 t h2 h3 hLv h5 h6 h7⟩
    · -- beyond `Un.UnForm`: `Ur.UrCarry` at `Ur.UrForm`, `UyCarry` beyond
      have huk : ¬ Uk.UkForm S l β g := fun h' => hun (unForm_of_uk h')
      by_cases hur : Ur.UrForm S l β g
      · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hur
        exact ⟨g, h, t, hg, h0, h1, qsY_of_qs t h2, h3, h4, h5, h6, h7,
          fun μ f Os _ _ _ _ hUr _ hgO hn3 hn4 hhO hLv =>
          hUr g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 huk hun h hhO h0 t h2 h3 hLv h5 h6 h7⟩
      · obtain ⟨h, t, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hfm
        exact ⟨g, h, t, hg, h0, h1, h2, h3, h4, h5, h6, h7, fun μ f Os _ _ _ _ _ hUy hgO hn3 hn4 hhO hLv =>
          hUy g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 huk hun hur h hhO h0 t h2 h3 hLv h5 h6 h7⟩
  -- the inner restarts of `Y` whose reach has the fifth form: `Uy.UyForm` or `VlForm`
  set r5 : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    (UyForm S l β g ∨ VlForm S l β g) with hr5def
  have hc5 : ∀ y, r5 y → ∃ g h, ∃ t : UnC, ∃ Lf : Finset Ordinal.{0}, ∃ δ : Ordinal.{0},
      (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧ 0 < h ∧ h < β ∧
      ((QsY (upsilon l) t ∧ Lf = ∅) ∨
        (ZW (upsilon (l + h)) t ∧ ZL (fun p => p ∈ Lf ∨ p < δ) t ∧ δ < upsilon l)) ∧
      (∀ p ∈ Lf, p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) ∧ WFr (upsilon (l + h)) t ∧
      UnT.Lv (fun p => p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) t ∧
      upsilon (l + h) ≤ cdR S (l + g) ∧ cdR S (l + g) < upsilon (succ (l + h)) ∧
      UnT.ev (upsilon (l + h)) t = cdR S (l + g) ∧
      (∀ μ f (Os : Finset Ordinal.{0}), Ue.UeCarry S l β μ f Os → Uh.UhCarry S l β μ f Os →
        Uk.UkCarry S l β μ f Os → UnCarry S l β μ f Os → Ur.UrCarry S l β μ f Os → UyCarry S l β μ f Os →
        VlCarry S l β μ f Os → g ∈ Os → ¬ UbF3 S l β g → ¬ UbForm S l β g → h ∈ Os →
        UnT.Lv (fun p => p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ h ∧ p = upsilon (l + h')) t →
        (∀ p ∈ Lf, p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ h ∧ p = upsilon (l + h')) →
        UnT.ev (upsilon (μ + f h)) (vmap (ubLf l μ f) t) ≤ cdR S (μ + f g)) := by
    rintro y ⟨g, hg, hfm⟩
    by_cases huy : UyForm S l β g
    · -- constant levels: the witnesses and carries of `Uy` (`vmap = map`, every level leaf below `υ_λ`)
      obtain ⟨g', h, t, hg', h0, h1, hq, hw, hL, hlo, hhi, hev, K⟩ := hc5U y ⟨g, hg, huy⟩
      refine ⟨g', h, t, ∅, 0, hg', h0, h1, Or.inl ⟨hq, rfl⟩, fun p hp => absurd hp (Finset.notMem_empty p), hw, hL,
        hlo, hhi, hev, fun μ f Os c1 c2 c3 c4 c5 c6 _ hgO hn3 hn4 hhO hLv _ => ?_⟩
      have hfix : ZL (fun x => ubLf l μ f x = x) t :=
        vl_ZL_mono (fun x _ hx => by simp only [ubLf, if_pos hx]) t (vl_ZL_of_qsY hlE t hq)
      rw [vl_vmap_map _ t hfix]
      exact K μ f Os c1 c2 c3 c4 c5 c6 hgO hn3 hn4 hhO hLv
    · -- levels with moving leaves: `VlCarry`
      obtain ⟨h, t, Lf, δ, h0, h1, hδ, hz, hw, hL, hzl, hLf, hlo, hhi, hev⟩ := hfm.resolve_left huy
      exact ⟨g, h, t, Lf, δ, hg, h0, h1, Or.inr ⟨hz, hzl, hδ⟩, hLf, hw, hL, hlo, hhi, hev,
        fun μ f Os _ _ _ _ _ _ hVl hgO hn3 hn4 hhO hLv hLfO =>
          hVl g hgO hg.1 hg.2.1 hg.2.2.1 hn3 hn4 huy h hhO h0 t Lf δ hδ hz hw hLv hzl hLfO hlo hhi hev⟩
  choose! g5 h5 t5 Lf5 δ5 hg5 h50 h5β hQ5 hLf5f hW5 hL5 hlo5 hhi5 hev5 hK5 using hc5

  set T5 := Y.filter r5 with hT5def
  set A5 : Ordinal.{0} → Finset Ordinal.{0} := fun y =>
    insert (upsilon (l + h5 y)) (insert (cdR S (l + g5 y)) ((UnT.lvs (t5 y) ∪ Lf5 y).filter (upsilon l ≤ ·)))
    with hA5def
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
  set Y' := Y ∪ T.biUnion A ∪ T2.biUnion A2 ∪ T3.biUnion A3 ∪ T5.biUnion A5 with hY'def
  set X' := X ∪ (T.image cf).filter (· < upsilon l) ∪
    T3.biUnion (fun y => (UbT.lvs (t4 y)).filter (· < upsilon l)) ∪
    T5.biUnion (fun y => (UnT.lvs (t5 y) ∪ Lf5 y).filter (· < upsilon l)) ∪
    T5.biUnion (fun y => (insert (δ5 y) (lvqY (t5 y))).filter (· < upsilon l)) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · rcases Finset.mem_union.1 hx with hx | hx
        · rcases Finset.mem_union.1 hx with hx | hx
          · exact hX x hx
          · exact (Finset.mem_filter.1 hx).2
        · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
          exact (Finset.mem_filter.1 hxu).2
      · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
        exact (Finset.mem_filter.1 hxu).2
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
  have hA5 : ∀ y ∈ T5, ∀ z ∈ A5 y, upsilon l ≤ z ∧ z < upsilon (l + β) := by
    intro y hyT z hz
    have hr := (Finset.mem_filter.1 hyT).2
    have hh0' := h50 y hr
    have hlh : upsilon l < upsilon (l + h5 y) := hm (lt_add_of_pos_right l hh0')
    have hsβ : upsilon (succ (l + h5 y)) ≤ upsilon (l + β) := by
      refine hm.monotone ?_
      rw [lr_succ_add]; exact lr_addLe (a := l) (Order.succ_le_of_lt (h5β y hr))
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hlh.le, (hm (lt_succ _)).trans_le hsβ⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hlh.le.trans (hlo5 y hr), (hhi5 y hr).trans_le hsβ⟩
    obtain ⟨hzl, hlz⟩ := Finset.mem_filter.1 hz
    have hzf : z < upsilon l ∨ ∃ h', h' ≤ h5 y ∧ z = upsilon (l + h') := by
      rcases Finset.mem_union.1 hzl with hzl | hzl
      · exact UnT.mem_lvs (hL5 y hr) z hzl
      · exact hLf5f y hr z hzl
    rcases hzf with hzl' | ⟨h', hh', rfl⟩
    · exact absurd hzl' (not_lt.2 hlz)
    · exact ⟨hlz, hm (add_lt_add_right (hh'.trans_lt (h5β y hr)) l)⟩
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 hy with hy | hy
      · rcases Finset.mem_union.1 hy with hy | hy
        · rcases Finset.mem_union.1 hy with hy | hy
          · exact hY y hy
          · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
            exact hA u hu y hyu
        · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
          exact hA2 u hu y hyu
      · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
        exact hA3 u hu y hyu
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      exact hA5 u hu y hyu
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll, hubAll, heAll, -, hDid, hγU⟩ :=
    vlShiftCore (Q := fun μ f B _ Os => TvCarry S l β μ f B Os ∧ UbCarry S l β μ f Os ∧
        Ue.UeCarry S l β μ f Os ∧ Uh.UhCarry S l β μ f Os ∧ Uk.UkCarry S l β μ f Os ∧
          UnCarry S l β μ f Os ∧ Ur.UrCarry S l β μ f Os ∧ UyCarry S l β μ f Os ∧ VlCarry S l β μ f Os)
      hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩) hstd hlL X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))
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
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, hz⟩))))
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
            · have hCX : C ∈ X' := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hT, not_le.1 hc⟩))))
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
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT2, hz⟩)))
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
      · by_cases hF4 : UbForm S l β g
        · -- the fourth form: the hull isomorphism on the term `t`, leaves fixed below `υ_λ` or inner `υ`-points
          have hr4 : r4 (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, hF4⟩
          have hT3 : upsilon (l + g) ∈ T3 := Finset.mem_filter.2 ⟨hy, hr4⟩
          have hgg : g4 (upsilon (l + g)) = g := by
            have e := (hg4 _ hr4).2.2.2
            exact (add_left_cancel (hm.injective e)).symm
          have hlo := hlo4 _ hr4
          have hhi := hhi4 _ hr4
          have hev := hev4 _ hr4
          rw [hgg] at hlo hhi hev
          have hAY : ∀ z ∈ A3 (upsilon (l + g)), z ∈ Y' := fun z hz =>
            Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT3, hz⟩))
          have hRm : cdR S (l + g) ∈ Y' := hAY _ (Finset.mem_insert_of_mem (by
            rw [hgg]; exact Finset.mem_insert_self _ _))
          have hleaf : ∀ p ∈ UbT.lvs (t4 (upsilon (l + g))), p ∈ X' ∪ Y' ∧ D p = ubLf l μ f p ∧
              (p < upsilon l ∨ ∃ h' ∈ Os, p = upsilon (l + h')) := by
            intro p hp
            have hLp := UbT.mem_lvs (hL4 _ hr4) p hp
            by_cases hpl : p < upsilon l
            · have hpX : p ∈ X' := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.2 ⟨_, hT3, Finset.mem_filter.2 ⟨hp, hpl⟩⟩)))
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
          exact h5.trans (hQ.2.1 g hgO hg0 hgβ hgd h3 _ hHO (h40 _ hr4) _ (hA4 _ hr4) (hW4 _ hr4)
            (UbT.Lv_mono (fun p hp => (hleaf p hp).2.2) _ hLt) hlo hhi hev)
        · -- the fifth form: `Uy.UyForm` (constant levels) or `VlForm` (levels with moving leaves), by the hull
          -- isomorphism on `thz`-terms (`vlShiftCore`)
          have h5f : UyForm S l β g ∨ VlForm S l β g :=
            ((hform g hg0 hgβ hgd).resolve_left h3).resolve_left hF4
          have hr5 : r5 (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h5f⟩
          have hT5 : upsilon (l + g) ∈ T5 := Finset.mem_filter.2 ⟨hy, hr5⟩
          have hgg : g5 (upsilon (l + g)) = g := by
            have e := (hg5 _ hr5).2.2.2
            exact (add_left_cancel (hm.injective e)).symm
          have hlo := hlo5 _ hr5
          have hhi := hhi5 _ hr5
          have hev := hev5 _ hr5
          rw [hgg] at hlo hhi hev
          have hAY : ∀ z ∈ A5 (upsilon (l + g)), z ∈ Y' := fun z hz =>
            Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hT5, hz⟩)
          have hRm : cdR S (l + g) ∈ Y' := hAY _ (Finset.mem_insert_of_mem (by
            rw [hgg]; exact Finset.mem_insert_self _ _))
          set H := h5 (upsilon (l + g)) with hHdef
          set t := t5 (upsilon (l + g)) with htdef
          set Lf := Lf5 (upsilon (l + g)) with hLfdef
          have hH1 : upsilon (l + H) < Om1 :=
            lt_of_le_of_lt hlo (lt_of_lt_of_le (hY' _ hRm).2 (hνβ.trans nuC_le_Om1))
          have hHE : InE (upsilon (l + H)) :=
            upsPt_inE (upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) le_self_add))
          -- every parameter and every level leaf of `Lf`: in the configuration, moved by `ubLf`, of the form
          -- `p < υ_λ` or `p = υ_{λ+h'}` (`h' ∈ Os`, `h' ≤ H`), in `T^{υ_{λ+H}}`
          have hform1 : ∀ p, p ∈ UnT.lvs t ∪ Lf → p ∈ X' ∪ Y' ∧ D p = ubLf l μ f p ∧
              (p < upsilon l ∨ ∃ h' ∈ Os, h' ≤ H ∧ p = upsilon (l + h')) ∧ p ∈ Tset (upsilon (l + H)) := by
            intro p hp
            have hLp : p < upsilon l ∨ ∃ h', h' ≤ H ∧ p = upsilon (l + h') := by
              rcases Finset.mem_union.1 hp with hp' | hp'
              · exact UnT.mem_lvs (hL5 _ hr5) p hp'
              · exact hLf5f _ hr5 p hp'
            by_cases hpl : p < upsilon l
            · have hpX : p ∈ X' := Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_biUnion.2 ⟨_, hT5, Finset.mem_filter.2 ⟨hp, hpl⟩⟩))
              refine ⟨Finset.mem_union_left _ hpX, ?_, Or.inl hpl, ?_⟩
              · rw [hW.fix p hpX]; simp only [ubLf, if_pos hpl]
              · exact uh_T_le hHE hH1 (hpl.le.trans (hm.monotone le_self_add))
            · obtain ⟨h', hh', rfl⟩ := hLp.resolve_left hpl
              have hpY : upsilon (l + h') ∈ Y' := hAY _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_filter.2 ⟨hp, not_lt.1 hpl⟩)))
              obtain ⟨hO', hD'⟩ := hres h' hpY
              refine ⟨Finset.mem_union_right _ hpY, ?_, Or.inr ⟨h', hO', hh', rfl⟩, ?_⟩
              · rw [hD']; simp only [ubLf, if_neg hpl, lrIx_up, Ordinal.add_sub_cancel]
              · exact uh_T_le hHE hH1 (hm.monotone (add_le_add_right hh' l))
          have hHO : H ∈ Os := (hres _ (hAY _ (Finset.mem_insert_self _ _))).1
          have hLt := UnT.Lv_lvs t
          have hLvX : UnT.Lv (· ∈ X' ∪ Y') t :=
            UnT.Lv_mono (fun p hp => (hform1 p (Finset.mem_union_left _ hp)).1) _ hLt
          have hLvT : UnT.Lv (· ∈ Tset (upsilon (l + H))) t :=
            UnT.Lv_mono (fun p hp => (hform1 p (Finset.mem_union_left _ hp)).2.2.2) _ hLt
          have hLvD : UnT.Lv (fun p => D p = ubLf l μ f p) t :=
            UnT.Lv_mono (fun p hp => (hform1 p (Finset.mem_union_left _ hp)).2.1) _ hLt
          have hγl : γ < upsilon l := hγμ.trans hμl
          have e1 : D (cdR S (l + g)) = UnT.ev (upsilon (μ + f H)) (vmap (ubLf l μ f) t) := by
            rcases hQ5 _ hr5 with ⟨hq, -⟩ | ⟨hz, hzl, hδ⟩
            · -- constant levels: the level leaves lie below `γ`, fixed by `D` and by `ubLf`
              have hQγ : QsY γ t := QsY_of_lvqY t hq (fun q hq' => hXγ q (Finset.mem_union_right _
                (Finset.mem_biUnion.2 ⟨_, hT5,
                  Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hq', lvqY_lt _ hq q hq'⟩⟩)))
              have hBl : Bases (upsilon l) (upsilon (l + H)) :=
                ⟨hlE, hHE, hm (lt_add_of_pos_right l (h50 _ hr5)), hH1⟩
              have hzγ : ZL (· < γ) t := vl_ZL_of_qsY (upsPt_inE hγU) t hQγ
              obtain ⟨e1, -⟩ := heAll _ hRm _ hlo hhi t (vl_ZW_of_qsY hBl t hLvT (hW5 _ hr5) hq) (hW5 _ hr5)
                hLvX (vl_ZL_mono (fun p _ hp => Or.inr hp) t hzγ) hLvT
                (vl_ZL_mono (fun p _ hp => uh_T_le hHE hH1 ((hp.trans hγl).le.trans (hm.monotone le_self_add)))
                  t hzγ) hev
              have hmap : vmap D t = vmap (ubLf l μ f) t := vmap_congr t hLvD
                (vl_ZL_mono (fun p _ hp => by rw [hDid p hp]; simp only [ubLf, if_pos (hp.trans hγl)]) t hzγ)
              rw [hmap] at e1; exact e1
            · -- levels with moving leaves: the level leaves lie in `Lf` or below `δ < γ`
              have hδX : δ5 (upsilon (l + g)) ∈ X' := Finset.mem_union_right _
                (Finset.mem_biUnion.2 ⟨_, hT5, Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hδ⟩⟩)
              have hδγ := hXγ _ hδX
              obtain ⟨e1, -⟩ := heAll _ hRm _ hlo hhi t hz (hW5 _ hr5) hLvX
                (vl_ZL_mono (fun p _ hp => hp.elim (fun h => Or.inl (hform1 p (Finset.mem_union_right _ h)).1)
                  (fun h => Or.inr (h.trans hδγ))) t hzl)
                hLvT (vl_ZL_mono (fun p _ hp => hp.elim (fun h => (hform1 p (Finset.mem_union_right _ h)).2.2.2)
                  (fun h => uh_T_le hHE hH1 (((h.trans hδγ).trans hγl).le.trans (hm.monotone le_self_add)))) t hzl)
                hev
              have hmap : vmap D t = vmap (ubLf l μ f) t := vmap_congr t hLvD
                (vl_ZL_mono (fun p _ hp => hp.elim (fun h => (hform1 p (Finset.mem_union_right _ h)).2.1)
                  (fun h => by rw [hDid p (h.trans hδγ)]; simp only [ubLf, if_pos ((h.trans hδγ).trans hγl)])) t hzl)
              rw [hmap] at e1; exact e1
          have h5' : D y' ≤ D (cdR S (l + g)) :=
            hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (Finset.mem_union_right _ hRm) hyr
          rw [e1] at h5'
          have hK := hK5 _ hr5 μ f Os hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1 hQ.2.2.2.2.2.2.1
            hQ.2.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2.2
          rw [hgg] at hK
          exact h5'.trans (hK hgO h3 hF4 hHO
            (UnT.Lv_mono (fun p hp => (hform1 p (Finset.mem_union_left _ hp)).2.2.1) _ hLt)
            (fun p hp => (hform1 p (Finset.mem_union_right _ hp)).2.2.1))
    have hge : upsilon (μ + f g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Vl
