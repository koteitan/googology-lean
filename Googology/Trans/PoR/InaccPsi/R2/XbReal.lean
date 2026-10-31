import Googology.Trans.PoR.InaccPsi.R2.XbImg

/-!
# The realizer bridge for `ϑ`-nodes, reduced to one clause of the shift

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`Ww.WwRealB` asks the realizer `Lr.LrReal S υ_λ υ_{λ+β}` from `Ww.WwGen`.  The proof of `Wf.wfReal_gen` goes
through `Vl.vlShiftCore`, whose term clause covers the nodes `thz (Ω₁·q) r` with `Ω₁·q < B₂` only (`Vi.Nz.qB`), and
through `Vr.vrD_eq` (`D(value) = image` on decompositions).  For a `ϑ`-node `th h M e` of `Ww.WwE` two things are
missing:

1. **the clause of the shift at a `ϑ`-node** (`XbThCl`): `D(ϑ^{υ_{λ+h}}(Ω₁·M + η)) = ϑ^{υ_{μ+f(h)}}(Ω₁·M + D(η))`
   for a constant level (`1 ≤ M`, the data of `M` below the bottom `γ` of the shift: `Vd.VdLtIn M γ`), `η` a point of
   the configuration.  `XbShift S` is `Vl.vlShiftCore` with this clause added to its conclusion.
2. **the level must be constant**: `Ww.WwCarry` asks the image bound only for decompositions with `Ww.WwR`
   (data of every `ϑ`-level below `υ_μ`), and `Ww.WwWF` puts no bound on the data of `M`; a form whose `ϑ`-level has a
   datum in `[υ_λ, υ_{λ+h})` gets no image bound from the carry.  `XbForm` is `Ww.WwForm` with every `ϑ`-level
   constant over some `c < υ_λ` (`XbCL c`); `XbGen`, `XbVisGen` are `Ww.WwGen`, `Ww.WwVisGen` with `XbForm`
   (`xbGen_ww`, `xbVisGen_ww`: they imply the old ones).  The gap witness has such a form (`xbForm_X`, `xbForm_gap`).

* `xb_ltIn_mono`, `XbThCl`, `XbShift`, `XbCL`, `xbCL_mono`, `XbForm`, `XbGen`, `XbVisGen`, `xbForm_ww`,
  `xbForm_of_vr` (**old forms are forms with constant `ϑ`-levels**), `xbGen_ww`,
  `xbVisGen_ww`;
* `xbPts`, `xbVal_mem`, `xbPts_lt`, `xbPrm`, `xbPrm_lt`, `xbR_of` (**the restriction `Ww.WwR` from the points**),
  `xbD_eq` (**`D(value) = image` on repaired decompositions with constant `ϑ`-levels**);
* `xbReal_gen` (**`XbShift S` and `XbGen` give the realizer**), `XbRealB` (the bridge with `XbGen`), `xbRealB`
  (**`XbShift S ⇒ XbRealB S`**);
* `xbForm_X`, `xbForm_gap` (**the gap witness has a form with a constant `ϑ`-level**: `M = B₂`, data below `Γ₀`).

No new axiom.  New definitions (statements and syntax functions only): `XbThCl`, `XbShift`, `XbCL`, `XbForm`,
`XbGen`, `XbVisGen`, `xbPts`, `xbPrm`, `XbRealB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Ww

variable {S : InaccSeq.{0}}

/-- `Vd.VdLtIn` is monotone in the bound. -/
theorem xb_ltIn_mono {M v v' : Ordinal.{0}} (h : Vd.VdLtIn M v) (hv : v ≤ v') : Vd.VdLtIn M v' := by
  rcases h with ⟨h1, h2⟩ | ⟨S', h1, h2, q, hq, hqv, hd⟩
  · exact Or.inl ⟨h1, h2.trans_le hv⟩
  · exact Or.inr ⟨S', h1, h2, q, hq, hqv.trans hv, hd⟩

/-- **The clause of the shift at a `ϑ`-node** (open): for `y ∈ Y` in the segment of `υ_{λ+h}` (`υ_{λ+h} ∈ Y`) with
`y = ϑ^{υ_{λ+h}}(Ω₁·M + η)`, `Ω₁·M + η ∈ T^{υ_{λ+h}} ∩ Ω₂`, `η < Ω₁` a point of `X ∪ Y`, and a constant level
(`1 ≤ M`, the data of `M` below the bottom `γ`): `D(y) = ϑ^{υ_{μ+f(h)}}(Ω₁·M + D(η))`. -/
def XbThCl (l μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ y ∈ Y, ∀ h M η : Ordinal.{0}, 0 < h → upsilon (l + h) ∈ Y → η ∈ X ∪ Y → 1 ≤ M → Vd.VdLtIn M γ →
    η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h)) → Om1 * M + η < OmTwo →
    y = vt (upsilon (l + h)) (Om1 * M + η) → upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) →
    D y = vt (upsilon (μ + f h)) (Om1 * M + D η)

/-- **The shift with the `ϑ`-node clause** (open): the statement of `Vl.vlShiftCore` with `XbThCl` added to its
conclusion. -/
def XbShift (S : InaccSeq.{0}) : Prop :=
  ∀ (l β : Ordinal.{0})
    (Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop),
    IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    (∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os) →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) →
    ∀ (X Y : Finset Ordinal.{0}), (∀ x ∈ X, x < upsilon l) → (∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) →
    ∃ D μ f B γ Os, (Q μ f B γ Os ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ Ls.LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + B)) ∧
      (upsilon μ < upsilon l ∧ ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
        (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : Ub.UbT, Ub.UbT.IsA t →
        Ub.UbT.WF (upsilon (l + g)) t → Ub.UbT.Lv (· ∈ X ∪ Y) t → Ub.UbT.ev (upsilon (l + g)) t = y →
        D y = Ub.UbT.ev (upsilon (μ + f g)) (t.map D) ∧ Ub.UbT.WF (upsilon (μ + f g)) (t.map D)) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t)) ∧
      VlLC (fun p => p ∈ X ∪ Y ∨ p < γ) D ∧ (∀ x, x < γ → D x = x) ∧ UpsPt γ) ∧
      XbThCl l μ γ f D X Y

/-- **Constant `ϑ`-levels**: every `ϑ`-node `th h M e` has `1 ≤ M` and the data of `M` below `c`. -/
def XbCL (c : Ordinal.{0}) : WwE → Prop
  | .old _ => True
  | .th _ M e => 1 ≤ M ∧ Vd.VdLtIn M c ∧ XbCL c e
  | .add s t => XbCL c s ∧ XbCL c t

theorem xbCL_mono {c c' : Ordinal.{0}} (hc : c ≤ c') : ∀ E : WwE, XbCL c E → XbCL c' E
  | .old _, _ => trivial
  | .th _ _ e, h => ⟨h.1, xb_ltIn_mono h.2.1 hc, xbCL_mono hc e h.2.2⟩
  | .add s t, h => ⟨xbCL_mono hc s h.1, xbCL_mono hc t h.2⟩

/-- **The repaired form with constant `ϑ`-levels.** -/
def XbForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ E : WwE, ∃ c, c < upsilon l ∧ WwWF l β E ∧ XbCL c E ∧ wwVal l E = cdR S (l + g)

/-- `Ww.WwGen` with `XbForm`. -/
def XbGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ XbForm S l β g) ∧ WwSup S l β

/-- `Ww.WwVisGen` with `XbGen`. -/
def XbVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ Tk.TkCov S (upsilon l) ν →
    Tk.TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ XbGen S l β

theorem xbForm_ww {l β g : Ordinal.{0}} (h : XbForm S l β g) : WwForm S l β g := by
  obtain ⟨E, -, -, hW, -, hv⟩ := h
  exact ⟨E, hW, hv⟩

/-- **Old forms are forms with constant `ϑ`-levels** (they have no `ϑ`-node). -/
theorem xbForm_of_vr {l β g : Ordinal.{0}} (hl : 0 < upsilon l) (h : Vr.VrForm S l β g) : XbForm S l β g := by
  obtain ⟨E, hW, hv⟩ := h
  exact ⟨.old E, 0, hl, hW, trivial, hv⟩

theorem xbGen_ww {l β : Ordinal.{0}} (h : XbGen S l β) : WwGen S l β :=
  ⟨h.1, fun g h0 h1 h2 => (h.2.1 g h0 h1 h2).imp id xbForm_ww, h.2.2⟩

/-- **`XbVisGen ⇒ Ww.WwVisGen`.** -/
theorem xbVisGen_ww {l b c : Ordinal.{0}} (h : XbVisGen S l b c) : WwVisGen S l b c := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨β, e1, e2, e3⟩ := h ν h1 h2 h3 h4 h5 h6
  exact ⟨β, e1, e2, xbGen_ww e3⟩

/-! ## Points, parameters, restriction -/

/-- **The points a realizer configuration must contain** for a repaired decomposition. -/
noncomputable def xbPts (l : Ordinal.{0}) : WwE → Finset Ordinal.{0}
  | .old E => Vr.vrPts l E
  | .th h M e => insert (upsilon (l + h)) (insert (wwVal l (.th h M e)) (xbPts l e))
  | .add s t => insert (wwVal l s + wwVal l t) (xbPts l s ∪ xbPts l t)

theorem xbVal_mem (l : Ordinal.{0}) : ∀ E : WwE, wwVal l E ∈ xbPts l E
  | .old E => Vr.vrVal_mem l E
  | .th _ _ _ => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  | .add _ _ => Finset.mem_insert_self _ _

theorem xbPts_lt {l β : Ordinal.{0}} (hβ : 0 < β) :
    ∀ E : WwE, WwWF l β E → ∀ z ∈ xbPts l E, z < upsilon (l + β) := by
  have hm := upsilon_normal.strictMono
  have hE : InE (upsilon (l + β)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hβ le_add_self))
  intro E
  induction E with
  | old E => exact Vr.vrPts_lt hβ E
  | th h M e ih =>
    intro hw z hz
    obtain ⟨-, hh, hwe, -, -, -, -, h2⟩ := hw
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hm (add_lt_add_right hh l)
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact h2.trans_le (Vr.vr_seg_le hh)
    · exact ih hwe z hz
  | add s t ihs iht =>
    intro hw z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact (inE_indec hE).add_lt (ihs hw.1 _ (xbVal_mem l s)) (iht hw.2 _ (xbVal_mem l t))
    rcases Finset.mem_union.1 hz with hz | hz
    · exact ihs hw.1 z hz
    · exact iht hw.2 z hz

/-- The low parameters a realizer configuration must contain. -/
noncomputable def xbPrm (l : Ordinal.{0}) : WwE → Finset Ordinal.{0}
  | .old E => Wf.wfPrm l E
  | .th _ _ e => xbPrm l e
  | .add s t => xbPrm l s ∪ xbPrm l t

theorem xbPrm_lt (l : Ordinal.{0}) : ∀ E : WwE, ∀ q ∈ xbPrm l E, q < upsilon l
  | .old E => Wf.wfPrm_lt l E
  | .th _ _ e => xbPrm_lt l e
  | .add s t => fun q hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact xbPrm_lt l s q hq
    · exact xbPrm_lt l t q hq

/-- **The restriction `Ww.WwR` from the points and low parameters below `υ_μ`** and constant `ϑ`-levels over
`c ≤ υ_μ`. -/
theorem xbR_of {l β μ c : Ordinal.{0}} (hl0 : 0 < l) (hB : Bases (upsilon μ) (upsilon l)) (hc : c ≤ upsilon μ) :
    ∀ E : WwE, WwWF l β E → XbCL c E → (∀ z ∈ xbPts l E, z < upsilon l → z < upsilon μ) →
      (∀ q ∈ xbPrm l E, q < upsilon μ) → WwR l μ E := by
  intro E
  induction E with
  | old E => exact fun hw _ hz hq => Wf.wfR_of hl0 hB E hw hz hq
  | th h M e ih =>
    intro hw hcl hz hq
    exact ⟨xb_ltIn_mono hcl.2.1 hc, ih hw.2.2.1 hcl.2.2
      (fun z h1 h2 => hz z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)) h2) hq⟩
  | add s t ihs iht =>
    intro hw hcl hz hq
    exact ⟨ihs hw.1 hcl.1 (fun z h1 h2 => hz z (Finset.mem_insert_of_mem (Finset.mem_union_left _ h1)) h2)
        (fun q h => hq q (Finset.mem_union_left _ h)),
      iht hw.2 hcl.2 (fun z h1 h2 => hz z (Finset.mem_insert_of_mem (Finset.mem_union_right _ h1)) h2)
        (fun q h => hq q (Finset.mem_union_right _ h))⟩

/-- **`D(value) = image` on repaired decompositions with constant `ϑ`-levels**, from the same statement on the old
decompositions (`Vr.vrD_eq`), additivity of `D` on `X ∪ Y`, and the `ϑ`-node clause `XbThCl`. -/
theorem xbD_eq {l β μ γ c : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {Os X Y : Finset Ordinal.{0}}
    (hXl : ∀ x ∈ X, x < upsilon l)
    (hadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z))
    (hres : ∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g))
    (hold : ∀ E : Vr.VrE, Vr.VrWF l β E → (∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y) →
      D (Vr.vrVal l E) = Vr.vrImg l μ f E ∧ Vr.VrOs l Os E)
    (hth : XbThCl l μ γ f D X Y) (hcγ : c ≤ γ) :
    ∀ E : WwE, WwWF l β E → XbCL c E → (∀ z ∈ xbPts l E, z ∈ X ∪ Y) →
      D (wwVal l E) = wwImg l μ f E ∧ WwOs l Os E := by
  have hm := upsilon_normal.strictMono
  have hY : ∀ z ∈ X ∪ Y, upsilon l ≤ z → z ∈ Y := fun z hz hzl =>
    (Finset.mem_union.1 hz).resolve_left fun hx => absurd (hXl z hx) (not_lt.2 hzl)
  intro E
  induction E with
  | old E => exact fun hw _ hp => hold E hw hp
  | th h M e ih =>
    intro hw hcl hp
    obtain ⟨h0, -, hwe, hlt, hmem, hlt2, hge, hseg⟩ := hw
    obtain ⟨hM1, hd, hce⟩ := hcl
    have hbase : upsilon (l + h) ∈ Y :=
      hY _ (hp _ (Finset.mem_insert_self _ _)) (hm.monotone le_self_add)
    have hyY : wwVal l (.th h M e) ∈ Y :=
      hY _ (hp _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        ((hm.monotone le_self_add).trans hge)
    have hη : wwVal l e ∈ X ∪ Y :=
      hp _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (xbVal_mem l e)))
    obtain ⟨ie, io⟩ := ih hwe hce (fun z hz => hp z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))
    have e1 := hth _ hyY h M (wwVal l e) h0 hbase hη hM1 (xb_ltIn_mono hd hcγ) hlt hmem hlt2 rfl hge hseg
    refine ⟨?_, (hres h hbase).1, io⟩
    show D (vt (upsilon (l + h)) (Om1 * M + wwVal l e)) = vt (upsilon (μ + f h)) (Om1 * M + wwImg l μ f e)
    rw [← ie]; exact e1
  | add s t ihs iht =>
    intro hw hcl hp
    have hps : ∀ z ∈ xbPts l s, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
    have hpt : ∀ z ∈ xbPts l t, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    obtain ⟨es, os⟩ := ihs hw.1 hcl.1 hps
    obtain ⟨et, ot⟩ := iht hw.2 hcl.2 hpt
    have hsum := (hadd _ (hps _ (xbVal_mem l s)) _ (hpt _ (xbVal_mem l t)) _
      (hp _ (Finset.mem_insert_self _ _))).1 rfl
    refine ⟨?_, os, ot⟩
    show D (wwVal l s + wwVal l t) = wwImg l μ f s + wwImg l μ f t
    rw [← es, ← et, hsum]

/-! ## The realizer -/

/-- **`XbShift S` and `XbGen` give the realizer** (`Wf.wfReal_gen` for repaired decompositions with constant
`ϑ`-levels): UPPER at the inner restarts, the forms `υ_{λ+β} ≤ r(λ+g) ∨ XbForm`, and the supply `Ww.WwSup`. -/
theorem xbReal_gen (hS : XbShift S) {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ XbForm S l β g)
    (hsup : WwSup S l β)
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
    XbForm S l β g with hrrdef
  have hch : ∀ y, rr y → ∃ g, ∃ E : WwE, ∃ c, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      c < upsilon l ∧ WwWF l β E ∧ XbCL c E ∧ wwVal l E = cdR S (l + g) := by
    rintro y ⟨g, hg, E, c, hc, hW, hC, hv⟩
    exact ⟨g, E, c, hg, hc, hW, hC, hv⟩
  choose! gE EE cE hgE hcE hWE hCE hvE using hch
  set T := Y.filter rr with hTdef
  set Y' := Y ∪ T.biUnion (fun y => (xbPts l (EE y)).filter (upsilon l ≤ ·)) with hY'def
  set X' := X ∪ (T.biUnion (fun y => (xbPts l (EE y)).filter (· < upsilon l)) ∪
    (T.biUnion (fun y => xbPrm l (EE y)) ∪ T.image cE)) with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxu).2
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨u, -, hxu⟩ := Finset.mem_biUnion.1 hx
      exact xbPrm_lt l _ x hxu
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      exact hcE u (Finset.mem_filter.1 hu).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hY y hy
    · obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.1 hy
      obtain ⟨hyp, hly⟩ := Finset.mem_filter.1 hyu
      have hr := (Finset.mem_filter.1 hu).2
      exact ⟨hly, xbPts_lt ((hgE u hr).1.trans (hgE u hr).2.1) _ (hWE u hr) y hyp⟩
  obtain ⟨D, μ, f, B, γ, Os, ⟨hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmvAll, hubAll, heAll, -, hDid, -⟩,
      hth⟩ :=
    hS l β (fun μ f B _ Os => WwCarry S l β μ f B Os) hl hl1 hν hνβ
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
        set c := cE (upsilon (l + g)) with hcdef
        have hcX : c ∈ X' := Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, hT, rfl⟩)))
        have hcγ : c < γ := hXγ c hcX
        have hlowX : ∀ z ∈ xbPts l E, z < upsilon l → z ∈ X' := fun z hz hzl =>
          Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩))
        have hpts : ∀ z ∈ xbPts l E, z ∈ X' ∪ Y' := by
          intro z hz
          by_cases hzl : upsilon l ≤ z
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨_, hT, Finset.mem_filter.2 ⟨hz, hzl⟩⟩))
          · exact Finset.mem_union_left _ (hlowX z hz (not_le.1 hzl))
        have hR : WwR l μ E := xbR_of hl0 hBμ (hcγ.trans hγμ).le E (hWE _ hrr) (hCE _ hrr)
          (fun z hz hzl => (hXγ z (hlowX z hz hzl)).trans hγμ)
          (fun q hq => (hXγ q (Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨_, hT, hq⟩))))).trans hγμ)
        obtain ⟨e1, hOs⟩ := xbD_eq (β := β) hX' hW.add hres hDE hth hcγ.le E (hWE _ hrr) (hCE _ hrr) hpts
        have hRm : cdR S (l + g) ∈ X' ∪ Y' := hv ▸ hpts _ (xbVal_mem l E)
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

/-- **The bridge with constant `ϑ`-levels** (`Ww.WwRealB` with `XbGen` in place of `Ww.WwGen`). -/
def XbRealB (S : InaccSeq.{0}) : Prop :=
  ∀ l β : Ordinal.{0}, IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) → XbGen S l β → LrReal S (upsilon l) (upsilon (l + β))

/-- **THE BRIDGE FROM THE SHIFT: `XbShift S ⇒ XbRealB S`.** -/
theorem xbRealB (hS : XbShift S) : XbRealB S := fun _ _ hl hl1 hν hνβ hstd hlL h =>
  xbReal_gen hS hl hl1 hν hνβ h.1 h.2.1 h.2.2 hstd hlL

/-! ## The gap witness has a form with a constant `ϑ`-level -/

/-- `B₂` is a constant level: `1 ≤ B₂` and its `K⁽⁰⁾`-datum lies below `Γ₀`. -/
theorem xb_B_const (S : InaccSeq.{0}) : 1 ≤ Uc.ucB ∧ Vd.VdLtIn Uc.ucB (gamma 0) :=
  ⟨Order.one_le_iff_pos.2 (Rj.rj_Om1_pos.trans Uc.ucB_gt),
    Or.inr ⟨S, le_rfl, Vd.vd_B_lt_th, gamma 0, Lq.lq_gamma_SC 0, le_rfl, Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)⟩⟩

/-- `Γ₀ < υ_λ` for every restart index `λ = υ_λ`. -/
theorem xb_gam_lt (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl0 : 0 < l) (hlfix : upsilon l = l) : gamma 0 < upsilon l := by
  have hm := upsilon_normal.strictMono
  have h1l : (1 : Ordinal.{0}) < l := by
    rcases lt_or_ge 1 l with h | h
    · exact h
    have hl1 : l = 1 := le_antisymm h (Order.one_le_iff_pos.2 hl0)
    have hE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
    rw [hlfix, hl1] at hE
    have : (ω : Ordinal.{0}) = 1 := by
      have h' : ω ^ (1 : Ordinal.{0}) = 1 := hE
      rwa [opow_one] at h'
    exact absurd this (ne_of_gt one_lt_omega0)
  exact (Gq.gq_gam_le_ups S (upsPt_upsilon one_pos)).trans_lt (hm h1l)

/-- **The gap witness has a form with a constant `ϑ`-level** (`Ww.wwForm_X` with `XbCL Γ₀`, `Γ₀ < υ_λ`). -/
theorem xbForm_X (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : wwX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    XbForm S (Nc.ncL S (k : Ordinal.{0})) β (wwX S k) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨hP, hu1O, hlu1, hlfix, -, -⟩ := ww_seg (S := S) k
  obtain ⟨hξT, hξ2, -, -⟩ := ww_arg (S := S) k
  obtain ⟨-, hXE, hu1X, hXu2, -⟩ := wwX_spec (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set X := wwX S k with hXdef
  have hm := upsilon_normal.strictMono
  set h1 := X + ω + 1 with hh1
  set τ := upsilon (l + h1) with hτdef
  have hτO : τ < Om1 := (hm ((add_lt_add_iff_left l).2 hβ)).trans_le hb1
  have hτP : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlτ : upsilon l < τ := hm (lt_add_of_pos_right l (lt_of_le_of_lt zero_le (lt_add_one _)))
  have hX : vt (upsilon (l + 1)) (Om1 * Uc.ucB + Vr.vrVal l (.lo l)) = X := by
    show vt (upsilon (l + 1)) (Om1 * Uc.ucB + l) = X
    rw [Uf.uf_Om1_mul_B]; rfl
  refine ⟨.add (.old (.sg h1 τ)) (.th 1 Uc.ucB (.old (.lo l))), gamma 0, xb_gam_lt S hl0 hlfix,
    ⟨?_, ?_⟩, ⟨trivial, (xb_B_const S).1, (xb_B_const S).2, trivial⟩, ?_⟩
  · refine ⟨lt_of_le_of_lt zero_le (lt_add_one _), hβ, le_rfl, hm (lt_succ _), ?_⟩
    exact ww_par_self hlE hlτ (upsPt_inE hτP) hτO
  · have h1β : (1 : Ordinal.{0}) < β :=
      lt_of_le_of_lt ((one_le_iff_pos.2 (InE.pos hXE)).trans (le_self_add.trans le_self_add)) hβ
    refine ⟨zero_lt_one, h1β, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show l < upsilon (succ l)
      rw [succ_eq_add_one]; exact hlu1
    · show wwVal l (.old (.lo l)) < Om1
      exact hlu1.trans hu1O
    · show Om1 * Uc.ucB + l ∈ Tset (upsilon (l + 1))
      rw [Uf.uf_Om1_mul_B]; exact hξT
    · show Om1 * Uc.ucB + l < OmTwo
      rw [Uf.uf_Om1_mul_B]; exact hξ2
    · show upsilon (l + 1) ≤ vt (upsilon (l + 1)) (Om1 * Uc.ucB + Vr.vrVal l (.lo l))
      rw [hX]; exact hu1X.le
    · show vt (upsilon (l + 1)) (Om1 * Uc.ucB + Vr.vrVal l (.lo l)) < upsilon (succ (l + 1))
      rw [hX, succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hXu2
  · show Vr.vrVal l (.sg h1 τ) + vt (upsilon (l + 1)) (Om1 * Uc.ucB + Vr.vrVal l (.lo l)) = cdR S (l + X)
    rw [hX, Wu.wuR_X k hν hXE hXu2]; rfl

/-- **The refutation of `Ww.wwVis_ref` does not reach `XbVisGen`**: at every window `ν_X` of the gap witness the
forms clause of `XbGen` holds at the offset `X` (`Ww.wwForm_gap` with constant `ϑ`-levels). -/
theorem xbForm_gap (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + wwX S k + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β))
    (hβ2 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + wwX S k) ∨
      XbForm S (Nc.ncL S (k : Ordinal.{0})) β (wwX S k) := by
  right
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  have hm := upsilon_normal.strictMono
  have hνβ := hm.lt_iff_lt.1 hβ1
  rw [add_assoc] at hνβ
  have hXβ : wwX S k + ω ^ 2 < β := (add_lt_add_iff_left _).1 hνβ
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  refine xbForm_X k hν ?_ (hβ2.trans hL1O.le)
  rw [add_assoc]
  exact ((add_lt_add_iff_left _).2 hω).trans hXβ

end Googology.Trans.PoR.InaccPsi.R2.Xb
