import Googology.Trans.PoR.InaccPsi.R2.ZaThCl

/-!
# `Yq.XoShift2` from the moving-level shift: the statement with good nodes (proved), and the reduction

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

* `ZaThClW` (**the node clause `Yq.XoThCl` at nodes all of whose `ϑ`-nodes have good levels**, `Za.ZaNodesOK`),
  `ZaShift3` (**`Yq.XoShift2` with `ZaThClW` in place of `Yq.XoThCl`**), `zaShift3` (**`Za.ZaDlSC ⇒ ZaShift3 S`**:
  `Za.zaShiftCore` with `Za.zaDCl`);
* `ZaNodesAll`, `ZaShift4` (**`ZaShift3` with every restricted configuration node good**), `zaShift2_of4`
  (**`ZaShift4 S ⇒ Yq.XoShift2 S`**);
* `za_levOK_const` (**non-vacuity**: a constant level `lc M` whose leaves lie below a strongly critical `q ≤ γ` is
  good; with `zaShift3` this gives the constant-level clause `Xb.XbThCl` again).

No new axiom.  New definitions: `ZaThClW`, `ZaShift3`, `ZaNodesAll`, `ZaShift4` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The node clause at good nodes**: `Yq.XoThCl` asked only where every `ϑ`-node has a good level. -/
def ZaThClW (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → ZaNodesOK S l μ γ f D X Y (.th h L e) →
    D (xoVal S l (.th h L e)) = xoImg S l μ f (.th h L e)

/-- **Every restricted well-formed node of the configuration is good.** -/
def ZaNodesAll (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → ZaNodesOK S l μ γ f D X Y (.th h L e)

/-- **`Yq.XoShift2` with the node clause at good nodes.** -/
def ZaShift3 (S : InaccSeq.{0}) : Prop :=
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
      ZaThClW S l β μ γ f D X Y

/-- **`Yq.XoShift2` with the node clause at good nodes and every configuration node good.** -/
def ZaShift4 (S : InaccSeq.{0}) : Prop :=
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
      ZaThClW S l β μ γ f D X Y ∧ ZaNodesAll S l β μ γ f D X Y

/-- **`ZaShift3 S` holds under `ZaDlSC`** (`Za.zaShiftCore` at the constant levels `Xe.XeLev`, with `Za.zaDCl`). -/
theorem zaShift3 (hDl : ZaDlSC) : ZaShift3 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hLs, hups, hYB, hseg, hmv, hUb, hUn, hLC, hid, hγU, -, hZa⟩ :=
    zaShiftCore (S := S) hDl Xj.xjNodeXe hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, hXγ, hγμ, hLs, hups, hYB, hseg, hmv, hUb, hUn, hLC, hid, hγU⟩, ?_⟩
  intro h L e hW hF hR hp hOK
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hW.2.1
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hLs.rng.1.1))
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hseg.1, hl1⟩
  have hold := fun E hWE hp' =>
    (Vr.vrD_eq hl0 hb1 hX hY hLs.fix hLs.add hXγ hγμ hBμ hups hseg.2 hmv hUb hUn hid E hWE hp').1
  have hsb : upsilon (succ (l + h)) ≤ upsilon (l + β) :=
    upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hW.2.1))
  have hv : xoVal S l (.th h L e) < upsilon (l + β) := hW.2.2.2.2.2.2.2.2.trans_le hsb
  exact zaDCl hl0 hβ0 hb1 hX hY hLs.add hold hUn hLC hZa (.th h L e) hW hF hR hp hv hOK

/-- **`ZaShift4 S ⇒ Yq.XoShift2 S`.** -/
theorem zaShift2_of4 (h4 : ZaShift4 S) : XoShift2 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hA, hW, hN⟩ := h4 l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  exact ⟨D, μ, f, B, γ, Os, hA, fun h L e hW' hF hR hp => hW h L e hW' hF hR hp (hN h L e hW' hF hR hp)⟩

/-- **Non-vacuity of the good levels: a constant level.**  A level `lc M` (`1 ≤ M`, `Ω₁·M < θ`) whose leaves lie
below a strongly critical `q ≤ γ`, `q ≤ υ_{λ+h}`, is good for every map `D` that fixes the ordinals below `q`. -/
theorem za_levOK_const {l μ γ h M q : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl0 : 0 < l) (hτ1 : upsilon (l + h) < Om1) (hqγ : q ≤ γ) (hqτ : q ≤ upsilon (l + h)) (hM1 : 1 ≤ M)
    (hMθ : Om1 * M < ConjT.th S) (hL : YvLv S (· < q) (Om1 * M)) (hD : ∀ x, x < q → D x = x) :
    ZaLevOK S l μ γ f D X Y h (.lc M) := by
  have hτE : InE (upsilon (l + h)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  obtain ⟨r, hG, hr⟩ := yv_bound (S := S) hMθ
  have hid : YvR S id (Om1 * M) (Om1 * M) := yv_sub_id r _ hL hG hr
  have hR : YvR S D (Om1 * M) (Om1 * M) := yvR_congr (hL.mono fun x hx => (hD x hx).symm) hid
  refine ⟨hM1, hL.mono fun x hx => Or.inr (hx.trans_le hqγ),
    hL.mono fun x hx => Uh.uh_T_le hτE hτ1 (hx.trans_le hqτ).le, yvSub_eq hR⟩

end Googology.Trans.PoR.InaccPsi.R2.Za
