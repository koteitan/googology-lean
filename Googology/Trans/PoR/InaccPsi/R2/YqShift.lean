import Googology.Trans.PoR.InaccPsi.R2.YqReal

/-!
# The clause of the moving-leaf shift, reduced to one node clause on top of `Xb.XbShift`

`b = υ_{λ+β}`, `D` the realizer map of a configuration `X ∪ Y` (`X` below `υ_λ`, `Y` in `[υ_λ, b)`).  The clause
`Yq.XoDCl` (`D(value) = image` on restricted decompositions with an `old` / `th` / `add` skeleton, the shape the
covering lemma `Yq.yqCoverT` produces) is proved by induction on the skeleton from

* the clauses of `Xb.XbShift` on the old decompositions (through `Vr.vrD_eq`), the additivity of `D`, and
* one node clause **`XoThCl`**: the statement of `XoDCl` at decompositions whose root is a `ϑ`-node `th h L e` with a
  level TERM `L` (moving leaves included), `e` with an `old` / `th` / `add` skeleton.

* `yq_img_cl` (closed terms: image = value), `yqDCl` (**the induction**);
* `XoThCl`, `XoShift2` (**`Xb.XbShift` with `XoThCl` in place of `Xb.XbThCl`**; statements), `yqShift_of2`
  (**`XoShift2 S ⇒ XoShift S`**), `yqRealBL2` (**`XoShift2 S ⇒ XoRealBL S`**).

No new axiom.  New definitions: `XoThCl`, `XoShift2` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Xo
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi
  Googology.Trans.PoR.InaccPsi.R2.Vl

variable {S : InaccSeq.{0}}

/-- **Closed terms: the image is the value.** -/
theorem yq_img_cl (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ E : XoE, XoCl E → xoImg S l μ f E = xoVal S l E := by
  intro E
  induction E with
  | old _ => exact fun h => h.elim
  | th _ _ _ _ _ => exact fun h => h.elim
  | add s t ihs iht =>
    intro h; show xoImg S l μ f s + xoImg S l μ f t = xoVal S l s + xoVal S l t; rw [ihs h.1, iht h.2]
  | lc _ => intro _; rfl
  | phi a b iha ihb =>
    intro h
    show veblen (xoImg S l μ f a) (xoImg S l μ f b) = veblen (xoVal S l a) (xoVal S l b); rw [iha h.1, ihb h.2]
  | om a iha => intro h; show Om (xoImg S l μ f a) = Om (xoVal S l a); rw [iha h]
  | coll p e ihp ihe =>
    intro h
    show S.psi (xoImg S l μ f e) (xoImg S l μ f p) = S.psi (xoVal S l e) (xoVal S l p); rw [ihp h.1, ihe h.2]

/-- **The `ϑ`-node clause with a level term** (open): `XoDCl` at decompositions whose root is a `ϑ`-node. -/
def XoThCl (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (X Y : Finset Ordinal.{0}) :
    Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) →
    D (xoVal S l (.th h L e)) = xoImg S l μ f (.th h L e)

theorem yq_pts_sub {l b : Ordinal.{0}} {E F : XoE} (h : xoRaw S l E ⊆ xoRaw S l F) :
    xoPts S l b E ⊆ xoPts S l b F :=
  Finset.filter_subset_filter _ h

/-- **The induction**: `XoDCl` from the old clauses, additivity and `XoThCl`. -/
theorem yqDCl {l β μ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hβ0 : 0 < β)
    (hadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z))
    (hold : ∀ E : Vr.VrE, Vr.VrWF l β E → (∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y) → D (Vr.vrVal l E) = Vr.vrImg l μ f E)
    (hth : XoThCl S l β μ f D X Y) :
    ∀ E : XoE, XoWF S l β E → XoTopF E → XoR S l μ E → (∀ z ∈ xoPts S l (upsilon (l + β)) E, z ∈ X ∪ Y) →
      xoVal S l E < upsilon (l + β) → D (xoVal S l E) = xoImg S l μ f E := by
  set b := upsilon (l + β) with hbdef
  intro E
  induction E with
  | old E =>
    intro hW _ _ hp _
    have hp' : ∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_filter.2 ⟨hz, Vr.vrPts_lt hβ0 E hW z hz⟩)
    exact hold E hW hp'
  | th h L e _ _ => intro hW hF hR hp _; exact hth h L e hW hF hR hp
  | add s t ihs iht =>
    intro hW hF hR hp hv
    have hv' : xoVal S l s + xoVal S l t < b := hv
    have hvs : xoVal S l s < b := le_self_add.trans_lt hv'
    have hvt : xoVal S l t < b := le_add_self.trans_lt hv'
    have hps : xoPts S l b s ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
    have hpt : xoPts S l b t ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    have es := ihs hW.1 hF.1 hR.1 (fun z hz => hp z (hps hz)) hvs
    have et := iht hW.2 hF.2 hR.2.1 (fun z hz => hp z (hpt hz)) hvt
    have hsum := (hadd _ (hp _ (hps (xoVal_mem s hvs))) _ (hp _ (hpt (xoVal_mem t hvt))) _
      (hp _ (xoVal_mem (.add s t) hv))).1 rfl
    show D (xoVal S l s + xoVal S l t) = xoImg S l μ f s + xoImg S l μ f t
    rw [← es, ← et, hsum]; rfl
  | lc _ => intro _ hF; exact hF.elim
  | phi _ _ _ _ => intro _ hF; exact hF.elim
  | om _ _ => intro _ hF; exact hF.elim
  | coll _ _ _ _ => intro _ hF; exact hF.elim

/-- **The shift with the `ϑ`-node clause** (open): `Xb.XbShift` with `XoThCl` in place of `Xb.XbThCl`. -/
def XoShift2 (S : InaccSeq.{0}) : Prop :=
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
      XoThCl S l β μ f D X Y

/-- **`XoShift2 S ⇒ XoShift S`.** -/
theorem yqShift_of2 (h2 : XoShift2 S) : XoShift S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, ⟨hQ, hXγ, hγμ, hW, hres, himg, ⟨hμl, hpi⟩, hmv, hub, hun, -, hDid, -⟩,
      hth⟩ := h2 l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, hQ, hXγ, hγμ, hW, hres, himg, hμl, fun hβ0 => ?_⟩
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hW.rng.1.1))
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
  exact yqDCl hβ0 hW.add
    (fun E hWE hp => (Vr.vrD_eq hl0 hb1 hX hY hW.fix hW.add hXγ hγμ hBμ hres hpi hmv hub hun hDid E hWE hp).1)
    hth

/-- **`XoShift2 S ⇒ XoRealBL S`.** -/
theorem yqRealBL2 (h2 : XoShift2 S) : XoRealBL S := yqRealBL (yqShift_of2 h2)

end Googology.Trans.PoR.InaccPsi.R2.Yq
