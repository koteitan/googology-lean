import Googology.Trans.PoR.InaccPsi.R2.ZaShift
import Googology.Trans.PoR.InaccPsi.R2.YqShift

/-!
# The `ϑ`-node clause of the moving-leaf shift from the moving-level clause of FRAG, at nodes with good levels

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Yq.XoShift2 S` (leaf `skShift2`) is `Xb.XbShift` with the node clause `Yq.XoThCl`: `D(ϑ^{υ_{λ+h}}(Ω₁·val L + val e))
= ϑ^{υ_{μ+f h}}(Ω₁·img L + img e)` at every restricted well-formed node of the configuration (`img = Xo.xoImg`, the
leaf substitution of the term).  The shift of `Za.zaShiftCore` gives, at a node whose level `Ω₁·M` has its leaves in
`X ∪ Y ∪ γ` and in `T^{υ_{λ+h}}`: `D(node) = ϑ^{υ_{μ+f h}}(yvSub D (Ω₁·M) + D(val e))` (`Za.ZaHiD` at the term `par
(val e)` for `M ≥ B₂`; the term clause of `Vl.vlShiftCore` at `thc M (par (val e))` with the level clause for `M <
B₂`).  So the node clause holds at every node whose level is **good** (`ZaLevOK`: the two leaf conditions and the
level image `yvSub D (Ω₁·val L) = Ω₁·img L`), by induction on the decomposition (argument `e` first).

* `za_lt_vt_all` (`η < ϑᵗ(Ω₁·M + η)` for every level `1 ≤ M`, `Ω₁·M < θ`, from `R2.luLt_vt_self`,
  `R2.lvLevel_lt_vt`, `R2.vdLevel_lt`);
* `ZaLevOK`, `ZaNodesOK` (statements: good levels at every `ϑ`-node of a decomposition);
* `zaDCl` (**the node clause at decompositions all of whose `ϑ`-nodes have good levels**);
* `ZaThClW`, `ZaShift3` (`Yq.XoShift2` with the node clause asked only at good nodes), `zaShift3`
  (**`ZaDlSC ⇒ ZaShift3 S`**);
* `ZaNodesAll`, `ZaShift4` (`ZaShift3` with all restricted configuration nodes good), `zaShift2_of4`
  (**`ZaShift4 S ⇒ Yq.XoShift2 S`**);
* `za_nodesOK_lc` (non-vacuity: a node with a constant level `lc M`, data below `γ`, is good).

No new axiom.  New definitions: `ZaLevOK`, `ZaNodesOK`, `ZaThClW`, `ZaShift3`, `ZaNodesAll`, `ZaShift4` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The countable part is below the value at every level** `1 ≤ M`, `Ω₁·M < θ`: `η < ϑᵗ(Ω₁·M + η)` for
`Ω₁·M + η ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`. -/
theorem za_lt_vt_all {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : 1 ≤ M)
    (hMθ : Om1 * M < ConjT.th S) (hη : η ∈ Tset τ) (hη1 : η < Om1) (h : Om1 * M + η ∈ Tset τ) :
    η < vt τ (Om1 * M + η) := by
  rcases lt_or_ge M τ with hMτ | hτM
  · exact luLt_vt_self hτ hτ1 hM1 hMτ hη hη1
  rcases lt_or_ge M Om1 with hMΩ | hΩM
  · have h' : Om1 * (Om1 * 0 + M) + η ∈ Tset τ := by simpa using h
    have hMT := Rj.rjArgT_beta hτ hτ1 Rj.rj_Om1_pos hMΩ hη1 h'
    exact (lvLevel_lt_vt hτ hτ1 hMT hτM hMΩ hη hη1).2
  · have hM : M < ConjT.th S := (Xe.xe_le_mul M).trans_lt hMθ
    have hA := vdArg_dat hτ hτ1 hΩM hη1 h
    have hIn : Vd.VdDatIn (· ∈ Tset τ) M := by
      rcases lt_or_ge M Uc.ucB with hB | hB
      · exact Vd.vdDatIn_uc hB (hA.1 hB)
      · exact Vd.vdDatIn_th hB hM (hA.2 S hB hM)
    exact (vdLevel_lt hτ hτ1 hΩM hIn hη hη1).2

/-- **A good level** at the base `υ_{λ+h}`: `1 ≤ M`, the leaves of `Ω₁·M` lie in `X ∪ Y ∪ γ` and in `T^{υ_{λ+h}}`, and
the leaf substitution of the value is the image of the term: `yvSub D (Ω₁·M) = Ω₁·img L` (`M = val L`). -/
def ZaLevOK (S : InaccSeq.{0}) (l μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (X Y : Finset Ordinal.{0})
    (h : Ordinal.{0}) (L : XoE) : Prop :=
  1 ≤ xoVal S l L ∧ YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) ∧
    YvLv S (· ∈ Tset (upsilon (l + h))) (Om1 * xoVal S l L) ∧
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **Every `ϑ`-node of the countable skeleton has a good level.** -/
def ZaNodesOK (S : InaccSeq.{0}) (l μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : XoE → Prop
  | .old _ => True
  | .th h L e => ZaLevOK S l μ γ f D X Y h L ∧ ZaNodesOK S l μ γ f D X Y e
  | .add s t => ZaNodesOK S l μ γ f D X Y s ∧ ZaNodesOK S l μ γ f D X Y t
  | .lc _ => True
  | .phi _ _ => True
  | .om _ => True
  | .coll _ _ => True

/-- **The node clause at decompositions with good levels**, from the clauses of the shift: the old clause, `+`, the
term clause, the level clause of `D`, and the moving-level clause `ZaHiD`. -/
theorem zaDCl {l β μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl0 : 0 < l) (hβ0 : 0 < β) (hb1 : upsilon (l + β) ≤ Om1) (hXl : ∀ x ∈ X, x < upsilon l)
    (hYl : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β))
    (hadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z))
    (hold : ∀ E : Vr.VrE, Vr.VrWF l β E → (∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y) →
      D (Vr.vrVal l E) = Vr.vrImg l μ f E)
    (hUn : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t))
    (hLC : VlLC (fun p => p ∈ X ∪ Y ∨ p < γ) D) (hZa : ZaHiD S l μ γ f D X Y) :
    ∀ E : XoE, XoWF S l β E → XoTopF E → XoR S l μ E → (∀ z ∈ xoPts S l (upsilon (l + β)) E, z ∈ X ∪ Y) →
      xoVal S l E < upsilon (l + β) → ZaNodesOK S l μ γ f D X Y E → D (xoVal S l E) = xoImg S l μ f E := by
  have hm := upsilon_normal.strictMono
  set b := upsilon (l + β) with hbdef
  intro E
  induction E with
  | old E =>
    intro hW _ _ hp _ _
    have hp' : ∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_filter.2 ⟨hz, Vr.vrPts_lt hβ0 E hW z hz⟩)
    exact hold E hW hp'
  | th h L e _ ihe =>
    intro hW hF hR hp hv hOK
    obtain ⟨h0, hhβ, _, hWe, hη1, hξT, hξ2, hby, hys⟩ := hW
    obtain ⟨⟨hM1, hlvF, hlvT, hsubeq⟩, hOKe⟩ := hOK
    set M := xoVal S l L with hMdef
    set η := xoVal S l e with hηdef
    set τ := upsilon (l + h) with hτdef
    have hτU : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτE : InE τ := upsPt_inE hτU
    have hsb : upsilon (succ (l + h)) ≤ b := hm.monotone (Order.succ_le_of_lt (by
      exact (add_lt_add_iff_left l).2 hhβ))
    have hyb : vt τ (Om1 * M + η) < b := hys.trans_le hsb
    have hτ1 : τ < Om1 := (hby.trans_lt hyb).trans_le hb1
    have hηT : η ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 rfl (dvd_mul_right Om1 M) hη1
    have hτb : τ < b := hm ((add_lt_add_iff_left l).2 hhβ)
    have hbU : UpsPt b := upsPt_upsilon (hl0.trans_le le_self_add)
    have hηb : η < b := Za.za_lt_next hτE hτ1 hηT hη1 hτb hbU
    have hpe : xoPts S l b e ⊆ xoPts S l b (.th h L e) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)))
    have IHe := ihe hWe hF hR.2 (fun z hz => hp z (hpe hz)) hηb hOKe
    have hηXY : η ∈ X ∪ Y := hp _ (hpe (xoVal_mem e hηb))
    have hyXY : vt τ (Om1 * M + η) ∈ X ∪ Y := hp _ (xoVal_mem (.th h L e) hyb)
    have hlτ : upsilon l ≤ τ := hm.monotone le_self_add
    have hyY : vt τ (Om1 * M + η) ∈ Y := by
      rcases Finset.mem_union.1 hyXY with hx | hy
      · exact absurd (hXl _ hx) (not_lt.2 (hlτ.trans hby))
      · exact hy
    have hξθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτE hτ1 _ hξT hξ2
    have hMθ : Om1 * M < ConjT.th S := le_self_add.trans_lt hξθ
    show D (vt τ (Om1 * M + η)) = vt (upsilon (μ + f h)) (Om1 * xoImg S l μ f L + xoImg S l μ f e)
    rw [← IHe, ← hsubeq]
    rcases lt_or_ge M Uc.ucB with hMB | hMB
    · -- a level below `B₂`: the term `thc M (par η)`
      have hqB : Om1 * M < Uc.ucB := Xe.xe_mul_lt_B hMB
      have hVT : Vc.VcLv (· ∈ Tset τ) (Om1 * M) := by
        cases hlvT with
        | low _ hV => exact hV
        | om hs _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs))
        | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      have hVF : Vc.VcLv (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * M) := by
        cases hlvF with
        | low _ hV => exact hV
        | om hs _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs))
        | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      have hGT : Om1 * M ∈ Tset τ := vl_lv_mem hτE hτ1 hM1 hqB hVT
      have hZW : ZW τ (UnT.thc M (UnT.par η)) :=
        ⟨⟨hM1, hqB, hGT, hξT, za_lt_vt_all hτE hτ1 hM1 hMθ hηT hη1 hξT⟩, trivial⟩
      have hWF : WFr τ (UnT.thc M (UnT.par η)) := ⟨trivial, hη1⟩
      obtain ⟨e1, -, -⟩ := hUn _ hyY h hby hys (UnT.thc M (UnT.par η)) hZW hWF hηXY ⟨hVF, trivial⟩ hηT
        ⟨hVT, trivial⟩ rfl
      obtain ⟨e2, -⟩ := hLC M hM1 hqB hVF
      rw [e1, yvSub_low D hqB, ← e2]
      rfl
    · -- a level `≥ B₂`: the moving-level clause at the term `par η`
      obtain ⟨q', e1, -, -, -, -, -, -, hnode, -⟩ := hZa _ hyY h hby hys M (UnT.par η) hM1 hMB hMθ hlvF hlvT
        trivial trivial hη1 hηXY trivial hηT trivial rfl
      rw [hnode, e1]
      rfl
  | add s t ihs iht =>
    intro hW hF hR hp hv hOK
    have hv' : xoVal S l s + xoVal S l t < b := hv
    have hvs : xoVal S l s < b := le_self_add.trans_lt hv'
    have hvt : xoVal S l t < b := le_add_self.trans_lt hv'
    have hps : xoPts S l b s ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
    have hpt : xoPts S l b t ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    have es := ihs hW.1 hF.1 hR.1 (fun z hz => hp z (hps hz)) hvs hOK.1
    have et := iht hW.2 hF.2 hR.2.1 (fun z hz => hp z (hpt hz)) hvt hOK.2
    have hsum := (hadd _ (hp _ (hps (xoVal_mem s hvs))) _ (hp _ (hpt (xoVal_mem t hvt))) _
      (hp _ (xoVal_mem (.add s t) hv))).1 rfl
    show D (xoVal S l s + xoVal S l t) = xoImg S l μ f s + xoImg S l μ f t
    rw [← es, ← et, hsum]; rfl
  | lc _ => intro _ hF; exact hF.elim
  | phi _ _ _ _ => intro _ hF; exact hF.elim
  | om _ _ => intro _ hF; exact hF.elim
  | coll _ _ _ _ => intro _ hF; exact hF.elim

end Googology.Trans.PoR.InaccPsi.R2.Za
