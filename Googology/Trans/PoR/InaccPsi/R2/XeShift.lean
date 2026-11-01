import Googology.Trans.PoR.InaccPsi.R2.XbRoad
import Googology.Trans.PoR.InaccPsi.R2.XeFix

/-!
# The `ϑ`-node clause of the shift at constant levels below `θ`: the case of a constant argument

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Xb.XbShift S` is `Vl.vlShiftCore` with the clause `Xb.XbThCl` added: `D(ϑ^{υ_{λ+h}}(Ω₁·M + η)) = ϑ^{υ_{μ+f(h)}}(Ω₁·M
+ D η)` for a constant level `M` (data below the bottom `γ`) and a point `η ∈ X ∪ Y`.  Here the case `η ∈ X` (a point
below `γ`, fixed by `D`) is proved for every level `Ω₁·M < θ`, from the move clause of `Vl.vlShiftCore` (`D = mv` on a
point whose parameters are below `υ_λ`) and the node lemmas `Xe.xe_arg_TB`, `Xe.xeMv` of `R2.XeFix` (which use the
code `π`-fix `Xe.xe_pi_fix_th` on `[B₂, θ)`; no translation is needed).  The case `η ∈ Y` at a level `Ω₁·M < B₂` is the
term clause of `Vl.vlShiftCore` itself, at the term `thc M (par η)` of `Un.UnC` (`xe_thCl_lowLev`).  What is left of
`Xb.XbShift` is the case `η ∈ Y` at a level `M ≥ B₂` (`XeThHi`).

* `XeThHi` (**the clause for `η ∈ Y`, `M ≥ B₂`**), `xe_thCl_low` (**the clause for `η ∈ X`**, every constant level
  `Ω₁·M < θ`), `xe_thCl_lowLev` (**the clause for every `η ∈ X ∪ Y` at a level `Ω₁·M < B₂`**), `xe_thCl_of_hi` (**`XeThHi ⇒ Xb.XbThCl`** under the conclusion of the shift);
* `XeShift` (`Xb.XbShift` with `XeThHi` in place of `Xb.XbThCl`), `xbShift_of_xe` (**`XeShift S ⇒ Xb.XbShift S`**),
  `xbRealB_of_xe` (**`XeShift S ⇒ Xb.XbRealB S`**), `xeShift_of_xb` (**the converse: `XeShift S ⇔
  Xb.XbShift S`**).

No new axiom.  New definitions: `XeThHi`, `XeShift` (Props).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xe

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xb

variable {S : InaccSeq.{0}}

/-- **The `ϑ`-node clause for a point `η ∈ Y` at a level `M ≥ B₂`** (open): `Xb.XbThCl` with `η ∈ Y` in place of
`η ∈ X ∪ Y` and the extra hypothesis `B₂ ≤ M`. -/
def XeThHi (l μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0}) (Y : Finset Ordinal.{0}) : Prop :=
  ∀ y ∈ Y, ∀ h M η : Ordinal.{0}, 0 < h → upsilon (l + h) ∈ Y → η ∈ Y → Uc.ucB ≤ M → Vd.VdLtIn M γ →
    η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h)) → Om1 * M + η < OmTwo →
    y = vt (upsilon (l + h)) (Om1 * M + η) → upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) →
    D y = vt (upsilon (μ + f h)) (Om1 * M + D η)

/-- **The `ϑ`-node clause for a point `η ∈ X`** at every constant level `Ω₁·M < θ`: if `X` lies below the `υ`-point
`γ < υ_μ < υ_λ`, `D` is the identity below `γ` and `mv` on the points of `Y` with parameters below `υ_λ`, and the
images `υ_{μ+f(h)}` of the points `υ_{λ+h} ∈ Y` are countable, then `D(ϑ^{υ_{λ+h}}(Ω₁·M + η)) = ϑ^{υ_{μ+f(h)}}(Ω₁·M +
D η)` for `η ∈ X`. -/
theorem xe_thCl_low {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hγ : UpsPt γ) (hγμ : γ < upsilon μ) (hμl : upsilon μ < upsilon l)
    (hY1 : ∀ y ∈ Y, y < Om1) (hXγ : ∀ x ∈ X, x < γ) (hid : ∀ x, x < γ → D x = x)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (hc1 : ∀ h, upsilon (l + h) ∈ Y → upsilon (μ + f h) < Om1) :
    ∀ y ∈ Y, ∀ h M η : Ordinal.{0}, 0 < h → upsilon (l + h) ∈ Y → η ∈ X → 1 ≤ M → Vd.VdLtIn M γ →
      η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h)) → Om1 * M + η < OmTwo →
      y = vt (upsilon (l + h)) (Om1 * M + η) → upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) →
      D y = vt (upsilon (μ + f h)) (Om1 * M + D η) := by
  intro y hy h M η h0 hbY hηX h1 hd _ _ _ hyv hby hys
  have hm := upsilon_normal.strictMono
  have hmono := upsilon_normal.monotone
  have hηγ : η < γ := hXγ η hηX
  have hγE : InE γ := upsPt_inE hγ
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hμ0 : 0 < μ := by
    refine pos_iff_ne_zero.2 fun e => ?_
    rw [e, upsilon_zero] at hγμ
    exact absurd hγμ (not_lt.2 zero_le)
  set b := upsilon (l + h) with hbdef
  set c := upsilon (μ + f h) with hcdef
  have hbE : InE b := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hcE : InE c := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  have hb1 : b < Om1 := hby.trans_lt (hY1 y hy)
  have hc1' : c < Om1 := hc1 h hbY
  have hγb : γ < b := (hγμ.trans hμl).trans_le (hmono le_self_add)
  have hγc : γ < c := hγμ.trans_le (hmono le_self_add)
  have hM : XeLev γ M := xeLev_of_ltIn hγE h1 hd
  -- the parameters of `y` are below `γ`
  have hBγ : Bases γ b := ⟨hγE, hbE, hγb, hb1⟩
  have hξ := (xe_arg_TB hBγ le_rfl hM (mem_TB_of_lt hBγ hηγ)).1
  have hξ2 : Om1 * M + η < OmTwo :=
    (Lq.lq_SC_indec Uc.uc_SC_Om2).add_lt hM.one_le.2 ((hηγ.trans (hγb.trans hb1)).trans Uc.uc_Om1_lt_Om2)
  have hpar : ∀ p ∈ Par b y, p < upsilon l := by
    intro p hp
    rw [hyv, (vt_memTwo hbE hb1 hξ.1 hξ2).2.2.2.2] at hp
    exact (hξ.2 (Finset.mem_coe.2 hp) : p < γ).trans (hγμ.trans hμl)
  rw [hmv y hy h hby hys hpar, hyv, hid η hηγ]
  exact xeMv hγE hbE hb1 hcE hc1' hγb hγc hM hηγ


/-- **The `ϑ`-node clause for a point `η ∈ Y` at a level `Ω₁·M < B₂`**, from the term clause of `Vl.vlShiftCore`
(the term `thc M (par η)` of `Un.UnC`; its level leaves are below `γ`, so fixed by `D`). -/
theorem xe_thCl_lowLev {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hγ : UpsPt γ) (hγμ : γ < upsilon μ) (hμl : upsilon μ < upsilon l)
    (hY1 : ∀ y ∈ Y, y < Om1) (hid : ∀ x, x < γ → D x = x)
    (hUn : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t)) :
    ∀ y ∈ Y, ∀ h M η : Ordinal.{0}, 0 < h → upsilon (l + h) ∈ Y → η ∈ X ∪ Y → M < Uc.ucB → 1 ≤ M →
      Vd.VdLtIn M γ → η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h)) → Om1 * M + η < OmTwo →
      y = vt (upsilon (l + h)) (Om1 * M + η) → upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) →
      D y = vt (upsilon (μ + f h)) (Om1 * M + D η) := by
  intro y hy h M η _ _ hη hMB h1 hd hη1 hξT hξ2 hyv hby hys
  have hmono := upsilon_normal.monotone
  have hγE : InE γ := upsPt_inE hγ
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  set b := upsilon (l + h) with hbdef
  have hbE : InE b := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hb1 : b < Om1 := hby.trans_lt (hY1 y hy)
  have hγb : γ < b := (hγμ.trans hμl).trans_le (hmono le_self_add)
  have hBγ : Bases γ b := ⟨hγE, hbE, hγb, hb1⟩
  have hU : Uy.UyLev γ M := by
    rcases xeLev_of_ltIn hγE h1 hd with hU | ⟨hB, -⟩
    · exact hU
    · exact absurd hMB (not_lt.2 hB)
  have hlv : Vc.VcLv (· < γ) (Om1 * M) := (Vc.vc_dat_lt hγE _ hU.2.1).2 hU.2.2.2
  have hηT : η ∈ Tset b := vzRem_T hbE hb1 hξT hξ2 rfl (dvd_mul_right Om1 M) hη1
  have hZW : ZW b (UnT.thc M (UnT.par η)) :=
    ⟨⟨hU.1, hU.2.1, (Uy.uy_Om1_mul_TB hBγ le_rfl hU).1.1, hξT, Uy.uyLt_vt_self hBγ hU hηT hη1⟩, trivial⟩
  have hWF : WFr b (UnT.thc M (UnT.par η)) := ⟨trivial, hη1⟩
  have hZL : ZL (fun p => p ∈ X ∪ Y ∨ p < γ) (UnT.thc M (UnT.par η)) :=
    ⟨Vc.VcLv_mono (fun x _ hx => Or.inr hx) _ hlv, trivial⟩
  have hZLT : ZL (· ∈ Tset b) (UnT.thc M (UnT.par η)) :=
    ⟨Vc.VcLv_mono (fun x _ hx => (mem_TB_of_lt hBγ hx).1) _ hlv, trivial⟩
  obtain ⟨e1, -, -⟩ := hUn y hy h hby hys (UnT.thc M (UnT.par η)) hZW hWF hη hZL hηT hZLT hyv.symm
  have hvq : vq D M = M := by
    unfold vq
    rw [Vc.vcSub_fix _ (Vc.VcLv_mono (fun x _ hx => hid x hx) _ hlv)]
    exact Ordinal.mul_div_cancel M Rj.rj_Om1_pos.ne'
  rw [e1]
  simp only [vmap, UnT.ev, hvq]

/-- **`XeThHi ⇒ Xb.XbThCl`** under the conclusion of the shift (`xe_thCl_low`, `xe_thCl_lowLev`). -/
theorem xe_thCl_of_hi {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl : IsRestartIdx l) (hγ : UpsPt γ) (hγμ : γ < upsilon μ) (hμl : upsilon μ < upsilon l)
    (hY1 : ∀ y ∈ Y, y < Om1) (hXγ : ∀ x ∈ X, x < γ) (hid : ∀ x, x < γ → D x = x)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (hc1 : ∀ h, upsilon (l + h) ∈ Y → upsilon (μ + f h) < Om1)
    (hUn : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t))
    (hHi : XeThHi l μ γ f D Y) :
    XbThCl l μ γ f D X Y := by
  intro y hy h M η h0 hbY hη h1 hd
  rcases Finset.mem_union.1 hη with hηX | hηY
  · exact xe_thCl_low hl hγ hγμ hμl hY1 hXγ hid hmv hc1 y hy h M η h0 hbY hηX h1 hd
  · rcases lt_or_ge M Uc.ucB with hMB | hMB
    · exact xe_thCl_lowLev hl hγ hγμ hμl hY1 hid hUn y hy h M η h0 hbY hη hMB h1 hd
    · exact hHi y hy h M η h0 hbY hηY hMB hd

/-- **`Xb.XbShift` with the clause only for `η ∈ Y`** (open): the statement of `Vl.vlShiftCore` with `XeThHi` added
to its conclusion. -/
def XeShift (S : InaccSeq.{0}) : Prop :=
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
      XeThHi l μ γ f D Y

/-- **`XeShift S ⇒ Xb.XbShift S`**: the case `η ∈ X` of `Xb.XbThCl` is `xe_thCl_low`. -/
theorem xbShift_of_xe (H : XeShift S) : XbShift S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  have hm := upsilon_normal.strictMono
  have hY1 : ∀ y ∈ Y, y < Om1 := fun y hy => lt_of_lt_of_le (hY y hy).2 (hνβ.trans nuC_le_Om1)
  obtain ⟨D, μ, f, B, γ, Os, ⟨⟨hQ, hμB⟩, hXγ, hγμ, hLs, hups, hYB, hseg, hmv, hUb, hUn, hLC, hid, hγU⟩, hHi⟩ :=
    H l β (fun μ f B γ Os => Q μ f B γ Os ∧ μ + B ≤ l) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, a1, a2, a3, a4, a5, a6, a7, a8, a4⟩) hstd hlL X Y hX hY
  have hc1 : ∀ h, upsilon (l + h) ∈ Y → upsilon (μ + f h) < Om1 := fun h hb => by
    rw [← (hups h hb).2]
    exact (hYB _ hb).trans_le ((upsilon_normal.monotone hμB).trans hl1.le)
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, hXγ, hγμ, hLs, hups, hYB, hseg, hmv, hUb, hUn, hLC, hid, hγU⟩, ?_⟩
  exact xe_thCl_of_hi hl hγU hγμ hseg.1 hY1 hXγ hid hmv hc1 hUn hHi

/-- **`Xb.XbShift S ⇒ XeShift S`**: the reduction loses nothing (`XeShift S ⇔ Xb.XbShift S`). -/
theorem xeShift_of_xb (H : XbShift S) : XeShift S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hc, hTh⟩ := H l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, hc, ?_⟩
  intro y hy h M η h0 hbY hηY hMB hd
  exact hTh y hy h M η h0 hbY (Finset.mem_union_right X hηY)
    ((Order.one_le_iff_pos).2 (lt_of_le_of_lt zero_le (Uc.ucB_gt.trans_le hMB))) hd

/-- **`XeShift S ⇒ Xb.XbRealB S`** (`Xb.xbRealB`). -/
theorem xbRealB_of_xe (H : XeShift S) : XbRealB S := xbRealB (xbShift_of_xe H)

#print axioms xe_thCl_low
#print axioms xe_thCl_lowLev
#print axioms xbShift_of_xe
#print axioms xbRealB_of_xe
#print axioms xeShift_of_xb

end Googology.Trans.PoR.InaccPsi.R2.Xe
