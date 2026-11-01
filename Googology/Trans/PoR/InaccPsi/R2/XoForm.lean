import Googology.Trans.PoR.InaccPsi.R2.WwRoad
import Googology.Trans.PoR.InaccPsi.R2.XjGap

/-!
# Decompositions whose `ϑ`-levels carry moving leaves

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ww.WwE` writes a `ϑ`-node `th h M e` with a **constant** level `M`; its image keeps `M`, and the restriction
`Ww.WwR` asks the data of `M` below `υ_μ`.  The witness `Xj.xjX` (level `B₂ + λ`, leaf `λ = υ_λ`) shows that a level
may carry a leaf in `[υ_λ, υ_{λ+h})`, which the realizer moves.  Here the level of a `ϑ`-node is itself a term:

* `XoE` (one syntax for both sorts): `old E` (a decomposition of `Vr.VrE`, also a countable leaf of a level), `th h L
  e` (`ϑ^{υ_{λ+h}}(Ω₁·val L + val e)`), `add`, and the level constructors `lc M` (a **fixed** constant: its data lie
  below `υ_μ`), `phi a b` (`φ(a, b)`), `om a` (`Ω_a`), `coll p e` (`ψ_p(e)`) — the closure operations of `Ul.UlK`, so
  every level below `θ` is a value (`Xo.XoCover`);
* `xoVal` (value over `υ_λ`), `xoImg` (**the leaf substitution**: every leaf is moved by its own segment map — `lo c ↦
  π_{υ_μ,υ_λ}(c)`, `sg h y ↦ mv(υ_{λ+h}, υ_{μ+f h}) y`, a node `th h L e ↦ ϑ^{υ_{μ+f h}}(Ω₁·img L + img e)` — and the
  operations are kept; a fixed constant `lc M` is kept);
* `XoWF`, `XoOs`, `XoCl` (closed: no moving leaf), `XoLow`, `XoR` (restriction, repaired in round 125: `Wf.WfR` on
  old nodes, `VdLtIn M υ_μ` on fixed constants, every closed sub-term low, every countable collapse closed and below
  `υ_μ`);
* `XoForm`, `XoCarry`, `XoSup`, `XoGen`, `XoVisGen`, `XoRealB` (statements, as `Ww.WwForm` … `Ww.WwRealB`);
* `xoOfWw` (`th h M e ↦ th h (lc M) e`), `xoOfWw_val`, `xoOfWw_img`, `xoOfWw_WF`, `xoOfWw_Os`, `xoOfWw_R`;
  `xoOfWw_notCl`; `xoForm_of_ww` (**old forms are new forms**), `xoCarry_ww` / `xoSup_ww` (**the new carry contains `Ww.WwCarry`**).

No new axiom.  New definitions: the syntax `XoE` and the statements above (`XoR` repaired, `XoCl`, `XoLow` new).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **Decompositions and level terms** (one syntax). -/
inductive XoE : Type 1
  | old (E : Vr.VrE)
  | th (h : Ordinal.{0}) (L e : XoE)
  | add (s t : XoE)
  | lc (M : Ordinal.{0})
  | phi (a b : XoE)
  | om (a : XoE)
  | coll (p e : XoE)

instance : Inhabited XoE := ⟨.lc 0⟩

/-- The value over `υ_λ`. -/
noncomputable def xoVal (S : InaccSeq.{0}) (l : Ordinal.{0}) : XoE → Ordinal.{0}
  | .old E => Vr.vrVal l E
  | .th h L e => vt (upsilon (l + h)) (Om1 * xoVal S l L + xoVal S l e)
  | .add s t => xoVal S l s + xoVal S l t
  | .lc M => M
  | .phi a b => veblen (xoVal S l a) (xoVal S l b)
  | .om a => Om (xoVal S l a)
  | .coll p e => S.psi (xoVal S l e) (xoVal S l p)

/-- **The image under `(μ, f)`: the leaf substitution** (leaves moved by their segment maps, operations kept). -/
noncomputable def xoImg (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : XoE → Ordinal.{0}
  | .old E => Vr.vrImg l μ f E
  | .th h L e => vt (upsilon (μ + f h)) (Om1 * xoImg S l μ f L + xoImg S l μ f e)
  | .add s t => xoImg S l μ f s + xoImg S l μ f t
  | .lc M => M
  | .phi a b => veblen (xoImg S l μ f a) (xoImg S l μ f b)
  | .om a => Om (xoImg S l μ f a)
  | .coll p e => S.psi (xoImg S l μ f e) (xoImg S l μ f p)

/-- **Well-formed decompositions** over `υ_λ` with offsets below `β` (a `ϑ`-node as in `Ww.WwWF`, with the level
a term; level constructors only ask their parts). -/
def XoWF (S : InaccSeq.{0}) (l β : Ordinal.{0}) : XoE → Prop
  | .old E => Vr.VrWF l β E
  | .th h L e => 0 < h ∧ h < β ∧ XoWF S l β L ∧ XoWF S l β e ∧ xoVal S l e < Om1 ∧
      Om1 * xoVal S l L + xoVal S l e ∈ Tset (upsilon (l + h)) ∧ Om1 * xoVal S l L + xoVal S l e < OmTwo ∧
      upsilon (l + h) ≤ vt (upsilon (l + h)) (Om1 * xoVal S l L + xoVal S l e) ∧
      vt (upsilon (l + h)) (Om1 * xoVal S l L + xoVal S l e) < upsilon (succ (l + h))
  | .add s t => XoWF S l β s ∧ XoWF S l β t
  | .lc _ => True
  | .phi a b => XoWF S l β a ∧ XoWF S l β b
  | .om a => XoWF S l β a
  | .coll p e => XoWF S l β p ∧ XoWF S l β e

/-- The offsets of a decomposition lie in `Os`. -/
def XoOs (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) : XoE → Prop
  | .old E => Vr.VrOs l Os E
  | .th h L e => h ∈ Os ∧ XoOs l Os L ∧ XoOs l Os e
  | .add s t => XoOs l Os s ∧ XoOs l Os t
  | .lc _ => True
  | .phi a b => XoOs l Os a ∧ XoOs l Os b
  | .om a => XoOs l Os a
  | .coll p e => XoOs l Os p ∧ XoOs l Os e

/-- **Closed** terms: no `old` leaf and no `ϑ`-node (only fixed constants and the level operations). -/
def XoCl : XoE → Prop
  | .old _ => False
  | .th _ _ _ => False
  | .add s t => XoCl s ∧ XoCl t
  | .lc _ => True
  | .phi a b => XoCl a ∧ XoCl b
  | .om a => XoCl a
  | .coll p e => XoCl p ∧ XoCl e

/-- **A fixed value is low**: below `θ` it has a data reading below `υ_μ` (`Vd.VdLtIn`; for a countable value this is
`value < υ_μ`, `Uc.ucDat_small`). -/
def XoLow (S : InaccSeq.{0}) (μ v : Ordinal.{0}) : Prop :=
  v < ConjT.th S → Vd.VdLtIn v (upsilon μ)

/-- **The restriction (repaired, round 125)**: old nodes as `Wf.WfR`; a fixed constant has its data below `υ_μ`;
**every closed sub-term has a low value** (`XoLow`), and **a collapse `ψ_p(e)` with a countable value is closed and
below `υ_μ`** (a countable point `≥ υ_μ` is never spelled by fixed parts: neither by a closed term such as
`F_k = ψ_{Ω₁}(Ω_ω·2 + P′·k) = L(k)`, nor by a collapse whose moving leaf is absorbed, `ψ_{Ω₁}(λ + Ω_ω·2 + P′·k) =
L(k)`). -/
def XoR (S : InaccSeq.{0}) (l μ : Ordinal.{0}) : XoE → Prop
  | .old E => Wf.WfR l μ E
  | .th _ L e => XoR S l μ L ∧ XoR S l μ e
  | .add s t => XoR S l μ s ∧ XoR S l μ t ∧ (XoCl s ∧ XoCl t → XoLow S μ (xoVal S l s + xoVal S l t))
  | .lc M => Vd.VdLtIn M (upsilon μ)
  | .phi a b => XoR S l μ a ∧ XoR S l μ b ∧
      (XoCl a ∧ XoCl b → XoLow S μ (veblen (xoVal S l a) (xoVal S l b)))
  | .om a => XoR S l μ a ∧ (XoCl a → XoLow S μ (Om (xoVal S l a)))
  | .coll p e => XoR S l μ p ∧ XoR S l μ e ∧ (XoCl p ∧ XoCl e → XoLow S μ (S.psi (xoVal S l e) (xoVal S l p))) ∧
      (S.psi (xoVal S l e) (xoVal S l p) < Om1 →
        XoCl p ∧ XoCl e ∧ S.psi (xoVal S l e) (xoVal S l p) < upsilon μ)

/-- **The form** of the reach of the inner restart `λ+g`. -/
def XoForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ E : XoE, XoWF S l β E ∧ xoVal S l E = cdR S (l + g)

/-- **The carry with moving-leaf levels** (`Ww.WwCarry` over `XoE`). -/
def XoCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : XoE, XoWF S l β E → xoVal S l E = cdR S (l + g) → XoOs l Os E → XoR S l μ E →
      xoImg S l μ f E ≤ cdR S (μ + f g)

/-- **The supply clause.** -/
def XoSup (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
    ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
      upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ XoCarry S l β μ f B Os

/-- **The supply hypotheses at `(λ, β)`.** -/
def XoGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ XoForm S l β g) ∧ XoSup S l β

/-- **The visible supply.** -/
def XoVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ Tk.TkCov S (upsilon l) ν →
    Tk.TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ XoGen S l β

/-- **The realizer bridge for moving-leaf levels** (open): `XoGen` at `(λ, β)` gives the realizer up to
`υ_{λ+β}`. -/
def XoRealB (S : InaccSeq.{0}) : Prop :=
  ∀ l β : Ordinal.{0}, IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) → XoGen S l β → Lr.LrReal S (upsilon l) (upsilon (l + β))

/-! ## The constant-level decompositions inside the new ones -/

/-- `th h M e ↦ th h (lc M) e`. -/
def xoOfWw : Ww.WwE → XoE
  | .old E => .old E
  | .th h M e => .th h (.lc M) (xoOfWw e)
  | .add s t => .add (xoOfWw s) (xoOfWw t)

variable {S : InaccSeq.{0}}

theorem xoOfWw_val (l : Ordinal.{0}) : ∀ E : Ww.WwE, xoVal S l (xoOfWw E) = Ww.wwVal l E
  | .old _ => rfl
  | .th h M e => by
    show vt (upsilon (l + h)) (Om1 * M + xoVal S l (xoOfWw e)) = vt (upsilon (l + h)) (Om1 * M + Ww.wwVal l e)
    rw [xoOfWw_val l e]
  | .add s t => by
    show xoVal S l (xoOfWw s) + xoVal S l (xoOfWw t) = Ww.wwVal l s + Ww.wwVal l t
    rw [xoOfWw_val l s, xoOfWw_val l t]

theorem xoOfWw_img (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ E : Ww.WwE, xoImg S l μ f (xoOfWw E) = Ww.wwImg l μ f E
  | .old _ => rfl
  | .th h M e => by
    show vt (upsilon (μ + f h)) (Om1 * M + xoImg S l μ f (xoOfWw e)) =
      vt (upsilon (μ + f h)) (Om1 * M + Ww.wwImg l μ f e)
    rw [xoOfWw_img l μ f e]
  | .add s t => by
    show xoImg S l μ f (xoOfWw s) + xoImg S l μ f (xoOfWw t) = Ww.wwImg l μ f s + Ww.wwImg l μ f t
    rw [xoOfWw_img l μ f s, xoOfWw_img l μ f t]

theorem xoOfWw_WF (l β : Ordinal.{0}) : ∀ E : Ww.WwE, Ww.WwWF l β E → XoWF S l β (xoOfWw E)
  | .old _, h => h
  | .th h M e, ⟨h0, hβ, he, hv, hT, h2, hl, hu⟩ => by
    have hv' : xoVal S l (xoOfWw e) = Ww.wwVal l e := xoOfWw_val l e
    refine ⟨h0, hβ, trivial, xoOfWw_WF l β e he, ?_⟩
    show xoVal S l (xoOfWw e) < Om1 ∧
      Om1 * M + xoVal S l (xoOfWw e) ∈ Tset (upsilon (l + h)) ∧ Om1 * M + xoVal S l (xoOfWw e) < OmTwo ∧
      upsilon (l + h) ≤ vt (upsilon (l + h)) (Om1 * M + xoVal S l (xoOfWw e)) ∧
      vt (upsilon (l + h)) (Om1 * M + xoVal S l (xoOfWw e)) < upsilon (succ (l + h))
    rw [hv']; exact ⟨hv, hT, h2, hl, hu⟩
  | .add s t, ⟨hs, ht⟩ => ⟨xoOfWw_WF l β s hs, xoOfWw_WF l β t ht⟩

theorem xoOfWw_Os (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) :
    ∀ E : Ww.WwE, XoOs l Os (xoOfWw E) ↔ Ww.WwOs l Os E
  | .old _ => Iff.rfl
  | .th h M e => by
    show (h ∈ Os ∧ True ∧ XoOs l Os (xoOfWw e)) ↔ (h ∈ Os ∧ Ww.WwOs l Os e)
    rw [xoOfWw_Os l Os e]; simp
  | .add s t => by
    show (XoOs l Os (xoOfWw s) ∧ XoOs l Os (xoOfWw t)) ↔ (Ww.WwOs l Os s ∧ Ww.WwOs l Os t)
    rw [xoOfWw_Os l Os s, xoOfWw_Os l Os t]

theorem xoOfWw_notCl : ∀ E : Ww.WwE, ¬ XoCl (xoOfWw E)
  | .old _ => fun h => h
  | .th _ _ _ => fun h => h
  | .add s _ => fun h => xoOfWw_notCl s h.1

theorem xoOfWw_R (l μ : Ordinal.{0}) : ∀ E : Ww.WwE, Ww.WwR l μ E → XoR S l μ (xoOfWw E)
  | .old _, h => h
  | .th _ _ e, ⟨hM, he⟩ => ⟨hM, xoOfWw_R l μ e he⟩
  | .add s t, ⟨hs, ht⟩ => ⟨xoOfWw_R l μ s hs, xoOfWw_R l μ t ht, fun h => absurd h.1 (xoOfWw_notCl s)⟩

/-- **Old (constant-level) forms are new forms.** -/
theorem xoForm_of_ww {l β g : Ordinal.{0}} (h : Ww.WwForm S l β g) : XoForm S l β g := by
  obtain ⟨E, hW, hv⟩ := h
  exact ⟨xoOfWw E, xoOfWw_WF l β E hW, (xoOfWw_val l E).trans hv⟩

/-- **The new carry contains `Ww.WwCarry`.** -/
theorem xoCarry_ww {l β μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (h : XoCarry S l β μ f B Os) : Ww.WwCarry S l β μ f B Os := fun g hg h0 hd =>
  ⟨(h g hg h0 hd).1, (h g hg h0 hd).2.1, fun E hE hv ho hr => by
    have := (h g hg h0 hd).2.2 (xoOfWw E) (xoOfWw_WF l β E hE) ((xoOfWw_val l E).trans hv)
      ((xoOfWw_Os l Os E).2 ho) (xoOfWw_R l μ E hr)
    rwa [xoOfWw_img] at this⟩

theorem xoSup_ww {l β : Ordinal.{0}} (h : XoSup S l β) : Ww.WwSup S l β := by
  intro γ hγ Os hOs
  obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h γ hγ Os hOs
  exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, xoCarry_ww h8⟩

end Googology.Trans.PoR.InaccPsi.R2.Xo
