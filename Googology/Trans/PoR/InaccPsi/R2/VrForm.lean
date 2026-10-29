import Googology.Trans.PoR.InaccPsi.R2.VoRoad

/-!
# Repaired forms of inner reaches: finite sums of decompositions over several inner segments

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The forms of `Ub.UbF3`, `Ub.UbForm`, `Vl.VlForm`, `Vl.VlGdForm` write the reach `r(λ+g)` over ONE base `υ_{λ+h}` with
leaves below `υ_λ` or `υ`-points; `Vo.voNoGo` shows this misses `τ + c` with `c` in a lower segment.  Here a reach is
a finite sum of nodes, each node over its own inner segment:

* `lo c` (`c < υ_{λ+1}`, moved by `π_{υ_μ,υ_λ}`), `sg h y` (`y ∈ seg(υ_{λ+h})` with parameters below `υ_λ`, moved by
  the segment move), `ub h t` (`Ub.UbT`-term over `υ_{λ+h}`), `tm h t Lf δ` (`Un.UnC`-term over `υ_{λ+h}`, the terms of
  `Vl.VlForm`), `add s t`;
* leaves of terms: `p < υ_{λ+1}` (moved by `π`) or inner `υ`-points `υ_{λ+h'}`, `h' > 0` (moved to `υ_{μ+f(h')}`).

* `VrE`, `vrVal`, `vrImg` (the image under `(μ, f)`), `VrWF`, `VrOs`, `vrPts` (the points the realizer must contain),
  `VrForm`, `VrCarry`;
* `vrVal_mem`, `vrPts_lt` (every point lies below `υ_{λ+β}`);
* `vrForm_of_f3` (**the second and third forms of `Ub.UbF3` are repaired forms**), `vrForm_of_ub`
  (**`Ub.UbForm ⇒ VrForm`**), `vrForm_of_vl` (**`Vl.VlForm ⇒ VrForm`**), `vrForm_of_gd` (**`Vl.VlGdForm ⇒ VrForm`**).

New definitions: `VrE`, `vrVal`, `vrImg`, `vrLf`, `vrLv`, `vrLvO`, `VrWF`, `VrOs`, `vrPts`, `VrForm`, `VrCarry`
(statements and syntax).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tv Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi
  Googology.Trans.PoR.InaccPsi.R2.Vl

variable {S : InaccSeq.{0}}

/-- **A decomposition of an ordinal over the inner segments of `υ_λ`** (syntax). -/
inductive VrE : Type 1
  | lo (c : Ordinal.{0})
  | sg (h y : Ordinal.{0})
  | ub (h : Ordinal.{0}) (t : UbT)
  | tm (h : Ordinal.{0}) (t : UnC) (Lf : Finset Ordinal.{0}) (δ : Ordinal.{0})
  | add (s t : VrE)

instance : Inhabited VrE := ⟨.lo 0⟩

/-- The value of a decomposition over `υ_λ`. -/
noncomputable def vrVal (l : Ordinal.{0}) : VrE → Ordinal.{0}
  | .lo c => c
  | .sg _ y => y
  | .ub h t => UbT.ev (upsilon (l + h)) t
  | .tm h t _ _ => UnT.ev (upsilon (l + h)) t
  | .add s t => vrVal l s + vrVal l t

/-- The leaf map: `p < υ_{λ+1}` goes to `π_{υ_μ,υ_λ}(p)`, `υ_{λ+h'}` to `υ_{μ+f(h')}`. -/
noncomputable def vrLf (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (p : Ordinal.{0}) : Ordinal.{0} :=
  if p < upsilon (succ l) then pi (upsilon μ) (upsilon l) p else upsilon (μ + f (Lr.lrIx p - l))

/-- **The image of a decomposition under `(μ, f)`**: each node moved by its own segment map. -/
noncomputable def vrImg (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : VrE → Ordinal.{0}
  | .lo c => pi (upsilon μ) (upsilon l) c
  | .sg h y => mv (upsilon (l + h)) (upsilon (μ + f h)) y
  | .ub h t => UbT.ev (upsilon (μ + f h)) (t.map (vrLf l μ f))
  | .tm h t _ _ => UnT.ev (upsilon (μ + f h)) (vmap (vrLf l μ f) t)
  | .add s t => vrImg l μ f s + vrImg l μ f t

/-- The leaves of the terms: `p < υ_{λ+1}` or `p = υ_{λ+h'}` with `0 < h' < B`. -/
def vrLv (l B p : Ordinal.{0}) : Prop :=
  p < upsilon (succ l) ∨ ∃ h', 0 < h' ∧ h' < B ∧ p = upsilon (l + h')

/-- The leaves with offsets in `Os`. -/
def vrLvO (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) (p : Ordinal.{0}) : Prop :=
  p < upsilon (succ l) ∨ ∃ h' ∈ Os, 0 < h' ∧ p = upsilon (l + h')

/-- **Well-formed decompositions** over `υ_λ` with offsets below `β`. -/
def VrWF (l β : Ordinal.{0}) : VrE → Prop
  | .lo c => c < upsilon (succ l)
  | .sg h y => 0 < h ∧ h < β ∧ upsilon (l + h) ≤ y ∧ y < upsilon (succ (l + h)) ∧
      ∀ p ∈ Par (upsilon (l + h)) y, p < upsilon l
  | .ub h t => 0 < h ∧ h < β ∧ UbT.IsA t ∧ UbT.WF (upsilon (l + h)) t ∧ UbT.Lv (vrLv l β) t ∧
      upsilon (l + h) ≤ UbT.ev (upsilon (l + h)) t ∧ UbT.ev (upsilon (l + h)) t < upsilon (succ (l + h))
  | .tm h t Lf δ => 0 < h ∧ h < β ∧ δ < upsilon l ∧ ZW (upsilon (l + h)) t ∧ WFr (upsilon (l + h)) t ∧
      UnT.Lv (vrLv l (succ h)) t ∧ ZL (fun p => p ∈ Lf ∨ p < δ) t ∧ (∀ p ∈ Lf, vrLv l (succ h) p) ∧
      upsilon (l + h) ≤ UnT.ev (upsilon (l + h)) t ∧ UnT.ev (upsilon (l + h)) t < upsilon (succ (l + h))
  | .add s t => VrWF l β s ∧ VrWF l β t

/-- **The offsets of a decomposition lie in `Os`.** -/
def VrOs (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) : VrE → Prop
  | .lo _ => True
  | .sg h _ => h ∈ Os
  | .ub h t => h ∈ Os ∧ UbT.Lv (vrLvO l Os) t
  | .tm h t Lf _ => h ∈ Os ∧ UnT.Lv (vrLvO l Os) t ∧ ∀ p ∈ Lf, vrLvO l Os p
  | .add s t => VrOs l Os s ∧ VrOs l Os t

/-- **The points a realizer configuration must contain** for a decomposition: every node value, every partial sum,
every leaf, every node base `υ_{λ+h}`, every level-leaf bound `δ`. -/
noncomputable def vrPts (l : Ordinal.{0}) : VrE → Finset Ordinal.{0}
  | .lo c => {c}
  | .sg h y => {upsilon (l + h), y}
  | .ub h t => insert (upsilon (l + h)) (insert (UbT.ev (upsilon (l + h)) t) (UbT.lvs t))
  | .tm h t Lf δ => insert (upsilon (l + h)) (insert (UnT.ev (upsilon (l + h)) t) (insert δ (UnT.lvs t ∪ Lf)))
  | .add s t => insert (vrVal l s + vrVal l t) (vrPts l s ∪ vrPts l t)

/-- **The repaired form** of the reach of the inner restart `λ+g`: a well-formed decomposition with value
`r(λ+g)`. -/
def VrForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ E : VrE, VrWF l β E ∧ vrVal l E = cdR S (l + g)

/-- **The carry for the repaired forms** (EQ under `(μ, f)`): LOWER at `μ + f(g)`, the big reaches, and
`D(r(λ+g)) = (image of the decomposition) ≤ r(μ+f(g))` for every decomposition of `r(λ+g)` with offsets in `Os`. -/
def VrCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : VrE, VrWF l β E → vrVal l E = cdR S (l + g) → VrOs l Os E → vrImg l μ f E ≤ cdR S (μ + f g)

/-- The value of a decomposition is one of its points. -/
theorem vrVal_mem (l : Ordinal.{0}) : ∀ E : VrE, vrVal l E ∈ vrPts l E
  | .lo _ => Finset.mem_singleton_self _
  | .sg _ _ => Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  | .ub _ _ => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  | .tm _ _ _ _ => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  | .add _ _ => Finset.mem_insert_self _ _

/-- `υ_{λ+1} ≤ υ_{λ+h}` for `h > 0`. -/
theorem vr_succ_le {l h : Ordinal.{0}} (h0 : 0 < h) : upsilon (succ l) ≤ upsilon (l + h) :=
  upsilon_normal.strictMono.monotone (by rw [succ_eq_add_one]; exact add_le_add_right (one_le_iff_pos.2 h0) l)

/-- `υ_{succ(λ+h)} ≤ υ_{λ+β}` for `h < β`. -/
theorem vr_seg_le {l h β : Ordinal.{0}} (hh : h < β) : upsilon (succ (l + h)) ≤ upsilon (l + β) := by
  refine upsilon_normal.strictMono.monotone ?_
  rw [Lr.lr_succ_add]; exact Lr.lr_addLe (Order.succ_le_of_lt hh)

/-- A leaf of a term lies below `υ_{λ+β}` when `B ≤ β`, `0 < β`. -/
theorem vrLv_lt {l B β p : Ordinal.{0}} (hB : B ≤ β) (hβ : 0 < β) (h : vrLv l B p) : p < upsilon (l + β) := by
  rcases h with h | ⟨h', -, hh', rfl⟩
  · exact h.trans_le (upsilon_normal.strictMono.monotone (by
      rw [succ_eq_add_one]; exact add_le_add_right (one_le_iff_pos.2 hβ) l))
  · exact upsilon_normal.strictMono (add_lt_add_right (hh'.trans_le hB) l)

/-- **Every point of a well-formed decomposition lies below `υ_{λ+β}`** (`υ_{λ+β}` is additive principal). -/
theorem vrPts_lt {l β : Ordinal.{0}} (hβ : 0 < β) :
    ∀ E : VrE, VrWF l β E → ∀ z ∈ vrPts l E, z < upsilon (l + β) := by
  have hm := upsilon_normal.strictMono
  have hE : InE (upsilon (l + β)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hβ le_add_self))
  intro E
  induction E with
  | lo c =>
    intro hw z hz
    rw [vrPts, Finset.mem_singleton] at hz; subst hz
    exact vrLv_lt le_rfl hβ (Or.inl hw)
  | sg h y =>
    intro hw z hz
    obtain ⟨h0, hh, -, h2, -⟩ := hw
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hm (add_lt_add_right hh l)
    · rw [Finset.mem_singleton.1 hz]; exact h2.trans_le (vr_seg_le hh)
  | ub h t =>
    intro hw z hz
    obtain ⟨h0, hh, -, -, hL, -, h2⟩ := hw
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hm (add_lt_add_right hh l)
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact h2.trans_le (vr_seg_le hh)
    · exact vrLv_lt le_rfl hβ (UbT.mem_lvs hL z hz)
  | tm h t Lf δ =>
    intro hw z hz
    obtain ⟨h0, hh, hδ, -, -, hL, -, hLf, -, h2⟩ := hw
    have hsβ : succ h ≤ β := Order.succ_le_of_lt hh
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hm (add_lt_add_right hh l)
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact h2.trans_le (vr_seg_le hh)
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hδ.trans (hm (lt_add_of_pos_right l hβ))
    rcases Finset.mem_union.1 hz with hz | hz
    · exact vrLv_lt hsβ hβ (UnT.mem_lvs hL z hz)
    · exact vrLv_lt hsβ hβ (hLf z hz)
  | add s t ihs iht =>
    intro hw z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact (inE_indec hE).add_lt (ihs hw.1 _ (vrVal_mem l s)) (iht hw.2 _ (vrVal_mem l t))
    rcases Finset.mem_union.1 hz with hz | hz
    · exact ihs hw.1 z hz
    · exact iht hw.2 z hz

/-! ## The old forms are repaired forms -/

/-- A leaf below `υ_λ` or an inner `υ`-point `υ_{λ+h'}` (`h' < B`) is a leaf of `vrLv`. -/
theorem vrLv_of_old {l B p : Ordinal.{0}} (h : p < upsilon l ∨ ∃ h', h' < B ∧ p = upsilon (l + h')) :
    vrLv l B p := by
  have hlt : upsilon l < upsilon (succ l) := upsilon_normal.strictMono (lt_succ l)
  rcases h with h | ⟨h', hh', rfl⟩
  · exact Or.inl (h.trans hlt)
  · rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ h') with e | h0
    · rw [← e, add_zero]; exact Or.inl hlt
    · exact Or.inr ⟨h', h0, hh', rfl⟩

/-- **The second and third forms of `Ub.UbF3` are repaired forms**: `υ_{λ+h} + c` (`c < υ_{λ+1}`) is
`ub h base + lo c`, a low point of `seg(υ_{λ+h})` is `sg h r`. -/
theorem vrForm_of_f3 {l β g : Ordinal.{0}}
    (h : (∃ h c, 0 < h ∧ h < β ∧ c < upsilon (succ l) ∧ cdR S (l + g) = upsilon (l + h) + c) ∨
      ∃ h, 0 < h ∧ h < β ∧ TvLowAt S l g h) : VrForm S l β g := by
  rcases h with ⟨h, c, h0, hh, hc, e⟩ | ⟨h, h0, hh, hL⟩
  · refine ⟨.add (.ub h .base) (.lo c), ⟨⟨h0, hh, trivial, trivial, trivial, le_rfl,
      upsilon_normal.strictMono (lt_succ _)⟩, hc⟩, ?_⟩
    rw [e]; rfl
  · exact ⟨.sg h (cdR S (l + g)), ⟨h0, hh, hL.1, hL.2.1, hL.2.2⟩, rfl⟩

/-- **`Ub.UbForm ⇒ VrForm`** (one `ub`-node). -/
theorem vrForm_of_ub {l β g : Ordinal.{0}} (h : UbForm S l β g) : VrForm S l β g := by
  obtain ⟨h, t, h0, hh, hA, hW, hL, h1, h2, e⟩ := h
  refine ⟨.ub h t, ⟨h0, hh, hA, hW, UbT.Lv_mono (fun p hp => vrLv_of_old hp) t hL, e ▸ h1, e ▸ h2⟩, e⟩

/-- **`Vl.VlForm ⇒ VrForm`** (one `tm`-node). -/
theorem vrForm_of_vl {l β g : Ordinal.{0}} (h : VlForm S l β g) : VrForm S l β g := by
  obtain ⟨h, t, Lf, δ, h0, hh, hδ, hz, hw, hL, hzl, hLf, h1, h2, e⟩ := h
  have hc : ∀ p, (p < upsilon l ∨ ∃ h', h' ≤ h ∧ p = upsilon (l + h')) → vrLv l (succ h) p := fun p hp =>
    vrLv_of_old (hp.imp id fun ⟨h', hh', e'⟩ => ⟨h', Order.lt_succ_of_le hh', e'⟩)
  exact ⟨.tm h t Lf δ, ⟨h0, hh, hδ, hz, hw, UnT.Lv_mono hc t hL, hzl, fun p hp => hc p (hLf p hp),
    e ▸ h1, e ▸ h2⟩, e⟩

/-- **`Vl.VlGdForm ⇒ VrForm`** (`Vl.vlForm_of_gd`). -/
theorem vrForm_of_gd {l β g : Ordinal.{0}} (hl : IsRestartIdx l) (h : VlGdForm S l β g) : VrForm S l β g :=
  vrForm_of_vl (vlForm_of_gd hl h)

end Googology.Trans.PoR.InaccPsi.R2.Vr
