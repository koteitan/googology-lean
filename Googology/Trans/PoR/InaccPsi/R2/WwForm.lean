import Googology.Trans.PoR.InaccPsi.R2.WwGap

/-!
# Repaired forms with `ϑ`-nodes at every level: the gap witness gets a form

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Ww.wwGap` shows that the forms of `Vr.VrForm` (term levels below `B₂`, `sg`-nodes with parameters below `υ_λ`) miss
the reach `r(λ+X) = υ_{λ+(X+ω+1)} + X`, `X = ϑ^{u₁}(B₂ + λ)`.  The reach is a true ordinal fact, so the term language
is too weak.  Here a decomposition may also contain a **`ϑ`-node** `th h M e` of any level `M`:

* value `ϑ^{υ_{λ+h}}(Ω₁·M + val(e))` (`e` a decomposition of a countable argument), well formed when the argument lies
  in `T^{υ_{λ+h}} ∩ Ω₂` and the value lies in the segment `[υ_{λ+h}, υ_{λ+h+1})`;
* image `ϑ^{υ_{μ+f(h)}}(Ω₁·M + img(e))`: the level `M` is kept, the countable argument is moved recursively;
* restriction (`WwR`, the analogue of `Wf.WfR`): the data of `M` lie below `υ_μ` (the level is fixed by the move).

* `WwE`, `wwVal`, `wwImg`, `WwWF`, `WwOs`, `WwR`, `WwForm`, `WwCarry`, `WwSup`, `WwGen`, `WwVisGen` (syntax and
  statements), `wwForm_of_vr` (**old forms are repaired forms**), `wwCarry_wf` / `wwSup_wf` (**the repaired carry
  contains the restricted carry `Wf.WfCarry`**), `wwForm_X` (**the gap witness has a repaired form**: `r(λ+X) =
  val(sg(υ_{λ+(X+ω+1)}) + th 1 B₂ (lo λ))`), `wwForm_gap` (**at every window `ν_X` of `Ww.wwVis_ref` the forms
  clause of `WwGen` holds at the offset `X`**: the refutation does not apply to `WwVisGen`).

No new axiom.  New definitions: the syntax `WwE` and the statements above.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ww

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Repaired decompositions**: the old ones, `ϑ`-nodes of any level, sums. -/
inductive WwE : Type 1
  | old (E : Vr.VrE)
  | th (h M : Ordinal.{0}) (e : WwE)
  | add (s t : WwE)

instance : Inhabited WwE := ⟨.old default⟩

/-- The value over `υ_λ`. -/
noncomputable def wwVal (l : Ordinal.{0}) : WwE → Ordinal.{0}
  | .old E => Vr.vrVal l E
  | .th h M e => vt (upsilon (l + h)) (Om1 * M + wwVal l e)
  | .add s t => wwVal l s + wwVal l t

/-- The image under `(μ, f)`: old nodes as `Vr.vrImg`, a `ϑ`-node keeps its level and moves its argument. -/
noncomputable def wwImg (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : WwE → Ordinal.{0}
  | .old E => Vr.vrImg l μ f E
  | .th h M e => vt (upsilon (μ + f h)) (Om1 * M + wwImg l μ f e)
  | .add s t => wwImg l μ f s + wwImg l μ f t

/-- **Well-formed repaired decompositions** over `υ_λ` with offsets below `β`. -/
def WwWF (l β : Ordinal.{0}) : WwE → Prop
  | .old E => Vr.VrWF l β E
  | .th h M e => 0 < h ∧ h < β ∧ WwWF l β e ∧ wwVal l e < Om1 ∧
      Om1 * M + wwVal l e ∈ Tset (upsilon (l + h)) ∧ Om1 * M + wwVal l e < OmTwo ∧
      upsilon (l + h) ≤ vt (upsilon (l + h)) (Om1 * M + wwVal l e) ∧
      vt (upsilon (l + h)) (Om1 * M + wwVal l e) < upsilon (succ (l + h))
  | .add s t => WwWF l β s ∧ WwWF l β t

/-- The offsets of a repaired decomposition lie in `Os`. -/
def WwOs (l : Ordinal.{0}) (Os : Finset Ordinal.{0}) : WwE → Prop
  | .old E => Vr.VrOs l Os E
  | .th h _ e => h ∈ Os ∧ WwOs l Os e
  | .add s t => WwOs l Os s ∧ WwOs l Os t

/-- **The restriction** (`Wf.WfR` on old nodes; at a `ϑ`-node the data of the level lie below `υ_μ`). -/
def WwR (l μ : Ordinal.{0}) : WwE → Prop
  | .old E => Wf.WfR l μ E
  | .th _ M e => Vd.VdLtIn M (upsilon μ) ∧ WwR l μ e
  | .add s t => WwR l μ s ∧ WwR l μ t

/-- **The repaired form** of the reach of the inner restart `λ+g`. -/
def WwForm (S : InaccSeq.{0}) (l β g : Ordinal.{0}) : Prop :=
  ∃ E : WwE, WwWF l β E ∧ wwVal l E = cdR S (l + g)

/-- **The repaired carry** (`Wf.WfCarry` over repaired decompositions). -/
def WwCarry (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : WwE, WwWF l β E → wwVal l E = cdR S (l + g) → WwOs l Os E → WwR l μ E →
      wwImg l μ f E ≤ cdR S (μ + f g)

/-- **The repaired supply clause.** -/
def WwSup (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
    ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
      upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ WwCarry S l β μ f B Os

/-- **The repaired supply hypotheses at `(λ, β)`.** -/
def WwGen (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧
  (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ WwForm S l β g) ∧ WwSup S l β

/-- **The repaired visible supply** (`Wf.WfVisGen` with `WwGen`). -/
def WwVisGen (S : InaccSeq.{0}) (l b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → upsilon l < upsilon ν → ¬ Tk.TkCov S (upsilon l) ν →
    Tk.TkIso S (upsilon l) ν → ∃ β, upsilon ν < upsilon (l + β) ∧ upsilon (l + β) ≤ b ∧ WwGen S l β

/-! ## The old notions inside the new ones -/

/-- **Old forms are repaired forms.** -/
theorem wwForm_of_vr {l β g : Ordinal.{0}} (h : Vr.VrForm S l β g) : WwForm S l β g := by
  obtain ⟨E, hW, hv⟩ := h
  exact ⟨.old E, hW, hv⟩

/-- **The repaired carry contains the restricted carry.** -/
theorem wwCarry_wf {l β μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (h : WwCarry S l β μ f B Os) : Wf.WfCarry S l β μ f B Os := fun g hg h0 hd =>
  ⟨(h g hg h0 hd).1, (h g hg h0 hd).2.1, fun E hE hv ho hr => (h g hg h0 hd).2.2 (.old E) hE hv ho hr⟩

theorem wwSup_wf {l β : Ordinal.{0}} (h : WwSup S l β) : Wf.WfSup S l β := by
  intro γ hγ Os hOs
  obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h γ hγ Os hOs
  exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, wwCarry_wf h8⟩

/-! ## The gap witness has a repaired form -/

/-- `Par^τ(τ) ⊆ υ_λ` for an inner point `τ = υ_{λ+h}` (`pi_base` with `σ = υ_λ`). -/
theorem ww_par_self {l τ : Ordinal.{0}} (hlE : InE (upsilon l)) (hlτ : upsilon l < τ) (hτE : InE τ)
    (hτ1 : τ < Om1) : ∀ p ∈ Par τ τ, p < upsilon l := by
  have h := (pi_base ⟨hlE, hτE, hlτ, hτ1⟩).1
  exact fun p hp => h.2 (Finset.mem_coe.2 hp)

/-- **The gap witness has a repaired form**: `r(λ+X) = υ_{λ+(X+ω+1)} + ϑ^{u₁}(Ω₁·B₂ + λ)` is the value of
`sg (X+ω+1) υ_{λ+(X+ω+1)} + th 1 B₂ (lo λ)` (given `L(k+1) ≤ ν_C`, `X + ω + 1 < β`, `υ_{λ+β} ≤ Ω₁`). -/
theorem wwForm_X (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : wwX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    WwForm S (Nc.ncL S (k : Ordinal.{0})) β (wwX S k) := by
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
  refine ⟨.add (.old (.sg h1 τ)) (.th 1 Uc.ucB (.old (.lo l))), ⟨?_, ?_⟩, ?_⟩
  · refine ⟨lt_of_le_of_lt zero_le (lt_add_one _), hβ, le_rfl, hm (lt_succ _), ?_⟩
    exact ww_par_self hlE hlτ (upsPt_inE hτP) hτO
  · have hlv : Vr.vrVal l (.lo l) = l := rfl
    have h1β : (1 : Ordinal.{0}) < β :=
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

/-- **The refutation of `Ww.wwVis_ref` does not reach `WwVisGen`**: at the window `ν_X` of the gap witness, every
`β` with `ν_X < υ_{λ+β} ≤ L(k+1)` has the forms clause of `WwGen` at the offset `X`. -/
theorem wwForm_gap (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + wwX S k + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β))
    (hβ2 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + wwX S k) ∨
      WwForm S (Nc.ncL S (k : Ordinal.{0})) β (wwX S k) := by
  right
  obtain ⟨-, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hXE, -, -, -⟩ := wwX_spec (S := S) k
  have hm := upsilon_normal.strictMono
  have hνβ := hm.lt_iff_lt.1 hβ1
  rw [add_assoc] at hνβ
  have hXβ : wwX S k + ω ^ 2 < β := (add_lt_add_iff_left _).1 hνβ
  have hω : ω + 1 < ω ^ 2 :=
    lt_of_lt_of_le ((add_lt_add_iff_left ω).2 (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num)))
      Vo.vo_om2.le
  refine wwForm_X k hν ?_ (hβ2.trans hL1O.le)
  rw [add_assoc]
  exact ((add_lt_add_iff_left _).2 hω).trans hXβ

end Googology.Trans.PoR.InaccPsi.R2.Ww
