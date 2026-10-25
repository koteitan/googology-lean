import Googology.Trans.PoR.InaccPsi.R2.UbTerm
import Googology.Trans.PoR.InaccPsi.R2.SiInd
import Googology.Trans.PoR.InaccPsi.R2.CitedUe

/-!
# Terms with uncountable `ϑ`-arguments of a constant level, their base changes and the translations of §6

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`UeT` extends the countable-argument terms of `Ub.UbT` (parameters, `+`, `ϑᵗ(0)`, `ϑᵗ(1 + ξ)`) by the node
`thc q r` with value `ϑᵗ(Ω₁·q + r)` (`r` countable, `q` a constant level, `1 ≤ q < κ` for a fixed `ε`-number `κ`
below every base, the predicate `Qs κ`).  `ev τ t` evaluates over the base `τ`; `WF τ t` asks the argument bounds;
`Nd τ P t` asks `P` of the value of every `thc`-node.  `tr a t` is the translation `t^a_b` of [W07a] Def 6.2
(`ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`, `ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)`).

* `ueMem` (**membership**: leaves in `Tᵗ` ⇒ the value is in `Tᵗ`), `ueLe` (**every leaf and every `thc`-value is
  `≤` the value**; [W07a] Lemma 3.30 through `R2.luLt_vt_self`);
* `ueDown` (**the base change with a general parameter map**: `π_{σ,τ}(t[τ; p]) = t[σ; π p]`), `ueUp`, `ueUp_eq`
  (**its inverse**), `ueMv` (**the segment move on terms**);
* `ueTrA` (**`t^α_τ` is correct**: for `α = Dl τ n`, if every `thc`-value over `α` is `< α⁺` then
  `(tr α t)[τ] = t[α]`; `R2.ueVt_tr` (i), `R2.vt_wbar`), `ueTrB` (**`t^τ_α` is correct**: if every `thc`-value of
  `tr α t` over `τ` is `< α⁺` then `(tr α t)[τ] = t[α]`; `R2.ueVt_tr` (ii)).

New definitions: `UeT`, `ev`, `map`, `Lv`, `Qs`, `WF`, `Nd`, `tr`.  No new axiom (uses `R2.ueVt_tr`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ue

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- Terms over a base: parameters, `+`, `ϑᵗ(0)`, `ϑᵗ(1 + ξ)`, `ϑᵗ(Ω₁·q + ρ)`. -/
inductive UeT : Type 1
  | par : Ordinal.{0} → UeT
  | add : UeT → UeT → UeT
  | base : UeT
  | th1 : UeT → UeT
  | thc : Ordinal.{0} → UeT → UeT

namespace UeT

instance : Inhabited UeT := ⟨UeT.base⟩

/-- Evaluation over the base `τ`. -/
noncomputable def ev (τ : Ordinal.{0}) : UeT → Ordinal.{0}
  | par p => p
  | add s t => ev τ s + ev τ t
  | base => τ
  | th1 s => vt τ (1 + ev τ s)
  | thc q r => vt τ (Om1 * q + ev τ r)

/-- Apply `f` to every leaf (the levels `q` are constants). -/
def map (f : Ordinal.{0} → Ordinal.{0}) : UeT → UeT
  | par p => par (f p)
  | add s t => add (map f s) (map f t)
  | base => base
  | th1 s => th1 (map f s)
  | thc q r => thc q (map f r)

/-- Every leaf satisfies `P`. -/
def Lv (P : Ordinal.{0} → Prop) : UeT → Prop
  | par p => P p
  | add s t => Lv P s ∧ Lv P t
  | base => True
  | th1 s => Lv P s
  | thc _ r => Lv P r

/-- Every level `q` of a `thc`-node satisfies `1 ≤ q < κ`. -/
def Qs (κ : Ordinal.{0}) : UeT → Prop
  | par _ => True
  | add s t => Qs κ s ∧ Qs κ t
  | base => True
  | th1 s => Qs κ s
  | thc q r => 1 ≤ q ∧ q < κ ∧ Qs κ r

/-- The argument bounds over `τ`: the arguments of `th1` and the countable parts of `thc` are `< Ω₁`. -/
def WF (τ : Ordinal.{0}) : UeT → Prop
  | par _ => True
  | add s t => WF τ s ∧ WF τ t
  | base => True
  | th1 s => WF τ s ∧ ev τ s < Om1
  | thc _ r => WF τ r ∧ ev τ r < Om1

/-- Every `thc`-node value over `τ` satisfies `P`. -/
def Nd (τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : UeT → Prop
  | par _ => True
  | add s t => Nd τ P s ∧ Nd τ P t
  | base => True
  | th1 s => Nd τ P s
  | thc q r => P (vt τ (Om1 * q + ev τ r)) ∧ Nd τ P r

/-- The translation `t^a_b` of [W07a] Def 6.2 (`ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`,
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)`). -/
def tr (a : Ordinal.{0}) : UeT → UeT
  | par p => par p
  | add s t => add (tr a s) (tr a t)
  | base => par a
  | th1 s => th1 (add (par a) (tr a s))
  | thc q r => thc q (add (par a) (tr a r))

theorem Lv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) : ∀ t : UeT, Lv P t → Lv Q t
  | par p, h => hPQ p h
  | add s t, h => ⟨Lv_mono hPQ s h.1, Lv_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_mono hPQ s h
  | thc _ r, h => Lv_mono hPQ r h

theorem Nd_mono {τ : Ordinal.{0}} {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) :
    ∀ t : UeT, Nd τ P t → Nd τ Q t
  | par _, _ => trivial
  | add s t, h => ⟨Nd_mono hPQ s h.1, Nd_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Nd_mono hPQ s h
  | thc _ r, h => ⟨hPQ _ h.1, Nd_mono hPQ r h.2⟩

theorem Qs_mono {κ κ' : Ordinal.{0}} (hκ : κ ≤ κ') : ∀ t : UeT, Qs κ t → Qs κ' t
  | par _, _ => trivial
  | add s t, h => ⟨Qs_mono hκ s h.1, Qs_mono hκ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Qs_mono hκ s h
  | thc _ r, h => ⟨h.1, h.2.1.trans_le hκ, Qs_mono hκ r h.2.2⟩

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ t : UeT, (t.map g).map f = t.map (f ∘ g)
  | par _ => rfl
  | add s t => by simp only [map, map_map f g s, map_map f g t]
  | base => rfl
  | th1 s => by simp only [map, map_map f g s]
  | thc _ r => by simp only [map, map_map f g r]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} : ∀ t : UeT, Lv (fun p => f p = g p) t → t.map f = t.map g
  | par _, h => by simp only [map]; rw [show _ = _ from h]
  | add s t, h => by simp only [map, map_congr s h.1, map_congr t h.2]
  | base, _ => rfl
  | th1 s, h => by simp only [map, map_congr s h]
  | thc _ r, h => by simp only [map, map_congr r h]

theorem map_id : ∀ t : UeT, t.map id = t
  | par _ => rfl
  | add s t => by simp only [map, map_id s, map_id t]
  | base => rfl
  | th1 s => by simp only [map, map_id s]
  | thc _ r => by simp only [map, map_id r]

theorem Lv_and {P Q : Ordinal.{0} → Prop} : ∀ (t : UeT), Lv P t → Lv Q t → Lv (fun p => P p ∧ Q p) t
  | par _, h1, h2 => ⟨h1, h2⟩
  | add s t, h1, h2 => ⟨Lv_and s h1.1 h2.1, Lv_and t h1.2 h2.2⟩
  | base, _, _ => trivial
  | th1 s, h1, h2 => Lv_and s h1 h2
  | thc _ r, h1, h2 => Lv_and r h1 h2

theorem Lv_map {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ t : UeT, Lv (fun p => P (f p)) t → Lv P (t.map f)
  | par _, h => h
  | add s t, h => ⟨Lv_map s h.1, Lv_map t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_map s h
  | thc _ r, h => Lv_map r h

theorem Qs_map {κ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UeT, Qs κ t → Qs κ (t.map f)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_map f s h.1, Qs_map f t h.2⟩
  | base, _ => trivial
  | th1 s, h => Qs_map f s h
  | thc _ r, h => ⟨h.1, h.2.1, Qs_map f r h.2.2⟩

theorem tr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ t : UeT, (tr a t).map f = tr (f a) (t.map f)
  | par _ => rfl
  | add s t => by simp only [tr, map, tr_map a f s, tr_map a f t]
  | base => rfl
  | th1 s => by simp only [tr, map, tr_map a f s]
  | thc _ r => by simp only [tr, map, tr_map a f r]

theorem Qs_tr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ t : UeT, Qs κ t → Qs κ (tr a t)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_tr a s h.1, Qs_tr a t h.2⟩
  | base, _ => trivial
  | th1 s, h => ⟨trivial, Qs_tr a s h⟩
  | thc _ r, h => ⟨h.1, h.2.1, trivial, Qs_tr a r h.2.2⟩

theorem Lv_tr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) : ∀ t : UeT, Lv P t → Lv P (tr a t)
  | par _, h => h
  | add s t, h => ⟨Lv_tr ha s h.1, Lv_tr ha t h.2⟩
  | base, _ => ha
  | th1 s, h => ⟨ha, Lv_tr ha s h⟩
  | thc _ r, h => ⟨ha, Lv_tr ha r h⟩

/-- The leaves of `tr a t` are those of `t` and `a`. -/
theorem Lv_tr_inv {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} : ∀ t : UeT, Lv P (tr a t) → Lv P t
  | par _, h => h
  | add s t, h => ⟨Lv_tr_inv s h.1, Lv_tr_inv t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_tr_inv s h.2
  | thc _ r, h => Lv_tr_inv r h.2

end UeT

open UeT

/-! ## Membership and the order of the parts -/

/-- A countable ordinal below an `ε`-number base `τ` lies in `Tᵗ`; so does `τ` ([W07b] Cor 5.10, `T_inter_Om1`). -/
theorem ue_T_le {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ≤ τ) : x ∈ Tset τ := by
  obtain ⟨m, hm, -, -, hT⟩ := T_inter_Om1 hτ hτ1
  exact (hT x (hx.trans_lt hτ1)).2 (hx.trans_lt hm)

/-- `Ω₁·q + x ∈ Tᵗ` and `< Ω₂` for a level `q < κ` (`κ < τ` a base) and `x ∈ Tᵗ ∩ Ω₁`. -/
theorem ue_arg_T {κ τ q x : Ordinal.{0}} (hB : Bases κ τ) (hq : q < κ) (hx : x ∈ Tset τ) (hx1 : x < Om1) :
    Om1 * q + x ∈ Tset τ ∧ Om1 * q + x < OmTwo := by
  have hτ1 := hB.2.2.2
  have hq1 : q < Om1 := hq.trans (hB.2.2.1.trans hτ1)
  exact ⟨vzT_add hB.2.1 hτ1 (Si.siOm1_mul_lt hB q hq).1.1 hx, lkcMul_lt hq1 hx1⟩

/-- **Membership**: leaves in `Tᵗ`, the argument bounds and levels below `κ` give `t[τ] ∈ Tᵗ`. -/
theorem ueMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UeT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (ueMem hB s hl.1 hw.1 hq.1) (ueMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => ue_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := ue_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (ueMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := ue_arg_T hB hq.2.1 (ueMem hB r hl hw.1 hq.2.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1

/-- **Every leaf and every `thc`-value is `≤` the value** ([W07a] Lemma 3.30 through `luLt_vt_self`, Lemma 4.2
through `vt_wbar`). -/
theorem ueLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UeT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t
  | .par _, _, _, _ => ⟨le_refl _, trivial⟩
  | .add s t, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ueLe hB s hl.1 hw.1 hq.1
    obtain ⟨b1, b2⟩ := ueLe hB t hl.2 hw.2 hq.2
    have hs : ev τ s ≤ ev τ (.add s t) := le_self_add
    have ht : ev τ t ≤ ev τ (.add s t) := le_add_self
    exact ⟨⟨Lv_mono (fun p hp => hp.trans hs) s a1, Lv_mono (fun p hp => hp.trans ht) t b1⟩,
      ⟨Nd_mono (fun p hp => hp.trans hs) s a2, Nd_mono (fun p hp => hp.trans ht) t b2⟩⟩
  | .base, _, _, _ => ⟨trivial, trivial⟩
  | .th1 s, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ueLe hB s hl hw.1 hq
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact ⟨Lv_mono (fun p hp => hp.trans hle) s a1, Nd_mono (fun p hp => hp.trans hle) s a2⟩
  | .thc q r, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := ueLe hB r hl hw.1 hq.2.2
    have hrT := ueMem hB r hl hw.1 hq.2.2
    have hlt : ev τ r < ev τ (.thc q r) :=
      luLt_vt_self hB.2.1 hB.2.2.2 hq.1 (hq.2.1.trans hB.2.2.1) hrT hw.2
    exact ⟨Lv_mono (fun p hp => hp.trans hlt.le) r a1, le_rfl, Nd_mono (fun p hp => hp.trans hlt.le) r a2⟩

/-! ## The base change on terms -/

/-- **The base change with a general parameter map** ([W07a] Def 5.1, Lemma 5.3 through `pi_lt`, `pi_base`,
`pi_add`, `pi_vt`, `pi_vt_two`, `Si.siOm1_mul_lt`): for bases `σ < τ`, levels below `σ`, a term with the argument
bounds over `τ` whose leaves lie in `Tᵗ[σ]`: `t[τ] ∈ Tᵗ[σ]`, `π_{σ,τ}(t[τ; p]) = t[σ; π p]`, and the image has the
argument bounds over `σ`. -/
theorem ueDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UeT, WF τ t → Lv (· ∈ TB τ σ) t → Qs κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WF σ (t.map (pi σ τ))
  | .par p, _, hp, _ => ⟨hp, rfl, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueDown h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := ueDown h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueDown h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueDown h hκσ r hw.1 hl hq.2.2
    obtain ⟨g1, g2⟩ := Si.siOm1_mul_lt h q (hq.2.1.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hq1 : q < Om1 := (hq.2.1.trans_le hκσ).trans (h.2.2.1.trans h.2.2.2)
    have hlt2 : Om1 * q + ev τ r < OmTwo := lkcMul_lt hq1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2

/-- **The inverse base change on terms**: leaves in `T^σ` ⇒ the term over `τ` with leaves `π_{σ,τ}⁻¹ p` lies in
`Tᵗ[σ]`, has the argument bounds, and is sent by `π_{σ,τ}` to `t[σ; p]`. -/
theorem ueUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UeT, WF σ t → Lv (· ∈ Tset σ) t → Qs κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ))
  | .par p, _, hp, _ => ⟨(up_spec h hp).1, (up_spec h hp).2, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueUp h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := ueUp h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueUp h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 : ev τ (s.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (s.map (up σ τ)) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := ueUp h hκσ r hw.1 hl hq.2.2
    have hy1 : ev τ (r.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨g1, g2⟩ := Si.siOm1_mul_lt h q (hq.2.1.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hq1 : q < Om1 := (hq.2.1.trans_le hκσ).trans (h.2.2.1.trans h.2.2.2)
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := lkcMul_lt hq1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem ueUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UeT) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := ueUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: for `ε`-numbers `b, c < Ω₁`, levels below `κ ≤ b, c` and leaves in `Tᵇ[κ]`:
`mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem ueMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UeT) (hq : Qs κ t) (hw : WF b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WF c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := ueDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact ueUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/

/-- **`t^α_τ` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.ueVt_tr` (i) and `R2.vt_wbar`): for
`α = Dl τ n` (`n ≥ 1`), levels below `κ < τ`, leaves in `T^α`, the argument bounds over `α`, and every `thc`-value
over `α` below `α⁺ = Dp τ n`: `tr α t` has the argument bounds over `τ` and `(tr α t)[τ] = t[α]`. -/
theorem ueTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UeT, Qs κ t → Lv (· ∈ Tset (Dl τ n)) t → WF (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WF τ (tr (Dl τ n) t) ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrA hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2⟩ := ueTrA hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrA hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrA hB hn r hq.2.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := ueMem hBα r hl hw.1 hq.2.2
    have hargT := (ue_arg_T hBα hq.2.1 hrT hw.2).1
    have e := (ueVt_tr hB.2.1 hB.2.2.2 hn hq.1 (hq.2.1.trans hB.2.2.1) hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]; rw [a2, e]

/-- **`t^τ_α` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.ueVt_tr` (ii) and `R2.vt_wbar`): for
`α = Dl τ n` (`n ≥ 1`), levels below `κ < τ`, if `tr α t` has the argument bounds over `τ`, leaves in `Tᵗ`, and every
`thc`-value of `tr α t` over `τ` is below `α⁺ = Dp τ n`, then `t` has the argument bounds over `α` and
`(tr α t)[τ] = t[α]`. -/
theorem ueTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UeT, Qs κ t → Lv (· ∈ Tset τ) (tr (Dl τ n) t) → WF τ (tr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (tr (Dl τ n) t) → WF (Dl τ n) t ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrB hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2⟩ := ueTrB hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrB hB hn s hq hl.2 hw.1.2 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_⟩
    simp only [tr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := ueTrB hB hn r hq.2.2 hl.2 hw.1.2 hd.2.2
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    -- the argument over `τ` is in `Tᵗ`
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (tr (Dl τ n) r) ∈ Tset τ :=
      ueMem hB _ hl.2 hw.1.2 (Qs_tr _ r hq.2.2)
    have hsT : Dl τ n + ev τ (tr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (ue_arg_T hB hq.2.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (ueVt_tr hB.2.1 hB.2.2.2 hn hq.1 (hq.2.1.trans hB.2.2.1) hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, e]

/-! ## The countable-argument terms of `Ub.UbT` -/

/-- The countable-argument terms of `Ub.UbT` as terms of `UeT` (`th`, `om` nodes are not used: sent to `base`). -/
def ofUb : Ub.UbT → UeT
  | .par p => .par p
  | .add s t => .add (ofUb s) (ofUb t)
  | .base => .base
  | .th1 s => .th1 (ofUb s)
  | .th _ => .base
  | .om _ => .base

theorem ofUb_ev (τ : Ordinal.{0}) : ∀ t : Ub.UbT, Ub.UbT.IsA t → ev τ (ofUb t) = Ub.UbT.ev τ t
  | .par _, _ => rfl
  | .add s t, h => by simp only [ofUb, ev, Ub.UbT.ev, ofUb_ev τ s h.1, ofUb_ev τ t h.2]
  | .base, _ => rfl
  | .th1 s, h => by simp only [ofUb, ev, Ub.UbT.ev, ofUb_ev τ s h]
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : Ub.UbT, ofUb (t.map f) = (ofUb t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUb, map, Ub.UbT.map, ofUb_map f s, ofUb_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUb, map, Ub.UbT.map, ofUb_map f s]
  | .th _ => rfl
  | .om _ => rfl

theorem ofUb_WF (τ : Ordinal.{0}) : ∀ t : Ub.UbT, Ub.UbT.IsA t → (WF τ (ofUb t) ↔ Ub.UbT.WF τ t)
  | .par _, _ => Iff.rfl
  | .add s t, h => by
    simp only [ofUb, WF, Ub.UbT.WF]; rw [ofUb_WF τ s h.1, ofUb_WF τ t h.2]
  | .base, _ => Iff.rfl
  | .th1 s, h => by
    simp only [ofUb, WF, Ub.UbT.WF]; rw [ofUb_WF τ s h, ofUb_ev τ s h]
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_Lv {P : Ordinal.{0} → Prop} : ∀ t : Ub.UbT, Ub.UbT.IsA t → (Lv P (ofUb t) ↔ Ub.UbT.Lv P t)
  | .par _, _ => Iff.rfl
  | .add s t, h => by
    simp only [ofUb, Lv, Ub.UbT.Lv]; rw [ofUb_Lv s h.1, ofUb_Lv t h.2]
  | .base, _ => Iff.rfl
  | .th1 s, h => by simp only [ofUb, Lv, Ub.UbT.Lv]; exact ofUb_Lv s h
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_Qs (κ : Ordinal.{0}) : ∀ t : Ub.UbT, Qs κ (ofUb t)
  | .par _ => trivial
  | .add s t => ⟨ofUb_Qs κ s, ofUb_Qs κ t⟩
  | .base => trivial
  | .th1 s => ofUb_Qs κ s
  | .th _ => trivial
  | .om _ => trivial

/-- The levels of the `thc`-nodes. -/
noncomputable def lvq : UeT → Finset Ordinal.{0}
  | .par _ => ∅
  | .add s t => lvq s ∪ lvq t
  | .base => ∅
  | .th1 s => lvq s
  | .thc q r => insert q (lvq r)

/-- Levels below `b`, each of them below `γ`, are levels below `γ`. -/
theorem Qs_of_lvq {b γ : Ordinal.{0}} : ∀ t : UeT, Qs b t → (∀ q ∈ lvq t, q < γ) → Qs γ t
  | .par _, _, _ => trivial
  | .add s t, h, hq => ⟨Qs_of_lvq s h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq t h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | .base, _, _ => trivial
  | .th1 s, h, hq => Qs_of_lvq s h hq
  | .thc q r, h, hq => ⟨h.1, hq q (Finset.mem_insert_self _ _),
      Qs_of_lvq r h.2.2 (fun q' hq' => hq q' (Finset.mem_insert_of_mem hq'))⟩

/-- The levels of a term with levels below `b` are below `b`. -/
theorem lvq_lt {b : Ordinal.{0}} : ∀ t : UeT, Qs b t → ∀ q ∈ lvq t, q < b
  | .par _, _, q, hq => absurd hq (Finset.notMem_empty q)
  | .add s t, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt s h.1 q hq
    · exact lvq_lt t h.2 q hq
  | .base, _, q, hq => absurd hq (Finset.notMem_empty q)
  | .th1 s, h, q, hq => lvq_lt s h q hq
  | .thc q' r, h, q, hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h.2.1
    · exact lvq_lt r h.2.2 q hq

/-- The set of leaves. -/
noncomputable def lvs : UeT → Finset Ordinal.{0}
  | .par p => {p}
  | .add s t => lvs s ∪ lvs t
  | .base => ∅
  | .th1 s => lvs s
  | .thc _ r => lvs r

theorem Lv_lvs : ∀ t : UeT, Lv (· ∈ lvs t) t
  | .par _ => Finset.mem_singleton_self _
  | .add s t => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) s (Lv_lvs s),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) t (Lv_lvs t)⟩
  | .base => trivial
  | .th1 s => Lv_lvs s
  | .thc _ r => Lv_lvs r

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {t : UeT}, Lv P t → ∀ p ∈ lvs t, P p
  | .par _, h, p, hp => by rw [lvs, Finset.mem_singleton] at hp; rw [hp]; exact h
  | .add s t, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := s) h.1 p hp
    · exact mem_lvs (t := t) h.2 p hp
  | .base, _, p, hp => absurd hp (Finset.notMem_empty p)
  | .th1 s, h, p, hp => mem_lvs (t := s) h p hp
  | .thc _ r, h, p, hp => mem_lvs (t := r) h p hp

end Googology.Trans.PoR.InaccPsi.R2.Ue
