import Googology.Trans.PoR.InaccPsi.R2.FragBase
import Googology.Trans.PoR.InaccPsi.R2.FragX
import Googology.Trans.PoR.InaccPsi.R2.CitedEv
import Googology.Trans.PoR.InaccPsi.R2.SePi

/-!
# A term type for `Tᵗ` with evaluation, and the base change on terms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`UbT` is a type of terms built from parameters (any ordinal, as a leaf), `+`, the base `ϑᵗ(0) = τ`, `ϑᵗ(1 + ξ)`
(`th1`, countable `ξ`), `ϑᵗ(ξ)` (`th`, `ξ < Ω₂`) and `ϑ₁(ξ) = Ω₁·ω^ξ` (`om`, `ξ` below every `ε`-number above
`Ω₁`).  `ev τ t` evaluates `t` over the base `τ`; `WF τ t` asks the argument bounds of [W07a] Def 3.22 at every
`ϑ`-node.  The link to `Tset`, `Par`, `π`, `ht` is by theorems from the existing cited clauses only (no new axiom):

* `ubDown` (**base change with a general parameter map**: if every leaf lies in `Tᵗ[σ]` then `ev τ t ∈ Tᵗ[σ]` and
  `π_{σ,τ}(t[τ; p]) = t[σ; π_{σ,τ} p]`; leaves above `τ` are allowed) — from [W07a] Def 5.1 (`pi_lt`, `pi_base`,
  `pi_add`, `pi_vt`, `pi_vt_two`, `om1_opow_TB_all`), Def 3.22 / 3.28 (`vt_mem`, `vt_memTwo`);
* `ubUp` (**the inverse base change on terms**: `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`, countable-argument terms);
* `ubMv` (**the segment move `mv b c` on terms**), `ubHtPar` (`ht` and `Par` agree on the two terms);
* `trA` (**the translation `t^a_b` of [W07a] Def 6.2 for countable arguments**: `ϑ^a(0) ↦ a`,
  `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`), `ubTr` (**`t^a_b` denotes the same ordinal**, i.e. [W07a] Lemma 6.3 on these
  terms, proved from [W07a] Lemma 4.2, `vt_wbar`);
* `ubSegPi` (**the base change at an inner base `α` with parameters in `Tᵗ[σ]`**: for `α ∈ Tᵗ[σ] ∩ E ∩ (τ, Ω₁)`
  and a countable-argument term `t` over `α` whose leaves lie in `Tᵗ[σ]` (they may lie in `[σ, α)`):
  `π_{σ,τ}(t[α; p]) = t[π α; π p]`);
* `ubLe` (**every leaf is `≤` the value**).

New definitions: `UbT`, `ev`, `map`, `Lv`, `IsA`, `BelowE`, `WF`, `trA`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ub

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- Terms over a base: parameters, `+`, `ϑᵗ(0)`, `ϑᵗ(1 + ξ)`, `ϑᵗ(ξ)`, `ϑ₁(ξ) = Ω₁·ω^ξ`. -/
inductive UbT : Type 1
  | par : Ordinal.{0} → UbT
  | add : UbT → UbT → UbT
  | base : UbT
  | th1 : UbT → UbT
  | th : UbT → UbT
  | om : UbT → UbT

namespace UbT

instance : Inhabited UbT := ⟨UbT.base⟩

/-- Evaluation over the base `τ` (`base` is `ϑᵗ(0) = τ`). -/
noncomputable def ev (τ : Ordinal.{0}) : UbT → Ordinal.{0}
  | par p => p
  | add s t => ev τ s + ev τ t
  | base => τ
  | th1 s => vt τ (1 + ev τ s)
  | th s => vt τ (ev τ s)
  | om s => Om1 * ω ^ ev τ s

/-- Apply `f` to every leaf. -/
def map (f : Ordinal.{0} → Ordinal.{0}) : UbT → UbT
  | par p => par (f p)
  | add s t => add (map f s) (map f t)
  | base => base
  | th1 s => th1 (map f s)
  | th s => th (map f s)
  | om s => om (map f s)

/-- Every leaf satisfies `P`. -/
def Lv (P : Ordinal.{0} → Prop) : UbT → Prop
  | par p => P p
  | add s t => Lv P s ∧ Lv P t
  | base => True
  | th1 s => Lv P s
  | th s => Lv P s
  | om s => Lv P s

/-- Countable-argument terms: only parameters, `+`, `ϑᵗ(0)` and `ϑᵗ(1 + ξ)`. -/
def IsA : UbT → Prop
  | par _ => True
  | add s t => IsA s ∧ IsA t
  | base => True
  | th1 s => IsA s
  | th _ => False
  | om _ => False

/-- `x` lies below every `ε`-number above `Ω₁` (`x < ε_{Ω₁+1}`). -/
def BelowE (x : Ordinal.{0}) : Prop := ∀ e : Ordinal.{0}, InE e → Om1 < e → x < e

/-- The argument bounds over the base `τ` ([W07a] Def 3.22: `ϑ_k` applied to arguments below `Ω_{k+2}`). -/
def WF (τ : Ordinal.{0}) : UbT → Prop
  | par _ => True
  | add s t => WF τ s ∧ WF τ t
  | base => True
  | th1 s => WF τ s ∧ ev τ s < Om1
  | th s => WF τ s ∧ ev τ s < OmTwo
  | om s => WF τ s ∧ BelowE (ev τ s)

/-- The translation `t^a_b` of [W07a] Def 6.2 on countable-argument terms: `ϑ^a(0) ↦ a`,
`ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)` (the case `Γ = 0`; the parameter `a` is the term `ϑ^b(Δ + η)`). -/
def trA (a : Ordinal.{0}) : UbT → UbT
  | par p => par p
  | add s t => add (trA a s) (trA a t)
  | base => par a
  | th1 s => th1 (add (par a) (trA a s))
  | th s => th (trA a s)
  | om s => om (trA a s)

theorem Lv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) : ∀ t : UbT, Lv P t → Lv Q t
  | par p, h => hPQ p h
  | add s t, h => ⟨Lv_mono hPQ s h.1, Lv_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_mono hPQ s h
  | th s, h => Lv_mono hPQ s h
  | om s, h => Lv_mono hPQ s h

/-- The set of leaves. -/
noncomputable def lvs : UbT → Finset Ordinal.{0}
  | par p => {p}
  | add s t => lvs s ∪ lvs t
  | base => ∅
  | th1 s => lvs s
  | th s => lvs s
  | om s => lvs s

theorem Lv_lvs : ∀ t : UbT, Lv (· ∈ lvs t) t
  | par _ => Finset.mem_singleton_self _
  | add s t => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) s (Lv_lvs s),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) t (Lv_lvs t)⟩
  | base => trivial
  | th1 s => Lv_lvs s
  | th s => Lv_lvs s
  | om s => Lv_lvs s

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {t : UbT}, Lv P t → ∀ p ∈ lvs t, P p
  | par _, h, p, hp => by rw [lvs, Finset.mem_singleton] at hp; rw [hp]; exact h
  | add s t, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := s) h.1 p hp
    · exact mem_lvs (t := t) h.2 p hp
  | base, _, p, hp => absurd hp (Finset.notMem_empty p)
  | th1 s, h, p, hp => mem_lvs (t := s) h p hp
  | th s, h, p, hp => mem_lvs (t := s) h p hp
  | om s, h, p, hp => mem_lvs (t := s) h p hp

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ t : UbT, (t.map g).map f = t.map (f ∘ g)
  | par _ => rfl
  | add s t => by simp only [map, map_map f g s, map_map f g t]
  | base => rfl
  | th1 s => by simp only [map, map_map f g s]
  | th s => by simp only [map, map_map f g s]
  | om s => by simp only [map, map_map f g s]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} : ∀ t : UbT, Lv (fun p => f p = g p) t → t.map f = t.map g
  | par _, h => by simp only [map]; rw [show _ = _ from h]
  | add s t, h => by simp only [map, map_congr s h.1, map_congr t h.2]
  | base, _ => rfl
  | th1 s, h => by simp only [map, map_congr s h]
  | th s, h => by simp only [map, map_congr s h]
  | om s, h => by simp only [map, map_congr s h]

theorem map_id : ∀ t : UbT, t.map id = t
  | par _ => rfl
  | add s t => by simp only [map, map_id s, map_id t]
  | base => rfl
  | th1 s => by simp only [map, map_id s]
  | th s => by simp only [map, map_id s]
  | om s => by simp only [map, map_id s]

theorem Lv_and {P Q : Ordinal.{0} → Prop} : ∀ (t : UbT), Lv P t → Lv Q t → Lv (fun p => P p ∧ Q p) t
  | par _, h1, h2 => ⟨h1, h2⟩
  | add s t, h1, h2 => ⟨Lv_and s h1.1 h2.1, Lv_and t h1.2 h2.2⟩
  | base, _, _ => trivial
  | th1 s, h1, h2 => Lv_and s h1 h2
  | th s, h1, h2 => Lv_and s h1 h2
  | om s, h1, h2 => Lv_and s h1 h2

theorem Lv_map {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ t : UbT, Lv (fun p => P (f p)) t → Lv P (t.map f)
  | par _, h => h
  | add s t, h => ⟨Lv_map s h.1, Lv_map t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_map s h
  | th s, h => Lv_map s h
  | om s, h => Lv_map s h

theorem IsA_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UbT, IsA t → IsA (t.map f)
  | par _, _ => trivial
  | add s t, h => ⟨IsA_map f s h.1, IsA_map f t h.2⟩
  | base, _ => trivial
  | th1 s, h => IsA_map f s h
  | th _, h => h.elim
  | om _, h => h.elim

theorem trA_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ t : UbT, (trA a t).map f = trA (f a) (t.map f)
  | par _ => rfl
  | add s t => by simp only [trA, map, trA_map a f s, trA_map a f t]
  | base => rfl
  | th1 s => by simp only [trA, map, trA_map a f s]
  | th s => by simp only [trA, map, trA_map a f s]
  | om s => by simp only [trA, map, trA_map a f s]

theorem IsA_trA (a : Ordinal.{0}) : ∀ t : UbT, IsA t → IsA (trA a t)
  | par _, _ => trivial
  | add s t, h => ⟨IsA_trA a s h.1, IsA_trA a t h.2⟩
  | base, _ => trivial
  | th1 s, h => ⟨trivial, IsA_trA a s h⟩
  | th _, h => h.elim
  | om _, h => h.elim

theorem Lv_trA {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) : ∀ t : UbT, Lv P t → Lv P (trA a t)
  | par _, h => h
  | add s t, h => ⟨Lv_trA ha s h.1, Lv_trA ha t h.2⟩
  | base, _ => ha
  | th1 s, h => ⟨ha, Lv_trA ha s h⟩
  | th s, h => Lv_trA ha s h
  | om s, h => Lv_trA ha s h

end UbT

open UbT

theorem ub_one_lt {e : Ordinal.{0}} (he : InE e) : (1 : Ordinal.{0}) < e := by
  have h1 : ω ≤ ω ^ e := left_le_opow ω (InE.pos he)
  have h2 : ω ^ e = e := he
  exact one_lt_omega0.trans_le (h2 ▸ h1)

theorem ub_TB_mono {τ κ c : Ordinal.{0}} (hκc : κ ≤ c) {x : Ordinal.{0}} (hx : x ∈ TB τ κ) : x ∈ TB τ c :=
  ⟨hx.1, fun _ hp => lt_of_lt_of_le (hx.2 hp) hκc⟩

/-- **The base change with a general parameter map** ([W07a] Def 5.1, Lemma 5.3 (c), Def 3.22, Def 3.28 through
`pi_lt`, `pi_base`, `pi_add`, `pi_vt`, `pi_vt_two`, `om1_opow_TB_all`, `vt_mem`, `vt_memTwo`): for a term `t` with
the argument bounds over `τ` and every leaf in `Tᵗ[σ]`, `ev τ t ∈ Tᵗ[σ]` and `π_{σ,τ}(t[τ; p]) = t[σ; π p]`; for a
countable-argument term the image has the argument bounds over `σ`. -/
theorem ubDown {σ τ : Ordinal.{0}} (h : Bases σ τ) : ∀ t : UbT, WF τ t → Lv (· ∈ TB τ σ) t →
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ (IsA t → WF σ (t.map (pi σ τ)))
  | .par p, _, hp => ⟨hp, rfl, fun _ => trivial⟩
  | .add s t, hw, hl => by
    obtain ⟨a1, a2, a3⟩ := ubDown h s hw.1 hl.1
    obtain ⟨b1, b2, b3⟩ := ubDown h t hw.2 hl.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, fun hA => ⟨a3 hA.1, b3 hA.2⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | .base, _, _ => ⟨(pi_base h).1, (pi_base h).2, fun _ => trivial⟩
  | .th1 s, hw, hl => by
    obtain ⟨a1, a2, a3⟩ := ubDown h s hw.1 hl
    have hσ1 : (1 : Ordinal.{0}) < σ := ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_,
      fun hA => ⟨a3 hA, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | .th s, hw, hl => by
    obtain ⟨a1, a2, -⟩ := ubDown h s hw.1 hl
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 a1.1 hw.2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact a1.2⟩, ?_,
      fun hA => hA.elim⟩
    simp only [ev, map]; rw [pi_vt_two h a1 hw.2, a2]
  | .om s, hw, hl => by
    obtain ⟨a1, a2, -⟩ := ubDown h s hw.1 hl
    obtain ⟨d1, d2⟩ := om1_opow_TB_all h hw.2
    refine ⟨d1.2 a1, ?_, fun hA => hA.elim⟩
    simp only [ev, map]; rw [d2 a1, a2]

/-- **Membership**: a term with the argument bounds over `τ` and leaves below `σ` (bases `σ < τ`) denotes an
element of `Tᵗ[σ]`; its value and `ht`, `Par` agree with those of the term over `σ`. -/
theorem ubHtPar {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UbT) (hw : WF τ t) (hl : Lv (· ∈ TB τ σ) t) :
    ev τ t ∈ Tset τ ∧ ht σ (ev σ (t.map (pi σ τ))) = ht τ (ev τ t) ∧
      Par σ (ev σ (t.map (pi σ τ))) = Par τ (ev τ t) := by
  obtain ⟨a1, a2, -⟩ := ubDown h t hw hl
  rw [← a2]
  exact ⟨a1.1, (pi_ht_Par h a1).1, (pi_ht_Par h a1).2⟩

/-- Leaves below `σ` are leaves in `Tᵗ[σ]`, and `π_{σ,τ}` fixes them: `π_{σ,τ}(t[τ]) = t[σ]`. -/
theorem ubDown_lt {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UbT) (hw : WF τ t) (hl : Lv (· < σ) t) :
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ t := by
  have hl' : Lv (· ∈ TB τ σ) t := Lv_mono (fun p hp => (TB_inter_lt h (hp.trans h.2.2.1)).2 hp) t hl
  obtain ⟨a1, a2, -⟩ := ubDown h t hw hl'
  refine ⟨a1, ?_⟩
  rw [a2, map_congr t (Lv_mono (fun p hp => pi_lt h hp) t hl)]
  exact congrArg _ (map_id t)

/-- **The inverse base change on countable-argument terms**: leaves in `T^σ` ⇒ the term over `τ` with leaves
`π_{σ,τ}⁻¹ p` lies in `Tᵗ[σ]`, has the argument bounds, and is sent by `π_{σ,τ}` to `t[σ; p]`. -/
theorem ubUp {σ τ : Ordinal.{0}} (h : Bases σ τ) : ∀ t : UbT, IsA t → WF σ t → Lv (· ∈ Tset σ) t →
    ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ))
  | .par p, _, _, hp => ⟨(up_spec h hp).1, (up_spec h hp).2, trivial⟩
  | .add s t, hA, hw, hl => by
    obtain ⟨a1, a2, a3⟩ := ubUp h s hA.1 hw.1 hl.1
    obtain ⟨b1, b2, b3⟩ := ubUp h t hA.2 hw.2 hl.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hA, hw, hl => by
    obtain ⟨a1, a2, a3⟩ := ubUp h s hA hw.1 hl
    have hσ1 : (1 : Ordinal.{0}) < σ := ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    -- the argument stays countable
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
  | .th _, hA, _, _ => hA.elim
  | .om _, hA, _, _ => hA.elim

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]` on countable-argument terms. -/
theorem ubUp_eq {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UbT) (hA : IsA t) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) : up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := ubUp h t hA hw hl
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on countable-argument terms**: for `ε`-numbers `b, c < Ω₁` and leaves in `Tᵇ[κ]`
(`κ ≤ b, c`), `mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem ubMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UbT) (hA : IsA t) (hw : WF b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WF c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := ubDown hB t hw (Lv_mono (fun p hp => ub_TB_mono hκc hp) t hl)
    rw [hmv]; exact ⟨a2, a3 hA⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact ubUp_eq hB t hA hw (Lv_mono (fun p hp => hp.1) t hl)

/-- **The translation `t^a_b` denotes the same ordinal** ([W07a] Def 6.2 case `Γ = 0` and Lemma 6.3, proved from
[W07a] Lemma 4.2, `vt_wbar`: `ϑ^a(1 + ξ) = ω̄_{a+ξ} = ϑ^b(1 + (a + ξ))` as `b + a = a`): for `ε`-numbers
`b < a < Ω₁` and a countable-argument term `t`, `t` has the argument bounds over `a` iff `trA a t` has them over
`b`, and then `ev b (trA a t) = ev a t`. -/
theorem ubTr {a b : Ordinal.{0}} (ha : InE a) (ha1 : a < Om1) (hb : InE b) (hba : b < a) :
    ∀ t : UbT, IsA t → (WF a t ↔ WF b (trA a t)) ∧ (WF a t → ev b (trA a t) = ev a t)
  | .par _, _ => ⟨Iff.rfl, fun _ => rfl⟩
  | .add s t, hA => by
    obtain ⟨a1, a2⟩ := ubTr ha ha1 hb hba s hA.1
    obtain ⟨b1, b2⟩ := ubTr ha ha1 hb hba t hA.2
    refine ⟨⟨fun h => ⟨a1.1 h.1, b1.1 h.2⟩, fun h => ⟨a1.2 h.1, b1.2 h.2⟩⟩, fun h => ?_⟩
    simp only [trA, ev]; rw [a2 h.1, b2 h.2]
  | .base, _ => ⟨⟨fun _ => trivial, fun _ => trivial⟩, fun _ => rfl⟩
  | .th1 s, hA => by
    obtain ⟨a1, a2⟩ := ubTr ha ha1 hb hba s hA
    have hb1 : b < Om1 := hba.trans ha1
    have hab : b + a = a := add_of_omega0_opow_le (show b < ω ^ a by rw [ha]; exact hba) (le_of_eq ha)
    refine ⟨⟨fun h => ⟨⟨trivial, a1.1 h.1⟩, ?_⟩, fun h => ?_⟩, fun h => ?_⟩
    · simp only [ev]; rw [a2 h.1]; exact Om1_add_lt ha1 h.2
    · have hw : WF a s := a1.2 h.1.2
      refine ⟨hw, ?_⟩
      have h2 := h.2
      simp only [ev] at h2; rw [a2 hw] at h2
      exact lt_of_le_of_lt le_add_self h2
    · simp only [trA, ev]
      rw [a2 h.1, vt_wbar hb hb1 (Om1_add_lt ha1 h.2), vt_wbar ha ha1 h.2, ← add_assoc, hab]
  | .th _, hA => hA.elim
  | .om _, hA => hA.elim

/-- **Every leaf is at most the value** (countable-argument terms with the argument bounds over a base). -/
theorem ubLe {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : ∀ t : UbT, IsA t → WF τ t → Lv (· ≤ ev τ t) t
  | .par _, _, _ => le_refl _
  | .add s t, hA, hw => by
    refine ⟨Lv_mono (fun p hp => ?_) s (ubLe hτ hτ1 s hA.1 hw.1),
      Lv_mono (fun p hp => ?_) t (ubLe hτ hτ1 t hA.2 hw.2)⟩
    · exact hp.trans (show ev τ s ≤ ev τ (.add s t) from le_self_add)
    · exact hp.trans (show ev τ t ≤ ev τ (.add s t) from le_add_self)
  | .base, _, _ => trivial
  | .th1 s, hA, hw => by
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hτ hτ1 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact Lv_mono (fun p hp => hp.trans hle) s (ubLe hτ hτ1 s hA hw.1)
  | .th _, hA, _ => hA.elim
  | .om _, hA, _ => hA.elim

/-- **The base change at an inner base with parameters in `Tᵗ[σ]`**: for bases `σ < τ`, an `ε`-number
`α ∈ Tᵗ[σ] ∩ (τ, Ω₁)` and a countable-argument term `t` with the argument bounds over `α` whose leaves lie in
`Tᵗ[σ]` (leaves in `[σ, α)` allowed): `t[α; p] ∈ Tᵗ[σ]`, `π_{σ,τ}(t[α; p]) = t[π α; π p]`, and the image has the
argument bounds over `π α`.  (Via `t^α_τ` over `τ` (`ubTr`), `ubDown`, and `t^{π α}_σ` over `σ` (`ubTr`).) -/
theorem ubSegPi {σ τ α : Ordinal.{0}} (h : Bases σ τ) (hα : α ∈ TB τ σ) (hαE : InE α) (hτα : τ < α)
    (hα1 : α < Om1) (t : UbT) (hA : IsA t) (hw : WF α t) (hl : Lv (· ∈ TB τ σ) t) :
    ev α t ∈ TB τ σ ∧ pi σ τ (ev α t) = ev (pi σ τ α) (t.map (pi σ τ)) ∧
      WF (pi σ τ α) (t.map (pi σ τ)) := by
  obtain ⟨t1, t2⟩ := ubTr hαE hα1 h.2.1 hτα t hA
  have hwτ : WF τ (trA α t) := t1.1 hw
  have hev : ev τ (trA α t) = ev α t := t2 hw
  obtain ⟨d1, d2, d3⟩ := ubDown h (trA α t) hwτ (Lv_trA hα t hl)
  rw [trA_map] at d2 d3
  have hpE : InE (pi σ τ α) := (down_E h hα hτα hα1).1 hαE
  have hp1 : pi σ τ α < Om1 := down_lt_Om1 h hα hα1
  have hσp : σ < pi σ τ α := down_gt h hα hτα
  obtain ⟨s1, s2⟩ := ubTr hpE hp1 h.1 hσp (t.map (pi σ τ)) (IsA_map _ t hA)
  have hwσ : WF σ (trA (pi σ τ α) (t.map (pi σ τ))) := d3 (IsA_trA _ t hA)
  have hwp : WF (pi σ τ α) (t.map (pi σ τ)) := s1.2 hwσ
  refine ⟨hev ▸ d1, ?_, hwp⟩
  rw [← hev, d2, s2 hwp]

end Googology.Trans.PoR.InaccPsi.R2.Ub
