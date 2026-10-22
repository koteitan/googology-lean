import Googology.Trans.PoR.InaccPsi.R2.GcLoc
import Googology.Trans.PoR.InaccPsi.R2.GcLim

/-!
# THE TRANSFINITE TOWER: one base for every constant offset, `Γ_{x+1+1+α}` for every `α` with `1 + α < ε₀`

By transfinite recursion on `α` (`Ordinal.limitRecOn`):

* `gcB 0 = lpTB 1` (top `ϑˣ(Ω₁·Ω₁ + 1)`), `gcB (α+1) = gqLimB (gcB α) (1 + α + 1)` (`R2.GbLim`, the ladder over the
  base and its limit), `gcB λ = gcLimB λ` (`R2.GcLim`, the union of the `gcB β`, `β < λ`, with THE GENERIC LIMIT
  WITNESS); `gcB_E` (**the top of `gcB α` is `ϑˣ(Ω₁·Ω₁ + 1 + α)`** whenever `1 + α < ε₀`), `gcB_succ`, `gcB_lim`;
* `gcB_lift` (**every term of `gcB γ` is a term of `gcB β` for `γ ≤ β`**), `gcB_topIn` (**the top of `gcB γ` is a term
  of `gcB β` for `γ < β`**), `gcB1_lt` (**`α ↦ Λ⁺(gcB α)` is strictly increasing**), `gcB_eq` (**`O_{gcB β} = O_{gcB γ}`
  below `Λ⁺(gcB γ)`**);
* `gcB_codes` (**THE UNIFORMITY THEOREM**: `E_{gcB α}(y) = Θ_y(gcG (1 + α))` at every strongly critical `y < Ω₁`, and
  `GcPoly (gcB α) (gcG (1 + α))`, for every `α` with `1 + α < ε₀`), `gcB_eN`.

No new axiom.  New definitions: `GcSt`, `gcSt0`, `gcStSucc`, `gcStLim`, `gcRec`, `gcB`, `gcH_succ`, `gcF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx

/-! ## The recursion -/

/-- The value of the recursion at `α`: a base package with top `ϑˣ(Ω₁·Ω₁ + 1 + α)` whenever `1 + α < ε₀`. -/
def GcSt (α : Ordinal.{0}) : Type 2 :=
  {B : LpB // 1 + α < ε₀ → ∀ x, InE x → x < Om1 → B.K.E x = gq (1 + α) x}

theorem gc_one_add_succ (α : Ordinal.{0}) : 1 + (α + 1) = 1 + α + 1 := (add_assoc 1 α 1).symm

theorem gc_lt_of_succ {α : Ordinal.{0}} (h : 1 + (α + 1) < ε₀) : 1 + α < ε₀ :=
  (lt_add_one (1 + α)).trans (by rw [← gc_one_add_succ]; exact h)

/-- The start: `lpTB 1`, top `ϑˣ(Ω₁·Ω₁ + 1)`. -/
noncomputable def gcSt0 : GcSt 0 :=
  ⟨lpTB 1, fun _ x _ _ => by
    show gk (0 + 1) x = gq (1 + 0) x
    rw [add_zero, zero_add, ← gq_nat, Nat.cast_one]⟩

/-- **The limit hypothesis of the successor step**: `ϑˣ(Ω₁·Ω₁ + j) ≤ ϑˣ(Ω₁·Ω₁ + 1 + α) < ϑˣ(Ω₁·Ω₁ + 1 + α + 1)` for
`j ≤ 1 + α`. -/
theorem gcH_succ {α : Ordinal.{0}} (s : GcSt α) (h : 1 + (α + 1) < ε₀) : GqLimH s.1 (1 + α + 1) := by
  have hc : 1 + α + 1 < ε₀ := by rw [← gc_one_add_succ]; exact h
  have hs := s.2 (gc_lt_of_succ h)
  refine ⟨gc_cst hc, fun x hx hx1 j hj => ?_, fun x hx hx1 => ?_⟩
  · rw [hs x hx hx1]
    exact gq_mono hx hx1 ((lt_add_one _).trans (gc_cst hc x hx)) (Order.lt_add_one_iff.1 hj)
  · rw [hs x hx hx1]
    exact gq_lt hx hx1 (gc_cst hc x hx) (lt_add_one _)

/-- The successor step: the limit of the ladder over the base. -/
noncomputable def gcStSucc (α : Ordinal.{0}) (s : GcSt α) : GcSt (α + 1) :=
  if h : 1 + (α + 1) < ε₀ then
    ⟨gqLimB s.1 (1 + α + 1) (gcH_succ s h), fun _ x _ _ => by
      show gq (1 + α + 1) x = gq (1 + (α + 1)) x
      rw [gc_one_add_succ]⟩
  else ⟨s.1, fun h' => absurd h' h⟩

theorem gc_omega_le {α : Ordinal.{0}} (hα : IsSuccLimit α) : ω ≤ α := omega0_le_of_isSuccLimit hα

theorem gc_one_add_lim {α : Ordinal.{0}} (hα : IsSuccLimit α) : 1 + α = α := one_add_of_omega0_le (gc_omega_le hα)

theorem gc_limH {α : Ordinal.{0}} (hα : IsSuccLimit α) (h : 1 + α < ε₀) : GcLimH α :=
  ⟨hα, gc_cst (by rw [gc_one_add_lim hα] at h; exact h)⟩

/-- The family of the earlier bases at a limit. -/
noncomputable def gcF {α : Ordinal.{0}} (h : 1 + α < ε₀) (IH : ∀ β < α, GcSt β) : GcLimF α where
  K := fun β => (IH β.1 β.2).1.K
  E_eq := fun β x hx hx1 => (IH β.1 β.2).2 ((add_lt_add_iff_left 1).2 β.2 |>.trans h) x hx hx1

/-- The limit step: the union with the generic limit witness. -/
noncomputable def gcStLim (α : Ordinal.{0}) (hα : IsSuccLimit α) (IH : ∀ β < α, GcSt β) : GcSt α :=
  if h : 1 + α < ε₀ then
    ⟨gcLimB α (gc_limH hα h) (gcF h IH), fun _ x _ _ => by
      show gq α x = gq (1 + α) x
      rw [gc_one_add_lim hα]⟩
  else ⟨lpTB 1, fun h' => absurd h' h⟩

/-- **The recursion.** -/
noncomputable def gcRec (α : Ordinal.{0}) : GcSt α := Ordinal.limitRecOn α gcSt0 gcStSucc gcStLim

/-- **The base of the tower at `α`**: top `ϑˣ(Ω₁·Ω₁ + 1 + α)` (`gcB_E`). -/
noncomputable def gcB (α : Ordinal.{0}) : LpB := (gcRec α).1

theorem gcB_E {α : Ordinal.{0}} (h : 1 + α < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gcB α).K.E x = gq (1 + α) x := (gcRec α).2 h x hx hx1

theorem gcB_zero : gcB 0 = lpTB 1 := by
  unfold gcB gcRec
  rw [Ordinal.limitRecOn_zero]; rfl

theorem gcRec_succ (α : Ordinal.{0}) : gcRec (α + 1) = gcStSucc α (gcRec α) := by
  unfold gcRec
  rw [Ordinal.limitRecOn_add_one]

theorem gcB_succ {α : Ordinal.{0}} (h : 1 + (α + 1) < ε₀) :
    gcB (α + 1) = gqLimB (gcB α) (1 + α + 1) (gcH_succ (gcRec α) h) := by
  show (gcRec (α + 1)).1 = _
  rw [gcRec_succ]
  show (gcStSucc α (gcRec α)).1 = _
  unfold gcStSucc
  rw [dif_pos h]
  rfl

theorem gcRec_lim {α : Ordinal.{0}} (hα : IsSuccLimit α) :
    gcRec α = gcStLim α hα (fun β _ => gcRec β) := by
  unfold gcRec
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

theorem gcB_lim {α : Ordinal.{0}} (hα : IsSuccLimit α) (h : 1 + α < ε₀) :
    gcB α = gcLimB α (gc_limH hα h) (gcF h fun β _ => gcRec β) := by
  show (gcRec α).1 = _
  rw [gcRec_lim hα]
  show (gcStLim α hα (fun β _ => gcRec β)).1 = _
  unfold gcStLim
  rw [dif_pos h]

theorem gcF_K {α : Ordinal.{0}} (h : 1 + α < ε₀) (β : Iio α) :
    (gcF h fun β _ => gcRec β).K β = (gcB β.1).K := rfl

/-! ## Comparison of the bases -/

/-- **Every term of `gcB γ` is a term of `gcB β` for `γ ≤ β`** (`1 + β < ε₀`). -/
theorem gcB_lift : ∀ β : Ordinal.{0}, 1 + β < ε₀ → ∀ γ, γ ≤ β → GcLift (gcB β).K.sys (gcB γ).K.sys := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro h γ hγ
  rcases hγ.lt_or_eq with hγ | rfl
  · rcases zero_or_succ_or_isSuccLimit β with rfl | ⟨δ, rfl⟩ | hα
    · exact absurd hγ (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at h hγ IH ⊢
      rw [gcB_succ h]
      exact gcLift_trans (gc_lift_gq (gcB δ) (1 + δ + 1) (gcH_succ (gcRec δ) h))
        (IH δ (lt_add_one δ) (gc_lt_of_succ h) γ (Order.lt_add_one_iff.1 hγ))
    · rw [gcB_lim hα h]
      exact gcLim_lift (gc_limH hα h) _ ⟨γ, hγ⟩
  · exact gcLift_refl _

theorem gcB_top {α : Ordinal.{0}} (h : 1 + α < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gcB α).K.sys.top x = gq (1 + α) x := by
  rw [(gcB α).K.top_eq x hx hx1, gcB_E h hx hx1]
  exact (gq_facts hx hx1 (gc_cst h x hx)).2.2.2.1

/-- **The top of `gcB γ` is a term of `gcB β`** for `γ < β` (`1 + β < ε₀`), with gap `> 1`. -/
theorem gcB_topIn {β γ : Ordinal.{0}} (h : 1 + β < ε₀) (hγβ : γ < β) :
    LyTopIn (gcB β).K.sys (gcB γ).K.sys := by
  have hγ1 : 1 + (γ + 1) < ε₀ := (add_le_add_iff_left 1).2 (Order.add_one_le_of_lt hγβ) |>.trans_lt h
  have hT := gqLim_topIn_K (gcH_succ (gcRec γ) hγ1)
  obtain ⟨t, ht, -⟩ := hT
  have hL := gcB_lift β h (γ + 1) (Order.add_one_le_of_lt hγβ)
  rw [gcB_succ hγ1] at hL
  refine gc_topIn_of_lift hL ht fun r hr hr1 => ?_
  have hρE := ups_inE hr
  have hρ1 := ups_lt_Om1 r hr1
  have hγε : 1 + γ < ε₀ := ((add_lt_add_iff_left 1).2 hγβ).trans h
  rw [gcB_top hγε hρE hρ1, gcB_top h hρE hρ1]
  have hE := (gq_facts hρE hρ1 (gc_cst h _ hρE)).2.2.2.1
  exact (inE_indec hE).add_lt (gq_lt hρE hρ1 (gc_cst h _ hρE) ((add_lt_add_iff_left 1).2 hγβ))
    (Lu.lu_one_lt_E hE)

/-- **`α ↦ Λ⁺(gcB α)` is strictly increasing** below `ε₀`. -/
theorem gcB1_lt {β γ : Ordinal.{0}} (h : 1 + β < ε₀) (hγβ : γ < β) :
    xtB1 (gcB γ).K.sys < xtB1 (gcB β).K.sys :=
  lyB1_lt (XtLay.topPkg (gcB β).K) (XtLay.topPkg (gcB γ).K) (gcB_topIn h hγβ)

/-- **`O_{gcB β} = O_{gcB γ}` below `Λ⁺(gcB γ)`** for `γ ≤ β`. -/
theorem gcB_eq {β γ : Ordinal.{0}} (h : 1 + β < ε₀) (hγβ : γ ≤ β) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (hμγ : μ < xtB1 (gcB γ).K.sys) : xtOrec (gcB β).K.sys μ = xtOrec (gcB γ).K.sys μ := by
  rcases hγβ.lt_or_eq with hlt | rfl
  · exact lyEq (XtLay.topPkg (gcB γ).K) (gcB_topIn h hlt) hμ hμγ
  · rfl

/-! ## THE UNIFORMITY THEOREM: the tops read the atoms, and every code below has a term -/

theorem gc_one_add_le_eps {α : Ordinal.{0}} (h : 1 + α < ε₀) : gcG (1 + α) ≤ gcV := gcG_le h.le

/-- **THE UNIFORMITY THEOREM**: for every `α` with `1 + α < ε₀`, the top of `gcB α` reads the atom `gcG (1 + α) =
Γ_{Ω₁+2+α}` at every strongly critical `y < Ω₁`, and `gcB α` has terms for every code below it. -/
theorem gcB_codes (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, 1 + α < ε₀ →
    (∀ y, SC y → y < Om 1 → (gcB α).K.E y = gxTh y gcAt (gcG (1 + α))) ∧ GcPoly (gcB α).K.sys (gcG (1 + α)) := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH0 =>
  rcases zero_or_succ_or_isSuccLimit α with rfl | ⟨δ, rfl⟩ | hα
  · intro _
    have e1 : gcG (1 + 0) = gaG 1 := by rw [add_zero, ← gcG_nat S 1, Nat.cast_one]
    rw [gcB_zero, e1]
    have hle : gaG 1 ≤ gaW := (gaG_lt_W S 1).le
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · show (lpTK 0).E y = _
      rw [(gaTow S 0).1 y hy hy1, gcTh_eq_gaTh S hle]
    · exact gcPoly_of_ga S hle (gaTow S 0).2
  · rw [succ_eq_add_one]
    intro h
    have IH := IH0 δ (by rw [succ_eq_add_one]; exact lt_add_one δ)
    obtain ⟨ihE, ihP⟩ := IH (gc_lt_of_succ h)
    have hδ : 1 + δ < ε₀ := gc_lt_of_succ h
    have hc : ∀ Z, SC Z → GxCl Z gcAt (gcG (1 + δ)) := fun _ _ => GxCl.atom (gcG_atom hδ)
    have hcO : Om 1 ≤ gcG (1 + δ) := (gcG_Om1_lt _).le
    have hQ : cQs (gcG (1 + δ)) = gcG (1 + (δ + 1)) := by rw [gc_cQs, gc_one_add_succ]
    rw [gcB_succ h]
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have e := gcLim_top S hc ihE (gcH_succ (gcRec δ) h) hy hy1
      rw [hQ] at e
      exact e
    · have e := gcLim_poly S hc hcO ihE ihP (gcH_succ (gcRec δ) h)
      rw [hQ] at e
      exact e
  · have IH : ∀ β < α, 1 + β < ε₀ → (∀ y, SC y → y < Om 1 → (gcB β).K.E y = gxTh y gcAt (gcG (1 + β))) ∧
        GcPoly (gcB β).K.sys (gcG (1 + β)) := IH0
    intro h
    have hα' : 1 + α = α := gc_one_add_lim hα
    have hβε : ∀ β < α, 1 + β < ε₀ := fun β hβ => ((add_lt_add_iff_left 1).2 hβ).trans h
    rw [hα']
    refine ⟨fun y hy hy1 => ?_, ?_⟩
    · have hyE := gg_SC_eps hy
      have hy1' := lp_y1 hy1
      have hαy : α < y := gc_cst (by rw [hα'] at h; exact h) y hyE
      rw [gcB_lim hα h, gcLimB_E]
      refine le_antisymm (le_of_forall_lt fun v hv => ?_) ?_
      · obtain ⟨ν, hν, hvν⟩ := gc_lt_lim_iff hyE hy1' hα hαy v hv
        have h1 : gq ν y ≤ gq (1 + ν) y := gq_mono hyE hy1' ((gc_one_add_lt hα hν).trans hαy) le_add_self
        have h2 : gq (1 + ν) y = gxTh y gcAt (gcG (1 + ν)) := by
          rw [← gcB_E (hβε ν hν) hyE hy1']; exact (IH ν hν (hβε ν hν)).1 y hy hy1
        calc v < gq ν y := hvν
          _ ≤ gq (1 + ν) y := h1
          _ = gxTh y gcAt (gcG (1 + ν)) := h2
          _ ≤ gxTh y gcAt (gcG α) := gxTh_mono (gcG_le (gc_one_add_lt hα hν).le)
      · rw [gcTh_limit hα]
        refine ciSup_le' fun β => ?_
        have h2 : gxTh y gcAt (gcG (1 + β.1)) = gq (1 + β.1) y := by
          rw [← (IH β.1 β.2 (hβε β.1 β.2)).1 y hy hy1, gcB_E (hβε β.1 β.2) hyE hy1']
        calc gxTh y gcAt (gcG β.1) ≤ gxTh y gcAt (gcG (1 + β.1)) := gxTh_mono (gcG_le le_add_self)
          _ = gq (1 + β.1) y := h2
          _ ≤ gq α y := gq_mono hyE hy1' hαy (gc_one_add_lt hα β.2).le
    · intro Z c hc hcE
      obtain ⟨β, hβ, hcβ⟩ := gcG_lt_of_lt_limit hα hcE
      obtain ⟨s, hs⟩ := (IH β hβ (hβε β hβ)).2 Z c hc (hcβ.trans_le (gcG_le le_add_self))
      obtain ⟨t, ht⟩ := gcB_lift α h β hβ.le s
      exact ⟨t, fun y hy hy1 hZy => ⟨(ht y).1 (hs y hy hy1 hZy).1, (ht y).2.trans (hs y hy hy1 hZy).2⟩⟩

/-- **`ε_{x+1} < E_{gcB α}(x)`.** -/
theorem gcB_eN {α : Ordinal.{0}} (h : 1 + α < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    eN x < (gcB α).K.E x := by
  rw [gcB_E h hx hx1]
  have h1 : gk 1 x = gq 1 x := by rw [← gq_nat, Nat.cast_one]
  refine (ga_eN_lt_gk 1 hx hx1).trans_le ?_
  rw [h1]
  exact gq_mono hx hx1 (gc_cst h x hx) le_self_add

end Googology.Trans.PoR.InaccPsi.R2.Gc
