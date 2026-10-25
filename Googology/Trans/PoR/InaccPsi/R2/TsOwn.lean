import Googology.Trans.PoR.InaccPsi.R2.TsFn

/-!
# Own arguments of `ψ_{Ω₂}`: normalization and own points below a collapse

`ψ_κ(a) = S.psi a κ`; an argument `e` is *own* (for `κ`) when `e ∈ Cl(e, ψ_κ(e))`.  Below `Ω₁` every strongly
critical point below a collapse is the value of an own argument read off its `InaccPsi` normal form
(`Rb.rb_own_of_SC`); between `Ω₁` and `Ω₂` most points are not values of the notation (every countable ordinal is a
small member of the hulls), so the normal-form route is replaced by two hull arguments:

* `ts_CSet_sub` (**`Cl(e', b) ⊆ Cl(e, b)` for `e ≤ e'` when no member of `Cl(e, b)` lies in `[e, e')`**);
* `ts_norm` (**normalization**: if some member of `Cl(e, ψ_κ(e))` is `≥ e`, the least one `e'` is own and
  `ψ_κ(e') = ψ_κ(e)`), `ts_norm_of_lt` (such a member exists once `ψ_κ(e) < ψ_κ(a)` for some `a`);
* `ts_hull_coll` (**a strongly critical `y` with `Ω₁ < y < ψ_{Ω₂}(B)` is reached by a collapse**: some `e < B` in
  `Cl(B, y)` has `y ≤ ψ_{Ω₂}(e)`);
* `ts_own_below` (**own points below a collapse**: for such `y` there is an own `e` with
  `y ≤ ψ_{Ω₂}(e) < ψ_{Ω₂}(B)`), `ts_own_below_lt` (and `e < B` when `B` is own).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **`Cl(e', b) ⊆ Cl(e, b)`** for `e ≤ e'` when every member `c ≥ e` of `Cl(e, b)` is `≥ e'`. -/
theorem ts_CSet_sub {e e' b : Ordinal.{0}} (hgap : ∀ c ∈ S.CSet e b, e ≤ c → e' ≤ c) :
    S.CSet e' b ⊆ S.CSet e b := by
  intro x hx
  induction hx with
  | small h => exact CSet.of_lt h
  | zero => exact CSet.zero_mem _ _
  | inacc n => exact CSet.I_mem _ _ n
  | inaccW => exact CSet.Iw_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | @coll π e0 hπ _ _ ihπ ihe =>
    have h : e0.1 < e := by
      by_contra hle
      exact absurd (hgap _ ihe (not_lt.1 hle)) (not_le.2 e0.2)
    exact CSet.psi_mem h hπ ihπ ihe

/-- **Normalization**: if some member of `Cl(e, ψ_κ(e))` is `≥ e`, the least such member `e'` is own,
`e' ∈ Cl(e, ψ_κ(e))` and `ψ_κ(e') = ψ_κ(e)`. -/
theorem ts_norm {κ e : Ordinal.{0}} (hκ : S.InR κ) (hex : ∃ c ∈ S.CSet e (S.psi e κ), e ≤ c) :
    ∃ e', e ≤ e' ∧ e' ∈ S.CSet e (S.psi e κ) ∧ e' ∈ S.CSet e' (S.psi e' κ) ∧ S.psi e' κ = S.psi e κ := by
  set p := S.psi e κ with hpdef
  set P : Set Ordinal.{0} := {c | c ∈ S.CSet e p ∧ e ≤ c} with hPdef
  have hne : P.Nonempty := by
    obtain ⟨c, h1, h2⟩ := hex
    exact ⟨c, h1, h2⟩
  set e' := sInf P with he'
  have hmem : e' ∈ P := csInf_mem hne
  have hmin : ∀ c ∈ S.CSet e p, e ≤ c → e' ≤ c := fun c h1 h2 => csInf_le' ⟨h1, h2⟩
  have hsub : S.CSet e' p ⊆ S.CSet e p := ts_CSet_sub hmin
  have heq : S.psi e' κ = p := by
    apply le_antisymm
    · exact psi_le_of_good (mem_CSet_psi_any hκ e' e) fun x hx hxκ => lt_psi_of_mem hκ (hsub hx) hxκ
    · exact (psi_mono hκ hmem.2).1
  refine ⟨e', hmem.2, hmem.1, ?_, heq⟩
  rw [heq]
  exact CSet_mono hmem.2 le_rfl hmem.1

/-- **A member `≥ e` of `Cl(e, ψ_κ(e))` exists** once `ψ_κ(e) < ψ_κ(a)` for some `a`. -/
theorem ts_norm_of_lt {κ e a : Ordinal.{0}} (hκ : S.InR κ) (hlt : S.psi e κ < S.psi a κ) :
    ∃ c ∈ S.CSet e (S.psi e κ), e ≤ c := by
  by_contra hno
  push Not at hno
  have hsub : S.CSet a (S.psi e κ) ⊆ S.CSet e (S.psi e κ) :=
    ts_CSet_sub fun c hc hec => absurd (hno c hc) (not_lt.2 hec)
  have hle : S.psi a κ ≤ S.psi e κ :=
    psi_le_of_good (mem_CSet_psi_any hκ a e) fun x hx hxκ => lt_psi_of_mem hκ (hsub hx) hxκ
  exact absurd hlt (not_lt.2 hle)

/-- **A strongly critical `y` with `Ω₁ < y < ψ_{Ω₂}(B)` is reached by a collapse**: some `e < B` in `Cl(B, y)` has
`y ≤ ψ_{Ω₂}(e)`. -/
theorem ts_hull_coll {B y : Ordinal.{0}} (hy : SC y) (hy1 : Om 1 < y) (hyx : y < S.psi B (Om (1 + 1))) :
    ∃ e, e < B ∧ e ∈ S.CSet B y ∧ y ≤ S.psi e (Om (1 + 1)) := by
  by_contra hno
  push Not at hno
  have hgood : ∀ x ∈ S.CSet B y, x < Om (1 + 1) → x < y := by
    intro x hx
    induction hx with
    | small h => exact fun _ => h
    | zero => exact fun _ => hy.1
    | inacc n => exact fun h => absurd (h.trans (Mx.mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW => exact fun h => absurd (h.trans Mx.mxOm2_lt_Iw) (lt_irrefl _)
    | @add x z _ _ ihx ihz =>
      intro h
      exact hy.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihz (lt_of_le_of_lt le_add_self h))
    | @phi x z _ _ ihx ihz =>
      intro h
      exact hy.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x z) h)) _
        (ihz (lt_of_le_of_lt (right_le_veblen x z) h))
    | @om x _ _ =>
      intro h
      have hx2 : x < 1 + 1 := Om_lt_Om.1 h
      exact (Om_le_Om.2 (Order.lt_add_one_iff.1 hx2)).trans_lt hy1
    | @coll π e hπ _ heC _ _ =>
      intro h
      show S.psi e.1 π < y
      by_cases hπ1 : π = Om 1
      · subst hπ1; exact (psi_lt Low.InR_Om_one _).trans hy1
      by_cases hπ2 : π = Om (1 + 1)
      · subst hπ2; exact hno e.1 e.2 heC
      · exact absurd h (not_lt.2 (ts_Om2_le_psi hπ hπ1 hπ2))
  have hle : S.psi B (Om (1 + 1)) ≤ y := psi_le_of_good (Mx.mxOm2_mem _ _) hgood
  exact absurd hyx (not_lt.2 hle)

/-- **Own points below a collapse**: for a strongly critical `y` with `Ω₁ < y < ψ_{Ω₂}(B)` there is an own `e` with
`y ≤ ψ_{Ω₂}(e) < ψ_{Ω₂}(B)`. -/
theorem ts_own_below {B y : Ordinal.{0}} (hy : SC y) (hy1 : Om 1 < y) (hyx : y < S.psi B (Om (1 + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ y ≤ S.psi e (Om (1 + 1)) ∧
      S.psi e (Om (1 + 1)) < S.psi B (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  obtain ⟨e, heB, heC, hye⟩ := ts_hull_coll hy hy1 hyx
  have heC' : e ∈ S.CSet B (S.psi B (Om (1 + 1))) := CSet_mono le_rfl hyx.le heC
  have hlt : S.psi e (Om (1 + 1)) < S.psi B (Om (1 + 1)) :=
    lt_psi_of_mem hκ (CSet.psi_mem heB hκ (mem_CSet_psi hκ B) heC') (psi_lt hκ _)
  obtain ⟨e', -, -, hown, heq⟩ := ts_norm hκ (ts_norm_of_lt hκ hlt)
  exact ⟨e', hown, heq ▸ hye, heq ▸ hlt⟩

/-- **Own points below an own collapse**: for an own `B` and a strongly critical `y` with `Ω₁ < y < ψ_{Ω₂}(B)` there is
an own `e < B` with `y ≤ ψ_{Ω₂}(e) < ψ_{Ω₂}(B)`. -/
theorem ts_own_below_lt {B y : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hy : SC y)
    (hy1 : Om 1 < y) (hyx : y < S.psi B (Om (1 + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ e < B ∧ y ≤ S.psi e (Om (1 + 1)) ∧
      S.psi e (Om (1 + 1)) < S.psi B (Om (1 + 1)) := by
  obtain ⟨e, hown', hye, hlt⟩ := ts_own_below hy hy1 hyx
  refine ⟨e, hown', ?_, hye, hlt⟩
  have h := compare_psi (InR_Om_succ 1) hown' hown
  rw [compare_lt_iff_lt.2 hlt] at h
  exact compare_lt_iff_lt.1 h.symm

end Googology.Trans.PoR.InaccPsi.R2.Ts
