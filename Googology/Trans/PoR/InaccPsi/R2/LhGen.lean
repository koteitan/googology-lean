import Googology.Trans.PoR.InaccPsi.R2.BaseC
import Googology.Trans.PoR.InaccPsi.R2.CitedW

/-!
# The general reach of `R₁⁺`: `lh(α)` for every countable `α`

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`lh(α) = max{β | α ≤₁ β}` in `R₁⁺` (`IsLh1`, [W07b] Def 3.1), `lh(α) = ∞` if `α ≤₁ β` for every `β ≥ α`
(`LtInf1`).  `υ` enumerates `{0} ∪ {α > 0 | α <₁ ∞}` (`R2.Points`), and `υ_{ξ+1}` is the least `υ`-point above
`υ_ξ`.  For every `α < Ω₁` (`lhR1_all`):

* `α` a `υ`-point: `lh(α) = ∞` (no maximum, `lhUps_none`);
* otherwise `υ_ξ ≤ α < υ_{ξ+1}` for one `ξ` (`lhBracket`), `α ≤ lh(α) < υ_{ξ+1}` (`lhGap_lt`: a reach never passes
  the next `υ`-point), and
  - `α` decomposable (`0` included): `lh(α) = α` (`lhDecomp`; [W07b] Def 4.1, second clause);
  - `α = 1`: `lh(1) = 1` (`lhOne`);
  - `α = ω^{α'}` additive principal, not an `ε`-number, `α' ≠ 0`: `lh(α) = α + logend(α')` (`lhNonE`), from
    [W07b] Thm 2.2 alone (the case `Δ = 0` of [W07b] Def 4.1, in closed form);
  - `α` an `ε`-number: `lh(α) = lhᵗ(α)` with `τ = υ_ξ` (`τ = 1` for `ξ = 0`), and `α·2 ≤ lh(α)` (`lhEps`;
    [W07b] Thm 5.3 with Def 4.1, through the repo axiom `lh_eq_lhT`, and Thm 2.2 at `ξ = α`).

`lhR1_at` is the same with the bracket `υ_ξ ≤ α < υ_{ξ+1}` given.  No new axiom, no new definition: the cited
facts are the repo axioms `le1R_refl`, `le1R_le`, `le1R_of_le`, `le1R_lim_P`, `le1R_two_iff`, `le1R_thm22`
([W07b] Lemma 2.1, §2, Thm 2.2), `lh_eq_lhT` ([W07b] Thm 5.3) and those behind `upsilon_succ_T`, `next_lt_Om1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lh

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- The reach is unique. -/
theorem lhUnique {a r r' : Ordinal.{0}} (h : IsLh1 a r) (h' : IsLh1 a r') : r = r' :=
  le_antisymm (h'.2 r h.1) (h.2 r' h'.1)

/-- **At a `υ`-point the reach is `∞`**: no maximum of `{β | α ≤₁ β}`. -/
theorem lhUps_none {a : Ordinal.{0}} (ha : UpsPt a) : ¬ ∃ r, IsLh1 a r := by
  rintro ⟨r, h1, h2⟩
  have har : a ≤ r := le1R_le h1
  have := h2 (r + 1) (ha.2 (r + 1) (har.trans le_self_add))
  exact absurd this (not_le.2 (lt_add_one r))

/-- **A decomposable ordinal (or `0`) has reach itself** ([W07b] Def 4.1, second clause; §2). -/
theorem lhDecomp {a : Ordinal.{0}} (ha : ¬ Indec a) : IsLh1 a a := by
  refine ⟨le1R_refl a, fun g hg => ?_⟩
  by_contra hlt
  exact ha (indec_of_lt1R hg (not_le.1 hlt))

/-- `lh(1) = 1`: no additive principal number lies in `(0, 1)` ([W07b] §2). -/
theorem lhOne : IsLh1 1 1 := by
  refine ⟨le1R_refl 1, fun g hg => ?_⟩
  by_contra hlt
  obtain ⟨-, hc⟩ := le1R_lim_P hg (not_le.1 hlt)
  obtain ⟨p, hp0, hp1, -⟩ := hc 0 zero_lt_one
  exact hp0.ne' (Order.lt_one_iff.1 hp1)

theorem lhOpow_inj {b c : Ordinal.{0}} (h : ω ^ b = ω ^ c) : b = c :=
  (opow_right_inj one_lt_omega0).1 h

/-- **The reach of a non-`ε` additive principal number** ([W07b] Thm 2.2): for `α = ω^{α'}`, `α' ≠ 0`,
`α ∉ E`: `lh(α) = α + logend(α')`. -/
theorem lhNonE {a' : Ordinal.{0}} (ha0 : a' ≠ 0) (hE : ¬ InE (ω ^ a')) :
    IsLh1 (ω ^ a') (ω ^ a' + lg a') := by
  have hle : a' ≤ ω ^ a' := right_le_opow a' one_lt_omega0
  have hlt : a' < ω ^ a' := by
    refine lt_of_le_of_ne hle fun e => hE ?_
    unfold InE; rw [← e]; exact e.symm
  have hlg : lg a' < ω ^ a' := lt_of_le_of_lt (lg_le ha0) hlt
  refine ⟨?_, fun g hg => ?_⟩
  · rcases eq_or_ne (lg a') 0 with h0 | h0
    · rw [h0, add_zero]; exact le1R_refl _
    · exact (le1R_thm22 (pos_iff_ne_zero.2 h0) hlg.le).2 ⟨a', ha0, rfl, le_rfl⟩
  · by_contra hgt
    have hgt' : ω ^ a' + lg a' < g := not_le.1 hgt
    have h1 : ω ^ a' + (lg a' + 1) ≤ g := by
      rw [← add_assoc]; exact Order.add_one_le_of_lt hgt'
    have h2 : le1R (ω ^ a') (ω ^ a' + (lg a' + 1)) := le1R_of_le le_self_add h1 hg
    obtain ⟨b, -, hb, hξ⟩ :=
      (le1R_thm22 (lt_of_lt_of_le zero_lt_one le_add_self) (Order.add_one_le_of_lt hlg)).1 h2
    rw [← lhOpow_inj hb] at hξ
    exact absurd hξ (not_le.2 (lt_add_one _))

/-- Every ordinal lies in one `υ`-gap: `υ_ξ ≤ α < υ_{ξ+1}`. -/
theorem lhBracket (a : Ordinal.{0}) : ∃ ξ, upsilon ξ ≤ a ∧ a < upsilon (ξ + 1) := by
  classical
  set S : Set Ordinal.{0} := {ι | a < upsilon ι} with hSdef
  have hS : S.Nonempty :=
    ⟨a + 1, lt_of_lt_of_le (lt_add_one a) (upsilon_normal.strictMono.id_le (a + 1))⟩
  have hm : a < upsilon (sInf S) := csInf_mem hS
  have hmin : ∀ ι < sInf S, upsilon ι ≤ a := fun ι hι =>
    not_lt.1 fun h => absurd (csInf_le' (s := S) h) (not_le.2 hι)
  rcases zero_or_succ_or_isSuccLimit (sInf S) with h0 | ⟨j, hj⟩ | hl
  · rw [h0, upsilon_zero] at hm; exact absurd hm (not_lt.2 zero_le)
  · refine ⟨j, hmin j (by rw [← hj]; exact lt_succ j), ?_⟩
    rw [← succ_eq_add_one, hj]; exact hm
  · exfalso
    have hle : upsilon (sInf S) ≤ a :=
      (upsilon_limit hl).2 (by rintro _ ⟨ι, hι, rfl⟩; exact hmin ι hι)
    exact absurd hm (not_lt.2 hle)

/-- **A reach never passes the next `υ`-point**: if `α` is not a `υ`-point, `υ_ξ ≤ α < υ_{ξ+1}` and
`α ≤₁ r`, then `r < υ_{ξ+1}`. -/
theorem lhGap_lt {a ξ r : Ordinal.{0}} (hU : ¬ UpsPt a) (h1 : upsilon ξ ≤ a) (h2 : a < upsilon (ξ + 1))
    (h : le1R a r) : r < upsilon (ξ + 1) := by
  by_contra hge
  have hge' : upsilon (ξ + 1) ≤ r := not_lt.1 hge
  have har : a < r := lt_of_lt_of_le h2 hge'
  have hI := indec_of_lt1R h har
  have hn := upsilon_isNext ξ
  rw [succ_eq_add_one] at hn
  have hlt : upsilon ξ < a := by
    refine lt_of_le_of_ne h1 fun e => ?_
    rcases eq_or_ne ξ 0 with hξ | hξ
    · rw [hξ, upsilon_zero] at e; exact hI.ne_zero e.symm
    · exact hU (e ▸ upsPt_upsilon (pos_iff_ne_zero.2 hξ))
  exact not_le1R_gap hn hlt h2 hge' h

theorem lhInE_pos {a : Ordinal.{0}} (hE : InE a) : 0 < a := by
  rcases eq_or_ne a 0 with h | h
  · rw [h] at hE; unfold InE at hE; rw [opow_zero] at hE; exact absurd hE one_ne_zero
  · exact pos_iff_ne_zero.2 h

theorem lhInE_indec {a : Ordinal.{0}} (hE : InE a) : Indec a := by
  have h := indec_opow a
  unfold InE at hE
  rwa [hE] at h

theorem lhInE_omega_le {a : Ordinal.{0}} (hE : InE a) : ω ≤ a := by
  have h1 : (1 : Ordinal.{0}) ≤ a := Order.one_le_iff_ne_zero.2 (lhInE_pos hE).ne'
  calc (ω : Ordinal.{0}) = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ ω ^ a := opow_le_opow_right omega0_pos h1
    _ = a := hE

/-- **The reach of a countable `ε`-number that is not a `υ`-point** ([W07b] Thm 5.3 with Def 4.1, Thm 2.2): with
`υ_ξ ≤ α < υ_{ξ+1}` and `τ = υ_ξ` (`τ = 1` for `ξ = 0`), `lh(α) = lhᵗ(α)`, and `α·2 ≤ lhᵗ(α) < υ_{ξ+1}`. -/
theorem lhEps {a ξ : Ordinal.{0}} (ha1 : a < Om1) (hξ1 : upsilon ξ ≤ a) (hξ2 : a < upsilon (ξ + 1))
    (hE : InE a) (hU : ¬ UpsPt a) :
    IsLh1 a (lhT (if ξ = 0 then 1 else upsilon ξ) a) ∧
      a * 2 ≤ lhT (if ξ = 0 then 1 else upsilon ξ) a ∧
      lhT (if ξ = 0 then 1 else upsilon ξ) a < upsilon (ξ + 1) := by
  have ha0 := lhInE_pos hE
  have hb : upsilon ξ = 0 ∨ UpsPt (upsilon ξ) := by
    rcases eq_or_ne ξ 0 with hξ | hξ
    · left; rw [hξ, upsilon_zero]
    · right; exact upsPt_upsilon (pos_iff_ne_zero.2 hξ)
  have hc : upsilon (succ ξ) < Om1 := next_lt_Om1 (upsilon_isNext ξ) hb (lt_of_le_of_lt hξ1 ha1)
  have hT := upsilon_succ_T ξ hc a ha1
  rw [succ_eq_add_one] at hT
  have haT : a ∈ Tset (if ξ = 0 then 1 else upsilon ξ) := hT.2 hξ2
  have hτ : ((if ξ = 0 then 1 else upsilon ξ) = 1 ∨ InE (if ξ = 0 then 1 else upsilon ξ)) ∧
      (if ξ = 0 then 1 else upsilon ξ) < a := by
    by_cases hξ : ξ = 0
    · rw [if_pos hξ]
      exact ⟨Or.inl rfl, lt_of_lt_of_le one_lt_omega0 (lhInE_omega_le hE)⟩
    · rw [if_neg hξ]
      have hu := upsPt_upsilon (pos_iff_ne_zero.2 hξ)
      exact ⟨Or.inr (upsPt_inE hu), lt_of_le_of_ne hξ1 fun e => hU (e ▸ hu)⟩
  have hτ1 : (if ξ = 0 then 1 else upsilon ξ) < Om1 := hτ.2.trans ha1
  have hlh := lh_eq_lhT hτ.1 hτ1 haT hτ.2 ha1 (lhInE_indec hE)
  exact ⟨hlh, hlh.2 _ ((le1R_two_iff ha0).2 hE), lhGap_lt hU hξ1 hξ2 hlh.1⟩

/-- **`lh(α)` for every countable `α` in a given `υ`-gap** (`υ_ξ ≤ α < υ_{ξ+1}`, `α` not a `υ`-point). -/
theorem lhR1_at {a ξ : Ordinal.{0}} (ha1 : a < Om1) (hU : ¬ UpsPt a) (hξ1 : upsilon ξ ≤ a)
    (hξ2 : a < upsilon (ξ + 1)) :
    ∃ r, IsLh1 a r ∧ a ≤ r ∧ r < upsilon (ξ + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (a = 1 ∧ r = 1) ∨
       (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (if ξ = 0 then 1 else upsilon ξ) a ∧ a * 2 ≤ r)) := by
  have fin : ∀ r, IsLh1 a r → a ≤ r ∧ r < upsilon (ξ + 1) := fun r h =>
    ⟨le1R_le h.1, lhGap_lt hU hξ1 hξ2 h.1⟩
  by_cases hI : Indec a
  · by_cases hE : InE a
    · obtain ⟨h1, h2, -⟩ := lhEps ha1 hξ1 hξ2 hE hU
      exact ⟨_, h1, (fin _ h1).1, (fin _ h1).2, Or.inr (Or.inr (Or.inr ⟨hE, rfl, h2⟩))⟩
    · obtain ⟨hne, hP⟩ := indec_iff.1 hI
      rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hP with h0 | ⟨a', ha'⟩
      · exact absurd h0 hne
      · replace ha' : ω ^ a' = a := ha'
        rcases eq_or_ne a' 0 with h0 | h0
        · have ha : a = 1 := by rw [← ha', h0, opow_zero]
          subst ha
          exact ⟨1, lhOne, le_rfl, (fin 1 lhOne).2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · subst ha'
          have h := lhNonE h0 hE
          exact ⟨_, h, (fin _ h).1, (fin _ h).2, Or.inr (Or.inr (Or.inl ⟨a', h0, rfl, hE, rfl⟩))⟩
  · have h := lhDecomp hI
    exact ⟨a, h, le_rfl, (fin a h).2, Or.inl ⟨hI, rfl⟩⟩

/-- **The general reach of `R₁⁺` for every `α < Ω₁`** ([W07b] Def 3.1, Def 4.1, Thm 2.2, Thm 5.3): `α` is a
`υ`-point with `lh(α) = ∞`, or `α` lies in a gap `[υ_ξ, υ_{ξ+1})` and `lh(α)` exists, lies in `[α, υ_{ξ+1})`, and
is `α` (decomposable `α`), `1` (`α = 1`), `α + logend(α')` (`α = ω^{α'} ∉ E`) or `lhᵗ(α)` with `τ = υ_ξ`
(`τ = 1` if `ξ = 0`) and `α·2 ≤ lhᵗ(α)` (`α ∈ E`). -/
theorem lhR1_all {a : Ordinal.{0}} (ha1 : a < Om1) :
    (UpsPt a ∧ LtInf1 a ∧ ¬ ∃ r, IsLh1 a r) ∨
    ∃ ξ r, upsilon ξ ≤ a ∧ a < upsilon (ξ + 1) ∧ IsLh1 a r ∧ a ≤ r ∧ r < upsilon (ξ + 1) ∧
      ((¬ Indec a ∧ r = a) ∨ (a = 1 ∧ r = 1) ∨
       (∃ a', a' ≠ 0 ∧ a = ω ^ a' ∧ ¬ InE a ∧ r = a + lg a') ∨
       (InE a ∧ r = lhT (if ξ = 0 then 1 else upsilon ξ) a ∧ a * 2 ≤ r)) := by
  by_cases hU : UpsPt a
  · exact Or.inl ⟨hU, hU.2, lhUps_none hU⟩
  · right
    obtain ⟨ξ, h1, h2⟩ := lhBracket a
    obtain ⟨r, hr⟩ := lhR1_at ha1 hU h1 h2
    exact ⟨ξ, r, h1, h2, hr⟩

/-- Every countable `α` that is not a `υ`-point has an `R₁⁺`-reach. -/
theorem lhR1_exists {a : Ordinal.{0}} (ha1 : a < Om1) (hU : ¬ UpsPt a) : ∃ r, IsLh1 a r := by
  rcases lhR1_all ha1 with h | ⟨ξ, r, -, -, h, -⟩
  · exact absurd h.1 hU
  · exact ⟨r, h⟩

end Googology.Trans.PoR.InaccPsi.R2.Lh
