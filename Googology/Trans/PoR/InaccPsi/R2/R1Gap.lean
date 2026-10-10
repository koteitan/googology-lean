import Googology.Trans.PoR.InaccPsi.R2.Ups

/-!
# `R₁⁺`: reaches, gaps between `υ`-points, and `<₁`-predecessors inside a gap

From the cited facts of `R2.Cited` and `R2.CitedR1` ([W07a], [W07b]):

* `exists_lh1`: the reach `lh(x)` of `R₁⁺` exists as soon as `x ≤₁ g` fails for some `g ≥ x`
  ([W07b] Lemma 2.1 (a), (b)).
* `Gap τ m x`: `x` lies strictly between the base `τ` (`1` or a `υ`-point) and `m = τ^∞`, the next
  `υ`-point, with `Tᵗ ∩ Ω₁ = m`; `exists_gap`: every countable `x > 1` that is not a `υ`-point lies
  in a gap ([W07b] Cor 5.10).
* `Gap.not_ups`, `Gap.not_le1R`, `Gap.exists_lh1`: no `υ`-point inside a gap; a point inside a gap is
  `≤₁` nothing `≥ m`, so its reach is `< m`.
* `preds_finite`, `greatest_pred`: an additive principal `α` inside a gap has only finitely many
  `<₁`-predecessors in `(τ, α)`, and either it is `τ`-`≤₁`-minimal or it has a greatest
  `<₁`-predecessor ([W07b] Def 5.8, Cor 5.9).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The reach of `R₁⁺` exists when `x ≤₁ g` fails for some `g ≥ x`, and it is `< g`. -/
theorem exists_lh1 {x g : Ordinal.{0}} (hxg : x ≤ g) (hg : ¬ le1R x g) :
    ∃ l, IsLh1 x l ∧ l < g := by
  set S := {t | le1R x t} with hS
  have hbdd : BddAbove S := ⟨g, fun t ht => by
    by_contra hlt; exact hg (le1R_of_le hxg (not_le.1 hlt).le ht)⟩
  have hxS : x ∈ S := le1R_refl x
  have hxl : x ≤ sSup S := le_csSup hbdd hxS
  have hl : le1R x (sSup S) := by
    by_cases hlS : sSup S ∈ S
    · exact hlS
    have hxl' : x < sSup S := lt_of_le_of_ne hxl (fun e => hlS (e ▸ hxS))
    have hbelow : ∀ b, x ≤ b → b < sSup S → le1R x b := fun b hxb hbl => by
      obtain ⟨s, hs, hbs⟩ := exists_lt_of_lt_csSup ⟨x, hxS⟩ hbl
      exact le1R_of_le hxb hbs.le hs
    rcases zero_or_succ_or_isSuccLimit (sSup S) with h0 | ⟨t, ht⟩ | hlim
    · rw [h0] at hxl'; exact absurd hxl' (not_lt.2 zero_le)
    · exfalso
      have htl : t < sSup S := by rw [← ht]; exact lt_succ t
      obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨x, hxS⟩ htl
      have hsl : s ≤ sSup S := le_csSup hbdd hs
      have : sSup S ≤ s := by rw [← ht]; exact succ_le_of_lt hts
      exact hlS (le_antisymm hsl this ▸ hs)
    · exact le1R_limit hlim hxl' hbelow
  refine ⟨sSup S, ⟨hl, fun t ht => le_csSup hbdd ht⟩, lt_of_le_of_ne ?_ (fun e => hg (e ▸ hl))⟩
  exact csSup_le ⟨x, hxS⟩ fun t ht => by
    by_contra hlt; exact hg (le1R_of_le hxg (not_le.1 hlt).le ht)

/-- `x` lies in the gap `(τ, m)`: `τ` is `1` or a `υ`-point, `m = τ^∞` is the next `υ`-point, and
`Tᵗ ∩ Ω₁ = m`. -/
structure Gap (τ m x : Ordinal.{0}) : Prop where
  base_E : τ = 1 ∨ InE τ
  base_Om1 : τ < Om1
  base_lt : τ < x
  lt_next : x < m
  next : UpsPt m
  noUps : ∀ u, τ < u → u < m → ¬ UpsPt u
  T : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m)

/-- Every countable `x > 1` that is not a `υ`-point lies in a gap. -/
theorem exists_gap {x : Ordinal.{0}} (h1x : 1 < x) (hx1 : x < Om1) (hnu : ¬ UpsPt x) :
    ∃ τ m, Gap τ m x := by
  set t := {u | u < x ∧ UpsPt u} with ht
  by_cases hne : t.Nonempty
  · have hbdd : BddAbove t := ⟨x, fun u hu => hu.1.le⟩
    have hτ : UpsPt (sSup t) := upsPt_sSup hne hbdd fun u hu => hu.2
    have hτx : sSup t < x := by
      refine lt_of_le_of_ne (csSup_le hne fun u hu => hu.1.le) fun e => hnu (e ▸ hτ)
    obtain ⟨m, hmn, hT⟩ := exists_next hτ (lt_trans hτx hx1)
    refine ⟨sSup t, m, Or.inr (upsPt_inE hτ), lt_trans hτx hx1, hτx, ?_, hmn.2.1, ?_, hT⟩
    · by_contra hmx
      have hmx' : m < x := lt_of_le_of_ne (not_lt.1 hmx) fun e => hnu (e ▸ hmn.2.1)
      exact absurd (le_csSup hbdd ⟨hmx', hmn.2.1⟩) (not_le.2 hmn.1)
    · intro u hu1 hu2 hu
      exact absurd (hmn.2.2 u hu1 hu) (not_le.2 hu2)
  · obtain ⟨m, h1m, hm, hmin, hT⟩ := T_inter_Om1_one
    have hmU : UpsPt m := ⟨lt_trans zero_lt_one h1m, hm⟩
    refine ⟨1, m, Or.inl rfl, lt_trans h1x hx1, h1x, ?_, hmU, ?_, hT⟩
    · by_contra hmx
      have hmx' : m < x := lt_of_le_of_ne (not_lt.1 hmx) fun e => hnu (e ▸ hmU)
      exact hne ⟨m, hmx', hmU⟩
    · intro u hu1 hu2 hu
      exact absurd (hmin u hu1 hu.2) (not_le.2 hu2)

namespace Gap

variable {τ m x : Ordinal.{0}}

theorem not_ups (hg : Gap τ m x) {y : Ordinal.{0}} (h1 : τ < y) (h2 : y < m) : ¬ UpsPt y :=
  hg.noUps y h1 h2

theorem not_le1R (hg : Gap τ m x) {y z : Ordinal.{0}} (h1 : τ < y) (h2 : y < m) (hz : m ≤ z) :
    ¬ le1R y z := by
  intro h
  have hy : LtInf1 y := (le1R_lt_ups hg.next h2 hz).1 h
  exact hg.noUps y h1 h2 ⟨lt_of_le_of_lt zero_le h1, hy⟩

theorem exists_lh1' (hg : Gap τ m x) {y : Ordinal.{0}} (h1 : τ < y) (h2 : y < m) :
    ∃ l, IsLh1 y l ∧ l < m :=
  exists_lh1 h2.le (hg.not_le1R h1 h2 le_rfl)

theorem mem_T (hg : Gap τ m x) {y : Ordinal.{0}} (hy : y < m) (hy1 : y < Om1) : y ∈ Tset τ :=
  (hg.T y hy1).2 hy

/-- Another point of the same gap. -/
theorem of_mem (hg : Gap τ m x) {y : Ordinal.{0}} (h1 : τ < y) (h2 : y < m) : Gap τ m y :=
  ⟨hg.base_E, hg.base_Om1, h1, h2, hg.next, hg.noUps, hg.T⟩

end Gap

/-- **[W07b] Cor 5.9**: an additive principal `α` in a gap has finitely many `<₁`-predecessors in
`(τ, α)`. -/
theorem preds_finite {τ m α : Ordinal.{0}} (hg : Gap τ m α) (hα1 : α < Om1) (hαP : Indec α) :
    ∃ F : Finset Ordinal.{0}, (∀ d ∈ F, d < α) ∧ ∀ d, τ < d → d < α → le1R d α → d ∈ F := by
  classical
  obtain ⟨n, β, hβn, hτβ0, hmin0, hstep⟩ :=
    le1R_loc hg.base_E hg.base_Om1 (hg.mem_T hg.lt_next hα1) hg.base_lt hα1 hαP
  have hmono : ∀ i j, i ≤ j → j ≤ n → β i ≤ β j := by
    intro i j hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ k hik ih => exact (ih (Nat.le_of_succ_le hjn)).trans (hstep k hjn).1.le
  have key : ∀ i ≤ n, ∀ d, le1R d (β i) → d < β i → d ≤ τ ∨ ∃ j < i, d = β j := by
    intro i
    induction i with
    | zero => intro _ d hd hdl; exact Or.inl (hmin0 d hd hdl)
    | succ k ih =>
      intro hk d hd hdl
      obtain ⟨hlt, hle1, hgr⟩ := hstep k hk
      have hdk : d ≤ β k := hgr d hd hdl
      rcases eq_or_lt_of_le hdk with e | hdk'
      · exact Or.inr ⟨k, Nat.lt_succ_self k, e⟩
      · rcases ih (Nat.le_of_succ_le hk) d (le1R_of_le hdk hlt.le hd) hdk' with h | ⟨j, hj, e⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, e⟩
  refine ⟨(Finset.range n).image β, ?_, ?_⟩
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hd
    have hjn := Finset.mem_range.1 hj
    rw [← hβn]
    exact lt_of_lt_of_le (hstep j hjn).1 (hmono (j + 1) n hjn le_rfl)
  · intro d hτd hdα hd
    rw [← hβn] at hdα hd
    rcases key n le_rfl d hd hdα with h | ⟨j, hj, rfl⟩
    · exact absurd h (not_le.2 hτd)
    · exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩

/-- **[W07b] Cor 5.9**: an additive principal `α` in a gap is `τ`-`≤₁`-minimal or has a greatest
`<₁`-predecessor `σ ∈ (τ, α)`. -/
theorem greatest_pred {τ m α : Ordinal.{0}} (hg : Gap τ m α) (hα1 : α < Om1) (hαP : Indec α) :
    (∀ d, le1R d α → d < α → d ≤ τ) ∨
      ∃ σ, τ < σ ∧ σ < α ∧ le1R σ α ∧ ∀ d, le1R d α → d < α → d ≤ σ := by
  obtain ⟨n, β, hβn, hτβ0, hmin0, hstep⟩ :=
    le1R_loc hg.base_E hg.base_Om1 (hg.mem_T hg.lt_next hα1) hg.base_lt hα1 hαP
  have hmono : ∀ j ≤ n, β 0 ≤ β j := by
    intro j hjn
    induction j with
    | zero => exact le_rfl
    | succ k ih => exact (ih (Nat.le_of_succ_le hjn)).trans (hstep k hjn).1.le
  rcases n with _ | k
  · left; rw [← hβn]; exact hmin0
  · right
    obtain ⟨hlt, hle1, hgr⟩ := hstep k (Nat.lt_succ_self k)
    rw [← hβn]
    exact ⟨β k, lt_of_lt_of_le hτβ0 (hmono k (Nat.le_succ k)), hlt, hle1, hgr⟩

end Googology.Trans.PoR.InaccPsi.R2
