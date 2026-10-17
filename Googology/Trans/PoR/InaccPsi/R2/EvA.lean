import Googology.Trans.PoR.InaccPsi.R2.EpsO

/-!
# The `ε`-numbers `ε_{x+c}` for every ordinal `c`

For an `ε`-number `x = ε_i` (`ε_` the `ε`-function of Mathlib, `Ordinal.epsilon`), `evA x c = ε_{i+c}`:
`evA x 0 = x`, `evA x (c+1) = eN (evA x c)`, continuous in `c`; `evA x n = eK n x` (`ε_{x+n}`) and
`evA x ω = eW x` (`ε_{x+ω}`).  No axiom.

* `evIx`, `evA`, `evA_E`, `evA_zero`, `evA_add_one`, `evA_add` (`ε_{ε_{x+a}+b} = ε_{x+(a+b)}`), `evA_lt_iff`,
  `evA_le_iff`, `evA_isNormal`, `le_evA`, `evA_eK` (`= eK n x`), `evA_eW` (`= eW x`), `evA_lim`;
* `evA_surj` (every `ε`-number `≥ x` is some `evA x c`), `evA_succ_le` (no `ε`-number strictly between
  `ε_{x+c}` and `ε_{x+c+1}`), `evA_bracket` (`[x, ε_{x+C})` is the union of the `[ε_{x+c}, ε_{x+c+1})`, `c < C`),
  `evA_bracket_eq` (the bracket is unique).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- `ω^·` is normal. -/
theorem ev_opow_normal : IsNormal (fun a : Ordinal.{0} => ω ^ a) := isNormal_opow one_lt_omega0

/-- An `ε`-number is a limit ordinal. -/
theorem ev_isSuccLimit_of_inE {s : Ordinal.{0}} (hs : InE s) : IsSuccLimit s := by
  have h : ω ∣ s := by
    have := opow_dvd_of_inE hs (one_le_iff_ne_zero.2 hs.pos.ne')
    rwa [opow_one] at this
  exact Ordinal.isSuccLimit_iff.2 ⟨hs.pos.ne', isSuccPrelimit_iff_omega0_dvd.2 h⟩

/-- `InE x` iff `x` is a value of `ε_`. -/
theorem inE_iff_mem_range_epsilon {x : Ordinal.{0}} : InE x ↔ x ∈ Set.range (fun i => Ordinal.epsilon i) := by
  have h := mem_range_deriv (f := fun a : Ordinal.{0} => ω ^ a) ev_opow_normal (a := x)
  have e : (fun i : Ordinal.{0} => Ordinal.epsilon i) = deriv (fun a : Ordinal.{0} => ω ^ a) :=
    funext epsilon_eq_deriv
  rw [e]
  exact h.symm

/-- The index of an `ε`-number: `ε_{evIx x} = x`. -/
noncomputable def evIx (x : Ordinal.{0}) : Ordinal.{0} := sInf {i | Ordinal.epsilon i = x}

theorem epsilon_evIx {x : Ordinal.{0}} (hx : InE x) : Ordinal.epsilon (evIx x) = x := by
  obtain ⟨i, hi⟩ := inE_iff_mem_range_epsilon.1 hx
  exact csInf_mem (s := {i | Ordinal.epsilon i = x}) ⟨i, hi⟩

theorem evIx_epsilon (i : Ordinal.{0}) : evIx (Ordinal.epsilon i) = i := by
  have h := epsilon_evIx (x := Ordinal.epsilon i) (omega0_opow_epsilon i)
  exact (veblen_injective 1) h

/-- **`ε_{x+c}`** (`= ε_{i+c}` for `x = ε_i`). -/
noncomputable def evA (x c : Ordinal.{0}) : Ordinal.{0} := Ordinal.epsilon (evIx x + c)

theorem evA_E (x c : Ordinal.{0}) : InE (evA x c) := omega0_opow_epsilon _

theorem evA_zero {x : Ordinal.{0}} (hx : InE x) : evA x 0 = x := by
  rw [evA, add_zero, epsilon_evIx hx]

theorem evA_add_one (x c : Ordinal.{0}) : evA x (c + 1) = eN (evA x c) := by
  rw [evA, evA, ← add_assoc, ← succ_eq_add_one, epsilon_succ_eq_nfp, succ_eq_add_one]; rfl

theorem evA_add (x a b : Ordinal.{0}) : evA (evA x a) b = evA x (a + b) := by
  rw [evA, evA, evA, evIx_epsilon, add_assoc]

theorem evA_isNormal (x : Ordinal.{0}) : IsNormal (evA x) :=
  (isNormal_veblen 1).comp (isNormal_add_right (evIx x))

theorem evA_strictMono (x : Ordinal.{0}) : StrictMono (evA x) := (evA_isNormal x).strictMono

theorem evA_lt_iff {x a b : Ordinal.{0}} : evA x a < evA x b ↔ a < b :=
  (evA_strictMono x).lt_iff_lt

theorem evA_le_iff {x a b : Ordinal.{0}} : evA x a ≤ evA x b ↔ a ≤ b :=
  (evA_strictMono x).le_iff_le

theorem le_evA {x : Ordinal.{0}} (hx : InE x) (c : Ordinal.{0}) : x ≤ evA x c := by
  have := evA_le_iff (x := x) (a := 0) (b := c) |>.2 zero_le
  rwa [evA_zero hx] at this

theorem lt_evA {x c : Ordinal.{0}} (hx : InE x) (hc : c ≠ 0) : x < evA x c := by
  have := evA_lt_iff (x := x) (a := 0) (b := c) |>.2 (pos_iff_ne_zero.2 hc)
  rwa [evA_zero hx] at this

/-- `ε_{x+n} = eK n x`. -/
theorem evA_eK {x : Ordinal.{0}} (hx : InE x) : ∀ n : ℕ, evA x n = eK n x
  | 0 => by rw [Nat.cast_zero, evA_zero hx]; rfl
  | n + 1 => by rw [Nat.cast_succ, evA_add_one, evA_eK hx n, eK_succ]

/-- The value at a limit is the supremum below. -/
theorem evA_lim (x : Ordinal.{0}) {c : Ordinal.{0}} (hc : IsSuccLimit c) :
    evA x c = ⨆ b : Set.Iio c, evA x b :=
  (evA_isNormal x).apply_of_isSuccLimit hc

/-- `ε_{x+ω} = eW x`. -/
theorem evA_eW {x : Ordinal.{0}} (hx : InE x) : evA x ω = eW x := by
  refine le_antisymm ?_ (eW_le (fun n => by rw [← evA_eK hx n]; exact evA_le_iff.2 (natCast_lt_omega0 n).le))
  rw [evA_lim x isSuccLimit_omega0]
  refine Ordinal.iSup_le (fun b => ?_)
  obtain ⟨n, hn⟩ := lt_omega0.1 b.2
  rw [hn, evA_eK hx n]
  exact eK_le_eW n x

/-- An `ε`-number above `ε_{x+c}` is at least `ε_{x+c+1}`. -/
theorem evA_succ_le {x c u : Ordinal.{0}} (hu : evA x c < u) (hE : InE u) : evA x (c + 1) ≤ u := by
  rw [evA_add_one]; exact eN_le hu hE

/-- An `ε`-number above every `ε_{x+b}`, `b < c` (`c ≠ 0`), is at least `ε_{x+c}`. -/
theorem evA_le_of_lt {x v c : Ordinal.{0}} (hv : InE v) (hc : c ≠ 0) (h : ∀ b < c, evA x b < v) :
    evA x c ≤ v := by
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨b, rfl⟩ | hlim
  · exact absurd h0 hc
  · rw [succ_eq_add_one]; exact evA_succ_le (h b (lt_succ b)) hv
  · rw [evA_lim x hlim]
    exact Ordinal.iSup_le (fun b => (h b.1 b.2).le)

/-- **Every `ε`-number `≥ x` is some `ε_{x+c}`.** -/
theorem evA_surj {x e : Ordinal.{0}} (hx : InE x) (he : InE e) (hxe : x ≤ e) : ∃ c, evA x c = e := by
  have h1 := epsilon_evIx hx
  have h2 := epsilon_evIx he
  have hle : evIx x ≤ evIx e := by
    rw [← h1, ← h2] at hxe
    exact (veblen_le_veblen_iff_right (o := 1)).1 hxe
  refine ⟨evIx e - evIx x, ?_⟩
  rw [evA, Ordinal.add_sub_cancel_of_le hle, h2]

/-- **The bracket**: a point of `[x, ε_{x+C})` lies in some `[ε_{x+c}, ε_{x+c+1})` with `c < C`. -/
theorem evA_bracket {x L C : Ordinal.{0}} (hx : InE x) (h1 : x ≤ L) (h2 : L < evA x C) :
    ∃ c, c < C ∧ evA x c ≤ L ∧ L < evA x (c + 1) := by
  set S := {c | L < evA x c} with hS
  have hne : S.Nonempty := ⟨C, h2⟩
  set c1 := sInf S with hc1
  have hc1S : L < evA x c1 := csInf_mem hne
  have hc1C : c1 ≤ C := csInf_le (OrderBot.bddBelow _) h2
  have hmin : ∀ c, c < c1 → evA x c ≤ L := fun c hc => by
    by_contra h; push Not at h
    exact absurd (csInf_le (OrderBot.bddBelow _) (show c ∈ S from h)) (not_le.2 hc)
  rcases zero_or_succ_or_isSuccLimit c1 with h0 | ⟨c, hc⟩ | hlim
  · rw [h0, evA_zero hx] at hc1S; exact absurd h1 (not_le.2 hc1S)
  · have hcc : c < c1 := by rw [← hc]; exact lt_succ c
    refine ⟨c, lt_of_lt_of_le hcc hc1C, hmin c hcc, ?_⟩
    rw [← succ_eq_add_one, hc]; exact hc1S
  · exfalso
    rw [evA_lim x hlim] at hc1S
    obtain ⟨b, hb⟩ := Ordinal.lt_iSup_iff.1 hc1S
    exact absurd (hmin b b.2) (not_le.2 hb)

/-- The bracket `[ε_{x+c}, ε_{x+c+1})` of a point is unique. -/
theorem evA_bracket_eq {x X a b : Ordinal.{0}} (ha1 : evA x a ≤ X) (ha2 : X < evA x (a + 1))
    (hb1 : evA x b ≤ X) (hb2 : X < evA x (b + 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (lt_of_le_of_lt ((evA_le_iff.2 (add_one_le_of_lt hab)).trans hb1) ha2) (lt_irrefl _)
  · exact hab
  · exact absurd (lt_of_le_of_lt ((evA_le_iff.2 (add_one_le_of_lt hab)).trans ha1) hb2) (lt_irrefl _)

end Googology.Trans.PoR.InaccPsi.R2
