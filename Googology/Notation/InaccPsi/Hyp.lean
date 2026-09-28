import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Principal

/-!
# The setting: `Ω`, strongly critical ordinals, and `ω` inaccessibles

* `Om v` is `Ω_v`: `Ω_0 = 0` and `Ω_v = ω_v` for `v > 0`, so `v ↦ Ω_v` enumerates `0`
  and the uncountable cardinals.
* `SC γ` says that `γ` is strongly critical: `0 < γ` and `γ` is closed under the binary
  Veblen function `veblen`.
* Every uncountable cardinal is strongly critical (`SC_Om`). For a regular cardinal this
  is `derivFamily_lt_ord`; a singular one is reduced to the successor of the larger
  cardinality of the two arguments.
* `InaccSeq` is the hypothesis: a strictly increasing sequence `I n` of uncountable
  regular cardinals that are fixed points of `Ω` (weakly inaccessible cardinals).
* `InR S κ` is the class `R` of collapsing subscripts: the `I n` and the successor
  cardinals `Ω_{s+1}`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Cardinal Set

universe u

/-! ## `Ω` -/

/-- `Ω_0 = 0`, and `Ω_v = ω_v` for `v > 0`. -/
noncomputable def Om (v : Ordinal.{u}) : Ordinal.{u} :=
  if v = 0 then 0 else ω_ v

@[simp] theorem Om_zero : Om (0 : Ordinal.{u}) = 0 := if_pos rfl

theorem Om_of_ne_zero {v : Ordinal.{u}} (h : v ≠ 0) : Om v = ω_ v := if_neg h

theorem Om_pos {v : Ordinal.{u}} (h : v ≠ 0) : 0 < Om v := by
  rw [Om_of_ne_zero h]
  exact lt_of_lt_of_le omega0_pos (omega0_le_omega v)

theorem Om_strictMono : StrictMono (Om : Ordinal.{u} → Ordinal.{u}) := by
  intro u v h
  have hv : v ≠ 0 := (lt_of_le_of_lt (zero_le : (0 : Ordinal.{u}) ≤ u) h).ne'
  by_cases hu : u = 0
  · rw [hu, Om_zero]; exact Om_pos hv
  · rw [Om_of_ne_zero hu, Om_of_ne_zero hv]; exact omega_lt_omega.2 h

theorem Om_lt_Om {u v : Ordinal.{u}} : Om u < Om v ↔ u < v := Om_strictMono.lt_iff_lt

theorem Om_le_Om {u v : Ordinal.{u}} : Om u ≤ Om v ↔ u ≤ v := Om_strictMono.le_iff_le

theorem Om_inj {u v : Ordinal.{u}} : Om u = Om v ↔ u = v := Om_strictMono.injective.eq_iff

theorem le_Om (v : Ordinal.{u}) : v ≤ Om v := by
  by_cases h : v = 0
  · rw [h]; exact zero_le
  · rw [Om_of_ne_zero h]; exact le_omega_self v

theorem Om_eq_ord {v : Ordinal.{u}} (h : v ≠ 0) : Om v = (ℵ_ v).ord := by
  rw [Om_of_ne_zero h, ord_aleph]

theorem card_Om {v : Ordinal.{u}} (h : v ≠ 0) : (Om v).card = ℵ_ v := by
  rw [Om_of_ne_zero h, card_omega]

theorem aleph0_lt_card_Om {v : Ordinal.{u}} (h : v ≠ 0) : ℵ₀ < (Om v).card := by
  rw [card_Om h, ← aleph_zero]
  exact aleph_lt_aleph.2 (pos_iff_ne_zero.2 h)

/-- `ω < Ω_v` for `v > 0`. -/
theorem omega0_lt_Om {v : Ordinal.{u}} (h : v ≠ 0) : ω < Om v := by
  rw [Om_of_ne_zero h, ← omega_zero]
  exact omega_lt_omega.2 (pos_iff_ne_zero.2 h)

/-! ## Strongly critical ordinals -/

/-- `γ` is strongly critical: positive and closed under the binary Veblen function. -/
def SC (γ : Ordinal.{u}) : Prop :=
  0 < γ ∧ ∀ x < γ, ∀ y < γ, veblen x y < γ

/-- A supremum of fewer than `c` ordinals below `c.ord` stays below, for regular `c`,
where the index type may live one universe up (like `Iio x`). -/
theorem iSup_lt_ord_big {c : Cardinal.{u}} (hc : c.IsRegular) {β : Type (u + 1)}
    {f : β → Ordinal.{u}} (hβ : #β < Cardinal.lift.{u + 1} c) (hf : ∀ i, f i < c.ord) :
    ⨆ i, f i < c.ord := by
  refine lift_iSup_lt_of_lt_cof ?_ hf
  rw [← lift_cof, hc.cof_ord, Cardinal.lift_id'.{u, u + 1}]
  exact hβ

theorem nfpFamily_lt_ord_big {c : Cardinal.{u}} (hc : c.IsRegular) (hunc : ℵ₀ < c)
    {ι : Type (u + 1)} {f : ι → Ordinal.{u} → Ordinal.{u}} (hι : #ι < Cardinal.lift.{u + 1} c)
    (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a : Ordinal.{u}} (ha : a < c.ord) :
    nfpFamily f a < c.ord := by
  show (⨆ l, List.foldr f a l) < c.ord
  refine iSup_lt_ord_big hc ?_ fun l => ?_
  · refine lt_of_le_of_lt (mk_list_le_max ι) (max_lt ?_ hι)
    rw [← lift_aleph0.{u + 1, u}]
    exact Cardinal.lift_lt.2 hunc
  · induction l with
    | nil => exact ha
    | cons i l H => exact hf _ _ H

theorem derivFamily_lt_ord_big {c : Cardinal.{u}} (hc : c.IsRegular) (hunc : ℵ₀ < c)
    {ι : Type (u + 1)} {f : ι → Ordinal.{u} → Ordinal.{u}} (hι : #ι < Cardinal.lift.{u + 1} c)
    (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a : Ordinal.{u}} :
    a < c.ord → derivFamily f a < c.ord := by
  induction a using limitRecOn with
  | zero =>
    intro ha
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_big hc hunc hι hf ha
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exact nfpFamily_lt_ord_big hc hunc hι hf
      ((isSuccLimit_ord hc.1).succ_lt (hb ((Order.lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    rw [derivFamily_limit f hb]
    refine iSup_lt_ord_big hc ?_ fun i => H i.1 i.2 (i.2.trans hb')
    rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lt]
    exact lt_ord.1 hb'

/-- A regular uncountable cardinal is closed under `veblen`. -/
theorem veblen_lt_ord_of_isRegular {c : Cardinal.{u}} (hc : c.IsRegular) (hc' : ℵ₀ < c) :
    ∀ x < c.ord, ∀ y < c.ord, veblen x y < c.ord := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  intro hx y hy
  by_cases h0 : x = 0
  · subst h0
    rw [veblen_zero_apply]
    exact isPrincipal_opow_ord hc.1 (omega0_lt_ord.2 hc') hy
  · have hveb : veblen x = derivFamily fun i : Iio x => veblen i.1 := by
      unfold veblen
      rw [veblenWith_of_ne_zero _ h0]
    rw [hveb]
    refine derivFamily_lt_ord_big hc hc' ?_ ?_ hy
    · rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lt]
      exact lt_ord.1 hx
    · intro i b hb
      exact ih i.1 i.2 (i.2.trans hx) b hb

/-- `Ω_v` for `v > 0` is strongly critical. -/
theorem SC_Om {v : Ordinal.{u}} (hv : v ≠ 0) : SC (Om v) := by
  refine ⟨Om_pos hv, fun x hx y hy => ?_⟩
  have hx' : x.card < ℵ_ v := lt_ord.1 (by rw [← Om_eq_ord hv]; exact hx)
  have hy' : y.card < ℵ_ v := lt_ord.1 (by rw [← Om_eq_ord hv]; exact hy)
  set m : Cardinal.{u} := max ℵ₀ (max x.card y.card) with hm
  have h0 : ℵ₀ < ℵ_ v := by
    rw [← aleph_zero]; exact aleph_lt_aleph.2 (pos_iff_ne_zero.2 hv)
  have hmlt : m < ℵ_ v := max_lt h0 (max_lt hx' hy')
  have hreg : (Order.succ m).IsRegular := isRegular_succ (le_max_left _ _)
  have hunc : ℵ₀ < Order.succ m := lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ m)
  have hle : Order.succ m ≤ ℵ_ v := Order.succ_le_of_lt hmlt
  have hxm : x < (Order.succ m).ord :=
    lt_ord.2 (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) (Order.lt_succ m))
  have hym : y < (Order.succ m).ord :=
    lt_ord.2 (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) (Order.lt_succ m))
  calc veblen x y < (Order.succ m).ord := veblen_lt_ord_of_isRegular hreg hunc x hxm y hym
    _ ≤ (ℵ_ v).ord := ord_le_ord.2 hle
    _ = Om v := (Om_eq_ord hv).symm

/-! ## The hypothesis -/

/-- A strictly increasing sequence of weakly inaccessible cardinals `I 0 < I 1 < ⋯`. -/
structure InaccSeq : Type (u + 1) where
  /-- The `n`-th inaccessible. -/
  I : ℕ → Ordinal.{u}
  strictMono : StrictMono I
  /-- Each `I n` is a regular cardinal. -/
  isRegular : ∀ n, (I n).card.IsRegular
  /-- Each `I n` is uncountable. -/
  uncountable : ∀ n, ℵ₀ < (I n).card
  /-- Each `I n` is a fixed point of `Ω`: a limit cardinal. -/
  fix : ∀ n, Om (I n) = I n

namespace InaccSeq

variable (S : InaccSeq.{u})

/-- `I_ω = sup_n I_n`. -/
noncomputable def Iw : Ordinal.{u} := ⨆ n, S.I n

theorem I_ne_zero (n : ℕ) : S.I n ≠ 0 := by
  intro h
  have := S.uncountable n
  rw [h, card_zero] at this
  exact absurd this (not_lt.2 zero_le)

theorem bddAbove_I : BddAbove (range S.I) := Ordinal.bddAbove_of_small

theorem I_le_Iw (n : ℕ) : S.I n ≤ S.Iw := le_ciSup S.bddAbove_I n

theorem I_lt_Iw (n : ℕ) : S.I n < S.Iw :=
  lt_of_lt_of_le (S.strictMono (Nat.lt_succ_self n)) (S.I_le_Iw (n + 1))

theorem Iw_ne_zero : S.Iw ≠ 0 := (lt_of_le_of_lt zero_le (S.I_lt_Iw 0)).ne'

/-- `I_ω` is a fixed point of `Ω`. -/
theorem Om_Iw : Om S.Iw = S.Iw := by
  rw [Om_of_ne_zero S.Iw_ne_zero, Iw, isNormal_omega.map_iSup S.bddAbove_I]
  congr 1
  funext n
  rw [← Om_of_ne_zero (S.I_ne_zero n), S.fix n]

/-- `I n` is the ordinal of its cardinality. -/
theorem I_eq_ord (n : ℕ) : S.I n = (S.I n).card.ord := by
  have h : S.I n = ω_ (S.I n) := by rw [← Om_of_ne_zero (S.I_ne_zero n), S.fix n]
  calc S.I n = ω_ (S.I n) := h
    _ = (ℵ_ (S.I n)).ord := (ord_aleph _).symm
    _ = (ω_ (S.I n)).card.ord := by rw [card_omega]
    _ = (S.I n).card.ord := by rw [← h]

/-- The class `R` of collapsing subscripts. -/
def InR (κ : Ordinal.{u}) : Prop :=
  (∃ n, κ = S.I n) ∨ ∃ s, κ = Om (s + 1)

/-- A subscript in `R` is an uncountable regular cardinal. -/
theorem InR.regular {κ : Ordinal.{u}} (h : S.InR κ) :
    κ.card.IsRegular ∧ ℵ₀ < κ.card ∧ κ = κ.card.ord := by
  rcases h with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨S.isRegular n, S.uncountable n, S.I_eq_ord n⟩
  · have hs : s + 1 ≠ 0 := by
      rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot s
    refine ⟨?_, aleph0_lt_card_Om hs, ?_⟩
    · rw [card_Om hs]; exact isRegular_aleph_add_one s
    · rw [card_Om hs, Om_eq_ord hs]

theorem InR.ne_zero {κ : Ordinal.{u}} (h : S.InR κ) : κ ≠ 0 := by
  intro h0
  have := (h.regular S).2.1
  rw [h0, card_zero] at this
  exact absurd this (not_lt.2 zero_le)

/-- A subscript in `R` is strongly critical. -/
theorem InR.SC {κ : Ordinal.{u}} (h : S.InR κ) : SC κ := by
  rcases h with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · rw [← S.fix n]; exact SC_Om (S.I_ne_zero n)
  · exact SC_Om (by rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot s)

end InaccSeq

end Googology.Notation.InaccPsi
