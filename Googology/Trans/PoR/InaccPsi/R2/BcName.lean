import Googology.Trans.PoR.InaccPsi.R2.BcMap
import Googology.Trans.PoR.InaccPsi.R2.BcOnto
import Googology.Trans.PoR.InaccPsi.R2.QqTc

/-!
# PAIR, (P), (Q) at `(L(ω), L(ω+1))` with the base changes `B_n = bcB S n`

The data of SHIFT (`R2.QqShift`) at `a = L(ω)`, `b = L(ω+1)`, `c_n = L(n+1)` and `B_n = bcB S n`
(the η-base change from `L(n+1)` to `L(ω)`, on `[0, c_{n+1}) = [0, L(n+2))`):

* proved (`BcMap`, `BcOnto`): `B_n` strictly increasing, `B_n x < L(ω+1)`, keeps and reflects the
  graph of `+`, closed range, `B_n = id` on `[0, L(n+1))` (and `B_n(L(n+1)) = L(ω)`,
  `B_n(L(n+2)) = L(ω+1)`), and ONTO-FIN (`bcOnto`: every finite `Y ⊆ [L(ω), L(ω+1))` lies in
  `B_n[[0, L(n+2))]` for every large `n`); `c` monotone, `c_n < L(ω)`, `{c_n}` cofinal in `L(ω)`
  (`QqName`);
* left as hypotheses (section variables, written out):
  (C1) `L(n+2) ≤₁ L(ω)` for every `n`;
  (TC) for every `x < L(n+2)`: `x` has a reach `r < L(n+2)` with `lh(B_n x) = B_n r`, or `x ≤₁ z`
  and `B_n x ≤₁ B_n z` for every `z ∈ [x, L(n+2))` (gives the `≤₁` clause of EMB, `qqLe1_of_reach`);
  (EMB₂) `x ≤₂ y ↔ B_n x ≤₂ B_n y` on `[0, L(n+2))`;
* `bcPair` (**PAIR**) `L(ω) <₂ L(ω+1)`; `bcP` (P); `bcQ` (Q) and `lh(L(ω)) = L(ω+1)` when
  `L(ω) < T_ω`; `bcCap` (CAP at `L(ω)`); `bcNuC_eq`: `ν_C = L(ω+1)` when moreover `L(ω)` is not a
  `τ`-point and `L(ω) ≤ ν_C`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nc

section Data

variable (S : InaccSeq.{0})

/-- `c_n = L(n+1)`. -/
noncomputable def bcC (n : ℕ) : Ordinal.{0} := ncL S (((n + 1 : ℕ)) : Ordinal.{0})

theorem bcC_mono : Monotone (bcC S) := fun _ _ h => Qq.qqL_mono S (Nat.succ_le_succ h)

theorem bcC_lt (n : ℕ) : bcC S n < ncL S Ordinal.omega0 := Qq.qqL_lt_omega S (n + 1)

theorem bcC_cof : ∀ γ < ncL S Ordinal.omega0, ∃ n, γ < bcC S n := by
  intro γ hγ
  obtain ⟨n, hn⟩ := Qq.qqL_cof S γ hγ
  exact ⟨n, hn.trans_le (Qq.qqL_mono S (Nat.le_succ n))⟩

theorem bcB_mono' (n : ℕ) : StrictMonoOn (bcB S n) (Set.Iio (bcC S (n + 1))) := bcB_mono n

theorem bcB_bound' (n : ℕ) : ∀ x < bcC S (n + 1), bcB S n x < ncL S (Ordinal.omega0 + 1) :=
  bcB_bound n

theorem bcB_addIff' (n : ℕ) : ∀ x < bcC S (n + 1), ∀ y < bcC S (n + 1), ∀ z < bcC S (n + 1),
    (x + y = z ↔ bcB S n x + bcB S n y = bcB S n z) := bcB_addIff n

theorem bcB_closed' (n : ℕ) : Closed (bcB S n '' Set.Iio (bcC S (n + 1))) := bcB_closed n

theorem bcB_fix' (n : ℕ) : ∀ x < bcC S n, bcB S n x = x := bcB_fixN n

theorem bcOnto' : ∀ Y : Finset Ordinal.{0},
    (∀ y ∈ Y, ncL S Ordinal.omega0 ≤ y ∧ y < ncL S (Ordinal.omega0 + 1)) → ∀ N, ∃ n, N ≤ n ∧
      ∀ y ∈ Y, ∃ y' < bcC S (n + 1), bcB S n y' = y := bcOnto S

end Data

section Pair

variable (S : InaccSeq.{0})
  (hc1 : ∀ n : ℕ, le1 (bcC S (n + 1)) (ncL S Ordinal.omega0))
  (hTC : ∀ n : ℕ, ∀ x < bcC S (n + 1),
    (∃ r < bcC S (n + 1), IsReach R2C x r ∧ IsReach R2C (bcB S n x) (bcB S n r)) ∨
      (∀ z, x ≤ z → z < bcC S (n + 1) → le1 x z ∧ le1 (bcB S n x) (bcB S n z)))
  (hB2 : ∀ n : ℕ, ∀ x < bcC S (n + 1), ∀ y < bcC S (n + 1),
    (le2 x y ↔ le2 (bcB S n x) (bcB S n y)))

include hTC in
/-- The `≤₁` clause of EMB from (TC). -/
theorem bcB1 : ∀ n : ℕ, ∀ x < bcC S (n + 1), ∀ y < bcC S (n + 1),
    (le1 x y ↔ le1 (bcB S n x) (bcB S n y)) :=
  fun n => Qq.qqLe1_of_reach (bcB_mono' S n) (hTC n)

include hc1 hTC hB2

/-- **PAIR**: `L(ω) <₂ L(ω+1)`. -/
theorem bcPair : ncL S Ordinal.omega0 < ncL S (Ordinal.omega0 + 1) ∧
    le2 (ncL S Ordinal.omega0) (ncL S (Ordinal.omega0 + 1)) :=
  ⟨Qq.qqL_lt_succ S, Qq.qqShift (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S).le
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S)⟩

/-- (P) at `(L(ω), L(ω+1))`. -/
theorem bcP : NcCofPred (ncL S Ordinal.omega0) (ncL S (Ordinal.omega0 + 1)) :=
  Qq.qqShift_P (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S).le
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S)

/-- **(Q)** at `(L(ω), L(ω+1))` and `lh(L(ω)) = L(ω+1)`, when `L(ω) < T_ω`. -/
theorem bcQ (hTw : ncL S Ordinal.omega0 < shTw) :
    ¬ le1 (ncL S Ordinal.omega0) (ncL S (Ordinal.omega0 + 1) + 1) ∧
      IsReach R2C (ncL S Ordinal.omega0) (ncL S (Ordinal.omega0 + 1)) :=
  ⟨Qq.qqQ_succ (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S)
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S) hTw,
   Qq.qqReach (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S)
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S) hTw⟩

/-- **CAP at `L(ω)`**: when `L(ω) < T_ω`, for `g ≥ L(ω)`, `L(ω) ≤₁ g ⇔ g ≤ L(ω+1)`. -/
theorem bcCap (hTw : ncL S Ordinal.omega0 < shTw) {g : Ordinal.{0}}
    (hg : ncL S Ordinal.omega0 ≤ g) :
    le1 (ncL S Ordinal.omega0) g ↔ g ≤ ncL S (Ordinal.omega0 + 1) :=
  Qq.qqCap (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S)
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S) hTw hg

/-- If `L(ω)` is not a `τ`-point and `L(ω) ≤ ν_C`, then `ν_C = L(ω+1)`. -/
theorem bcNuC_eq (hτ : ¬ NcTauPt (ncL S Ordinal.omega0)) (hν : ncL S Ordinal.omega0 ≤ nuC) :
    nuC = ncL S (Ordinal.omega0 + 1) :=
  Qq.qqNu_eq (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S)
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S) hτ hν

/-- The upper bound `ν_C ≤ L(ω+1)` when `L(ω)` is not a `τ`-point. -/
theorem bcNu_le (hτ : ¬ NcTauPt (ncL S Ordinal.omega0)) : nuC ≤ ncL S (Ordinal.omega0 + 1) :=
  Qq.qqNu_le (bcC_mono S) (bcC_lt S) (bcC_cof S) hc1 (Qq.qqL_lt_succ S)
    (bcB_mono' S) (bcB_bound' S) (bcB_addIff' S) (bcB1 S hTC) hB2 (bcB_closed' S)
    (bcB_fix' S) (bcOnto' S) hτ

end Pair

end Googology.Trans.PoR.InaccPsi.R2.Bc
