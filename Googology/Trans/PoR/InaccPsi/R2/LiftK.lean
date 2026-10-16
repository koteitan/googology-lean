import Googology.Trans.PoR.InaccPsi.R2.NestK

/-!
# LIFT-0 and Theorem O^C at every level of `R₂^C`

With `C09_nestk` (a `k`-nest exists for every `k`, [C09] Lemma 15.11 and Theorem 14.10 (1)), the
results of `R2.NestK` hold for every level `k = m + 1` without hypothesis:

* `Tk_lt_Om1_all` (`T_k < Ω₁`), `Tk_lt_succ_all` (`T₁ < T₂ < T₃ < ⋯`), `Tk_strictMono`;
* `liftK` (**the first block of level `k`**: `T_k` has exactly one `<₂`-predecessor `x_k`, which has no
  other `<₂`-successor; `U_k = {u ≤ T_k : u ≤₁ T_k} = Pred₁(x_k) ∪ {x_k, T_k}`; no member of `Pred₁(x_k)`
  is a `<₂`-left end or a `<₂`-right end; every member of `U_k` has reach `T_k`; `Pred₁(x_k)` is cofinal
  in `x_k` and every proper initial segment of it is finite (**Theorem O^C**: order type `ω`; in the
  notation of the InaccPsi docs, not a Lean statement, `x_k = υ^k_ω`, `T_k = υ^k_{ω+1}`);
  `[0, T_k] ⊆ Core(R₂^C)`; `T_{k-1} < s` for every positive member `s ≤ x_k` of `U_k` (and
  `T_{k-1} < T_k`), so `T_{k-1} < s_k = min U_k`);
* `liftK_two` (at `k = 2` the top is `ν_C`; it does not use `C09_nestk`).

`C09_nestk` is an axiom of `R2.CitedCore`; its case `k = 2` is the theorem `C09_nest` of `R2.NestC`.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem nestEx_all (k : ℕ) : NestEx k := C09_nestk k

/-- **`T_k < Ω₁`** for every `k ≥ 1`. -/
theorem Tk_lt_Om1_all {k : ℕ} (hk : 1 ≤ k) : Tk k < Om1 := Tk_lt_Om1 hk (nestEx_all k)

/-- **`T_{m+1} < T_{m+2}`**. -/
theorem Tk_lt_succ_all (m : ℕ) : Tk (m + 1) < Tk (m + 2) := Tk_lt_succ (nestEx_all (m + 2))

/-- **`T₁ < T₂ < T₃ < ⋯`**. -/
theorem Tk_strictMono : StrictMono (fun m : ℕ => Tk (m + 1)) :=
  strictMono_nat_of_lt_succ (fun m => Tk_lt_succ_all m)

/-- **LIFT-0 and Theorem O^C at level `k = m + 1`** in `R₂^C`. -/
theorem liftK (m : ℕ) : ∃ x, x < Tk (m + 1) ∧ le2 x (Tk (m + 1)) ∧ Tk (m + 1) < Om1 ∧
    (∀ c < Tk (m + 1), le2 c (Tk (m + 1)) → c = x) ∧
    (∀ w, x < w → le2 x w → w = Tk (m + 1)) ∧
    (∀ u, (u ≤ Tk (m + 1) ∧ le1 u (Tk (m + 1))) ↔ ((u < x ∧ le1 u x) ∨ u = x ∨ u = Tk (m + 1))) ∧
    (∀ u < x, le1 u x → (∀ w, u < w → ¬ le2 u w) ∧ (∀ c < u, ¬ le2 c u)) ∧
    (∀ u ≤ Tk (m + 1), le1 u (Tk (m + 1)) → IsReach R2C u (Tk (m + 1))) ∧
    (∀ z < x, ∃ y, z < y ∧ y < x ∧ le1 y x) ∧
    (∀ s < x, Set.Finite {u | u < s ∧ le1 u x}) ∧
    Set.Iic (Tk (m + 1)) ⊆ Core R2C ∧
    (1 ≤ m → ∀ s, 0 < s → s ≤ x → le1 s (Tk (m + 1)) → Tk m < s) := by
  have h1 := Tk_lt_Om1_all (k := m + 1) (by omega)
  obtain ⟨a, b, hN, hT⟩ := Tk_attained h1
  have hcore := Tk_core (by omega) hN hT
  rw [← hT] at h1 hcore ⊢
  have hx1 := le2_le1 (lv_x2 hN)
  refine ⟨a 0, lv_xT hN, lv_x2 hN, h1, pred_T hN hT, succ_x hN hT, U_shape hN hT,
    fun u hu hu1 => ⟨noLeft_below hN hT hu (le1_trans hu1 hx1),
      noRight_U hN hT (hu.trans (lv_xT hN)) (le1_trans hu1 hx1)⟩,
    fun u hu hu1 => reach_U hN hT hu hu1, pred1_cof (lv_x2 hN) (lv_xT hN), oC hN hT, hcore,
    fun hm s hs0 hsx hs => Tk_lt_mem hN hT hm hs0 hsx hs⟩

/-- At `k = 2` the top of the first block is `ν_C`. -/
theorem liftK_two : Tk 2 = nuC := Tk_two

end Googology.Trans.PoR.InaccPsi.R2
