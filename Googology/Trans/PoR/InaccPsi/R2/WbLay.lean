import Googology.Trans.PoR.InaccPsi.R2.WbCode
import Googology.Trans.PoR.InaccPsi.R2.VnTopK

/-!
# The layers of a block at EVERY exponent `E` (no bound `Y₃`): past the `Y₃` wall

`W = Ω₂`, `W^E = Le.leWe E`, `T_E(β) = ψ_{Ω₂}(β + W^E)` (`Le.leTe`), `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(β + W^E·K_j)`
(`Le.leKe S E β`).

`Uj.ujKe_sup`, `Uj.ujTe_ge`, `Uj.ujTe_gt` ask **`E + 1 < Y₃`** (used only to read the codes modulo `Y₃` in
`Uj.ujPsi2_le`) and **`E` a level-2 code `Ug.UgC S 2 Q`** for every strongly critical `Q > K_1` (`hEL`).
`Vk.vkKe_sup` dropped the bound and asks `hEL` with the codes `Vk.VkA 2 Q`.  Here `hEL` is **derived** from the own
condition `E ∈ Cl(β + W^E, T_E(β))` (`Wb.wbA_own`), so the port differs from `Vk.vkKe_sup` only by **dropping `hEL`**
and from `Uj.ujKe_sup` by **dropping `E + 1 < Y₃` and `hEL`**; the conclusions are the same.

* `wbKe_sup` (**`T_{E+1}(β) = sup_j K_j` for every own `E`**, `W^{E+1} ∣ β`), `wbTe_ge`, `wbTe_gt`
  (**`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`**);
* `wbKe_sup_uj` (the old `Uj.ujKe_sup` is the case `E + 1 < Y₃`: its extra hypotheses are not used);
* `wbTe_gt_it`, `wbKe_sup_it` (**unconditional instances past the wall**: at the base `0` and the exponents
  `E = y^{(k)}_{n+1}`, the iterates of `ψ_{Ω_{k+3}}` from `0`, for every `k`, `n`; `k = 1`, `n = 0` is `E = ψ₄(0) =
  Γ_{Ω₃+1}`), `wbTe_gt_Om` (**the exponent `E = Ω_{k+3}` at the base `0`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Wb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

section Layers

variable {E β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (E + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hEC : E ∈ S.CSet (β + leWe E) (S.psi (β + leWe E) (Om (1 + 1))))

include hβown hEC

omit hβown in
/-- The code property of an own exponent over every `Q > K_1` (the hypothesis `hEL` of `Vk.vkKe_sup`). -/
theorem wbEL : ∀ Q, SC Q → leKe S E β 1 < Q → VkA (1 + 1) Q E := by
  intro Q _ hK1
  refine wbA_own hEC (le_trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1 hK1.le)
  calc leWe E = leWe E * 1 := (mul_one _).symm
    _ ≤ leWe E * Om 1 := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le

/-- **`T_{E+1}(β) = sup_j K_j` for every own exponent `E`** (`W^{E+1} ∣ β`): `Vk.vkKe_sup` without `hEL`. -/
theorem wbKe_sup (hβd : leWe (E + 1) ∣ β) {x : Ordinal.{0}}
    (hx : x < leTe S (E + 1) β) : ∃ j, x < leKe S E β j :=
  vkKe_sup hβown hEC hβd (wbEL hEC) hx

/-- `ψ_{Ω₂}(β + W^E·γ) ≥ T_{E+1}(β)` for `γ ≥ T_{E+1}(β)`, every own `E`. -/
theorem wbTe_ge (hβd : leWe (E + 1) ∣ β) {γ : Ordinal.{0}}
    (hγ : leTe S (E + 1) β ≤ γ) : leTe S (E + 1) β ≤ S.psi (β + leWe E * γ) (Om (1 + 1)) :=
  vkTe_ge hβown hEC hβd (wbEL hEC) hγ

/-- **`γ < ψ_{Ω₂}(β + W^E·γ)` for every `γ < T_{E+1}(β)`, every own `E`** (no bound, no code hypothesis). -/
theorem wbTe_gt (hβd : leWe (E + 1) ∣ β) {γ : Ordinal.{0}}
    (hγ : γ < leTe S (E + 1) β) : γ < S.psi (β + leWe E * γ) (Om (1 + 1)) :=
  vkTe_gt hβown hEC hβd (wbEL hEC) hγ

/-- The old `Uj.ujKe_sup` is the case `E + 1 < Y₃` of `wbKe_sup` (its hypotheses `hEG`, `hEL` are not used). -/
theorem wbKe_sup_uj (hβd : leWe (E + 1) ∣ β) (_hEG : E + 1 < ugY S)
    (_hEL : ∀ Q, SC Q → leKe S E β 1 < Q → UgC S (1 + 1) Q E) {x : Ordinal.{0}}
    (hx : x < leTe S (E + 1) β) : ∃ j, x < leKe S E β j :=
  wbKe_sup hβown hEC hβd hx

end Layers

/-- `Ω_{k+3} ≤ W^{Ω_{k+3}}`-type helper: the base `0` is own for every exponent. -/
theorem wbZero_own (E : Ordinal.{0}) :
    ∀ d, d ≤ leWe (E + 1) → (0 : Ordinal.{0}) ∈ S.CSet (0 + d) (S.psi (0 + d) (Om (1 + 1))) :=
  fun _ _ => CSet.zero_mem _ _

/-- **At the base `0` and every exponent `E = y^{(k)}_{n+1}` (the `(n+1)`-th iterate of `ψ_{Ω_{k+3}}` from `0`)**:
`T_{E+1}(0) = sup_j K_j`.  Unconditional; at `k ≥ 1` these exponents lie above `Ω₃ > Y₃`. -/
theorem wbKe_sup_it (k n : ℕ) {x : Ordinal.{0}}
    (hx : x < leTe S ((fun y => S.psi y (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0 + 1) 0) :
    ∃ j, x < leKe S ((fun y => S.psi y (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) 0 j := by
  set E := (fun y => S.psi y (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0 with hE
  have hEC : E ∈ S.CSet (0 + leWe E) (S.psi (0 + leWe E) (Om (1 + 1))) := by
    rw [zero_add]
    exact Vn.vnIt_mem (s := (k : Ordinal.{0}) + 1 + 1) (Vn.vnOmK3_mem k) (n + 1) _ _ (ujLe_We E)
  exact wbKe_sup (wbZero_own E) hEC (dvd_zero _) hx

/-- **`γ < ψ_{Ω₂}(W^E·γ)` for every `γ < T_{E+1}(0)`, at `E = y^{(k)}_{n+1}`**, for every `k`, `n`. -/
theorem wbTe_gt_it (k n : ℕ) {γ : Ordinal.{0}}
    (hγ : γ < leTe S ((fun y => S.psi y (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0 + 1) 0) :
    γ < S.psi (0 + leWe ((fun y => S.psi y (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))^[n + 1] 0) * γ)
      (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := wbKe_sup_it k n hγ
  exact leKe_gt _ 0 j γ hj

/-- **At the base `0` and the exponent `E = Ω_{k+3}`**: `γ < ψ_{Ω₂}(W^{Ω_{k+3}}·γ)` for every `γ < T_{Ω_{k+3}+1}(0)`. -/
theorem wbTe_gt_Om (k : ℕ) {γ : Ordinal.{0}}
    (hγ : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 1) 0) :
    γ < S.psi (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) * γ) (Om (1 + 1)) :=
  wbTe_gt (wbZero_own _) (Vn.vnOmK3_mem k _ _) (dvd_zero _) hγ

#print axioms wbEL
#print axioms wbKe_sup
#print axioms wbTe_ge
#print axioms wbTe_gt
#print axioms wbKe_sup_uj
#print axioms wbKe_sup_it
#print axioms wbTe_gt_it
#print axioms wbTe_gt_Om

end Googology.Trans.PoR.InaccPsi.R2.Wb
