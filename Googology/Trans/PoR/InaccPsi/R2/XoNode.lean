import Googology.Trans.PoR.InaccPsi.R2.CitedXo
import Googology.Trans.PoR.InaccPsi.R2.XjGap

/-!
# Both subcases of [W07a] Def 6.2 at the levels `B₂ ≤ M < θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`R2.xeVt_trL` (data below a strongly critical `q ≤ α`: the argument is shifted by `α`) and `R2.xoVt_trH` (a strongly
critical `q` with `α ≤ q ≤ d_S(M)`: the argument is kept).

* `xo_dat_ge` (**`q ≤ d_S(B₂ + q)` for every strongly critical countable `q`**), `xoH_wit` (**the hypotheses of
  `R2.xoVt_trH` hold at `M = B₂ + q`** for every strongly critical countable `q ≥ α`), `xoCase_disj` (**the two
  cases exclude each other**: the twin does not contradict `R2.xeVt_trL`), `XoCase`;
* `xoVt_up`, `xoVt_down` (**the two translations at every level `B₂ ≤ M < θ` in either case**, with the argument
  `Ω₁·M + ρ'`, `ρ' = α + ρ` in the low case and `ρ' = ρ` in the high case).

No new axiom (uses `R2.xoVt_trH`, `R2.xeVt_trL`).  New definition: `XoCase` (a predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **`q ≤ d_S(B₂ + q)`** for every strongly critical countable `q` (`(B₂ + q) % Ω₁ = q`, `Ul.ulK_mod`,
`Ul.ulK_lt_W`). -/
theorem xo_dat_ge {q : Ordinal.{0}} (hq : SC q) (hq1 : q < Om1) : q ≤ Vd.vdD S 0 (Uc.ucB + q) := by
  by_contra hlt
  rw [not_le, Vd.vdD_eq] at hlt
  have hK := (Ul.ul_vis hq).1 hlt
  have hK2 := Ul.ulK_mod hq _ hK Om1
  rw [Xj.xj_mod hq1] at hK2
  have h1 : (0 : Ordinal.{0}) < ω := omega0_pos
  have h2 : Om (0 : Ordinal.{0}) < q := by rw [Om_zero]; exact hq.1
  have h3 : q < Om ((0 : Ordinal.{0}) + 1) := by rw [zero_add, ← Rj.rj_Om1]; exact hq1
  exact lt_irrefl _ (Ul.ulK_lt_W h1 hq h2 hK2 h3)

/-- **NON-VACUITY of `R2.xoVt_trH`**: for every strongly critical countable `q ≥ α`, `M = B₂ + q` satisfies
`B₂ ≤ M < θ` and `q ≤ d_S(M)`. -/
theorem xoH_wit {q α : Ordinal.{0}} (hq : SC q) (hq1 : q < Om1) (hαq : α ≤ q) :
    Uc.ucB ≤ Uc.ucB + q ∧ Uc.ucB + q < ConjT.th S ∧ SC q ∧ α ≤ q ∧ q ≤ Vd.vdD S 0 (Uc.ucB + q) :=
  ⟨le_self_add, (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th (hq1.trans (Xe.xe_th S).2.1), hq, hαq, xo_dat_ge hq hq1⟩

/-- **The two cases exclude each other**: no level has both a strongly critical `q₁ ≤ α` with `d_S(M) < q₁` and a
strongly critical `q₂ ≥ α` with `q₂ ≤ d_S(M)`. -/
theorem xoCase_disj {M α q₁ q₂ : Ordinal.{0}} (h1 : q₁ ≤ α ∧ Vd.vdD S 0 M < q₁) (h2 : α ≤ q₂ ∧ q₂ ≤ Vd.vdD S 0 M) :
    False :=
  lt_irrefl _ ((h2.2.trans_lt h1.2).trans_le (h1.1.trans h2.1))

/-- The case hypothesis at a level `B₂ ≤ M < θ`: low (`xeVt_trL`) or high (`xoVt_trH`). -/
def XoCase (S : InaccSeq.{0}) (α M : Ordinal.{0}) : Prop :=
  (∃ q, SC q ∧ q ≤ α ∧ Vd.vdD S 0 M < q) ∨ (∃ q, SC q ∧ α ≤ q ∧ q ≤ Vd.vdD S 0 M)

/-- **`t^α_τ` at every level `B₂ ≤ M < θ`** (either case). -/
theorem xoVt_up {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hc : XoCase S (Dl τ n) M) (hρ1 : ρ < Om1)
    (hT : Om1 * M + ρ ∈ Tset (Dl τ n)) (hlt : vt (Dl τ n) (Om1 * M + ρ) < Dp τ n) :
    ∃ ρ', (ρ' = Dl τ n + ρ ∨ ρ' = ρ) ∧ Om1 * M + ρ' ∈ Tset τ ∧
      vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ') := by
  rcases hc with ⟨q, hq, hqα, hd⟩ | ⟨q, hq, hαq, hqd⟩
  · obtain ⟨h1, h2⟩ := (xeVt_trL (S := S) hτ hτ1 hn hMB hMθ hq hqα hd hρ1).1 hT hlt
    exact ⟨_, Or.inl rfl, h1, h2⟩
  · obtain ⟨h1, h2⟩ := (xoVt_trH (S := S) hτ hτ1 hn hMB hMθ hq hαq hqd hρ1).1 hT hlt
    exact ⟨_, Or.inr rfl, h1, h2⟩

/-- **`t^τ_α` at every level `B₂ ≤ M < θ`** (either case): from `Ω₁·M + ρ' ∈ Tᵗ` with `ρ' = α + ρ` (low case) or
`ρ' = ρ` (high case). -/
theorem xoVt_down {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hMB : Uc.ucB ≤ M) (hMθ : M < ConjT.th S) (hρ1 : ρ < Om1) :
    ((∃ q, SC q ∧ q ≤ Dl τ n ∧ Vd.vdD S 0 M < q) →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) ∧
    ((∃ q, SC q ∧ Dl τ n ≤ q ∧ q ≤ Vd.vdD S 0 M) →
      Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ)) :=
  ⟨fun ⟨_, hq, hqα, hd⟩ => (xeVt_trL (S := S) hτ hτ1 hn hMB hMθ hq hqα hd hρ1).2,
    fun ⟨_, hq, hαq, hqd⟩ => (xoVt_trH (S := S) hτ hτ1 hn hMB hMθ hq hαq hqd hρ1).2⟩

end Googology.Trans.PoR.InaccPsi.R2.Xo
