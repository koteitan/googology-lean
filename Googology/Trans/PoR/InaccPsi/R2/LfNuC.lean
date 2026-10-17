import Googology.Trans.PoR.InaccPsi.R2.BrLs13
import Googology.Trans.PoR.InaccPsi.R2.EpsLY
import Googology.Trans.PoR.InaccPsi.R2.NestK

/-!
# The points named by the bridge lie below `ν_C`

The bridge (`R2.BrLs13`) names `υ_{1+η} = ψ_{Ω₁}(Ω_ω + θ·η)` for `η = ω·m + n` and `υ_{ω²} =
ψ_{Ω₁}(Ω_ω + θ·ω²)`, `θ = ψ_{Ω₂}(Ω_ω)`, for every InaccPsi sequence `S`.  `R2.EpsLY` places the first
non-standard pair `ρ_L <₂ ν_C` with `Λ_{ε_{x+2}} + ω² ≤ L`.  So:

* `lfPsi_lt_nuC`, `lfPsi_ww_lt_nuC` (**`ψ_{Ω₁}(Ω_ω + θ·η) < ν_C` for `η = ω·m + n` and `η = ω²`**: the
  first InaccPsi lower bounds of `ν_C` in Lean);
* `lfPsi_lt_top2`, `lfPsi_ww_lt_top2` (**every `2`-nest has its top above `ψ_{Ω₁}(Ω_ω + θ·η)`**, `η ≤ ω²`,
  since `ν_C = T₂`).

So no `2`-nest is realized below a point the bridge names, and CAP at such a point cannot bound `ν_C`:
an upper bound of `ν_C` needs names past `υ_{ω²}`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

theorem lfIdx_lt_ww (m n : ℕ) : 1 + (ω * (m : Ordinal.{0}) + n) < ω * ω := by
  have hn : (n : Ordinal.{0}) < ω := natCast_lt_omega0 n
  have hm1 : (m : Ordinal.{0}) + 1 < ω := by exact_mod_cast natCast_lt_omega0 (m + 1)
  have h2 : ω * (m : Ordinal.{0}) + ω ≤ ω * ω := by
    rw [← mul_add_one]
    exact mul_le_mul_right hm1.le _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, mul_zero, zero_add]
    have : (1 : Ordinal.{0}) + n < ω := by exact_mod_cast natCast_lt_omega0 (1 + n)
    exact this.trans_le (le_mul_left _ omega0_pos)
  · rw [← add_assoc, one_add_of_omega0_le (le_mul_left _ (by exact_mod_cast hm))]
    exact lt_of_lt_of_le ((add_lt_add_iff_left _).2 hn) h2

/-- `υ_ι < ν_C` for every `ι ≤ ω²`. -/
theorem lfUps_lt_nuC {ι : Ordinal.{0}} (hι : ι ≤ ω * ω) : upsilon ι < nuC := by
  obtain ⟨L, -, -, -, hL, -, -, hLν, -⟩ := nuC_boundYw
  exact lt_of_le_of_lt (upsilon_normal.strictMono.monotone (hι.trans (le_add_self.trans hL))) hLν

/-- **`ψ_{Ω₁}(Ω_ω + θ·(ω·m + n)) < ν_C`**. -/
theorem lfPsi_lt_nuC (S : InaccSeq.{0}) (m n : ℕ) :
    S.psi (ConjT.Aη S (ω * m + n)) (Om 1) < nuC := by
  rw [← ups_eq S m n]
  exact lfUps_lt_nuC (lfIdx_lt_ww m n).le

/-- **`ψ_{Ω₁}(Ω_ω + θ·ω²) < ν_C`**. -/
theorem lfPsi_ww_lt_nuC (S : InaccSeq.{0}) : S.psi (ConjT.Aη S (ω * ω)) (Om 1) < nuC := by
  rw [← ups_eq_ww S]
  exact lfUps_lt_nuC le_rfl

/-- **Every `2`-nest has its top above `ψ_{Ω₁}(Ω_ω + θ·(ω·m + n))`.** -/
theorem lfPsi_lt_top2 (S : InaccSeq.{0}) (m n : ℕ) {a b : ℕ → Ordinal.{0}} (hN : NestSeq 2 a b) :
    S.psi (ConjT.Aη S (ω * m + n)) (Om 1) < b 0 :=
  lt_of_lt_of_le (lfPsi_lt_nuC S m n) (Tk_two ▸ Tk_le hN)

/-- **Every `2`-nest has its top above `ψ_{Ω₁}(Ω_ω + θ·ω²)`.** -/
theorem lfPsi_ww_lt_top2 (S : InaccSeq.{0}) {a b : ℕ → Ordinal.{0}} (hN : NestSeq 2 a b) :
    S.psi (ConjT.Aη S (ω * ω)) (Om 1) < b 0 :=
  lt_of_lt_of_le (lfPsi_ww_lt_nuC S) (Tk_two ▸ Tk_le hN)

end Googology.Trans.PoR.InaccPsi.R2.Br
