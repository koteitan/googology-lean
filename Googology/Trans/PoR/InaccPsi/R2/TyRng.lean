import Googology.Trans.PoR.InaccPsi.R2.TvRoad
import Googology.Trans.PoR.InaccPsi.R2.TkBlk

/-!
# The restarts of a window below `L(k)` and of the long region are Range restarts with `Λ_B⁺ ≤ λ`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

A *window* for `L(k)` is an ordinal `w` with `υ(Λ_B⁺) ≤ w < L(k)` and no `L(j)` in `(w, L(k))`.  Every restart `ν`
with `w < ρ_ν < L(k)` is a Range restart with `Λ_B⁺ ≤ ν` (`tyWin_rng`); so is every restart of the long region
`L(k) < ρ_ν < L(k+1)` (`tyInner_rng`).  Under the road hypotheses `hU`, `hL` (UPPER and LOWER at the Range
restarts with `RzRest`) their reaches are exact: `ρ_ν ≤₁ r(ν)` and every `≤₁`-successor of `ρ_ν` is `≤ r(ν)`
(`tyInner_exact`, `tyWin_exact`).  So the inner restarts of the long region and the supply restarts never need
ENUM-REACH at a code `≥ P'`: the only restarts in `[B₀, L(ω+1))` with code `≥ P'` are the `L(k)` and `L(ω)`
(`Te.teCode_hi_iff`).

* `TyWin S k w` (the window condition); `tyWin_M` (`w = υ(Λ_B⁺)` at `m* = L(0)`), `tyWin_L` (`w = L(n)` at
  `L(n+1)`);
* `tyWin_rng`, `tyInner_rng`, `tyInner_exact`, `tyWin_exact`.

No new axiom.  New definition: `TyWin` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ty

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **A window for `L(k)`**: `υ(Λ_B⁺) ≤ w < L(k)` and every `L(j) < L(k)` is `≤ w`. -/
def TyWin (S : InaccSeq.{0}) (k : ℕ) (w : Ordinal.{0}) : Prop :=
  upsilon Rz.rzLam ≤ w ∧ w < Nc.ncL S (k : Ordinal.{0}) ∧
    ∀ j : ℕ, Nc.ncL S (j : Ordinal.{0}) < Nc.ncL S (k : Ordinal.{0}) → Nc.ncL S (j : Ordinal.{0}) ≤ w

/-- `υ(Λ_B⁺) < L(k)`. -/
theorem tyRz_lt_L (k : ℕ) : upsilon Rz.rzLam < Nc.ncL S (k : Ordinal.{0}) :=
  ((Ph.phFr_order (S := S) 0).1.1).trans_le (Pp.ppL_mono (zero_le : (0 : Ordinal.{0}) ≤ (k : Ordinal.{0})))

/-- `Λ_B⁺ < L(k)` (as indices). -/
theorem tyRzIdx_lt_L (k : ℕ) : Rz.rzLam < Nc.ncL S (k : Ordinal.{0}) := by
  have h := tyRz_lt_L (S := S) k
  rw [← Te.teUps_L (S := S) k] at h
  exact upsilon_normal.strictMono.lt_iff_lt.1 h

/-- **The window `υ(Λ_B⁺)` for `m* = L(0)`.** -/
theorem tyWin_M : TyWin S 0 (upsilon Rz.rzLam) := by
  refine ⟨le_rfl, by simpa using tyRz_lt_L (S := S) 0, fun j hj => ?_⟩
  exact absurd hj (not_lt.2 (by simpa using Pp.ppL_mono (S := S) (zero_le : (0 : Ordinal.{0}) ≤ (j : Ordinal.{0}))))

/-- **The window `L(n)` for `L(n+1)`.** -/
theorem tyWin_L (n : ℕ) : TyWin S (n + 1) (Nc.ncL S (n : Ordinal.{0})) := by
  refine ⟨(tyRz_lt_L n).le, Te.teL_lt_succ n, fun j hj => ?_⟩
  apply Pp.ppL_mono
  have : j ≤ n := by
    by_contra hc
    push Not at hc
    exact absurd hj (not_lt.2 (Pp.ppL_mono (by exact_mod_cast hc)))
  exact_mod_cast this

/-- **A restart of a window below `L(k)` is a Range restart with `Λ_B⁺ ≤ ν`.** -/
theorem tyWin_rng {k : ℕ} {w ν : Ordinal.{0}} (hw : TyWin S k w) (hν : IsRestartIdx ν)
    (h1 : w < upsilon ν) (h2 : upsilon ν < Nc.ncL S (k : Ordinal.{0})) : CdRange S ν ∧ Rz.RzRest ν := by
  have hm := upsilon_normal.strictMono
  have hR : Rz.rzLam < ν := hm.lt_iff_lt.1 (hw.1.trans_lt h1)
  have hB : cdB0 ≤ ν := (Rz.rzB0_lt.trans hR).le
  have hkw : Nc.ncL S (k : Ordinal.{0}) < Nc.ncL S ω := Te.teL_lt_omega k
  have hlt : upsilon ν < Nc.ncL S (ω + 1) := (h2.trans hkw).trans (Qq.qqL_lt_succ S)
  refine ⟨(Te.teRange_iff hν hB hlt).2 ⟨fun j hj => ?_, fun hj => ?_⟩, Or.inl hR.le⟩
  · rcases lt_or_ge (Nc.ncL S (j : Ordinal.{0})) (Nc.ncL S (k : Ordinal.{0})) with hjk | hjk
    · exact absurd (hj ▸ hw.2.2 j hjk) (not_le.2 h1)
    · exact absurd (hj ▸ h2) (not_lt.2 hjk)
  · exact absurd (hj ▸ h2) (not_lt.2 hkw.le)

/-- **A restart of the long region `L(k) < ρ_ν < L(k+1)` is a Range restart with `Λ_B⁺ ≤ ν`.** -/
theorem tyInner_rng {k : ℕ} {ν : Ordinal.{0}} (hν : IsRestartIdx ν)
    (h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon ν) (h2 : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    CdRange S ν ∧ Rz.RzRest ν := by
  refine ⟨Tk.tkL_rng k ν hν h1 h2, Or.inl ?_⟩
  have h := (tyRz_lt_L (S := S) k).trans h1
  exact (upsilon_normal.strictMono.lt_iff_lt.1 h).le

/-- **The exact reach of an inner restart of the long region** (no ENUM-REACH at a code `≥ P'`): under UPPER and
LOWER at the Range restarts with `RzRest`, `ρ_ν ≤₁ r(ν)` and every `≤₁`-successor of `ρ_ν` is `≤ r(ν)`. -/
theorem tyInner_exact (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {ν : Ordinal.{0}} (hν : IsRestartIdx ν)
    (h1 : Nc.ncL S (k : Ordinal.{0}) < upsilon ν) (h2 : upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    le1 (upsilon ν) (cdR S ν) ∧ ∀ g, le1 (upsilon ν) g → g ≤ cdR S ν := by
  obtain ⟨hr, hz⟩ := tyInner_rng hν h1 h2
  exact ⟨hL ν hr hz, cdUpper_iff.1 (hU ν hr hz)⟩

/-- **The exact reach of a restart of a window below `L(k)`.** -/
theorem tyWin_exact (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) {k : ℕ} {w ν : Ordinal.{0}} (hw : TyWin S k w)
    (hν : IsRestartIdx ν) (h1 : w < upsilon ν) (h2 : upsilon ν < Nc.ncL S (k : Ordinal.{0})) :
    le1 (upsilon ν) (cdR S ν) ∧ ∀ g, le1 (upsilon ν) g → g ≤ cdR S ν := by
  obtain ⟨hr, hz⟩ := tyWin_rng hw hν h1 h2
  exact ⟨hL ν hr hz, cdUpper_iff.1 (hU ν hr hz)⟩

end Googology.Trans.PoR.InaccPsi.R2.Ty
