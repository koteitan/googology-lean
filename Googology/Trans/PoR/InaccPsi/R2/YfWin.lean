import Googology.Trans.PoR.InaccPsi.R2.YfCell
import Googology.Trans.PoR.InaccPsi.R2.PpRst
import Googology.Trans.PoR.InaccPsi.R2.LwName

/-!
# The cell transport does not reach the windows (refute-first result)

The base data of `R2.YfCell` (`Good O` at every block boundary up to `λ₀ + ω²`) say in particular that nothing
below `υ_{λ₀+ω²}` is `≤₁` a point `≥ υ_{λ₀+ω²}` (`Yf.yfBase_noCross`).  A long `≤₁` from below therefore kills
them:

* `yfNoBase_cross`: if `c < υ_{λ₀+ω²}`, `λ₁ > λ₀` a restart index and `c ≤₁ ρ_{λ₁}`, no `O` has the base data at
  `λ₀`;
* `yfNoBase_win` (**windows**): if `L(k) ≤₁ L(k+1)`, then no restart index `λ₀` with `L(k) ≤ ρ_{λ₀} < L(k+1)`
  (the base `b_k` of the window `W_k` and every restart of `W_k`) carries the base data;
* `yfNoBase_top` (**top window**): the same with `L(ω) ≤₁ L(ω+1)` for `L(ω) ≤ ρ_{λ₀} < L(ω+1)`.

So under the relations of the natural target (`L(k) ≤₁ L(k+1)`, `L(ω) ≤₁ L(ω+1)`) the transport theorem
`Yf.yfCell_UV` is vacuous inside the windows: `skWinA` / `skWinL` / `skTopA` / `skTopL` need a block induction
relative to the long reach of `L(k)`, not the one of `R2.YfRel`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- **A long `≤₁` from below kills the base data.** -/
theorem yfNoBase_cross {O : Ordinal.{0} → Ordinal.{0}} {l0 l1 c : Ordinal.{0}} (hl0 : IsRestartIdx l0)
    (hl1 : IsRestartIdx l1) (h01 : l0 < l1) (hc : c < upsilon (l0 + ω * ω)) (hx : le1 c (upsilon l1))
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) : False :=
  yfBase_noCross hl0 hG c hc (upsilon l1)
    (upsilon_normal.strictMono.monotone (next_mult (ri_iff.1 hl0).2 (ri_iff.1 hl1).2 h01)) hx

theorem yf_L_succ (S : InaccSeq.{0}) (k : ℕ) :
    IsRestartIdx (iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) =
        upsilon (iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
  ⟨Pp.ppIota_succ_restart k, by rw [Lw.lw_L_eq S]; exact (ups_iota S _).symm⟩

theorem yf_low_of_le {l0 c : Ordinal.{0}} (hc : c ≤ upsilon l0) : c < upsilon (l0 + ω * ω) :=
  hc.trans_lt (upsilon_normal.strictMono (lt_add_of_pos_right l0 (mul_pos omega0_pos omega0_pos)))

/-- **No base data in a window `W_k`** (base included) when `L(k) ≤₁ L(k+1)`. -/
theorem yfNoBase_win (S : InaccSeq.{0}) (k : ℕ)
    (hx : le1 (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})))
    {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0) (h1 : Nc.ncL S (k : Ordinal.{0}) ≤ upsilon l0)
    (h2 : upsilon l0 < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (O : Ordinal.{0} → Ordinal.{0}) :
    ¬ ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η) := by
  intro hG
  obtain ⟨hr, he⟩ := yf_L_succ S k
  rw [he] at hx h2
  exact yfNoBase_cross hl0 hr (upsilon_normal.strictMono.lt_iff_lt.1 h2) (yf_low_of_le h1) hx hG

/-- **No base data in the top window** (base included) when `L(ω) ≤₁ L(ω+1)`. -/
theorem yfNoBase_top (S : InaccSeq.{0}) (hx : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0) (h1 : Nc.ncL S ω ≤ upsilon l0)
    (h2 : upsilon l0 < Nc.ncL S (ω + 1)) (O : Ordinal.{0} → Ordinal.{0}) :
    ¬ ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η) := by
  intro hG
  obtain ⟨hr, he⟩ := Lw.lw_restart_L_omega_succ S
  rw [he] at hx h2
  exact yfNoBase_cross hl0 hr (upsilon_normal.strictMono.lt_iff_lt.1 h2) (yf_low_of_le h1) hx hG

end Googology.Trans.PoR.InaccPsi.R2.Yf
