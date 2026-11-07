import Googology.Trans.PoR.InaccPsi.R2.QfZeta
import Googology.Trans.PoR.InaccPsi.R2.HcLImg

/-!
# QfSep: THE SEPARATION BELOW A VEBLEN POINT `φ(A, B)` OVER A BASE `u`

For a strongly critical base `u < Ω₁` and `X = φ(A, B) ∈ (u, Γ_{u+1})` (`1 ≤ A`, `B < X`), and a lower bound `L ≥ u,
A, B` above every point `φ(A, b)`, `b < B`, with `logend(b) ≥ logend(B)`: no `ε`-number `w ∈ (L, X)` has
`w ≤₁ luL(w, A) + logend(B)` in `R₁⁺`.  The reach of `w = φ(q, b)` is `luL(w, q) + logend(b)` (`Qf.qf_lh`): a lower
level `q < A` gives less than `luL(w, q) + w ≤ luL(w, A)` (`qf_luL_gap`); the level `A` has `b < B` and, above `L`,
`logend(b) < logend(B)`; a higher level puts `w` among the fixed points of `φ(A, ·)` below `X`, hence below `B ≤ L`.

* `qf_luL_gap` (`luL(w, q) + w ≤ luL(w, q')` for `1 ≤ q < q' < w`), `qf_lg_lt_last` (**`b < B₁ + ω^g`,
  `ω^g ∣ B₁`, `g ≤ logend(b)` ⇒ `b ≤ B₁`**), `qf_sep` (**THE SEPARATION**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Hc

/-- **`luL(w, q) + w ≤ luL(w, q')`** for an `ε`-number `w` and `1 ≤ q < q' < w`. -/
theorem qf_luL_gap {w q q' : Ordinal.{0}} (hw : InE w) (hq1 : 1 ≤ q) (hqq : q < q') (hq'w : q' < w) :
    luL w q + w ≤ luL w q' := by
  have hqw : q < w := hqq.trans hq'w
  rw [hc_luL_dec hw hq1 hqw, hc_luL_dec hw (hq1.trans hqq.le) hq'w]
  have he : hcE q + w = w :=
    add_of_omega0_opow_le (b := w) (by rw [show ω ^ w = w from hw]; exact (hcE_le q).trans_lt hqw)
      (by rw [show ω ^ w = w from hw])
  rw [add_assoc, he, ← mul_add_one]
  refine le_trans ?_ le_self_add
  refine mul_le_mul_right ?_ w
  rw [add_assoc]
  exact (add_le_add_iff_left 1).2 (Order.add_one_le_of_lt hqq)

/-- **Below `B₁ + ω^g` (`ω^g ∣ B₁`), an ordinal with `logend ≥ g` is `≤ B₁`.** -/
theorem qf_lg_lt_last {b B₁ g : Ordinal.{0}} (hb : b < B₁ + ω ^ g) (hg : g ≤ lg b) : b ≤ B₁ := by
  by_contra hc
  push Not at hc
  obtain ⟨t, rfl⟩ := exists_add_of_le hc.le
  have ht0 : t ≠ 0 := by rintro rfl; rw [add_zero] at hc; exact lt_irrefl _ hc
  have htg : t < ω ^ g := (add_lt_add_iff_left B₁).1 hb
  rw [lu_lg_add_right ht0] at hg
  have h1 : ω ^ g ≤ t := le_of_dvd ht0 ((le_lg_iff ht0 g).1 hg)
  exact absurd htg (not_lt.2 h1)

section Sep

variable {u : Ordinal.{0}} (hu : SC u) (hu1 : u < Om1)
include hu hu1

/-- **THE SEPARATION BELOW `φ(A, B)`**: no `ε`-number `w ∈ (L, φ(A, B))` has `w ≤₁ luL(w, A) + logend(B)`. -/
theorem qf_sep {A B L : Ordinal.{0}} (hA1 : 1 ≤ A) (hXG : veblen A B < lgG u) (huL : u ≤ L) (hBL : B ≤ L)
    (hAL : A ≤ L) (hL2 : ∀ b, b < B → lg B ≤ lg b → veblen A b ≤ L) :
    ∀ w, InE w → L < w → w < veblen A B → ¬ le1R w (luL w A + lg B) := by
  intro w hw hLw hwX hle
  have huw : u < w := huL.trans_lt hLw
  obtain ⟨q, b, hq1, hqw, hbw, hqb⟩ := qf_dec hu hu1 hw huw (hwX.trans hXG)
  subst hqb
  have hlh := qf_lh hu hu1 hq1 huw (hwX.trans hXG) hbw
  have hR := hlh.2 _ hle
  have hlgb : lg b < veblen q b := by
    rcases eq_or_ne b 0 with rfl | hb0
    · have : lg (0 : Ordinal.{0}) = 0 := by unfold lg; simp
      rw [this]; exact hw.pos
    · exact (lg_le hb0).trans_lt hbw
  rcases lt_trichotomy q A with hqA | rfl | hAq
  · have hAw : A < veblen q b := hAL.trans_lt hLw
    have h1 : luL (veblen q b) q + lg b < luL (veblen q b) q + veblen q b := (add_lt_add_iff_left _).2 hlgb
    have h2 := qf_luL_gap hw hq1 hqA hAw
    exact absurd (hR.trans_lt (h1.trans_le (h2.trans le_self_add))) (lt_irrefl _)
  · have hbB : b < B := (veblen_lt_veblen_iff_right).1 hwX
    rcases lt_or_ge (lg b) (lg B) with hlt | hge
    · exact absurd (hR.trans_lt ((add_lt_add_iff_left _).2 hlt)) (lt_irrefl _)
    · exact absurd ((hL2 b hbB hge)) (not_le.2 hLw)
  · have hfix : veblen A (veblen q b) = veblen q b := veblen_veblen_of_lt hAq b
    rw [← hfix] at hwX
    have : veblen q b < B := (veblen_lt_veblen_iff_right).1 hwX
    exact absurd (this.trans_le hBL) (not_lt.2 hLw.le)

end Sep

end Googology.Trans.PoR.InaccPsi.R2.Qf
