import Googology.Trans.PoR.InaccPsi.R2.VbReach
import Googology.Trans.PoR.InaccPsi.R2.UgPart

/-!
# Division by powers of `ω` inside `Cl(a, b)`, and the parts of a member of the domain `D`

`Cl(a, b) = S.CSet a b`, `D = Vb.VbD S λ` (members of `H_λ ∩ Cl(Ω_ω, θ)` below `Ω_ω`), `W^g = Ω₂^g` (`leWe g`),
`log_W = Sg.sgLW`.

* `vhC_div` (**`Cl(a, b)` is closed under the division by `ω^p`**): for every member `w` and every ordinal `p`,
  `ω^p·(w / ω^p)` and `w mod ω^p` are members, and `w / ω^p` is a member when `p` is;
* `vhD_parts` (**the `W`-parts of a member of `D`**): for `x ∈ D`, `0 < x`, the exponent `log_W x` and the tail
  `x mod W^{log_W x}` are in `D`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

theorem vhC_opow {a b z : Ordinal.{0}} (hz : z ∈ S.CSet a b) : ω ^ z ∈ S.CSet a b := by
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) hz; rwa [veblen_zero_apply] at this

/-- **`Cl(a, b)` is closed under the division by `ω^p`.** -/
theorem vhC_div {a b : Ordinal.{0}} : ∀ w, w ∈ S.CSet a b → ∀ p : Ordinal.{0},
    ω ^ p * (w / ω ^ p) ∈ S.CSet a b ∧ w % ω ^ p ∈ S.CSet a b ∧
      (p ∈ S.CSet a b → w / ω ^ p ∈ S.CSet a b) := by
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IH =>
  intro hw p
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [Ordinal.zero_div, Ordinal.zero_mod, mul_zero]
    exact ⟨CSet.zero_mem a b, CSet.zero_mem a b, fun _ => CSet.zero_mem a b⟩
  have hp0 : ω ^ p ≠ 0 := (opow_pos p omega0_pos).ne'
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt w one_lt_omega0)
  have hdm : w = ω ^ log ω w * n + w % ω ^ log ω w := by
    rw [← hn]; exact (Ordinal.div_add_mod w _).symm
  have he : log ω w ∈ S.CSet a b := (rxCDec w hw).2
  have hs : w % ω ^ log ω w ∈ S.CSet a b := vbC_rem hw
  have hsw : w % ω ^ log ω w < w :=
    (Ordinal.mod_lt w (opow_pos _ omega0_pos).ne').trans_le (opow_log_le_self ω hw0)
  rcases lt_or_ge (log ω w) p with hep | hpe
  · have hwp : w < ω ^ p :=
      (lt_opow_succ_log_self one_lt_omega0 w).trans_le
        (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hep))
    rw [Ordinal.div_eq_zero_of_lt hwp, Ordinal.mod_eq_of_lt hwp, mul_zero]
    exact ⟨CSet.zero_mem a b, hw, fun _ => CSet.zero_mem a b⟩
  have hsplit : ω ^ log ω w = ω ^ p * ω ^ (log ω w - p) := by
    rw [← opow_add, Ordinal.add_sub_cancel_of_le hpe]
  have hw' : w = ω ^ p * (ω ^ (log ω w - p) * n) + w % ω ^ log ω w := by
    conv_lhs => rw [hdm]
    rw [hsplit, mul_assoc]
  have hdiv : w / ω ^ p = ω ^ (log ω w - p) * n + w % ω ^ log ω w / ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_div _ hp0]
  have hmod : w % ω ^ p = w % ω ^ log ω w % ω ^ p := by
    conv_lhs => rw [hw']
    rw [Ordinal.mul_add_mod_self]
  obtain ⟨i1, i2, i3⟩ := IH _ hsw hs p
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiv, mul_add, ← mul_assoc, ← hsplit]
    exact CSet.add_mem (ConjT.mul_nat_mem S (vhC_opow he) n) i1
  · rw [hmod]; exact i2
  · intro hp
    rw [hdiv]
    exact CSet.add_mem (ConjT.mul_nat_mem S (vhC_opow ((rxCDec _ he).1 p hp hpe)) n) (i3 hp)

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- `Ω₂ ∈ D`. -/
theorem vhD_Om2 : VbD S l (Om (1 + 1)) := by
  have h := vbD_Om (S := S) (l := l) 1
  rwa [Nat.cast_one] at h

/-- **The `W`-parts of a member of `D`**: `log_W x ∈ D` and `x mod W^{log_W x} ∈ D`. -/
theorem vhD_parts {x : Ordinal.{0}} (hx : VbD S l x) (h0 : 0 < x) :
    VbD S l (sgLW x) ∧ VbD S l (x % leWe (sgLW x)) := by
  obtain ⟨hgH, hgx, -, -, -, hrH, -, -⟩ := Ua.uaBase hl hX hx.1 h0
  have hΩ : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  have hlog : log ω x ∈ S.CSet (Om ω) (ConjT.th S) := (rxCDec x hx.2.1).2
  have hg : sgLW x ∈ S.CSet (Om ω) (ConjT.th S) := by
    have h := (vhC_div (log ω x) hlog (Om (1 + 1))).2.2 (vhD_Om2 (S := S) (l := l)).2.1
    rwa [hΩ] at h
  have hr : x % leWe (sgLW x) ∈ S.CSet (Om ω) (ConjT.th S) :=
    (vhC_div x hx.2.1 (Om (1 + 1) * sgLW x)).2.1
  exact ⟨⟨hgH, hg, hgx.trans_lt hx.2.2⟩, ⟨hrH, hr, (Ordinal.mod_le _ _).trans_lt hx.2.2⟩⟩

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vh
