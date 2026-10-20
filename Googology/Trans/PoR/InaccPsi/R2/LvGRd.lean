import Googology.Trans.PoR.InaccPsi.R2.LvGPh
import Googology.Trans.PoR.InaccPsi.R2.FpLoc

/-!
# ENUM-REACH below every `Λ⁺(lvgSys n)`, the roads without the notation hypothesis, and the exact frontiers

A named fixed point `λ = υ_λ` below `Λ⁺(lvgSys n) ≤ ι(ω^{gc n}·ω)` has `e(η_λ) ≤ gc n` (`Ph.phExp_le`), so THEOREM UNI
(`Gg.ggUniTh`) with `lvgPoly n` gives `Θ_λ(m_λ) = O(λ)` there:

* `lvgT_fix` (**the notation hypothesis below `Λ⁺(lvgSys n)`, proved**), `lvgEnum` (**ENUM-REACH, both halves, at every
  restart of the range below `Λ⁺(lvgSys n)`**), `lvgRoadPh` (**the road below `Λ⁺(lvgSys n)` without the notation
  hypothesis**: the rest is UPPER/LOWER at `λ ≥ Λ⁺(lvgSys n)`, CapV at the outer restarts below `L(ω)`, (CL), EQ,
  TCrest, (EMB₂));
* `lvg_loc` (**`Λ⁺(lvgSys (n+1)) = ι(gc (n+1)·ω)`, `ρ_{Λ⁺(lvgSys (n+1))} = P(gc (n+1)·ω) < L(0)`**, by `Fp.fpB1_eq`).

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu

variable {S : InaccSeq.{0}}

/-- **The notation hypothesis below `Λ⁺(lvgSys n)`**: `Θ_λ(m_λ) = O(λ)` at every fixed point of the range. -/
theorem lvgT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lvgSys n)) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (lvgSys n) l :=
  ggUniTh (gc_lt_Gam n).le (lvgPoly n) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) (hlB.trans_le (lvg_fr (S := S) n).2.2.1))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lvgSys n)`.** -/
theorem lvgEnum (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lvgSys n)) :
    CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lvg_init n hr hl hnf
  · exact (lvg_iff n hr.1 hl).2 (lvgT_fix n hr hl hfx.symm)

/-- **The road below `Λ⁺(lvgSys n)` without the notation hypothesis.** -/
theorem lvgRoadPh (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lvgSys n) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lvgSys n)) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lvgRoad3 n hU hL (fun _ hr hlB hfix => lvgT_fix n hr hlB hfix) hV hC hEQ hrest hB2

/-- **`Λ⁺(lvgSys (n+1)) = ι(gc (n+1)·ω)`, `ρ_{Λ⁺(lvgSys (n+1))} = P(gc (n+1)·ω) < L(0)`.** -/
theorem lvg_loc (n : ℕ) : xtB1 (lvgSys (n + 1)) = iota S (gc (n + 1) * ω) ∧
    upsilon (xtB1 (lvgSys (n + 1))) = Pv S (gc (n + 1) * ω) ∧ Pv S (gc (n + 1) * ω) < Nc.ncL S 0 := by
  have hg0 : gc n ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) (gc_Om1_le n)).ne'
  have e : ω ^ gc (n + 1) = gc (n + 1) := gg_veblen_eps hg0
  have h := Fp.fpB1_eq (S := S) (gc_lt_Gam (n + 1)) (lvgPoly (n + 1)) (fun _ hy hy1 => (gcTh hy hy1 (n + 1)).symm)
    (fun _ hZ => gc_cl hZ (n + 1)) (gc_Om1_le (n + 1))
    (fun _ hx hx1 => (gT_lt_succ hx hx1 0).trans_le (gT_mono hx hx1 (Nat.succ_le_succ (Nat.zero_le n))))
    (lvgSys_topPkg (n + 1))
  rwa [e] at h

end Googology.Trans.PoR.InaccPsi.R2
