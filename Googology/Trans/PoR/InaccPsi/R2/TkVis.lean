import Googology.Trans.PoR.InaccPsi.R2.ThObs

/-!
# The long region at the visible restarts: `a ≤₁ b` from `a ≤₁ ρ_ν` at the uncovered restarts only

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = m*` or `a = L(n+1)`, `b` the next point (`L(1)`, `L(n+2)`), `c = c_ω(a) = υ_{a+ε_{Γ_{a+1}+ω}}`
(`Te.teW`, `a ≤₁ c` by `Te.teShortW_M`, `Te.teShortW_L`).  A Range restart `ν` with `a < ρ_ν` is **covered
from `a`** (`TkCov`) if some Range restart `R` has `a < ρ_R < ρ_ν < r(R)`, and **isolated** (`TkIso`) if all
Range restarts in some interval `(y, ρ_ν)`, `a ≤ y`, are covered.  With LOWER at the Range restarts
(`a ≤₁ ρ_R ⇒ a ≤₁ r(R)`) and the Range restarts cofinal below `b`, the only targets left are the uncovered
restarts, and among them only the isolated ones (the others follow by continuity):

* `tkVis_of_iso` (**the isolated uncovered restarts give all uncovered restarts**), `tkLe1_of_vis`
  (**`a ≤₁ b` from `a ≤₁ ρ_ν` at the uncovered restarts above `c`**), `tkLe1_iff_vis`, `tkLe1_iff_visI`
  (both are equivalences, so nothing is lost);
* `tkCL_iff_vis`, `tkM_iff_vis`, `tkLong_iff_vis` (**(CL) and `m* ≤₁ L(1)` iff `a ≤₁ ρ_ν` at every
  isolated uncovered Range restart `ν` of `[c_ω(a), b)`, at `m*` and every `L(n+1)`**), `tkVis_iff_nu`
  (**these statements iff `L(k) ≤₁ ν_C` for every `k`**), `tkRoadVis` (**the road with these statements**);
* `tkVisI_of_real`, `tkRoadReal` (**the realizer road with targets only at the isolated uncovered restarts**:
  a realizer `Lr.LrReal S a t` with `ρ_ν < t ≤ b` for each such `ν`; `Lr.LrGap` asks one at every uncovered
  point `y ≥ c` with `a ≤₁ y`).

No new axiom.  New definitions: `TkCov`, `TkIso`, `TkVis`, `TkVisI`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`ν` is covered from `a`**: a restart `R` of the Range with `a < ρ_R < ρ_ν < r(R)`. -/
def TkCov (S : InaccSeq.{0}) (a ν : Ordinal.{0}) : Prop :=
  ∃ R, CdRange S R ∧ a < upsilon R ∧ upsilon R < upsilon ν ∧ upsilon ν < cdR S R

/-- **`ν` is isolated from below** among the uncovered Range restarts above `a`. -/
def TkIso (S : InaccSeq.{0}) (a ν : Ordinal.{0}) : Prop :=
  ∃ y, a ≤ y ∧ y < upsilon ν ∧
    ∀ ν', CdRange S ν' → y < upsilon ν' → upsilon ν' < upsilon ν → TkCov S a ν'

/-- **The visible-restart statements on `[c, b)`**: `a ≤₁ ρ_ν` at every uncovered Range restart. -/
def TkVis (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → a < upsilon ν → ¬ TkCov S a ν →
    le1 a (upsilon ν)

/-- **The same, only at the uncovered Range restarts isolated from below.** -/
def TkVisI (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → a < upsilon ν → ¬ TkCov S a ν →
    TkIso S a ν → le1 a (upsilon ν)

/-! ## The general criterion -/

/-- **The isolated uncovered restarts give all uncovered restarts** (continuity at the others). -/
theorem tkVis_of_iso {a b c : Ordinal.{0}} (hc : le1 a c) (h : TkVisI S a b c) : TkVis S a b c := by
  suffices H : ∀ x, ∀ ν, upsilon ν = x → CdRange S ν → c ≤ upsilon ν → upsilon ν < b →
      a < upsilon ν → ¬ TkCov S a ν → le1 a (upsilon ν) from
    fun ν h1 h2 h3 h4 h5 => H _ ν rfl h1 h2 h3 h4 h5
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro ν hx hR hcν hνb haν hcov
  by_cases hI : TkIso S a ν
  · exact h ν hR hcν hνb haν hcov hI
  · refine le1_of_cofinal haν.le fun y hay hyν => ?_
    have hn : ¬ ∀ ν', CdRange S ν' → y < upsilon ν' → upsilon ν' < upsilon ν → TkCov S a ν' :=
      fun hall => hI ⟨y, hay, hyν, hall⟩
    push Not at hn
    obtain ⟨ν', hR', hy', hν', hcov'⟩ := hn
    refine ⟨upsilon ν', hy', ?_⟩
    have haν' : a < upsilon ν' := lt_of_le_of_lt hay hy'
    by_cases hcν' : c ≤ upsilon ν'
    · exact IH _ (hx ▸ hν') ν' rfl hR' hcν' (hν'.trans hνb) haν' hcov'
    · exact le1_of_le_of_le1 haν'.le (not_le.1 hcν').le hc

/-- **`a ≤₁ b` from `a ≤₁ ρ_ν` at the uncovered Range restarts above `c`**, given LOWER, `a ≤₁ c` and Range
restarts cofinal below `b`. -/
theorem tkLe1_of_vis (hL : CdLOWER S) {a b c : Ordinal.{0}} (hab : a ≤ b) (hc : le1 a c)
    (hcof : ∀ y, a ≤ y → y < b → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b)
    (h : TkVis S a b c) : le1 a b := by
  refine Lr.lrLe1_of_open hab fun y hay hyb hy => ?_
  set s := {x | ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b ∧ upsilon ν = x} with hs
  obtain ⟨ν1, h1, h2, h3⟩ := hcof y hay hyb
  have hne : s.Nonempty := ⟨_, ν1, h1, h2, h3, rfl⟩
  obtain ⟨ν, hR, hyν, hνb, hνm⟩ := csInf_mem hne
  have hmin : ∀ ν', CdRange S ν' → y < upsilon ν' → upsilon ν' < b → upsilon ν ≤ upsilon ν' :=
    fun ν' g1 g2 g3 => hνm ▸ csInf_le' ⟨ν', g1, g2, g3, rfl⟩
  have haν : a < upsilon ν := lt_of_le_of_lt hay hyν
  by_cases hcov : TkCov S a ν
  · obtain ⟨R, hRR, haR, hRν, hνR⟩ := hcov
    have hRy : upsilon R ≤ y := by
      by_contra hlt
      exact absurd (hmin R hRR (not_le.1 hlt) (hRν.trans hνb)) (not_le.2 hRν)
    exact ⟨cdR S R, hyν.trans hνR, le1_trans (le1_of_le_of_le1 haR.le hRy hy) (hL R hRR)⟩
  · refine ⟨upsilon ν, hyν, ?_⟩
    by_cases hcν : c ≤ upsilon ν
    · exact h ν hR hcν hνb haν hcov
    · exact le1_of_le_of_le1 haν.le (not_le.1 hcν).le hc

/-- `a ≤₁ b` gives every visible statement. -/
theorem tkVis_of_le1 {a b c : Ordinal.{0}} (h : le1 a b) : TkVis S a b c :=
  fun _ _ _ hνb haν _ => le1_of_le_of_le1 haν.le hνb.le h

theorem tkVisI_of_vis {a b c : Ordinal.{0}} (h : TkVis S a b c) : TkVisI S a b c :=
  fun ν h1 h2 h3 h4 h5 _ => h ν h1 h2 h3 h4 h5

/-- **`a ≤₁ b` iff the visible statements.** -/
theorem tkLe1_iff_vis (hL : CdLOWER S) {a b c : Ordinal.{0}} (hab : a ≤ b) (hc : le1 a c)
    (hcof : ∀ y, a ≤ y → y < b → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b) :
    le1 a b ↔ TkVis S a b c :=
  ⟨tkVis_of_le1, tkLe1_of_vis hL hab hc hcof⟩

/-- **`a ≤₁ b` iff the visible statements at the isolated uncovered restarts.** -/
theorem tkLe1_iff_visI (hL : CdLOWER S) {a b c : Ordinal.{0}} (hab : a ≤ b) (hc : le1 a c)
    (hcof : ∀ y, a ≤ y → y < b → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b) :
    le1 a b ↔ TkVisI S a b c :=
  ⟨fun h => tkVisI_of_vis (tkVis_of_le1 h), fun h => tkLe1_of_vis hL hab hc hcof (tkVis_of_iso hc h)⟩

/-- **The visible statements from realizers at the isolated uncovered restarts** (`a = ρ_λ`, `b ≤ ν_C`). -/
theorem tkVisI_of_real (hL : CdLOWER S) {a b c lam : Ordinal.{0}} (hl : IsRestartIdx lam)
    (ha : a = upsilon lam) (hb : b ≤ nuC)
    (h : ∀ ν, CdRange S ν → c ≤ upsilon ν → upsilon ν < b → a < upsilon ν → ¬ TkCov S a ν →
      TkIso S a ν → ∃ t, upsilon ν < t ∧ t ≤ b ∧ Lr.LrReal S a t) :
    TkVisI S a b c := by
  intro ν h1 h2 h3 h4 h5 h6
  obtain ⟨t, hνt, htb, hR⟩ := h ν h1 h2 h3 h4 h5 h6
  have hat : le1 a t := Lr.lrLe1_of_real hL (h4.le.trans hνt.le) (Cv.cvNoPair_of_nu hl ha (htb.trans hb)) hR
  exact le1_of_le_of_le1 h4.le hνt.le hat

/-! ## At `m*` and the `L(n+1)` -/

/-- The Range restarts are cofinal below `L(n+1)`. -/
theorem tkCof_L (n : ℕ) : ∀ y, y < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) →
    ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  intro y hy
  obtain ⟨μ, h1, h2, h3, -⟩ := Ls.lsNames_L (S := S) n 0 y hy
  exact ⟨μ, h1, h2, h3⟩

/-- The Range restarts are cofinal below `L(1)`. -/
theorem tkCof_1 : ∀ y, y < Nc.ncL S 1 → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < Nc.ncL S 1 := by
  have h := tkCof_L (S := S) 0
  simpa using h

section Hyp

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- **(CL) at `n` iff `L(n+1) ≤₁ ρ_ν` at every isolated uncovered Range restart `ν` of
`[c_ω(L(n+1)), L(n+2))`.** -/
theorem tkCL_iff_vis (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) :=
  tkLe1_iff_visI (Rz.rzLOWER_of_rest hL) (Pp.ppL_lt_succ n).le (Te.teShortW_L hU hV hVt hL n)
    (fun y _ hy => tkCof_L (n + 1) y hy)

/-- **`m* ≤₁ L(1)` iff `m* ≤₁ ρ_ν` at every isolated uncovered Range restart `ν` of `[c_ω(m*), L(1))`.** -/
theorem tkM_iff_vis :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) :=
  tkLe1_iff_visI (Rz.rzLOWER_of_rest hL) (Rl.rlM_lt_L1 (S := S)).le (Te.teShortW_M hU hV hVt hL)
    (fun y _ hy => tkCof_1 y hy)

/-- **(CL) and `m* ≤₁ L(1)` iff the visible statements at `m*` and every `L(n+1)`.** -/
theorem tkLong_iff_vis :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔
      (TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
        ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) := by
  constructor
  · rintro ⟨hCL, hM⟩
    exact ⟨(tkM_iff_vis hU hV hVt hL).1 hM, fun n => (tkCL_iff_vis hU hV hVt hL n).1 (hCL n)⟩
  · rintro ⟨hM, hn⟩
    exact ⟨fun n => (tkCL_iff_vis hU hV hVt hL n).2 (hn n), (tkM_iff_vis hU hV hVt hL).2 hM⟩

end Hyp

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The visible statements iff `L(k) ≤₁ ν_C` for every `k < ω`** (the road hypotheses). -/
theorem tkVis_iff_nu :
    (TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
        ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
          (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) ↔
      ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC :=
  (tkLong_iff_vis hU hV hVt hL).symm.trans (Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove)

/-- **The road with the visible statements** (no `LrGap`, no `Tb.TbNoUncov`). -/
theorem tkRoadVis
    (h0 : TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hCL, hM⟩ := (tkLong_iff_vis hU hV hVt hL).2 ⟨h0, hn⟩
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove hM hCL

/-- **The realizer road with targets only at the isolated uncovered restarts.** -/
theorem tkRoadReal
    (h0 : ∀ ν, CdRange S ν → upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0)) ≤ upsilon ν →
      upsilon ν < Nc.ncL S 1 → Nc.ncL S 0 < upsilon ν → ¬ TkCov S (Nc.ncL S 0) ν →
      TkIso S (Nc.ncL S 0) ν → ∃ t, upsilon ν < t ∧ t ≤ Nc.ncL S 1 ∧ Lr.LrReal S (Nc.ncL S 0) t)
    (hn : ∀ n : ℕ, ∀ ν, CdRange S ν →
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ≤
        upsilon ν → upsilon ν < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) →
      Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < upsilon ν → ¬ TkCov S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ν →
      TkIso S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ν →
      ∃ t, upsilon ν < t ∧ t ≤ Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        Lr.LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) t) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hν := Sh.shNu hU hV hVt hL
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hle : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC := fun k =>
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans hν
  refine tkRoadVis hU hO hL hV hVt hEQ htop hmove ?_ ?_
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    exact tkVisI_of_real hLW hl e (by simpa using hle 0) h0
  · intro n
    obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact tkVisI_of_real hLW hl e (hle (n + 1)) (hn n)

end Road

end Googology.Trans.PoR.InaccPsi.R2.Tk
