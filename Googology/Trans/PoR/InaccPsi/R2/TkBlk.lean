import Googology.Trans.PoR.InaccPsi.R2.TkVis

/-!
# The long region inside single blocks: one statement per restart whose reach stays in its block

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`a = υ_{λ_a}` a restart (`a = L(k)`), `b` the next point, `c` a point with `a ≤₁ c` (`c = c_ω(a)`).  A Range
restart `ν` above `a` is a nonzero multiple of `ω²`; it is either `p + ω²` (the restart after `p`) or a limit of
restart indices.  At a limit the statement `a ≤₁ ρ_ν` follows by continuity; at `ν = p + ω²` with `a < ρ_p`
it follows from `a ≤₁ ρ_p` and LOWER at `p` (`a ≤₁ r(p)`) when `r(p) ≥ ρ_ν`; when `ν` is covered from `a` it
follows from the covering restart.  So only one case is left, inside the block `[ρ_p, υ_{p+ω²})` of `p`:

* `TkCovW` (weakly covered: `a < ρ_R < ρ_ν ≤ r(R)`), `TkSucc S a b c` (**the block statements**): for every
  Range restart `p` with `a < ρ_p`, `c ≤ υ_{p+ω²} < b` and `p + ω²` not weakly covered from `a` (so
  `r(p) < υ_{p+ω²}`, `tkSucc_r_lt`): `a ≤₁ r(p) ⇒ a ≤₁ υ_{p+ω²}`;
* `tkRi_cases` (a restart index is `p + ω²` with `ω² ∣ p`, or a limit of restart indices);
* `tkLe1_of_succ` (**`a ≤₁ b` from the block statements**, LOWER, `a ≤₁ c`, `υ_{λ_a+ω²} ≤ c`, every restart
  index strictly inside `(a, b)` in the Range, Range restarts cofinal below `b`), `tkLe1_iff_succ`;
* `tkL_rng`, `tkL_first`, `tkShort` (these hypotheses at `a = L(k)`, `b = L(k+1)`, `c = c_ω(L(k))`);
* `tkLk_iff_succ`, `tkLong_iff_succ` (**(CL) and `m* ≤₁ L(1)` iff the block statements at every `L(k)`**),
  `tkSucc_iff_nu` (**iff `L(k) ≤₁ ν_C` for every `k`**), `tkRoadSucc` (**the road with the block
  statements**).

No new axiom.  New definitions: `TkCovW`, `TkSucc`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`ν` is weakly covered from `a`**: a Range restart `R` with `a < ρ_R < ρ_ν ≤ r(R)`. -/
def TkCovW (S : InaccSeq.{0}) (a ν : Ordinal.{0}) : Prop :=
  ∃ R, CdRange S R ∧ a < upsilon R ∧ upsilon R < upsilon ν ∧ upsilon ν ≤ cdR S R

/-- **The block statements on `[c, b)`**: at every Range restart `p` above `a` such that no Range restart
`R` with `a < ρ_R < υ_{p+ω²}` has `r(R) ≥ υ_{p+ω²}` (so `r(p) < υ_{p+ω²}`), with `c ≤ υ_{p+ω²} < b`:
`a ≤₁ r(p) ⇒ a ≤₁ υ_{p+ω²}`. -/
def TkSucc (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ∀ p, CdRange S p → a < upsilon p → c ≤ upsilon (p + ω ^ 2) → upsilon (p + ω ^ 2) < b →
    ¬ TkCovW S a (p + ω ^ 2) → le1 a (cdR S p) → le1 a (upsilon (p + ω ^ 2))

/-- In a block statement `r(p) < υ_{p+ω²}`. -/
theorem tkSucc_r_lt {a p : Ordinal.{0}} (hp : CdRange S p) (hap : a < upsilon p)
    (h : ¬ TkCovW S a (p + ω ^ 2)) : cdR S p < upsilon (p + ω ^ 2) := by
  by_contra hle
  exact h ⟨p, hp, hap, upsilon_normal.strictMono (lt_add_of_pos_right p (pow_pos omega0_pos 2)),
    not_lt.1 hle⟩

/-- **A restart index is `p + ω²` with `ω² ∣ p`, or a limit of restart indices.** -/
theorem tkRi_cases {ν : Ordinal.{0}} (hν : IsRestartIdx ν) :
    (∃ p, ω ^ 2 ∣ p ∧ ν = p + ω ^ 2) ∨ (∀ i < ν, ∃ ν', IsRestartIdx ν' ∧ i < ν' ∧ ν' < ν) := by
  obtain ⟨hν0, j, rfl⟩ := hν
  have hω : (ω ^ 2 : Ordinal.{0}) ≠ 0 := (pow_pos omega0_pos 2).ne'
  rcases zero_or_succ_or_isSuccLimit j with rfl | ⟨j', rfl⟩ | hlim
  · exact absurd (mul_zero _) hν0
  · left
    exact ⟨ω ^ 2 * j', ⟨j', rfl⟩, by rw [Order.succ_eq_add_one, mul_add_one]⟩
  · right
    intro i hi
    set q := i / ω ^ 2 with hq
    have hqj : q < j := (Ordinal.lt_mul_iff_div_lt hω).1 hi
    have hq1 : q + 1 < j := hlim.add_one_lt hqj
    refine ⟨ω ^ 2 * (q + 1), ⟨mul_ne_zero hω (add_pos_of_right zero_lt_one q).ne', q + 1, rfl⟩, ?_, ?_⟩
    · have e := (Ordinal.div_add_mod i (ω ^ 2)).symm
      have hm : i % ω ^ 2 < ω ^ 2 := Ordinal.mod_lt i hω
      rw [mul_add_one]
      calc i = ω ^ 2 * q + i % ω ^ 2 := e
        _ < ω ^ 2 * q + ω ^ 2 := (add_lt_add_iff_left _).2 hm
    · exact (mul_lt_mul_iff_right₀ (pow_pos omega0_pos 2)).2 hq1

/-- **`a ≤₁ b` from the block statements.** -/
theorem tkLe1_of_succ (hL : CdLOWER S) {a b c la : Ordinal.{0}} (hla : IsRestartIdx la)
    (ha : upsilon la = a) (hab : a ≤ b) (hc : le1 a c) (hfirst : upsilon (la + ω ^ 2) ≤ c)
    (hrng : ∀ ν, IsRestartIdx ν → a < upsilon ν → upsilon ν < b → CdRange S ν)
    (hcof : ∀ y, a ≤ y → y < b → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b)
    (h : TkSucc S a b c) : le1 a b := by
  have hm := upsilon_normal.strictMono
  have key : ∀ x, ∀ ν, upsilon ν = x → CdRange S ν → a < upsilon ν → upsilon ν < b →
      le1 a (upsilon ν) := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IH =>
    intro ν hx hR haν hνb
    by_cases hcν : upsilon ν ≤ c
    · exact le1_of_le_of_le1 haν.le hcν hc
    rw [not_le] at hcν
    by_cases hcov : TkCovW S a ν
    · obtain ⟨R, hRR, haR, hRν, hνR⟩ := hcov
      have hR1 := IH _ (hx ▸ hRν) R rfl hRR haR (hRν.trans hνb)
      exact le1_of_le_of_le1 haν.le hνR (le1_trans hR1 (hL R hRR))
    rcases tkRi_cases hR.1 with ⟨p, hp, rfl⟩ | hlim
    · by_cases hpa : upsilon p ≤ a
      · -- `p = λ_a`: the first restart above `a`, below `c`
        exfalso
        have hpl : p ≤ la := by rw [← ha] at hpa; exact hm.le_iff_le.1 hpa
        have hlν : la < p + ω ^ 2 := by rw [← ha] at haν; exact hm.lt_iff_lt.1 haν
        rcases hpl.lt_or_eq with hlt | heq
        · exact absurd (Lr.lr_dvd_add_le hp hla.2 hlt) (not_le.2 hlν)
        · rw [heq] at hcν; exact absurd hfirst (not_le.2 hcν)
      rw [not_le] at hpa
      have hp0 : p ≠ 0 := by
        rintro rfl
        exact absurd (hm.monotone (zero_le : (0 : Ordinal.{0}) ≤ la)) (by rw [ha]; exact not_le.2 hpa)
      have hpν : upsilon p < upsilon (p + ω ^ 2) := hm (lt_add_of_pos_right p (pow_pos omega0_pos 2))
      have hpR : CdRange S p := hrng p ⟨hp0, hp⟩ hpa (hpν.trans hνb)
      have hpa1 := IH _ (hx ▸ hpν) p rfl hpR hpa (hpν.trans hνb)
      have hpr : le1 a (cdR S p) := le1_trans hpa1 (hL p hpR)
      exact h p hpR hpa hcν.le hνb hcov hpr
    · refine le1_of_cofinal haν.le fun y hay hyν => ?_
      obtain ⟨i, hi, hyi⟩ := (upsilon_normal.lt_iff_exists_lt (ri_lim hR.1)).1 hyν
      obtain ⟨ν', hν', hiν', hν'ν⟩ := hlim i hi
      have hyν' : y < upsilon ν' := hyi.trans (hm hiν')
      have haν' : a < upsilon ν' := lt_of_le_of_lt hay hyν'
      have hν'b : upsilon ν' < b := (hm hν'ν).trans hνb
      exact ⟨upsilon ν', hyν', IH _ (hx ▸ hm hν'ν) ν' rfl (hrng ν' hν' haν' hν'b) haν' hν'b⟩
  refine le1_of_cofinal hab fun y hay hyb => ?_
  obtain ⟨ν, hR, hyν, hνb⟩ := hcof y hay hyb
  exact ⟨upsilon ν, hyν, key _ ν rfl hR (lt_of_le_of_lt hay hyν) hνb⟩

/-- `a ≤₁ b` gives every block statement. -/
theorem tkSucc_of_le1 {a b c : Ordinal.{0}} (h : le1 a b) : TkSucc S a b c :=
  fun p _ hap _ hνb _ _ => le1_of_le_of_le1
    (hap.le.trans (upsilon_normal.strictMono (lt_add_of_pos_right p (pow_pos omega0_pos 2))).le) hνb.le h

/-- **`a ≤₁ b` iff the block statements.** -/
theorem tkLe1_iff_succ (hL : CdLOWER S) {a b c la : Ordinal.{0}} (hla : IsRestartIdx la)
    (ha : upsilon la = a) (hab : a ≤ b) (hc : le1 a c) (hfirst : upsilon (la + ω ^ 2) ≤ c)
    (hrng : ∀ ν, IsRestartIdx ν → a < upsilon ν → upsilon ν < b → CdRange S ν)
    (hcof : ∀ y, a ≤ y → y < b → ∃ ν, CdRange S ν ∧ y < upsilon ν ∧ upsilon ν < b) :
    le1 a b ↔ TkSucc S a b c :=
  ⟨tkSucc_of_le1, tkLe1_of_succ hL hla ha hab hc hfirst hrng hcof⟩

/-! ## At `a = L(k)`, `b = L(k+1)`, `c = c_ω(L(k))` -/

/-- **Every restart index strictly between `L(k)` and `L(k+1)` is in the Range.** -/
theorem tkL_rng (k : ℕ) : ∀ ν, IsRestartIdx ν → Nc.ncL S (k : Ordinal.{0}) < upsilon ν →
    upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) → CdRange S ν := by
  intro ν hν h1 h2
  have hm := upsilon_normal.strictMono
  have hkν : Nc.ncL S (k : Ordinal.{0}) < ν := by
    rw [← Te.teUps_L (S := S) k] at h1; exact hm.lt_iff_lt.1 h1
  have hB : cdB0 ≤ ν := (Te.teB0_le_L k).trans hkν.le
  have hk1w : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω := Te.teL_lt_omega (k + 1)
  have hlt : upsilon ν < Nc.ncL S (ω + 1) := (h2.trans hk1w).trans (Qq.qqL_lt_succ S)
  refine (Te.teRange_iff hν hB hlt).2 ⟨fun j hj => ?_, fun hw => ?_⟩
  · rcases le_or_gt j k with hjk | hjk
    · have := Pp.ppL_mono (S := S) (Nat.cast_le.2 hjk)
      rw [← hj] at this; exact absurd h1 (not_lt.2 this)
    · have := Pp.ppL_mono (S := S) (Nat.cast_le.2 (Nat.succ_le_of_lt hjk))
      rw [← hj] at this; exact absurd h2 (not_lt.2 this)
  · rw [hw] at h2; exact absurd (h2.trans hk1w) (lt_irrefl _)

/-- **`ω² ≤ ε_{Γ_{x+1}+ω}`**, so the first restart above `L(k)` lies below `c_ω(L(k))`. -/
theorem tkL_first (k : ℕ) :
    upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ 2) ≤
      upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) := by
  refine upsilon_normal.strictMono.monotone (add_le_add le_rfl ?_)
  set e := eN (lgG (Nc.ncL S (k : Ordinal.{0}))) with he
  have hE : InE e := eN_E _
  have h2 : (2 : Ordinal.{0}) ≤ e := by
    have := So.soOne_lt_E hE
    rw [← one_add_one_eq_two]; exact Order.add_one_le_of_lt this
  have h2' : ((2 : ℕ) : Ordinal.{0}) ≤ e := by simpa using h2
  calc (ω ^ 2 : Ordinal.{0}) = ω ^ ((2 : ℕ) : Ordinal.{0}) := (Ordinal.opow_natCast ω 2).symm
    _ ≤ ω ^ e := opow_le_opow_right omega0_pos h2'
    _ = e := hE
    _ ≤ Te.teW (Nc.ncL S (k : Ordinal.{0})) := Te.teW_ge 0 _

section Hyp

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
include hU hV hVt hL

/-- **`L(k) ≤₁ c_ω(L(k))`** (`Te.teShortW_M`, `Te.teShortW_L`). -/
theorem tkShort (k : ℕ) :
    le1 (Nc.ncL S (k : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  cases k with
  | zero => simpa using Te.teShortW_M hU hV hVt hL
  | succ n => exact Te.teShortW_L hU hV hVt hL n

/-- **`L(k) ≤₁ L(k+1)` iff the block statements at `L(k)`.** -/
theorem tkLk_iff_succ (k : ℕ) :
    le1 (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ↔
      TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) :=
  tkLe1_iff_succ (Rz.rzLOWER_of_rest hL) (Te.teRst_L k) (Te.teUps_L k) (Te.teL_lt_succ k).le
    (tkShort hU hV hVt hL k) (tkL_first k) (tkL_rng k) (fun y _ hy => tkCof_L k y hy)

/-- **(CL) and `m* ≤₁ L(1)` iff the block statements at every `L(k)`.** -/
theorem tkLong_iff_succ :
    (CdCL S ∧ le1 (Nc.ncL S 0) (Nc.ncL S 1)) ↔
      ∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) := by
  constructor
  · rintro ⟨hCL, hM⟩ k
    refine (tkLk_iff_succ hU hV hVt hL k).1 ?_
    cases k with
    | zero => simpa using hM
    | succ n => exact hCL n
  · intro h
    refine ⟨fun n => (tkLk_iff_succ hU hV hVt hL (n + 1)).2 (h (n + 1)), ?_⟩
    simpa using (tkLk_iff_succ hU hV hVt hL 0).2 (h 0)

end Hyp

section Road

variable (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
  (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
  (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
  (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
  (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
  (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
include hU hO hL hV hVt hEQ htop hmove

/-- **The block statements iff `L(k) ≤₁ ν_C` for every `k`.** -/
theorem tkSucc_iff_nu :
    (∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))))) ↔
      ∀ k : ℕ, le1 (Nc.ncL S (k : Ordinal.{0})) nuC :=
  (tkLong_iff_succ hU hV hVt hL).symm.trans (Te.teLong_iff_nu hU hO hL hV hVt hEQ htop hmove)

/-- **The road with the block statements** (no `LrGap`, no `Tb.TbNoUncov`). -/
theorem tkRoadSucc
    (h : ∀ k : ℕ, TkSucc S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  obtain ⟨hCL, hM⟩ := (tkLong_iff_succ hU hV hVt hL).2 h
  exact Sh.shRoad_CL hU hO hL hV hVt hEQ htop hmove hM hCL

end Road

end Googology.Trans.PoR.InaccPsi.R2.Tk
