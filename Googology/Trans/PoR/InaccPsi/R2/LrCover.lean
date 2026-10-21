import Googology.Trans.PoR.InaccPsi.R2.LrRoad

/-!
# Covering by the reaches of the restarts inside: realizers only at the uncovered targets

`le1` is `≤₁` of `R₂^C`; it is transitive (`R2.le1_trans`), closed downwards in its right end
(`R2.le1_of_le_of_le1`) and continuous (`R2.le1_of_cofinal`).  So `a ≤₁ b` follows as soon as every
`y ∈ [a, b)` with `a ≤₁ y` lies below some `z` with `a ≤₁ z` (`lrLe1_of_open`).  Such a `z` is given by a
restart `ρ_{λ'} ∈ [a, y]` of the Range with `y < r(λ')` and LOWER at `λ'` (`a ≤₁ ρ_{λ'} ≤₁ r(λ')`), or by a
realizer for a target `t ∈ (y, b]` (`Lr.lrLe1_of_real`).  Hence:

* `lrLe1_of_cover` (**`a ≤₁ b` from LOWER, `CvNoPair a b`, and at each reached `y` a covering restart or a
  realizer**);
* `LrGap S a b c`: realizers for the targets `y ≥ c` that no restart reach covers; `lrGap_of_above`
  (`LrRealAbove → LrGap`), `lrLe1_of_gap`;
* `lrNamed_gap`, `lrRoad_gap` (**the road with `h0`, `hn` asked only at the uncovered targets above
  `υ_{ι(a)+ω+1}`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Rm Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv

variable {S : InaccSeq.{0}}

/-- **`a ≤₁ b` when the set of `≤₁`-successors of `a` is open upwards below `b`.** -/
theorem lrLe1_of_open {a b : Ordinal.{0}} (hab : a ≤ b)
    (h : ∀ y, a ≤ y → y < b → le1 a y → ∃ z, y < z ∧ le1 a z) : le1 a b := by
  by_contra hn
  set s := {y | a ≤ y ∧ y ≤ b ∧ ¬ le1 a y} with hs
  have hne : s.Nonempty := ⟨b, hab, le_rfl, hn⟩
  have hr : sInf s ∈ s := csInf_mem hne
  have hbelow : ∀ y, a ≤ y → y < sInf s → le1 a y := by
    intro y h1 h2
    by_contra h3
    exact absurd (csInf_le (OrderBot.bddBelow s) ⟨h1, h2.le.trans hr.2.1, h3⟩) (not_le.2 h2)
  apply hr.2.2
  refine le1_of_cofinal hr.1 fun y hay hyr => ?_
  exact h y hay (hyr.trans_le hr.2.1) (hbelow y hay hyr)

/-- **`a ≤₁ b` from the covering restarts and the realizers at the other targets.** -/
theorem lrLe1_of_cover (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (h : ∀ y, a ≤ y → y < b → le1 a y →
      (∃ l', CdRange S l' ∧ a ≤ upsilon l' ∧ upsilon l' ≤ y ∧ y < cdR S l') ∨
        ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t) : le1 a b := by
  refine lrLe1_of_open hab fun y hay hyb hy => ?_
  rcases h y hay hyb hy with ⟨l', hR, h1, h2, h3⟩ | ⟨t, h1, h2, h3⟩
  · exact ⟨cdR S l', h3, le1_trans (le1_of_le_of_le1 h1 h2 hy) (hL l' hR)⟩
  · exact ⟨t, h1, lrLe1_of_real hL (hay.trans h1.le) (cvNoPair_mono hP h2) h3⟩

/-- Realizers for the targets `y ≥ c` (with `a ≤₁ y`) that no restart of the Range in `[a, y]` covers. -/
def LrGap (S : InaccSeq.{0}) (a b c : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → c ≤ y → y < b → le1 a y →
    (¬ ∃ l', CdRange S l' ∧ a ≤ upsilon l' ∧ upsilon l' ≤ y ∧ y < cdR S l') →
    ∃ t, y < t ∧ t ≤ b ∧ LrReal S a t

theorem lrGap_of_above {a b c : Ordinal.{0}} (h : LrRealAbove S a b c) : LrGap S a b c :=
  fun y hay hcy hyb _ _ => h y hay hcy hyb

/-- **`a ≤₁ b` from realizers up to `c` and at the uncovered targets above `c`.** -/
theorem lrLe1_of_gap (hL : CdLOWER S) {a b c : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hc : LrReal S a c) (hcb : c ≤ b) (h : LrGap S a b c) : le1 a b := by
  refine lrLe1_of_cover hL hab hP fun y hay hyb hy => ?_
  by_cases hcov : ∃ l', CdRange S l' ∧ a ≤ upsilon l' ∧ upsilon l' ≤ y ∧ y < cdR S l'
  · exact Or.inl hcov
  · right
    by_cases hcy : c ≤ y
    · exact h y hay hcy hyb hy hcov
    · exact ⟨c, not_le.1 hcy, hcb, hc⟩

/-- **The crossing relations at the named restarts from realizers at the uncovered targets.** -/
theorem lrNamed_gap (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S := by
  obtain ⟨⟨r0, b0⟩, rn⟩ := lrNamed_shift0 (S := S) hlow
  refine ⟨?_, fun n => ?_, lrLe1_of_realCof hL (Qq.qqL_lt_succ S).le hP hw⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    exact lrLe1_of_gap hL (Pp.ppL_mono zero_le)
      (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) r0 b0 h0
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact lrLe1_of_gap hL (Pp.ppL_lt_succ n).le
      (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (rn n).1 (rn n).2 (hn n)

/-- **The road with `h0`, `hn` asked only at the targets above `υ_{ι(a)+ω+1}` that no restart reach
covers.** -/
theorem lrRoad_gap (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (lrIx (Nc.ncL S 0) + ω + 1)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (lrIx (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) + ω + 1)))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hL' := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (lrNamed_gap hL' (cdLow_enum hU' hV') h0 hn hP hw) hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Lr
