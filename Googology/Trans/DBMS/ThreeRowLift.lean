import Googology.Trans.DBMS.ContentLift
import Googology.Trans.DBMS.ThreeRow
import Googology.Trans.BMS.RankVal
import Googology.Trans.BMS.Same

/-!
# Three-row DBMS against three-row BMS: the generators

`ContentLift.lean` writes the content generators of three-row DBMS as lifted
BMS generators, `cgen 2 (n + 2) = lift 3 (bgen3 n)` with
`bgen3 n = (0,0,0)(1,1,1)⋯(n,n,n)`, and shows that the lift commutes with
expansion there.  This file compares the ranks at the first place where both
are known.

* `rank_bmsL_gen_three_one`, `rkL_bgen3_one`: **the BMS matrix
  `(0,0,0)(1,1,1)` has rank `ψ_0(Ω_ω)`**, under three-row BMS and under the
  rule on all matrices.  It expands to the pair sequence generators with a row
  of zeros underneath (`RankVal.rank_gen_eq_iSup`), and the pair sequences fill
  the ordinals below `ψ_0(Ω_ω)` (`PSS.range_pairOrd`).  Every standard form of
  BMS is bounded by a generator (`rank_le_genB`).
* `rkL_lift_bgen3_one`: so **`rkL 2 (lift 3 B) = rkL 2 B` for
  `B = (0,0,0)(1,1,1)`**: the content `(0,0,0)(1,1,0)(2,2,1)` of the DBMS
  generator `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` has the rank of the BMS generator
  `(0,0,0)(1,1,1)` (both `ψ_0(Ω_ω)`, the first by `rkL_cgen_three`).
* `iSup_rank_dbmsL_two_lift`: the ordinal of three-row DBMS is
  `sup_n ω ^ rkL 2 (lift 3 (bgen3 n))`.

**What is conjectured, not proved.**  For every `n ≥ 1`,

    rkL 2 (lift 3 (bgen3 n)) = rkL 2 (bgen3 n),

that is, the DBMS generator with `n + 3` columns has the rank of the BMS
generator with `n + 1` columns, and the ordinal of three-row DBMS is the
ordinal of three-row BMS.  Numerically this is what MrredsharkFan's
conversion `dbmsToBms` of [w-Y-global-lngi](https://github.com/MrredsharkFan/w-Y-global-lngi)
says: it sends the DBMS generator `(0,0,0)(1,0,0)(2,1,0)⋯(n+2,n+1,n)` to
`(0,0,0)(1,1,1)⋯(n,n,n)` and its `N`-th expansion to the `N`-th expansion of
that (checked for `n = 2, 3`, `N ≤ 3`).  On about three hundred random
standard forms reached from the generators with five to seven columns it
lands on standard BMS matrices (`bms -s` of the yaBMS reference
implementation) and is inverted by `bmsToDbms`; on about three hundred more,
from the generators with five and six columns, it goes down under every
expansion (`D[N] ↦ M'` with `M' < M` in the dictionary order) and is cofinal
with the expansion of the image (`M[N] ≤ image of D[N']` for some `N' ≤ N + 3`).
If these held for every standard form, induction on the rank would give
`rank D = rank (dbmsToBms D)`.  The lift alone does not give it:
the lift commutes with expansion only when the last column keeps its parents
(`LiftGood`), and the matrices reached from the trio fragment `(bgen3 2)[N]`
have last columns `(x,0,0)`, where it does not.  From `n = 2` on, `rkL 2 (bgen3 n)` is expected
to lie above `ψ_0(Λ)`, the limit of the extended Buchholz terms (the BMS
analyses put `ψ_0(Λ)` at `(0,0,0)(1,1,1)(2,1,1)(3,1,0)(2,0,0)`, below
`(0,0,0)(1,1,1)(2,2,2)`), so it would have no name among the terms this
library has; this is not proved here.  What is proved at `n = 2` is only
`ψ_0(Ω_ω) < rkL 2 (cgen 2 4)` (`val_psiOmegaOmega_lt_rkL_cgen_two_four`) and
the shape of the expansions (`expandRL_cgen_two_four`).
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS

section BMSGen

local instance instWFB (r : Nat) : IsWellFounded (bmsL r).State (bmsL r).Rel := ⟨bmsL_wf r⟩

/-- **Every standard form of BMS is bounded by a generator.** -/
theorem rank_le_genB (r : Nat) (l : (bmsL r).State) :
    ∃ n, IsWellFounded.rank (bmsL r).Rel l
      ≤ IsWellFounded.rank (bmsL r).Rel ((bmsLStd r).gen n) := by
  obtain ⟨A, hA, hl⟩ := l.2
  induction hA generalizing l with
  | init n =>
    refine ⟨n, le_of_eq (congrArg _ (Subtype.ext ?_))⟩
    rw [← hl, entriesR_stair]
    rfl
  | @step A0 N hA0 ih =>
    let l0 : (bmsL r).State := ⟨entriesR A0, A0, hA0, rfl⟩
    obtain ⟨n, hn⟩ := ih l0 rfl
    refine ⟨n, le_trans ?_ hn⟩
    by_cases h0 : l0.1 = []
    · have hl' : l.1 = [] := by
        rw [← hl, entriesR_expand (Nat.succ_pos r)]
        show expandRL (r + 1) N l0.1 = []
        rw [h0, expandRL_nil]
      rw [Rewrite.rank_halted (show (bmsL r).halted l from hl')]
      exact zero_le
    · have hstep : l = (bmsL r).step l0 N := Subtype.ext (by
        rw [← hl, entriesR_expand (Nat.succ_pos r)]; rfl)
      rw [hstep]
      exact le_of_lt (IsWellFounded.rank_lt_of_rel ⟨h0, N, rfl⟩)

/-- Two-row BMS is the pair sequence system, rank for rank. -/
theorem rank_bmsL_one_eq_pair (s : (bmsL 1).State) :
    IsWellFounded.rank (bmsL 1).Rel s = PSS.pairOrdL (pairOfBmsHom.map s).1 := by
  rw [← PSS.rank_pairL_eq]
  exact (pairOfBmsHom.rank_map (fun k => ⟨k, rfl⟩) (fun s => by
    show s.1 = [] ↔ s.1.map (fun c => (c.head!, c.tail.head!)) = []
    rw [List.map_eq_nil_iff]) s).symm

theorem rank_bmsL_one_lt (s : (bmsL 1).State) :
    IsWellFounded.rank (bmsL 1).Rel s < Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  rw [rank_bmsL_one_eq_pair]
  have h : PSS.pairOrdEval.val (pairOfBmsHom.map s) ∈ Set.Iio
      (Notation.ExBuchholz.Term.val PSS.psiOmegaOmega) := by
    rw [← PSS.range_pairOrd]; exact Set.mem_range_self _
  exact h

/-- The two-row BMS generators are cofinal in `ψ_0(Ω_ω)`. -/
theorem iSup_rank_bmsL_one_gen :
    ⨆ N : Nat, succ (IsWellFounded.rank (bmsL 1).Rel ((bmsLStd 1).gen N))
      = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  refine le_antisymm (Ordinal.iSup_le (fun N => succ_le_of_lt (rank_bmsL_one_lt _)))
    (le_of_forall_lt (fun α hα => ?_))
  have himg : α ∈ Set.Iio (Notation.ExBuchholz.Term.val PSS.psiOmegaOmega) := hα
  rw [← PSS.range_pairOrd] at himg
  obtain ⟨p, hp⟩ := himg
  obtain ⟨N, hN⟩ := rank_le_genB 1 (bmsOfPairHom.map p)
  have hrank : IsWellFounded.rank (bmsL 1).Rel (bmsOfPairHom.map p) = α := by
    rw [bmsOfPairHom.rank_map (fun k => ⟨k, rfl⟩) (fun s => by
      show s.1 = [] ↔ s.1.map (fun x => [x.1, x.2]) = []
      rw [List.map_eq_nil_iff]) p, PSS.rank_pairL_eq]
    exact hp
  rw [hrank] at hN
  exact lt_of_lt_of_le (lt_succ_of_le hN)
    (Ordinal.le_iSup (fun N : Nat => succ (IsWellFounded.rank (bmsL 1).Rel ((bmsLStd 1).gen N))) N)

/-- **The three-row BMS generator `(0,0,0)(1,1,1)` has rank `ψ_0(Ω_ω)`.** -/
theorem rank_bmsL_gen_three_one :
    IsWellFounded.rank (bmsL 2).Rel ((bmsLStd 2).gen 1)
      = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  rw [rank_gen_eq_iSup 1]
  exact iSup_rank_bmsL_one_gen

end BMSGen

/-- **The same under the rule on all matrices.** -/
theorem rkL_bgen3_one : rkL 2 (bgen3 1) = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  rw [show bgen3 1 = ((bmsLHomAll 2).map ((bmsLStd 2).gen 1)).1 from rfl,
    rkL_eq ((bmsLHomAll 2).map ((bmsLStd 2).gen 1))]
  exact (rank_bmsAllL_of_bmsL 2 _).trans rank_bmsL_gen_three_one

/-- **At `n = 1` the lift keeps the rank**: the content
`(0,0,0)(1,1,0)(2,2,1) = lift 3 ((0,0,0)(1,1,1))` and the BMS matrix
`(0,0,0)(1,1,1)` both have rank `ψ_0(Ω_ω)`. -/
theorem rkL_lift_bgen3_one : rkL 2 (lift 3 (bgen3 1)) = rkL 2 (bgen3 1) := by
  rw [← cgen_two_eq_lift, rkL_cgen_three, rkL_bgen3_one]

/-- The same, stated for the generators of the two systems: the three-row
DBMS generator `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` and the three-row BMS generator
`(0,0,0)(1,1,1)` have the same rank. -/
theorem rank_genL_two_three_eq_bms :
    Rewrite.rank (dbmsL_wf 2) (genL 2 3)
      = @IsWellFounded.rank _ (bmsL 2).Rel ⟨bmsL_wf 2⟩ ((bmsLStd 2).gen 1) := by
  rw [rank_gen_three_three, rank_bmsL_gen_three_one]

/-- **The ordinal of three-row DBMS, through the lift**:
`sup_n ω ^ rkL 2 (lift 3 ((0,0,0)(1,1,1)⋯(n,n,n)))`. -/
theorem iSup_rank_dbmsL_two_lift :
    ⨆ l : (dbmsL 2).State, succ (Rewrite.rank (dbmsL_wf 2) l)
      = ⨆ n : Nat, ω ^ rkL 2 (lift 3 (bgen3 n)) := by
  haveI : IsWellFounded (dbmsL 2).State (dbmsL 2).Rel := ⟨dbmsL_wf 2⟩
  rw [iSup_rank_dbmsL_two]
  simp only [← cgen_two_eq_lift]
  have hmono : ∀ m n : Nat, m ≤ n → ω ^ rkL 2 (cgen 2 m) ≤ ω ^ rkL 2 (cgen 2 n) := by
    intro m n h
    rw [← rank_genL_eq, ← rank_genL_eq, Rewrite.rank_def, Rewrite.rank_def]
    exact rank_gen_mono 2 h
  refine le_antisymm (Ordinal.iSup_le (fun n => ?_)) (Ordinal.iSup_le (fun n => ?_))
  · exact le_trans (hmono n (n + 2) (by omega))
      (Ordinal.le_iSup (fun n : Nat => ω ^ rkL 2 (cgen 2 (n + 2))) n)
  · exact Ordinal.le_iSup (fun n : Nat => ω ^ rkL 2 (cgen 2 n)) (n + 2)

/-- The content generators go up strictly: `[0]` takes `cgen 2 (n + 1)` to
`cgen 2 n`. -/
theorem rkL_cgen_two_lt_succ (n : Nat) : rkL 2 (cgen 2 n) < rkL 2 (cgen 2 (n + 1)) := by
  have h := rank_gen_lt_succ 2 n
  rw [← Rewrite.rank_def (dbmsL_wf 2), ← Rewrite.rank_def (dbmsL_wf 2), rank_genL_eq,
    rank_genL_eq] at h
  exact (opow_lt_opow_iff_right one_lt_omega0).mp h

/-- So the first open content rank is above `ψ_0(Ω_ω)`:
`ψ_0(Ω_ω) < rkL 2 ((0,0,0)(1,1,0)(2,2,1)(3,3,2))`. -/
theorem val_psiOmegaOmega_lt_rkL_cgen_two_four :
    Notation.ExBuchholz.Term.val PSS.psiOmegaOmega < rkL 2 (cgen 2 4) := by
  rw [← rkL_cgen_three]
  exact rkL_cgen_two_lt_succ 3

end Googology.Trans.DBMS
