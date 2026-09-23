import Googology.Trans.DBMS.Blocks
import Googology.Trans.DBMS.TwoRow
import Googology.Trans.DBMS.ZeroRow

/-!
# Three-row DBMS: what the ranks are known to be

`Blocks.lean` reduces the rank of DBMS with `r + 1` rows to the rank of the
rule of BM4 on the content system `CReach r`.  This file adds what is known at
three rows.

**The first generator that uses every row.**  The DBMS generator with `s + 1`
rows and `s + 2` columns expands to the generators with `s` rows and a row of
zeros underneath (`expandRL_dsE`).  So its rank is the supremum of the ranks
of the `s`-row generators (`rank_gen_top`), which is the supremum of the ranks
of all `s`-row standard forms (`rank_le_gen`).  With three rows:

    rank (0,0,0)(1,0,0)(2,1,0)(3,2,1) = ψ_0(Ω_ω)          (rank_gen_three_three)

and so, by `rkL_dstair`, the content `(0,0,0)(1,1,0)(2,2,1)` satisfies
`ω ^ rank = ψ_0(Ω_ω)` (`opow_rkL_cgen_three`), hence its rank is `ψ_0(Ω_ω)`
(`rkL_cgen_three`).  The generators with at most three columns are two-row
generators with a row of zeros underneath (`zeroRow_dsE_of_le`), so their
ranks are those of the two-row generators (`rank_dbmsL_homSucc`), which
`TwoRow.lean` evaluates by `dOrdL` as `1, ω, ε₀`; these three values are not
restated here as theorems.

**The generators, in general.**  The rank of the three-row generator with
`n + 1` columns is `ω ^ rank(cgen 2 n)` (`rkL_dstair`), and the generators are
strictly increasing (`rank_gen_lt_succ`) and bound every standard form
(`rank_le_gen`).  So the ordinal of three-row DBMS, the supremum of its ranks,
is `sup_n ω ^ rank(cgen 2 n)` (`iSup_rank_dbmsL_two`).  From `n = 4` on these
ranks are not computed here.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Notation.DBMS
open Googology.Trans.BMS

/-- The generator of DBMS with `r + 1` rows and `n + 1` columns, as a state. -/
def genL (r n : Nat) : (dbmsL r).State := (dbmsLStd r).gen n

theorem genL_val (r n : Nat) : (genL r n).1 = dsE (r + 1) n := rfl

section Gen

variable (r : Nat)

local instance instWF (r : Nat) : IsWellFounded (dbmsL r).State (dbmsL r).Rel := ⟨dbmsL_wf r⟩

theorem dsE_dropLast (s n : Nat) : (dsE s (n + 1)).dropLast = dsE s n := by
  rw [dsE, List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat]
  rfl

/-- `[0]` takes the generator with `n + 2` columns to the one with `n + 1`. -/
theorem step_genL_zero (n : Nat) : (dbmsL r).step (genL r (n + 1)) 0 = genL r n := by
  apply Subtype.ext
  show expandRL (r + 1) 0 (dsE (r + 1) (n + 1)) = dsE (r + 1) n
  rw [expandRL_zero (r + 1) _ (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    simp), dsE_dropLast]

theorem genL_ne_nil (n : Nat) : (genL r n).1 ≠ [] := by
  rw [genL_val]; simp [dsE]

/-- **The generators are strictly increasing in rank.** -/
theorem rank_gen_lt_succ (n : Nat) :
    IsWellFounded.rank (dbmsL r).Rel (genL r n) < IsWellFounded.rank (dbmsL r).Rel (genL r (n + 1)) := by
  refine IsWellFounded.rank_lt_of_rel ⟨genL_ne_nil r (n + 1), 0, ?_⟩
  exact (step_genL_zero r n).symm

theorem rank_gen_mono {m n : Nat} (h : m ≤ n) :
    IsWellFounded.rank (dbmsL r).Rel (genL r m) ≤ IsWellFounded.rank (dbmsL r).Rel (genL r n) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (le_of_lt (rank_gen_lt_succ r _))

/-- **Every standard form is bounded by a generator.** -/
theorem rank_le_gen (l : (dbmsL r).State) :
    ∃ n, IsWellFounded.rank (dbmsL r).Rel l ≤ IsWellFounded.rank (dbmsL r).Rel (genL r n) := by
  obtain ⟨A, hA, hl⟩ := l.2
  induction hA generalizing l with
  | init n =>
    refine ⟨n, le_of_eq (congrArg _ (Subtype.ext ?_))⟩
    rw [← hl, genL_val, entriesR_dstair_eq_dsE]
  | @step A0 N hA0 ih =>
    let l0 : (dbmsL r).State := ⟨entriesR A0, A0, hA0, rfl⟩
    obtain ⟨n, hn⟩ := ih l0 rfl
    refine ⟨n, le_trans ?_ hn⟩
    by_cases h0 : l0.1 = []
    · have hl' : l.1 = [] := by
        rw [← hl, entriesR_expand (Nat.succ_pos r)]
        show expandRL (r + 1) N l0.1 = []
        rw [h0, expandRL_nil]
      rw [Rewrite.rank_halted (show (dbmsL r).halted l from hl')]
      exact zero_le
    · have hstep : l = (dbmsL r).step l0 N := Subtype.ext (by
        rw [← hl, entriesR_expand (Nat.succ_pos r)]; rfl)
      rw [hstep]
      exact le_of_lt (IsWellFounded.rank_lt_of_rel ⟨h0, N, rfl⟩)

/-- The supremum of the generators' ranks, over the tails. -/
theorem iSup_succ_rank_gen_shift (m : Nat) :
    ⨆ N : Nat, succ (IsWellFounded.rank (dbmsL r).Rel (genL r (m + N)))
      = ⨆ n : Nat, IsWellFounded.rank (dbmsL r).Rel (genL r n) := by
  refine le_antisymm (Ordinal.iSup_le (fun N => ?_)) (Ordinal.iSup_le (fun n => ?_))
  · exact le_trans (succ_le_of_lt (rank_gen_lt_succ r _))
      (Ordinal.le_iSup (fun n => IsWellFounded.rank (dbmsL r).Rel (genL r n)) _)
  · exact le_trans (le_trans (rank_gen_mono r (show n ≤ m + n by omega)) (le_succ _))
      (Ordinal.le_iSup (fun N : Nat => succ (IsWellFounded.rank (dbmsL r).Rel (genL r (m + N)))) n)

end Gen

/-- **The first generator with `r + 2` rows that uses every row has rank the
supremum of the ranks of the generators with `r + 1` rows.**  It expands to
them with a row of zeros underneath, and that keeps the rank. -/
theorem rank_gen_top (r : Nat) :
    @IsWellFounded.rank _ (dbmsL (r + 1)).Rel ⟨dbmsL_wf (r + 1)⟩ (genL (r + 1) (r + 2))
      = ⨆ n : Nat, @IsWellFounded.rank _ (dbmsL r).Rel ⟨dbmsL_wf r⟩ (genL r n) := by
  haveI : IsWellFounded (dbmsL r).State (dbmsL r).Rel := ⟨dbmsL_wf r⟩
  haveI : IsWellFounded (dbmsL (r + 1)).State (dbmsL (r + 1)).Rel := ⟨dbmsL_wf (r + 1)⟩
  have hstep : ∀ N, (dbmsL (r + 1)).step (genL (r + 1) (r + 2)) N
      = (dbmsL_homSucc r).map (genL r (r + 1 + N)) := by
    intro N
    apply Subtype.ext
    show expandRL (r + 1 + 1) N (dsE (r + 1 + 1) (r + 1 + 1)) = zeroRow (dsE (r + 1) (r + 1 + N))
    exact expandRL_dsE (r + 1) N
  rw [Rewrite.rank_eq_iSup_nat (genL_ne_nil (r + 1) (r + 2))]
  simp only [hstep]
  have hr : ∀ a : (dbmsL r).State, IsWellFounded.rank (dbmsL (r + 1)).Rel ((dbmsL_homSucc r).map a)
      = IsWellFounded.rank (dbmsL r).Rel a := fun a =>
    (dbmsL_homSucc r).rank_map (fun k => ⟨k, rfl⟩) (fun s => (zeroRow_nil_iff s.1).symm) a
  simp only [hr]
  exact iSup_succ_rank_gen_shift r (r + 1)

/-! ### Two rows: the supremum is `ψ_0(Ω_ω)` -/

theorem iSup_rank_genL_one :
    ⨆ n : Nat, @IsWellFounded.rank _ (dbmsL 1).Rel ⟨dbmsL_wf 1⟩ (genL 1 n)
      = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  haveI : IsWellFounded (dbmsL 1).State (dbmsL 1).Rel := ⟨dbmsL_wf 1⟩
  -- every rank of `dbmsL 1` is the ordinal of a two-row matrix
  have hval : ∀ c : (dbmsL 1).State, ∃ a : dbmsL2.State,
      IsWellFounded.rank (dbmsL 1).Rel c = dOrdL a.1 := by
    intro c
    obtain ⟨a, rfl⟩ := dbmsL2ToL_surjective c
    exact ⟨a, by rw [rank_dbmsL2ToL, rank_dbmsL2_eq]⟩
  refine le_antisymm (Ordinal.iSup_le (fun n => ?_)) (le_of_forall_lt (fun α hα => ?_))
  · obtain ⟨a, ha⟩ := hval (genL 1 n)
    rw [ha]
    exact le_of_lt (dOrdL_lt_val (dform_state a))
  · have himg : α ∈ Set.Iio (Notation.ExBuchholz.Term.val PSS.psiOmegaOmega) := hα
    rw [← dbmsL2Ord_image] at himg
    obtain ⟨a, -, ha⟩ := himg
    obtain ⟨n, hn⟩ := rank_le_gen 1 (dbmsL2ToL.map a)
    rw [rank_dbmsL2ToL, rank_dbmsL2_eq, ← dbmsL2OrdEval_val, ha] at hn
    exact lt_of_lt_of_le (lt_of_le_of_lt hn (rank_gen_lt_succ 1 n))
      (Ordinal.le_iSup (fun n => IsWellFounded.rank (dbmsL 1).Rel (genL 1 n)) (n + 1))

/-- **The three-row generator `(0,0,0)(1,0,0)(2,1,0)(3,2,1)` has rank
`ψ_0(Ω_ω)`**, the ordinal of two-row DBMS. -/
theorem rank_gen_three_three :
    Rewrite.rank (dbmsL_wf 2) (genL 2 3) = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  rw [Rewrite.rank_def]
  exact (rank_gen_top 1).trans iSup_rank_genL_one

/-- The rank of a three-row generator, through its content. -/
theorem rank_genL_eq (r n : Nat) :
    Rewrite.rank (dbmsL_wf r) (genL r n) = ω ^ rkL r (cgen r n) := by
  rw [rank_dbmsL_eq_rkL, genL_val, ← entriesR_dstair_eq_dsE, rkL_dstair]

/-- **The content `(0,0,0)(1,1,0)(2,2,1)` of that generator.** -/
theorem opow_rkL_cgen_three :
    ω ^ rkL 2 (cgen 2 3) = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  rw [← rank_genL_eq, rank_gen_three_three]

/-- **So the content `(0,0,0)(1,1,0)(2,2,1)` itself has rank `ψ_0(Ω_ω)`** under
the rule of BM4 on all three-row matrices; `ψ_0(Ω_ω)` is a fixed point of
`x ↦ ω ^ x`.  This matrix is not a standard form of three-row BMS. -/
theorem rkL_cgen_three :
    rkL 2 (cgen 2 3) = Notation.ExBuchholz.Term.val PSS.psiOmegaOmega := by
  have h := opow_rkL_cgen_three
  refine le_antisymm ?_ (not_lt.mp (fun hlt => ?_))
  · rw [← h]; exact Ordinal.right_le_opow _ one_lt_omega0
  · have := opow_lt_val_psiOmegaOmega hlt
    rw [h] at this
    exact lt_irrefl _ this

/-- **The ordinal of three-row DBMS** — the supremum of `rank + 1` over its
standard forms — is the supremum over the generators, `sup_n ω ^ rank(cgen 2 n)`. -/
theorem iSup_rank_dbmsL_two :
    ⨆ l : (dbmsL 2).State, succ (Rewrite.rank (dbmsL_wf 2) l)
      = ⨆ n : Nat, ω ^ rkL 2 (cgen 2 n) := by
  haveI : IsWellFounded (dbmsL 2).State (dbmsL 2).Rel := ⟨dbmsL_wf 2⟩
  simp only [← rank_genL_eq, Rewrite.rank_def]
  refine le_antisymm (Ordinal.iSup_le (fun l => ?_)) (Ordinal.iSup_le (fun n => ?_))
  · obtain ⟨n, hn⟩ := rank_le_gen 2 l
    exact le_trans (succ_le_of_lt (lt_of_le_of_lt hn (rank_gen_lt_succ 2 n)))
      (Ordinal.le_iSup (fun n => IsWellFounded.rank (dbmsL 2).Rel (genL 2 n)) (n + 1))
  · exact le_trans (le_succ _)
      (Ordinal.le_iSup (fun l : (dbmsL 2).State => succ (IsWellFounded.rank (dbmsL 2).Rel l))
        (genL 2 n))

end Googology.Trans.DBMS
