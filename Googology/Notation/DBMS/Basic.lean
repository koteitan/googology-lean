import Googology.Notation.BMS

/-!
# DBMS as an expansion system

DBMS expands exactly as BM4 does.  What differs is where the expansion starts:
BM4's generators are the stairs `(0,…,0)(1,…,1)⋯(n,…,n)`, and DBMS's are the
arrays whose column `i` holds `i - k` in row `k`, truncated at `0`:

    (0,0,0)(1,0,0)(2,1,0)(3,2,1)⋯

So `dbms r` is `Notation.BMS.bms r` with `dstair` in place of `stair`, and a
matrix is a DBMS standard form when it is reachable from one of these.  The
two notions of standard form are genuinely different: `(0,0)(1,1)` is a BM4
standard form and not a DBMS one, and `(0,0)(1,0)(2,1)` is the other way
round.  With one row they agree, because `i - 0 = i`.

Termination holds, for every number of rows: `dbms_terminates`.  It does not
come from the generators at all.  `Notation.BMS.terminates_any` says expansion
ends from **any** array, standard or not — the label whose height descends is
the `Λ`-chain, which never looks at the array — so where a system starts makes
no difference to whether it halts.  `dbms_wf` and `dbmsEval` follow.
-/

namespace Googology.Notation.DBMS

open BM4

/-- The DBMS generators: column `i` holds `i - k` in row `k`. -/
def dstair (r n : ℕ) : Arr r := ⟨n + 1, fun i k => i - k⟩

@[simp] theorem dstair_len (r n : ℕ) : (dstair r n).len = n + 1 := rfl

@[simp] theorem dstair_col (r n i k : ℕ) : (dstair r n).col i k = i - k := rfl

/-- Arrays with `r` rows reachable from a DBMS generator. -/
inductive DStd (r : ℕ) : Arr r → Prop
  | init (n : ℕ) : DStd r (dstair r n)
  | step {A : Arr r} (N : ℕ) : DStd r A → DStd r (expand A N)

/-- A DBMS standard form with `r` rows. -/
def DStdElt (r : ℕ) : Type := {A : Arr r // DStd r A}

/-- **DBMS with `r` rows**, as an expansion system. -/
noncomputable def dbms (r : ℕ) : Rewrite where
  State := DStdElt r
  step := fun A k => ⟨expand A.1 k, DStd.step k A.2⟩
  halted := fun A => A.1.len = 0

@[simp] theorem dbms_step_val (r : ℕ) (A : DStdElt r) (k : ℕ) :
    ((dbms r).step A k).1 = expand A.1 k := rfl

@[simp] theorem dbms_halted_iff (r : ℕ) (A : DStdElt r) :
    (dbms r).halted A ↔ A.1.len = 0 := Iff.rfl

/-- The generators. -/
def dbmsStd (r : ℕ) : (dbms r).Std where
  Standard := fun _ => True
  gen := fun n => ⟨dstair r n, DStd.init n⟩
  gen_std := fun _ => trivial
  step_std := fun _ _ _ => trivial


/-- The DBMS standard arrays sit inside all arrays. -/
def dbmsSim (r : ℕ) : Sim (dbms r) (Googology.Notation.BMS.bmsAll r) where
  map := Subtype.val
  map_rel := fun _ _ h => ⟨h.1, h.2.choose, congrArg Subtype.val h.2.choose_spec⟩

/-- **DBMS terminates, for every number of rows.**  Not because of its
generators: expansion ends from any array at all. -/
theorem dbms_terminates (r : ℕ) : (dbms r).Terminates :=
  (dbmsSim r).terminates (Googology.Notation.BMS.bmsAll_wf r)

/-- **And is well founded.** -/
theorem dbms_wf (r : ℕ) : (dbms r).WF :=
  (dbmsSim r).wf (Googology.Notation.BMS.bmsAll_wf r)

/-- DBMS carries an ordinal measure: the rank of one-step expansion. -/
noncomputable def dbmsEval (r : ℕ) :
    Eval (dbms r) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (dbms_wf r)

end Googology.Notation.DBMS
