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

Termination is **not** proved here.  The label-system proof this library
imports is about arrays reachable from a stair; whether it carries over to
these generators is not settled in this file.  One row does terminate, and
`Trans/DBMS/OneRow.lean` shows it by translation.
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

end Googology.Notation.DBMS
