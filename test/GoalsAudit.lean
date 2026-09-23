import Googology.Goals
import Lean

/-!
# The audit of the goal records

Prints, in format `1` of section 7.7 of `spec.md`, one line per record and
column, and then the axioms the records use.  `scripts/check_readme.py`
compares the output with the tables of `README.md` and `README-ja.md`:

```sh
lake env lean test/GoalsAudit.lean > audit.txt
python3 scripts/check_readme.py --audit audit.txt
```
-/

-- The first line is not a marker, so that the prefix a runner puts before a
-- message (`lake build` writes `info: <file>:<line>:<col>: `) lands on it.
#eval do
  IO.println "the goal records of Googology.Goals.audit"
  Googology.AuditLine.printAll Googology.Goals.audit

open Lean Elab Command in
/-- Prints `GOALS-AXIOMS` and the axioms `Googology.Goals.audit` depends on,
sorted and separated by commas. -/
elab "#goals_axioms" : command => do
  let axs ← liftCoreM <| collectAxioms ``Googology.Goals.audit
  let names := (axs.map toString).qsort (· < ·)
  logInfo m!"the axioms of Googology.Goals.audit\nGOALS-AXIOMS\t{",".intercalate names.toList}"

#goals_axioms
