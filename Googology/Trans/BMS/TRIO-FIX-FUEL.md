[← Back](../README.md) | [English](TRIO-FIX-FUEL.md) | [Japanese](TRIO-FIX-FUEL-ja.md)

# Fix Fuel: a fuel that grows with the term

The merged rules of [koteitan/trio](https://github.com/koteitan/trio)
([`TrioRulesAll.lean`](TrioRulesAll.lean), Fixes A–E and N) run every recursion on
one fixed fuel, `TrioRules.fuel = 200`. Past depth 200 a recursion stops early and
the matrix is wrong. [`TrioTree.lean`](TrioTree.lean) found two different standard
terms, `ψ_0(Ω + T_205)` and `ψ_0(Ω + T_206)` (`T_n` = `n` nested `ψ_0`, depths 206
and 207), with the same matrix.

## The patch

Files: [`TrioFixFuel.lean`](TrioFixFuel.lean) (the patch),
[`TrioFixFuelE0.lean`](TrioFixFuelE0.lean) (theorems below `ε₀`),
[`TrioFixFuelSheet.lean`](TrioFixFuelSheet.lean) (checks).

* No rule changes. Every definition that reads `fuel` gets a parameter `F`
  (the table in the docstring of `TrioFixFuel.lean`); the bodies are the old
  ones with `fuel` replaced by `F`.
* The fuel of a normal form `α` is `fuelOf α = max 200 (odDep α)`, `odDep` the
  nesting depth. The builder is `MD α = MF (fuelOf α) α`.
* The fuel of a term `α` is `fuelT α = max 200 (tDep α)` (depth with subscripts),
  used for both the reading `ofTerm` and the builder:
  `trioMatrixLD α = toRows (MF (fuelT α) (ofTerm (fuelT α) α))`.

## Proved

* `MF_200 : MF 200 = MAll`: at fuel 200 the copies are the old program.
* `MD_eq_MAll : odDep α ≤ 200 → MD α = MAll α`, and for terms
  `trioMatrixLD_eq : tDep α ≤ 200 → trioMatrixLD α = trioMatrixLAll α`.
  So up to depth 200 nothing changes.
* Below `ε₀`, at every depth: `trioMatrixLD α = trioMatrix α`
  (`trioMatrixLD_eq_trioMatrix`), so
  `trioMatrixLD α < trioMatrixLD β ↔ α < β` and `trioMatrixLD` is injective
  (`trioMatrixLD_lt_iff`, `trioMatrixLD_injective`).
* `MstepAll_countable`: for a countable `α` (`lvlO F α = none`), the merged step
  equals the step of rules 1–10, for every `F` and every `Mf`.
  `MstepAll_countable_200` is the fuel-200 case: the statement that
  `TrioRulesAll.lean` lists as not proved.

The proof is a simulation: with no regime, Fixes B–D and N never act, and the
Fix N program (`blockN`, `placeUnitsN`) runs step by step as the plain program
(`blockF`, `placeUnits`) on the inner state.

## Checked (`#guard`, not proved)

* All 932 `#guard`s of [`TrioRulesAllSheet.lean`](TrioRulesAllSheet.lean) for the
  patched map, with the same numbers: the sheet rows, the order checks (783 and
  784 chosen matrices, 0 disagreements), the guards of Fixes A–E and N, and the
  step counts `(171, 0), (32, 6), (152, 7), (870, 257)`.
* 23 new `#guard`s:
  * Every label used has depth `≤ 8`; the patched matrix = the `TrioRulesAll` matrix on all of them.
  * Fuel `odDep α` alone gives the same matrix as fuel `fuelOf α + 200` on every label.
  * `ψ_0(Ω + T_205)`, `ψ_0(Ω + T_206)`: the old map gives one matrix, the new map gives
    two, in the right order.
  * On `ψ_0(Ω + T_n)` the new map equals `TrioTree.trioE` (the fuel-free map, proved to
    keep the order and to give standard forms) for depths 191, 201, …, 301. The old map
    equals it only up to depth 200.
  * Depths 191–251 of that family: strictly increasing matrices.
  * `ψ_0` towers below `ε₀`: at depths 202, 210, 211, 260 equal to `trioMatrix`; the old
    map gives depths 210 and 211 one matrix.
  * Uncountable family `ω^ω^…^(Ω+1)`, depth 200–252: at depth 201 fuel 200 cannot find
    the level `Ω_1` (it reads the ordinal as countable); from depth 203 the old matrices
    are in the wrong order. The new map is strictly increasing on depths 197–209, and
    fuel `fuelOf α + 50` gives the same matrix at depths 201, 202, 252.
* yaBMS (`bms -s`, `bms -c`, outside Lean): the new matrices of the three families near
  depth 200 are standard and increasing. The old matrices of the uncountable family are
  not standard from depth 205 and in the wrong order from depth 203.

## Still open

* Two fuel-200 reads stay under the patched builder: `lvl` inside
  `TrioRules.cmpAtomWith` and `cmpExp` inside `TrioRules.add`. They do not depend on
  the depth of the input: the first is only called on atoms and stops after one step
  (theorem `lvl_atom`), the second only on the constants `ω + 1` and `Ω + 1`.

* That `fuelOf α` is enough for every `α` above `ε₀` (more fuel changes nothing) is
  not proved. It is checked on the sheet labels and the families above.
* Injectivity above `ε₀` is not proved (it is not proved at fuel 200 either).
  The result of `TrioTreeRules.lean` (terms with subscripts 0 or 1) is for
  `TrioRules` at fuel 200; it is not carried over to the patched merged map.
* Computation: deep uncountable terms like `Ω_{Ω_{…}}` with depth 150 do not finish
  (the builder calls itself many times on the same argument). That is a cost of the
  program, not of the fuel.
