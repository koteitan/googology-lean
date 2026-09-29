import Googology.Trans.PSS.TR.Term
import Googology.Trans.PSS.Phi.Order

/-!
# The translation `𝒯` into Wilken's `T¹`

This is the translation of `proof/PROOF-2.md` §12.1, as in `por/tr.py`
(`T_term`, `T_eps`, `T_node`).  A term `s = (k, ch)` of a pair sequence
(`Forest.Tm`) is sent to a principal term of level `k`:

* **no children:** `ϑ_k(0)`;
* **non-epsilon** (the last child does not have `y = k + 1`): with `hi` the
  children with `y = k + 1` and `lo` the children with `y ≤ k`,
  `𝒯_k(s) = ω^Z` at level `k`, where
  `Z = [𝒯_k((k, hi)) if hi ≠ (), else Ω_k if k ≥ 1] ⊕ 𝒯(lo_1) ⊕ ⋯`;
* **epsilon** (the last child has `y = k + 1`): with children `H_1..H_r`,
  `X_i = log_ω 𝒯_{k+1}(H_i) = D_i + ρ_i` (`D_i` the part of level `≥ k + 1`),
  the final run `H_{j+1}..H_r` with `D_i = D_r =: Δ`,
  `c = ω^{ρ_{j+1}} ⊕ ⋯ ⊕ ω^{ρ_r}` and `η = -1 + c`; if `j > 0` and
  `e_p = 𝒯_k((k, H_1..H_j))` is above every `ϑ_k`-subterm of `Δ`, then
  `η = e_p ⊕ (-1 + c)`.  `𝒯_k(s) = ϑ_k(Δ ⊕ η)`.

A node (a list of root terms) goes to the sum of the images of its roots
(`trNode`).  The recursion is on a fuel; `trTm s = trF s.size s`.
-/

namespace Googology.Trans.PSS.TR

open Forest

/-- The level of the first summand of `ρ` (`0` for `ρ = 0`): `ω^ρ` is formed at
this level. -/
def expLvl (ρ : List WP) : ℕ :=
  match ρ with
  | p :: _ => p.lvl
  | [] => 0

/-- The start `j` of the final run of equal `D`s: the length of the list with its
last run of entries equal to the last entry removed. -/
def runStart (ds : List (List WP)) : ℕ :=
  match ds.getLast? with
  | some Δ => (ds.reverse.dropWhile (fun d => d == Δ)).length
  | none => 0

/-- The epsilon case, from the images `vs` of the children `H_1..H_r` at level
`k + 1` and the image `pre j` of the prefix `(k, H_1..H_j)` (`T_eps`). -/
def epsImg (k : ℕ) (vs : List WP) (pre : ℕ → WP) : WP :=
  let mons := vs.map (fun v => splitLevel (logOmega v) (k + 1))
  let Δ := (mons.getLast?.map Prod.fst).getD []
  let j := runStart (mons.map Prod.fst)
  let c := addAll ((mons.drop j).map (fun m => [omegaExp m.2 (expLvl m.2)]))
  let η := minusOnePlus c
  let η' :=
    if 0 < j then
      let ep := pre j
      if (starS k Δ).any (fun q => cmpP ep q != .gt) then η else addS [ep] η
    else η
  .th k (addS Δ η')

/-- The translation with fuel: `trF f s = 𝒯_{y(s)}(s)` when `f ≥ size s`. -/
def trF : ℕ → Tm → WP
  | 0, s => .th s.y []
  | f + 1, .node k ch =>
    match ch.getLast? with
    | none => .th k []
    | some last =>
      if last.y = k + 1 then
        epsImg k (ch.map (trF f)) (fun j => trF f (.node k (ch.take j)))
      else
        let hi := ch.filter (fun c => decide (c.y = k + 1))
        let lo := ch.filter (fun c => decide (c.y ≤ k))
        let head : List (List WP) :=
          if hi ≠ [] then [[trF f (.node k hi)]] else if 1 ≤ k then [[.th k []]] else []
        omegaExp (addAll (head ++ lo.map (fun c => [trF f c]))) k

/-- **The translation** `𝒯_{y(s)}(s)` of a term. -/
def trTm (s : Tm) : WP := trF s.size s

/-- The translation of a node (a list of root terms): the sum of the images of
the roots (`T_node`). -/
def trNode (S : List Tm) : List WP := addAll (S.map (fun t => [trTm t]))

/-! ## Checks against `por/tr.py`

Each line is `python3 tr.py M` for a matrix `M` (written as its root terms),
with `show` of `tr.py`. -/

/-- `(0,0) ↦ 1`. -/
example : trNode [.node 0 []] = [one] := by decide
/-- `(0,0)(0,0) ↦ 1+1`. -/
example : trNode [.node 0 [], .node 0 []] = [one, one] := by decide
/-- `(0,0)(1,0) ↦ t0(1)`. -/
example : trNode [.node 0 [.node 0 []]] = [.th 0 [one]] := by decide
/-- `(0,0)(1,1) ↦ t0(W)`. -/
example : trNode [.node 0 [.node 1 []]] = [.th 0 [om 1]] := by decide
/-- `(0,0)(1,1)(1,1) ↦ t0(W+1)`. -/
example : trNode [.node 0 [.node 1 [], .node 1 []]] = [.th 0 [om 1, one]] := by decide
/-- `(0,0)(1,1)(2,0) ↦ t0(W+t0(1))`. -/
example : trNode [.node 0 [.node 1 [.node 0 []]]] = [.th 0 [om 1, .th 0 [one]]] := by decide
/-- `(0,0)(1,1)(1,0) ↦ t0(t0(W))`. -/
example : trNode [.node 0 [.node 1 [], .node 0 []]] = [.th 0 [.th 0 [om 1]]] := by decide
/-- `(0,0)(1,1)(2,1) ↦ t0(W+W)`. -/
example : trNode [.node 0 [.node 1 [.node 1 []]]] = [.th 0 [om 1, om 1]] := by decide
/-- `(0,0)(1,1)(2,2) ↦ t0(t1(W2))`. -/
example : trNode [.node 0 [.node 1 [.node 2 []]]] = [.th 0 [.th 1 [om 2]]] := by decide
/-- `(0,0)(1,0)(1,0) ↦ t0(1+1)`. -/
example : trNode [.node 0 [.node 0 [], .node 0 []]] = [.th 0 [one, one]] := by decide
/-- `(0,0)(1,1)(2,2)(1,1) ↦ t0(W+t0(t1(W2)))`. -/
example : trNode [.node 0 [.node 1 [.node 2 []], .node 1 []]] =
    [.th 0 [om 1, .th 0 [.th 1 [om 2]]]] := by decide
/-- `(0,0)(1,1)(2,1)(3,0) ↦ t0(t1(1))`. -/
example : trNode [.node 0 [.node 1 [.node 1 [.node 0 []]]]] = [.th 0 [.th 1 [one]]] := by
  decide
/-- `(0,0)(1,1)(2,1)(1,1) ↦ t0(W+t0(W+W))`. -/
example : trNode [.node 0 [.node 1 [.node 1 []], .node 1 []]] =
    [.th 0 [om 1, .th 0 [om 1, om 1]]] := by decide
/-- `(0,0)(1,1)(2,2)(3,1) ↦ t0(t1(W2+W))`. -/
example : trNode [.node 0 [.node 1 [.node 2 [.node 1 []]]]] = [.th 0 [.th 1 [om 2, om 1]]] := by
  decide
/-- `(0,0)(1,1)(2,2)(3,2) ↦ t0(t1(W2+W2))`. -/
example : trNode [.node 0 [.node 1 [.node 2 [.node 2 []]]]] = [.th 0 [.th 1 [om 2, om 2]]] := by
  decide

end Googology.Trans.PSS.TR
