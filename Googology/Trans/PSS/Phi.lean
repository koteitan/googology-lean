import Googology.Trans.PSS.Phi.Defs
import Googology.Trans.PSS.Phi.Order
import Googology.Trans.PSS.Phi.Bridge
import Googology.Trans.PSS.Phi.Std
import Googology.Trans.PSS.Phi.LemmaC
import Googology.Trans.PSS.Phi.Lh
import Googology.Trans.PSS.Phi.Term
import Googology.Trans.PSS.Phi.Nodes
import Googology.Trans.PSS.Phi.CNF
import Googology.Trans.PSS.Phi.LogMono
import Googology.Trans.PSS.Phi.LemmaR

/-!
# The term operations of `Φ` give standard matrices

`POR.md` §3 builds the pattern `Φ(M)` of a standard pair sequence from the
operations anchor, `log`, `Coll_A` and the reach `lh` on terms.  This file
collects what is proved about them, following `proof/COMB.md`.

## Contents

* `Phi/Defs.lean`: the operations, computable and close to `por/phi.py`, with
  small examples checked by `decide`.  Terms are trees `Forest.Tm`; an ordinal
  is a list of root terms, with matrix `mat`.  `lh N = lhF (fuelOf N) N`, where
  the fuel is one more than the height of the last child (COMB §8, Theorem T).
* `Phi/Order.lean`: the linear order on terms (`Tm.cols_injective`), the sum
  with absorption `addT` (K2: `le_addT`; monotone: `addT_lt_addT`).
* `Phi/Bridge.lean`: **Theorem SC on terms** (`sc_mat_iff`, `ctps_cols_iff`):
  a matrix `mat ts` is standard iff `ts ≠ []`, the roots have `y = 0`, the root
  terms are non-increasing, and each satisfies the tree condition `TGood []`
  ((A), Sib and G\* at every node, with the context of ancestors).  So a list
  of terms is a node iff it is non-increasing and each term is standard
  (`stdOrd_iff`, COMB S1).
* `Phi/Std.lean`: Lemma 4 (`std_of_tgood_y0`), **Lemma 2.4 (i)**
  (`std_anchor`), **Lemma 6** (`stdOrd_log0`, `stdOrd_bigL`), and
  **Lemma 2.4 (ii)** (`stdOrd_lhF_of_not_eps`).
* `Phi/LemmaC.lean`: **Lemma 10** (`coll_lt_coll`) and **Lemma C**
  (`std_lemmaC`).
* `Phi/Lh.lean`: **Lemma 2.4 (iii)**: every fold input is standard
  (`std_foldInputs`), so `lhF f N` is a node for every fuel `f`
  (`stdOrd_lhF`, `stdOrd_lh`).
* `Phi/Term.lean`: **Theorem T** (`lhF_eq_lh`): for every term `N`, standard or
  not, `lhF f N = lh N` for all `f ≥ fuelOf N`.  The proof follows the
  provenance invariant of COMB §8 (`Inv`, `jump_inv`, `lhF_stable`).
* `Phi/Nodes.lean`: every standard matrix is the matrix of a node
  (`exists_mat_eq`); `o` on nodes (`ordOf`) is order-preserving with a
  downward closed image; **Lemma 5 (a)** `o(A ++ B) = o(A) + o(B)`
  (`ordOf_append`).
* `Phi/CNF.lean`: the Cantor normal form as sums `ω^β_1 + ⋯ + ω^β_m`.
* `Phi/LogMono.lean`: `𝓛 N = (0, H) + Lo` (`bigL_eq`); **`𝓛` is strictly
  monotone** (`bigL_lt_bigL`) and **onto the nodes** (`exists_bigL_eq`).
* `Phi/LemmaR.lean`: **Lemma R** (`lemmaR`): `o(N) = ω^{o(𝓛 N)}` for standard
  `N`; `lemmaR_log` (non-epsilon), `lemmaR_eps` (epsilon: `o(N) = ω^{o(N)}`),
  `bigL_lt_iff` (`𝓛` is an order embedding).  The proof reads order types
  (Lemma 5 (a), the Cantor normal form, and `𝓛` onto the nodes) instead of the
  fundamental sequences of COMB §7.

## Main statements (on matrices)
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (CTPS)

/-- **Lemma 2.4 (i).**  The anchor of a standard term is standard. -/
theorem ctps_anchor {N a : Tm} (hN : CTPS N.cols) (ha : anchor N = some a) : CTPS a.cols :=
  std_anchor hN ha

/-- **Lemma 6.**  `𝓛 N` (`()`, `(N)` or `log N`) of a standard term is a node. -/
theorem node_bigL {N : Tm} (hN : CTPS N.cols) : bigL N = [] ∨ CTPS (mat (bigL N)) :=
  stdOrd_bigL hN

/-- **Lemma 6** for `log`. -/
theorem node_log0 {N : Tm} (hN : CTPS N.cols) : log0 N = [] ∨ CTPS (mat (log0 N)) :=
  stdOrd_log0 hN

/-- **Lemma C.**  For a standard `N = (0, A)`, a node `s` of `N` with `y = 1` (given
with the context `ctx` of its ancestors, as in the tree condition of `N`), and any
`i`, the term `(0, A + Coll_A(s_1) + ⋯ + Coll_A(s_i))` of the first `i` children of `s`
is standard. -/
theorem ctps_lemmaC {A : List Tm} (hN : CTPS (Tm.node 0 A).cols) {s : Tm} (hs1 : s.y = 1)
    {ctx : List (ℕ × Forest.PS)} (hs : TGood ctx s) (hz : ZeroLe A ctx) (i : ℕ) :
    CTPS (Tm.node 0 (addT A (collSum A (s.cs.take i)))).cols :=
  std_lemmaC hN hs1 hs hz i

/-- **Lemma 2.4.**  The reach `lh N` of a standard term is a standard matrix. -/
theorem ctps_lh {N : Tm} (hN : CTPS N.cols) : CTPS (mat (lh N)) :=
  (stdOrd_lh hN).resolve_left (lhF_ne_nil _ _)

end Googology.Trans.PSS.Phi
