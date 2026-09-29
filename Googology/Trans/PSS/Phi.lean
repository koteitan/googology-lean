import Googology.Trans.PSS.Phi.Defs
import Googology.Trans.PSS.Phi.Order
import Googology.Trans.PSS.Phi.Bridge
import Googology.Trans.PSS.Phi.Std
import Googology.Trans.PSS.Phi.LemmaC
import Googology.Trans.PSS.Phi.Lh

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

theorem foldl_oplus_ne_nil {lhY : Tm → List Tm} (hne : ∀ Y, lhY Y ≠ []) :
    ∀ (ys : List Tm) {S : List Tm}, S ≠ [] → ys.foldl (oplus lhY) S ≠ []
  | [], _, hS => hS
  | Z :: ys, S, hS => by
    refine foldl_oplus_ne_nil hne ys ?_
    unfold oplus
    cases S with
    | nil => exact absurd rfl hS
    | cons s1 S =>
      simp only
      split_ifs
      · exact hne Z
      · simp [addT]

/-- `lhF f Y` is never empty. -/
theorem lhF_ne_nil : ∀ (f : ℕ) (Y : Tm), lhF f Y ≠ []
  | 0, _ => by simp [lhF]
  | f + 1, Y => by
    unfold lhF
    split_ifs
    · simp
    · simp only [addT]
      cases lam Y <;> simp
    · exact foldl_oplus_ne_nil (lhF_ne_nil f) _ (by simp)

/-- **Lemma 2.4.**  The reach `lh N` of a standard term is a standard matrix. -/
theorem ctps_lh {N : Tm} (hN : CTPS N.cols) : CTPS (mat (lh N)) :=
  (stdOrd_lh hN).resolve_left (lhF_ne_nil _ _)

end Googology.Trans.PSS.Phi
