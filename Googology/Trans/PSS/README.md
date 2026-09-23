[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# PSS

The translation of pair sequences (Bashicu matrices with two rows) into the
ordinals. It goes through the translation `Trans` of p進大好きbot's article
[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7),
whose bijectivity Naruyoko proved and
[koteitan/pss-proof](https://github.com/koteitan/pss-proof) formalizes. That
repository is a Lake dependency; its theorems are used, not copied.

## Files

| file | contents |
|---|---|
| `Expand.lean` | pss-proof's expansion is this library's: `oper M (N+1) = expand2L N M` on every standard pair sequence of length at least 2 (`oper_succ_eq_expand2L_of_ctps`), and the two notions of standard agree (`isPair_iff`) |
| `Terms.lean` | pss-proof's Buchholz terms, with subscripts in `ℕ ∪ {ω}`, map injectively and order-preservingly into extended Buchholz terms (`toTerm_injective`, `lessBT_iff_lt`), standard exactly when their image is (`OT_toTerm_iff`), onto the standard forms below `ψ_0(Ω_ω)` (`toTerm_bijOn_TransRange`) |
| `Rank.lean` | **the rank of a pair sequence is `1 + val` of its term** (`rank_pairL_eq`), 0 for the empty sequence; the values are exactly the ordinals below `ψ_0(Ω_ω)` (`range_pairOrd`); the map is injective and order-preserving for the lexicographic order (`pairOrd_injective`, `ltPS_iff_pairOrd_lt`); and the rank is the order type of the standard pair sequences below (`rank_eq_typein`) |

## Why `1 +`

The pair sequence system of this library runs one step further than
pss-proof's: pss-proof stops at `(0,0)`, and this library expands `(0,0)` to
the empty sequence. So every nonempty sequence has one more state below it,
and its rank is `1 + val (Trans M)`. For an infinite value `1 + α = α`, so the
generator `(0,0)(1,1)` still has rank `ε₀`.

## Route

1. `Expand.lean` puts the two expansion systems side by side.
2. pss-proof's `trans_bijOn` and `trans_order_iso` make `Trans` an order
   isomorphism from the standard pair sequences onto the standard Buchholz
   terms below `D_0 D_ω 0`.
3. `Terms.lean` carries that onto the standard extended Buchholz terms below
   `ψ_0(Ω_ω)`.
4. `belowEquiv` (in `Notation/ExBuchholz/Onto.lean`) says the standard forms
   below a countable standard form `X` are, in order, the ordinals below
   `val X`. So the order type below a pair sequence is the value of its term.
5. Expansion is cofinal among the standard pair sequences below (from
   pss-proof's `ltPS_ltExpPS` and `expand_lePS`), so the rank is that order type.
