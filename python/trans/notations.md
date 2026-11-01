# ASCII notations of `trans`

`python/trans/trans` converts a term of one notation into another. This file
fixes how each notation is written in ASCII, on input and on output.

Every notation here is a notation of the Lean library (`Googology/Notation/`,
`Googology/Trans/`). For each one, the Lean type that the ASCII form stands for
is given, so that a printed term and a Lean `#eval` can be compared.

## 0. Common rules

- Spaces are ignored on input.
- Output is in the **canonical form** given in each section. Parsing the
  canonical form and printing it again gives the same string.
- A notation is chosen by its **system name** (`--from`, `--to`). The parser
  never guesses the system from the string: `0,1,2` is a primitive sequence
  of length 3 under `bms1`, and a sequence of length 3 under `y`.
- Natural numbers are written in decimal: `0`, `1`, `12`.
- The ordinal symbols follow one rule everywhere: `p` is ψ, `w` is ω, `W` is
  Ω, `e0` is ε₀, `z0` is ζ₀.

### System names

| name | aliases | notation | Lean type | in / out |
|---|---|---|---|---|
| `bms1` | `prim` | primitive sequence (BMS, 1 row) | `List Nat` (`PrimState`) | in, out |
| `bms2` | `pss` | pair sequence (BMS, 2 rows) | `List (Nat × Nat)` | in, out |
| `bms3` | `trio` | trio sequence (BMS, 3 rows) | `List (List Nat)`, columns of length 3 | in, out |
| `bmsN` | | BMS with `N` rows, `N ≥ 1` | `List (List Nat)`, columns of length `N` | in, out |
| `dbms1`, `dbms2`, …, `dbmsN` | | DBMS with `N` rows | as BMS | in, out |
| `exb` | | extended Buchholz ψ | `Notation.ExBuchholz.Term` | in, out |
| `ord` | | ordinals as the trio sheet labels | `Trans.BMS.TrioRules.Od` | in |
| `inacc` | | ψ over ω weakly inaccessibles | `Notation.InaccPsi.Term` | in, out |
| `y` | | Y sequence | `List Nat` | in, out |
| `omegay` | | ω-Y sequence | `List Nat` | in, out |
| `por1` | | pattern of resemblance of order 1 (R₁⁺) | (`phi.py`) | out |
| `por2` | | pattern of resemblance of order 2 | (`phi3def2.py`) | out |
| `wilken1` | | Wilken's ϑ terms T¹ | `Trans.BMS.PoR.PSS.TR.WP` | out |
| `wilken2` | | Wilken's R₂ terms | (`tr3.py`) | out |

Lean note: `bms r` in `Notation/BMS` has `r` rows, but the list state
`BmsState r` in `Trans/BMS/common/Agree.lean` has `r + 1` rows. The name
`bmsN` here always counts the rows: `bms3` is `bms 3` = `BmsState 2`.

## 1. Matrices: `bmsN`, `dbmsN`

```
matrix ::= column*
         | '()'                       the empty matrix
column ::= '(' nat (',' nat)* ')'
```

- A matrix is its columns from left to right. A column lists its entries from
  the top row (row 0) down.
- Every column has exactly `N` entries for `bmsN` / `dbmsN`. A column of any
  other length is an error.
- The empty matrix is `()`. (An empty argument `""` is also accepted.)
- Two short forms are accepted on input only:
  - the Lean list form, as printed by `#eval`:
    `[[0,0],[1,1],[2,2]]`, and for `N = 1` also `[0,1,2]`;
  - for `N = 1` only, a bare list without parentheses: `0,1,2`. For `N ≥ 2`
    every column must be in parentheses.
- Canonical output: `(0,0)(1,1)(2,2)`, no spaces; `()` for the empty matrix.

| system | example | meaning |
|---|---|---|
| `bms1` | `(0)(1)(2)` = `0,1,2` | the primitive sequence 0,1,2 |
| `bms2` | `(0,0)(1,1)(2,2)` | a pair sequence |
| `bms3` | `(0,0,0)(1,1,1)(2,2,1)` | a trio sequence |
| `dbms2` | `(0,0)(1,1)` | a 2-row DBMS array |

The parser checks the shape only. It does not check that the matrix is
standard, although most maps are proved on standard forms only.

## 2. Sequences: `y`, `omegay`

```
seq ::= nat (',' nat)*
      | '()'                           the empty sequence
```

- No parentheses: `1,3,4,2,5`. This is also the canonical output.
- The empty sequence is `()`, because an empty string cannot be seen in the
  output.
- The Lean type is `List Nat` in both systems. The seeds are `1,h+1` for `y`
  and `1,h+2` for `omegay`.
- No translation in the library touches `y` or `omegay` yet. The parser and the
  printer are there so that later maps have their ends ready.

## 3. Extended Buchholz ψ: `exb`

Lean: `Term.nil` is 0 and `Term.cons a b t` is ψ_a(b) + t. A term is a sum of
principal terms ψ_a(b), and the subscript `a` is itself a term.

### Grammar

```
term    ::= '0'
          | summand ('+' summand)*
summand ::= nat                      n ≥ 1:  p0(0) + … + p0(0)  (n times)
          | 'w'                      p0(1)
          | 'W'                      p1(0)
          | 'W_' sub                 p_sub(0),  sub ≠ 0
          | 'e' nat                  eN = p0(W + … + W)          (N+1 copies of W)
          | 'z' nat                  zN = p0(p1(W) + … + p1(W))  (N+1 copies of p1(W))
          | 'p' digits '(' term ')'  p_k(…) with a numeral subscript k
          | 'p_' sub '(' term ')'    p_sub(…)
          | 'p(' term ')'            p0(…)
sub     ::= nat | 'w' | 'W' | 'e' nat | 'z' nat | '(' term ')'
```

- `p3(x)` is ψ₃(x). `p12(x)` is ψ₁₂(x). Other subscripts take `_`: `p_w(x)`,
  `p_(w+1)(x)`, `W_w`, `W_(W+1)`.
- `W_1` is `W`. `W_0` is rejected, because ψ₀(0) is 1, not Ω₀.
- `eN` is ε_N for a numeral `N`: ψ₀(Ω·(N+1)) = ε_N is proved in Lean
  (`Notation/ExBuchholz/Eps.lean:633`). `e0` is the Lean term `te0`
  (`Trans/BMS/ExBuchholz/Basic.lean:81`).
- `zN` is ζ_N for a numeral `N`, with Ω² = ψ₁(ψ₁(0)) = `p1(W)`. `z0` is the
  Lean term `tzeta0` (`Trans/BMS/ExBuchholz/Zeta.lean:295`), and
  ψ₀(Ω²) = ζ₀ is proved (`Notation/ExBuchholz/Ladder.lean:706`).
  **For N ≥ 1, ψ₀(Ω²·(N+1)) = ζ_N is not proved in Lean.** It is the usual
  fact about Buchholz's ψ, and `zN` takes it as the definition of the
  shorthand.
- `eN` and `zN` take a numeral only: `ew` and `e(w+1)` are not accepted.
- Γ₀ (`g0`) and Λ are not accepted: the library has no Lean term for Γ₀, and
  ψ₀(Λ) is the limit of the system, not a term of it.
- `*` and `^` are not part of `exb`. They belong to `ord` (section 4).
- The parser accepts any sum, standard or not. Standardness (`Term.isOT`, and
  `X < Ω` for the countable part) is not checked yet.

### Canonical output

The printer applies these rules, in this order:

| term | printed as |
|---|---|
| nil | `0` |
| a run of `n` copies of ψ₀(0) | `n` |
| ψ₀(ψ₀(0)) | `w` |
| ψ₁(0) | `W` |
| ψ₀(Ω·(N+1)), N a numeral | `eN` |
| ψ₀(Ω²·(N+1)), N a numeral | `zN` |
| ψ_a(0), `a` ≥ 2 | `W_a` |
| ψ_a(b), `a` a numeral `k` | `pk(b)` |
| ψ_a(b), otherwise | `p_a(b)` |

Here Ω·(N+1) is the term W+…+W, and Ω²·(N+1) is the term p1(W)+…+p1(W). The
rule applies to a whole principal term only: p0(W+1) stays `p0(W+1)`.

A subscript `a` is printed bare when it is a numeral, `w`, `W`, `eN` or `zN`,
and as `(a)` otherwise. With these rules each term has exactly one printed
form.

| ordinal | `exb` |
|---|---|
| 0 | `0` |
| 3 | `3` |
| ω+1 | `w+1` |
| ω² | `p0(2)` |
| ε₀ | `e0` (input `p0(W)` also accepted) |
| ε₁ | `e1` (= `p0(W+W)`) |
| ε₀·ω | `p0(W+1)` |
| ζ₀ | `z0` (= `p0(p1(W))`) |
| ζ₁ | `z1` (= `p0(p1(W)+p1(W))`) |
| ψ₀(Ω_{ε₀}) | `p0(W_e0)` |
| ψ₀(Ω₂) | `p0(W_2)` |
| ψ₀(Ω_ω) | `p0(W_w)` |
| ψ₀(Ω_Ω) | `p0(W_W)` |

## 4. Sheet labels: `ord` (input only)

This is the syntax of the trio sheet labels. The Lean parser
`Trans.BMS.TrioRules.parse` (`Trans/ExBuchholz/BMS/Trio/TrioRules.lean:317`)
reads it into the Cantor-style normal form `Od`. Its only use is as the input
of the map `ord → bms3` (`trioRuleMatrixSt`, with `--wide`), whose domain
reaches ψ₀(Λ). As on the sheet, a label `a` is the index: the output is the
matrix of ψ₀(Ω_a), not of `a`.

```
expr  ::= term ('+' term)*
term  ::= pw (('*' pw) | pw-starting-with-a-numeral)*
pw    ::= atom ('^' pw)?             right associative
atom  ::= nat | 'w' | 'W' | 'W_' atom
        | 'psi' ('_' atom)? '(' expr ')'
        | 'p'   ('_' atom)? '(' expr ')'
        | '(' expr ')'
```

- The parser is the Lean one, ported. It accepts the same strings and gives
  the same `Od`.
- **Two differences from `exb`.** In `ord`, a numeral right after an atom is a
  product: `W2` is Ω·2 and `w2` is ω·2. And `p0(` is not accepted; write
  `p(` or `p_0(`.
  In `exb`, write Ω₂ as `W_2`.

| ordinal | `ord` |
|---|---|
| ψ₀(Ω_ω·Ω) | `p(W_w*W)` |
| ψ₀(Ω_ω·Ω + Ω·ω) | `p(W_w*W+W*w)` |

## 5. ψ over ω weakly inaccessibles: `inacc`

Lean: `Notation.InaccPsi.Term` (`Notation/InaccPsi/Term.lean:27`).

```
t ::= '0'                            zero
    | 'I_' nat                       inacc n        = I_n
    | 'I_w'                          inaccW         = I_ω
    | t '+' t                        add a b, right associative
    | 'phi(' t ',' t ')'             phi a b        = φ(a, b)
    | 'W_' a                         om a           = Ω_a
    | 'pS_' a '(' t ')'              psiS s t       = ψ_{Ω_{s+1}}(t)
    | 'pI_' nat '(' t ')'            psiI n t       = ψ_{I_n}(t)
    | '(' t ')'
a ::= nat | 'w' | '(' t ')'
```

Short forms, accepted on input and used on output:

| short | full |
|---|---|
| `1` | `phi(0,0)` |
| `n` (n ≥ 2) | `1+1+…+1` |
| `w` | `phi(0,1)` |
| `W` | `W_1` |

- `a+b+c` is `add a (add b c)`, as in `Term.NF`.
- No map reaches `inacc` yet: there is no Lean map PoR → InaccPsi. The parser
  and the printer exist so that the terms in `Trans/PoR/InaccPsi/` can be read
  and compared (`Term.cmp`, `Term.NF`).

## 6. Output-only notations

These are results of maps that exist only as Python programs in the repo, or
whose Lean target is not a `Notation/` system. `trans` prints them in the
format of those programs and does not parse them.

### `por1`: R₁⁺ patterns (from `bms2`)

The format of `Trans/BMS/PoR/PSS/por/phi.py`:

```
0 a (*n0 (n1 n1+n1))
```

- The nodes are listed from left to right, separated by spaces.
- `0` is the node of the ordinal 0 and `a` the node of 1. `n0`, `n1`, … are
  the other additively principal nodes, and `x+y` is a sum of them.
- `(` before a node and `)` after a later node mean that the first node
  ≤₁-reaches the second.
- `*` marks the node of the input matrix.

### `por2`: patterns of order 2 (from `bms3`)

The format of `Trans/BMS/PoR/Trio/por/phi3def2.py`: as `por1`, with `[` `]`
for ≤₂.

```
0 a (*n0 ([[n1 n2] n3]))
```

### `wilken1`: ϑ terms T¹ (from `bms2`)

The format of `Trans/BMS/PoR/PSS/por/tr.py`, the same map as Lean `trNode`:

```
t0(t1(W2))
```

`tm(x)` is ϑ_m(x), `ta(x)` is ϑ^α(x) (Wilken, Def 7.1), `W` is Ω₁,
`Wm` is Ω_m, `1` is ϑ₀(0), and `+` is the sum.

### `wilken2`: R₂ terms (from `bms3`)

The format of `Trans/BMS/PoR/Trio/por/tr3.py`: `u[x]`, `u*<M>`, `{x}`,
`tau`, `tm(x)`, `Wm`, joined by ` + `.

```
u[1 + 1]
```

## 7. Checks

- `tests/test_notation.py` (`python3 -m unittest discover -s tests` in
  `python/trans`): the tables of this file, the errors, and parse ∘ show = id
  on random `exb` and `inacc` terms.
- `tests/gen_lean_check.py` writes a Lean file of `#guard`s, to be run with
  `leanman check -C <Lean project>`:
  - every `ord` label in `Googology/Trans/ExBuchholz/BMS/Trio/` (158 strings)
    gives the same `Od` in Python and in Lean `TrioRules.parse`;
  - `0`, `1`, `3`, `W`, `w`, `e0`, `p0(W)`, `e1`, `z0`, `W_w`, `p0(W_w)` give the
    Lean terms `nil`, `t1`, `numeral 3`, `tW`, `tw`, `te0`, `te0`, `te1`,
    `tzeta0`, `tOmegaW`, `psiOmegaOmega`;
  - the `inacc` values elaborate as `InaccPsi.Term`.

## 8. Open points


1. `ord` keeps the label syntax of the sheet, so `W2` means two different
   things in `ord` and `wilken1`. Both are kept as they are, because they
   follow existing programs.
