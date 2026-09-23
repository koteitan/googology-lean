import Googology.Trans.BMS.TrioRulesAll

/-!
# Fix L: a last leaf naming a level that one leaf cannot name

A patch on top of `TrioRulesAll.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N).

## The fault

Under a regime `r` that is a tower over `1` (`r ∈ {Ω, Ω_Ω, Ω_{Ω_Ω}, …}`), a unit's
last leaf names its level `Ω_p` with one column and an upgrade.  For some `p` no
single column is right, even when the leaf is the last column
([TRIO-NONLAST-LEAF.md](TRIO-NONLAST-LEAF.md), open item 3).  With
`TrioRulesAll.lean`:

* `Ω_{Ω_Ω}+Ω_3` gets the matrix of `Ω_{Ω_Ω}+Ω_{Ω+1}`;
* `Ω_{Ω_Ω}+Ω_{Ω·2}` gets the matrix of `Ω_{Ω_Ω}+Ω_2`;
* `Ω_{Ω_Ω}+Ω_{Ω+2}`, `Ω_{Ω_Ω}+Ω_{Ω_2+1}`, `Ω_{Ω_Ω}+Ω_{Ω_3}` and `Ω_Ω+Ω_3` are not
  standard (yaBMS `bms -s`).

## The change (exactly this, nothing else)

`MstepFix Mf α = MstepAll Mf α`, except when `lastLeafFix Mf α = some cs`; then
`MstepFix Mf α = cs`.  `lastLeafFix` returns `none` unless all of these hold:

* `α` is in the sum branch of `MstepAll` (`lvlO α = some r`, `α` is not
  `ψ_{Ω_u}(X)` and not `Ω_r`);
* `r` is a tower over `1`: `lvlO r ≠ none`, `r = Ω_w`, `chainBase r = 1`;
* the last term of `α` is `Ω_p·c` (a sum `γ + Ω_p·c`), or `ω^β·c` with `β` ending in
  `Ω_p·k` (a product); that last `Ω_p` is the level `tailLevel α` names;
* `p` is not in `tops(r) = [r, w, w', …]`.

`rb q` is `α` with that last `Ω_p` replaced by `Ω_q` (keeping the other copies:
`γ + Ω_p·(c-1) + Ω_q`, a normal form since `q < p`).  Let `b = chainBase p`
(`p = Ω_{Ω_{…b}}`), `p[b := b']` the chain with its base replaced, `P₁` the row-1
parent, and `s₀ = copyRoot M` = `P₁(last column of M)`, moved to the start of the last
lifted or kept copy of `M[s₀:f]` while `M[f:2f-s₀]` is such a copy.  `liftAt M s₀`
is the lifted copy of `M[s₀:]` (`blift` of `TrioRulesNonLast.lean` with the last leaf
lifted, not kept).  The four cases, tried in this order:

1. **L (successor, lifted copy).**  `b = c + m`, `c = 0` and `m ≥ 3`, or `c = Ω_w`
   and `m ≥ 2`.  With `B = M(rb(p[b := c + (m-1)]))` (its last column a leaf):
   `M(α) = B ++ liftAt B (copyRoot B)`.  (`Ω_3`, `Ω_4`, `Ω_{Ω+2}`, `Ω_{Ω_3}`,
   `Ω_{Ω_2+2}`.)
2. **K' (a mark after K).**  `b = Ω_w + ω^k` (`k ≥ 1` finite), `p = b`,
   `Ω_w ∉ tops(r)`: `M(α) = appendSuffix (K(Ω_w)) b`.  (`Ω_{Ω_2+ω}`.)
3. **K (successor of a level with sub-units).**  `b = Ω_w + 1`, `p = b`,
   `Ω_w ∉ tops(r)`, and `M(chainBase Ω_w)` has no suffix.  `K(c)` is: `B = M(rb c)`,
   its kept copy `blift B (copyRoot B)` (the copy of Fix N 2), then one unit on the
   last root `(x, y)`: `(x+1,y,0)(x+2,y+1,1)(x+3,y+1,1)(x+4,N(r)+1,0)`, the leaf
   one above the regime's own leaf (Fix N 3: one higher per copy).
   (`Ω_{Ω_2+1}`.)
4. **D (a top doubled).**  `b = Ω_w·2` with `Ω_w ∈ tops(r)`: with
   `B = M(rb(p[b := Ω_{w+1}]))`, `M(α)` is `B` with its last leaf set to `N(w)`.
   (`Ω_{Ω·2}`: `M(Ω_{Ω_Ω}+Ω_{Ω_2})` with the last leaf `2` lowered to `1`.)

In every other case `lastLeafFix` is `none`.  `N(v)` is Fix B's `leafNameOrY` in a
fresh state with regime `r`.

## Why these matrices

* L is what BMS itself writes.  `M(γ+Ω_{c+ω})[n] = M(γ+Ω_{c+n+1})` (BM4, `n+1`
  copies) for `c = 1, Ω, Ω_Ω`, chains, products, and after a Fix N copy, in 16
  contexts (`TrioFixLastLeafSheet.lean`).
* K and K' are confirmed together: `M(γ+Ω_{Ω_2+ω})[n] = M(γ+Ω_{Ω_2+n+1})` for
  `n = 0, 1, 2` in five contexts, and the mark `appendSuffix` writes is the only
  single column with that property (a search over all `(x, y, 1)`, outside Lean).
  The leaf `N(r)+1` makes `M(γ+Ω_{Ω_2+1})[1]` the same shape as
  `M(γ+Ω_{Ω+1})[1]`, the successor of the top `Ω`.
* D: `M(Ω_{Ω_Ω}+Ω_{Ω·2})` is `M(Ω_{Ω_Ω}+Ω_{Ω+1})` followed by the tail
  `(4,3,1)(5,3,1)(6,1,0)` that the sheet's row 4502 puts after `M(Ω_{Ω+1})` for
  `Ω_{Ω·2}`; its expansion `[0]` is `M(Ω_{Ω_Ω}+Ω_{Ω+ω²})`, and `[n]` continues
  with a `(6,0,0)` column (a countable `ψ_0`), the shape of `M(Ω·2)[n]`.
  This is support, not a derivation.

The checks are `#guard`s in `TrioFixLastLeafSheet.lean`: a calibration, not a
theorem.  Standard form is yaBMS `bms -s`, outside Lean.
-/

namespace Googology.Trans.BMS.TrioFixLastLeaf

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll

/-! ### Ordinal pieces -/

/-- `p` with the end of its `Ω`-chain replaced by `b`: `p[b := ·]`. -/
def replBase : Nat → Od → Od → Od
  | 0, p, _ => p
  | n + 1, p, b =>
    match omArg p with
    | some w => [(.W (replBase n w b), 1)]
    | none => b

/-- The last `Ω_p` of `α` (a sum `γ + Ω_p·c`, or a product whose last exponent ends
in `Ω_p·k`), and `rb`: `α` with that `Ω_p` replaced by `Ω_q`. -/
def splitLast (alpha : Od) : Option (Od × (Od → Od)) :=
  match alpha.getLast? with
  | some (.W p, c) =>
    some (p, fun q => alpha.dropLast ++ (if c == 1 then [] else [(.W p, c - 1)]) ++ [(.W q, 1)])
  | some (.o beta, c) =>
    match beta.getLast? with
    | some (.W p, k) =>
      let b2 : Od → Od := fun q =>
        beta.dropLast ++ (if k == 1 then [] else [(.W p, k - 1)]) ++ [(.W q, 1)]
      some (p, fun q =>
        alpha.dropLast ++ (if c == 1 then [] else [(.o beta, c - 1)]) ++ [(.o (b2 q), 1)])
    | _ => none
  | _ => none

/-- `b = c + m` with `m` finite (`m = 0` when `b` has no finite part). -/
def finPart (b : Od) : Od × Nat :=
  match b.getLast? with
  | some (.o [], m) => (b.dropLast, m)
  | _ => (b, 0)

/-! ### Copies -/

/-- The lifted copy of `cs[s0:]`, the last leaf lifted too (`blift` keeps it). -/
def liftAt (cs : Cols) (s0 : Nat) : Cols :=
  let seg := blift cs s0
  setLastY seg ((lastC seg).y + 1)

/-- `cs[f : 2f - s0]` is a lifted or kept copy of `cs[s0:f]`. -/
def isCopyAt (cs : Cols) (s0 f : Nat) : Bool :=
  let a := colAt cs s0
  2 * f ≤ cs.size + s0 && colAt cs f == ⟨a.x + 1, a.y + 1, a.z⟩ &&
    (let pre := cs.extract 0 f
     let seg := cs.extract f (2 * f - s0)
     seg == blift pre s0 || seg == liftAt pre s0)

/-- Move `s0` to the start of a copy of `cs[s0:f]`, while there is one. -/
def copyRootGo : Nat → Cols → Nat → Nat
  | 0, _, s0 => s0
  | n + 1, cs, s0 =>
    match ((List.range cs.size).reverse.filter (· > s0)).find? (isCopyAt cs s0 ·) with
    | some f => copyRootGo n cs f
    | none => s0

/-- Where the lifted copy starts: `P₁` of the last column, moved past earlier copies. -/
def copyRoot (cs : Cols) : Nat :=
  copyRootGo cs.size cs (((par1 cs).getD (cs.size - 1) none).getD 0)

section
variable (Mf : Od → Cols)

/-- `N(v)` in a fresh state with regime `r` (Fix B). -/
def nameIn (cols : Cols) (r v : Od) : Int :=
  leafNameOrY Mf ({ cols := cols, regime := some r } : Ctx) v

/-- **K**: `M(rb c)`, its kept copy, then one unit whose leaf is `N(r) + 1`. -/
def kstruct (rb : Od → Od) (c r : Od) : Option Cols :=
  if !(suffixOf Mf (chainBase c)).isEmpty then none else
  let base := Mf (rb c)
  if base.isEmpty || (lastC base).z then none else
  let cols := base ++ blift base (copyRoot base)
  let lr := lastRootPlain cols
  let ytop := nameIn Mf cols r r + 1
  some (cols ++ #[⟨lr.2 + 1, lr.1, false⟩, ⟨lr.2 + 2, lr.1 + 1, true⟩,
                  ⟨lr.2 + 3, lr.1 + 1, true⟩, ⟨lr.2 + 4, ytop, false⟩])

/-- The four cases L, K', K, D for the last leaf naming `Ω_p` under the regime `r`. -/
def lastLeafAt (r p : Od) (rb : Od → Od) : Option Cols :=
  let tp := omChain fuel r
  let isTop : Od → Bool := fun x => tp.any fun t => cmpOrd x t == .eq
  if isTop p then none else
  let b := chainBase p
  let c := (finPart b).1
  let m := (finPart b).2
  let catom := (omArg c).isSome
  if (c.isEmpty && m ≥ 3) || (catom && m ≥ 2) then
    -- L
    let base := Mf (rb (replBase fuel p (c ++ nat (m - 1))))
    if base.isEmpty || (lastC base).z then none
    else some (base ++ liftAt base (copyRoot base))
  else
    match b with
    | [(.W w, 1), (.o [(.o [], _)], 1)] =>
      -- K'
      if (omArg p).isNone && !isTop [(.W w, 1)] then
        (kstruct Mf rb [(.W w, 1)] r).map fun k => appendSuffix Mf k b 0 none
      else none
    | _ =>
      if catom && m == 1 && (omArg p).isNone && !isTop c then kstruct Mf rb c r   -- K
      else
        match b with
        | [(.W w, 2)] =>
          -- D
          if isTop [(.W w, 1)] then
            let base := Mf (rb (replBase fuel p [(.W (add w one), 1)]))
            if base.isEmpty || (lastC base).z then none
            else some (setLastY base (nameIn Mf base r w))
          else none
        | _ => none

/-- **Fix L**: the matrix of `α` when its last leaf is one of the four cases. -/
def lastLeafFix (alpha : Od) : Option Cols :=
  match lvlO alpha with
  | none => none
  | some r =>
    if (isPsiLevel alpha).isSome || alpha == [(.W r, 1)] then none
    else if !((lvlO r).isSome && (omArg r).isSome && cmpOrd (chainBase r) one == .eq) then none
    else
      match splitLast alpha, tailLevel alpha with
      | some (p, rb), some t => if cmpOrd t p == .eq then lastLeafAt Mf r p rb else none
      | _, _ => none

/-- **One step of the patched builder**: Fix L, else `MstepAll`. -/
def MstepFix (alpha : Od) : Cols := (lastLeafFix Mf alpha).getD (MstepAll Mf alpha)

/-- Where Fix L does not act, the step is `MstepAll`'s. -/
theorem MstepFix_eq (alpha : Od) (h : lastLeafFix Mf alpha = none) :
    MstepFix Mf alpha = MstepAll Mf alpha := by
  simp [MstepFix, h]

/-- Fix L never acts on a countable `α`. -/
theorem lastLeafFix_countable (alpha : Od) (h : lvlO alpha = none) :
    lastLeafFix Mf alpha = none := by
  simp [lastLeafFix, h]

/-- Fix L never acts on `ψ_{Ω_u}(X)` (rule 9, Fix E). -/
theorem lastLeafFix_psi (alpha : Od) (uX : Od × Od) (hp : isPsiLevel alpha = some uX) :
    lastLeafFix Mf alpha = none := by
  unfold lastLeafFix
  cases lvlO alpha <;> simp [hp]

end

/-- The patched builder with fuel. -/
def MfuelFix : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepFix (MfuelFix n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, by rules 1–10 with Fixes A–E, N and L. -/
def MFix (alpha : Od) : Cols := MfuelFix fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with Fixes A–E, N and L.** -/
def trioRuleMatrixFix (alpha : Od) : List (List Nat) := toRows (MFix alpha)

/-- The matrix for a label. -/
def trioRuleMatrixOfFix (s : String) : Option (List (List Nat)) := do
  let a ← parse s
  if a.isEmpty then none else some (trioRuleMatrixFix a)

/-- The matrix of a label, `[]` when it does not parse. -/
def fixOf (s : String) : List (List Nat) := (trioRuleMatrixOfFix s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixFix (alpha : Od) : WF3 (trioRuleMatrixFix alpha) := WF3_toRows _

end Googology.Trans.BMS.TrioFixLastLeaf
