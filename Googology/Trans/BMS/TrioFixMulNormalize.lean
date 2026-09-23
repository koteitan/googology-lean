import Googology.Trans.BMS.TrioRulesAll

/-!
# Patch on `TrioRulesAll`: `ω^atom = atom` in `mul` and `power`

A separate patch on top of `TrioRulesAll.lean` (rules 1–10 of
[koteitan/trio](https://github.com/koteitan/trio) with Fixes A–E and N).
Side finding of [TRIO-SHEET-41.md](TRIO-SHEET-41.md): `mul` builds the exponent
`ω^(3+Ω)` of `ω^3·Ω` as `.o [(.W 1, 1)]` (the normal form `Ω`, wrapped as an
exponent) instead of the atom `.W 1`.  The two denote the same ordinal (`ato` sends
both to `[(.W 1, 1)]`, and `cmpOrd` calls them equal), but the builder reads the
shape: on `Ω_{ω^3·Ω}` it takes the level `ω^Ω` (not an `Ω_v` term) through
`placeUnits`, and on `Ω_Ω` it takes rule 2.  So the literal label of row 4369,
`W_(w^3*W)`, got another matrix than `W_W`.

## The change, precisely

Everything of `TrioRulesAll.lean` is reused unchanged except these points.

1. **Smart constructor** `mkExp : Od → Ex`: `mkExp [(x, 1)] = x` when `x` is an atom
   (`.W v` or `.psi v X`), `mkExp a = .o a` otherwise.  `ato (mkExp a) = a`
   (`ato_mkExp`), and `mkExp` never returns `.o [(atom, 1)]` (`mkExp_normal`).
2. **`mulM`** = `TrioRules.mul` with the new exponent `.o (addExp e1 e)` replaced by
   `mkExp (addExp e1 e)`, and the test `e == .o []` replaced by the pattern match
   `isZeroEx e`.
3. **`powerM`** = `TrioRules.power` with `mul` replaced by `mulM`, `wpow b` by
   `wpowM b = [(mkExp b, 1)]` (so `ω^Ω = Ω`), and the tests `a == one`, `b == one`,
   `e1 == .o []` replaced by the pattern matches `isOneOd a`, `isOneOd b`,
   `isZeroEx e1`.
4. **The parser** `pAtomM … pExprM`, `parseM`: `TrioRules`'s `pAtom … pExpr`, `parse`
   verbatim, with `mul`, `power` replaced by `mulM`, `powerM`.  Nothing else in the
   rules calls `mul` or `power`, so this is the whole effect on the labels.
5. **The step** `MstepFix` = `TrioRulesAll.MstepAll` with the test
   `alpha == [(.W v, 1)]` (where `v` is the level of `alpha`) replaced by the pattern
   match `isOmegaForm alpha` (`alpha = [(.W _, 1)]`).  When `alpha = [(.W w, 1)]`,
   `lvlO alpha = some w`, so the two tests say the same; this is a refactoring for
   provability only (the derived `BEq` on `Ex` does not reduce in proofs, not even
   `Ex.W v == Ex.o []`).  `MstepFix_omega` proves rule 2 on every `Ω_w` from it.
   `MfuelFix`, `MFix` are `MfuelAll`, `MAll` with `MstepFix`.

The top-level map `trioRuleMatrixOfFix` = `trioRuleMatrixOfAll` with `parseM` and
`MFix`.  To merge with other patches: take points 1–4 as they are (they touch only
the label reader), and point 5 only replaces one `if` in the step.

## What it proves and what is checked

Proved here: points 1 and 5 above (`ato_mkExp`, `mkExp_normal`, `mkExp_eq_o`,
`MstepFix_omega`, `MstepFix_psi`, `MstepFix_countable`) and, by evaluation,
`mulM (ω^3) Ω = Ω` and `powerM ω Ω = Ω`.  The relation of `mulM` to `mul` cannot be
proved (the derived `==` of `mul` does not reduce); it is checked on every label in
`TrioFixMulNormalizeSheet.lean`, with the rest of the checks.
-/

namespace Googology.Trans.BMS.TrioFixMulNormalize

open Googology.Trans.BMS.TrioRules
open Googology.Trans.BMS.TrioRules2
open Googology.Trans.BMS.TrioRules3
open Googology.Trans.BMS.TrioRulesNL
open Googology.Trans.BMS.TrioRulesAll

/-! ### Point 1: the smart constructor -/

/-- The exponent `ω^a` names: the atom itself when `a` is one atom with coefficient
1 (`ω^atom = atom`), else `.o a`. -/
def mkExp : Od → Ex
  | [(.W v, 1)] => .W v
  | [(.psi v X, 1)] => .psi v X
  | a => .o a

/-- `mkExp` denotes the normal form it is given. -/
theorem ato_mkExp (a : Od) : ato (mkExp a) = a := by
  unfold mkExp
  split <;> rfl

/-- `mkExp` never writes `ω^atom` as `.o [(atom, 1)]`. -/
theorem mkExp_normal (a : Od) (x : Ex) (h : mkExp a = .o [(x, 1)]) : x.isAtom = false := by
  unfold mkExp at h
  split at h
  · cases h
  · cases h
  · rename_i hW hP
    cases h
    cases x with
    | o _ => rfl
    | W v => exact absurd rfl (hW v)
    | psi v X => exact absurd rfl (hP v X)

/-- Off the atom case, `mkExp` is `.o`. -/
theorem mkExp_eq_o (a : Od) (h : ∀ x, a = [(x, 1)] → x.isAtom = false) : mkExp a = .o a := by
  unfold mkExp
  split
  · exact absurd (h _ rfl) (by simp [Ex.isAtom])
  · exact absurd (h _ rfl) (by simp [Ex.isAtom])
  · rfl

/-! ### Points 2 and 3: `mul` and `power` -/

/-- The zero exponent `.o []`, by pattern (in place of `== .o []`). -/
def isZeroEx : Ex → Bool
  | .o [] => true
  | _ => false

theorem isZeroEx_iff (e : Ex) : isZeroEx e = true ↔ e = .o [] := by
  unfold isZeroEx
  split <;> simp_all

/-- The normal form `1`, by pattern (in place of `== one`). -/
def isOneOd : Od → Bool
  | [(.o [], 1)] => true
  | _ => false

theorem isOneOd_iff (a : Od) : isOneOd a = true ↔ a = one := by
  unfold isOneOd
  split <;> simp_all [one, nat]

/-- `ω^x` with `ω^atom = atom`. -/
def wpowM (x : Od) : Od := [(mkExp x, 1)]

/-- `mul` with `ω^atom = atom` on the new exponents. -/
def mulM (a b : Od) : Od :=
  match a with
  | [] => []
  | (e1, c1) :: ta =>
    if b.isEmpty then []
    else b.foldl (fun out ec =>
      if isZeroEx ec.1 then add out ((e1, c1 * ec.2) :: ta)
      else add out [(mkExp (addExp e1 ec.1), ec.2)]) []

/-- `power` with `mulM` and `ω^atom = atom`. -/
def powerM (a b : Od) : Od :=
  if b.isEmpty then one
  else if isOneOd a then one
  else if isOneOd b then a
  else match b with
    | [(.o [], k)] => (List.range (k - 1)).foldl (fun r _ => mulM r a) a
    | _ =>
      match a with
      | [] => []
      | (e1, _) :: _ => if isZeroEx e1 then wpowM b else wpowM (mulM (ato e1) b)

/-- `ω^3·Ω = Ω` (rules 1–10's `mul` gives `ω^(ω^Ω)` written `[(.o [(.W 1, 1)], 1)]`). -/
theorem mulM_omega3_Omega : mulM [(.o (nat 3), 1)] [(.W one, 1)] = [(.W one, 1)] := by
  rfl

/-- `ω^Ω = Ω`. -/
theorem powerM_omega_Omega : powerM (wpow one) [(.W one, 1)] = [(.W one, 1)] := by
  rfl

/-! ### Point 4: the label reader with `mulM`, `powerM` -/

mutual
/-- `pAtom` of `TrioRules.lean`, unchanged. -/
def pAtomM : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, .sym '(' :: r => do
      let (e, r) ← pExprM n r
      match r with
      | .sym ')' :: r => some (e, r)
      | _ => none
  | _ + 1, .w :: r => some (wpow one, r)
  | n + 1, .W :: r =>
      match r with
      | .sym '_' :: r' => do
          let (v, r'') ← pAtomM n r'
          some (ato (.W v), r'')
      | _ => some (ato (.W one), r)
  | n + 1, .psi :: r => do
      let (v, r) ← match r with
        | .sym '_' :: r' => pAtomM n r'
        | _ => some ([], r)
      match r with
      | .sym '(' :: r => do
          let (x, r) ← pExprM n r
          match r with
          | .sym ')' :: r => some ([(.psi v x, 1)], r)
          | _ => none
      | _ => none
  | _ + 1, .num k :: r => some (nat k, r)
  | _, _ => none

/-- `pPw` with `powerM`. -/
def pPwM : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (b, r) ← pAtomM n ts
      match r with
      | .sym '^' :: r => do
          let (e, r) ← pPwM n r
          some (powerM b e, r)
      | _ => some (b, r)

/-- `pTermLoop` with `mulM`. -/
def pTermLoopM : Nat → Od → List Tok → Option (Od × List Tok)
  | 0, _, _ => none
  | n + 1, f, .sym '*' :: r => do
      let (g, r) ← pPwM n r
      pTermLoopM n (mulM f g) r
  | n + 1, f, r@(.num _ :: _) => do
      let (g, r) ← pPwM n r
      pTermLoopM n (mulM f g) r
  | _ + 1, f, r => some (f, r)

/-- `pTerm`, unchanged. -/
def pTermM : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (f, r) ← pPwM n ts
      pTermLoopM n f r

/-- `pExprLoop`, unchanged. -/
def pExprLoopM : Nat → Od → List Tok → Option (Od × List Tok)
  | 0, _, _ => none
  | n + 1, e, .sym '+' :: r => do
      let (t, r) ← pTermM n r
      pExprLoopM n (add e t) r
  | _ + 1, e, r => some (e, r)

/-- `pExpr`, unchanged. -/
def pExprM : Nat → List Tok → Option (Od × List Tok)
  | 0, _ => none
  | n + 1, ts => do
      let (t, r) ← pTermM n ts
      pExprLoopM n t r
end

/-- `parse` with `mulM`, `powerM`. -/
def parseM (s : String) : Option Od := do
  let cs := canonGo none (s.toList.filter (· != ' '))
  let ts ← tokGo none cs
  let (e, r) ← pExprM (4 * ts.length + 16) ts
  if r.isEmpty then some e else none

/-! ### Point 5: the step with a pattern match for rule 2 -/

/-- `alpha = Ω_w` for some `w`, by pattern (in place of `alpha == [(.W v, 1)]`). -/
def isOmegaForm : Od → Bool
  | [(.W _, 1)] => true
  | _ => false

section
variable (Mf : Od → Cols)

/-- `MstepAll` with `isOmegaForm alpha` in place of `alpha == [(.W v, 1)]`. -/
def MstepFix (alpha : Od) : Cols :=
  match lvlO alpha with
  | none => finishN Mf alpha (placeUnitsN Mf #[] alpha 0 (-1) none)
  | some v =>
    match isPsiLevel alpha with
    | some uX => MpsiLevel3 Mf uX.1 uX.2
    | none =>
      if isOmegaForm alpha then MOmega2 Mf v
      else
        let base := MOmega2 Mf v
        let ya := lastRoot base
        finishN Mf alpha (placeUnitsN Mf base alpha ya.1 (ya.2 - 1) (some v))

/-- The level of `Ω_w` is `w`. -/
theorem lvlO_omega (w : Od) : lvlO [(.W w, 1)] = some w := by
  simp [lvlO, lvl, fuel, lvlF]

/-- **Rule 2 on `Ω_w`** (with Fix A's base). -/
theorem MstepFix_omega (w : Od) : MstepFix Mf [(.W w, 1)] = MOmega2 Mf w := by
  simp [MstepFix, lvlO_omega, isPsiLevel, isOmegaForm]

/-- On `ψ_{Ω_u}(X)` the step is `MstepAll`'s (Fix E's rule 9). -/
theorem MstepFix_psi (alpha v : Od) (uX : Od × Od)
    (hv : lvlO alpha = some v) (hp : isPsiLevel alpha = some uX) :
    MstepFix Mf alpha = MstepAll Mf alpha := by
  simp [MstepFix, MstepAll, hv, hp]

/-- On countable `alpha` the step is `MstepAll`'s. -/
theorem MstepFix_countable (alpha : Od) (hv : lvlO alpha = none) :
    MstepFix Mf alpha = MstepAll Mf alpha := by
  simp [MstepFix, MstepAll, hv]

end

/-- The patched builder with fuel. -/
def MfuelFix : Nat → Od → Cols
  | 0, _ => #[]
  | n + 1, a => MstepFix (MfuelFix n) a

/-- `α ↦` the columns of `ψ_0(Ω_α)`, rules 1–10 with Fixes A–E, N and this patch. -/
def MFix (alpha : Od) : Cols := MfuelFix fuel alpha

/-- **The trio matrix of `ψ_0(Ω_α)` with the patch.** -/
def trioRuleMatrixFix (alpha : Od) : List (List Nat) := toRows (MFix alpha)

/-- The matrix for a label of the sheet, read by `parseM`. -/
def trioRuleMatrixOfFix (s : String) : Option (List (List Nat)) := do
  let a ← parseM s
  if a.isEmpty then none else some (trioRuleMatrixFix a)

/-- The matrix of a label, `[]` when it does not parse. -/
def fixOf (s : String) : List (List Nat) := (trioRuleMatrixOfFix s).getD []

/-- **Every column is three rows deep with `z < 2`.** -/
theorem WF3_trioRuleMatrixFix (alpha : Od) : WF3 (trioRuleMatrixFix alpha) := WF3_toRows _

end Googology.Trans.BMS.TrioFixMulNormalize
