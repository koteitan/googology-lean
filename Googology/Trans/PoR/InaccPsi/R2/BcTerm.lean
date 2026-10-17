import Googology.Trans.PoR.InaccPsi.CountSeg

/-!
# The base change `B_k` on InaccPsi terms: summand lists, the constants, the map

Terms are those of `Googology.Notation.InaccPsi.Term`.  A normal-form sum is a right-nested
chain `add p₀ (add p₁ (⋯ p_m))` of principal terms; `bcSl t` is its list of summands.

* `bcApp P r`: the chain with the summands `P` followed by the summands of `r`;
  `bcDrop j t`: the chain `t` without its first `j` summands;
* the constant terms `tW` (`Ω_ω`), `tPp` (`P' = ψ_{Ω₂}(Ω_ω·2)`), `tWp` (`ω^{P'+1} = P'·ω`), and the
  prefixes `bcPre k = [Ω_ω, Ω_ω, P', …, P']` (`k` copies of `P'`, value `Ω_ω·2 + P'·k`) and
  `bcPreW = [Ω_ω, Ω_ω, ω^{P'+1}]` (value `Ω_ω·2 + P'·ω`);
* `bcSig Ps Pt` (**the base change on terms**): it commutes with every constructor, except that
  the argument `a` of a `ψ_{Ω₁}`-collapse `ψ^S_0(a)` whose summands begin with `Ps` is rewritten
  to `Pt` followed by the image of the remaining summands.  With `Ps = bcPre k`, `Pt = bcPreW`
  this is the η-base change that sends `L(k) = ψ_{Ω₁}(Ω_ω·2 + P'·k)` to
  `L(ω) = ψ_{Ω₁}(Ω_ω·2 + P'·ω)` and `ψ_{Ω₁}(Ω_ω·2 + P'·k + δ)` to `ψ_{Ω₁}(Ω_ω·2 + P'·ω + B(δ))`;
* syntactic facts: `bcSig` keeps `zero`, the kinds (`isPrin`, `isSC`, `isK`, `isF`), heads and
  `cardT`; `bcArg` is the image of a `ψ^S_0`-argument.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

/-! ## Summand lists -/

/-- The summands of a chain. -/
def bcSl : Term → List Term
  | zero => []
  | inacc n => [inacc n]
  | inaccW => [inaccW]
  | add a b => a :: bcSl b
  | phi a b => [phi a b]
  | om a => [om a]
  | psiS s a => [psiS s a]
  | psiI n a => [psiI n a]

/-- `bcApp P r`: the chain with the summands `P`, then `r`. -/
def bcApp : List Term → Term → Term
  | [], r => r
  | [x], r => if r = zero then x else add x r
  | x :: y :: ys, r => add x (bcApp (y :: ys) r)

/-- `bcDrop j t`: the chain `t` without its first `j` summands. -/
def bcDrop : ℕ → Term → Term
  | 0, t => t
  | j + 1, add _ b => bcDrop j b
  | _ + 1, zero => zero
  | _ + 1, inacc _ => zero
  | _ + 1, inaccW => zero
  | _ + 1, phi _ _ => zero
  | _ + 1, om _ => zero
  | _ + 1, psiS _ _ => zero
  | _ + 1, psiI _ _ => zero

theorem bcDrop_size_le : ∀ (j : ℕ) (t : Term), (bcDrop j t).size ≤ t.size
  | 0, t => le_rfl
  | j + 1, add a b => by
    have := bcDrop_size_le j b; simp only [bcDrop, size]; omega
  | _ + 1, zero => le_rfl
  | _ + 1, inacc _ => by simp [bcDrop, size]
  | _ + 1, inaccW => by simp [bcDrop, size]
  | _ + 1, phi _ _ => by simp [bcDrop, size]
  | _ + 1, om _ => by simp [bcDrop, size]
  | _ + 1, psiS _ _ => by simp [bcDrop, size]
  | _ + 1, psiI _ _ => by simp [bcDrop, size]

/-- Lexicographic comparison of summand lists. -/
def bcLcmp : List Term → List Term → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if cmp x y = .eq then bcLcmp xs ys else cmp x y

/-! ## The constants -/

/-- `1 = φ(0, 0)`. -/
def tOne : Term := phi zero zero
/-- `ω = φ(0, 1)`. -/
def tOm : Term := phi zero tOne
/-- `Ω_ω`. -/
def tW : Term := om tOm
/-- `P' = ψ_{Ω₂}(Ω_ω + Ω_ω)` (`ψ^S_1`, i.e. `ψ_{Ω_{1+1}}`). -/
def tPp : Term := psiS tOne (add tW tW)
/-- `ω^{P'+1}`. -/
def tWp : Term := phi zero (add tPp tOne)

/-- `[Ω_ω, Ω_ω, P', …, P']` with `k` copies of `P'`. -/
def bcPre (k : ℕ) : List Term := tW :: tW :: List.replicate k tPp

/-- `[Ω_ω, Ω_ω, ω^{P'+1}]`. -/
def bcPreW : List Term := [tW, tW, tWp]

/-! ## The base change on terms -/

/-- **The base change on terms.**  It commutes with the constructors, except at a
`ψ_{Ω₁}`-argument whose summands begin with `Ps`: those summands are replaced by `Pt`. -/
def bcSig (Ps Pt : List Term) : Term → Term
  | zero => zero
  | inacc n => inacc n
  | inaccW => inaccW
  | add a b => add (bcSig Ps Pt a) (bcSig Ps Pt b)
  | phi a b => phi (bcSig Ps Pt a) (bcSig Ps Pt b)
  | om a => om (bcSig Ps Pt a)
  | psiS s a =>
      if s = zero ∧ Ps.isPrefixOf (bcSl a) = true then
        psiS zero (bcApp Pt (bcSig Ps Pt (bcDrop Ps.length a)))
      else psiS (bcSig Ps Pt s) (bcSig Ps Pt a)
  | psiI n a => psiI n (bcSig Ps Pt a)
termination_by t => t.size
decreasing_by
  all_goals first
    | (simp only [Term.size]; omega)
    | exact Nat.lt_of_le_of_lt (bcDrop_size_le _ _) (by simp only [Term.size]; omega)

/-- The image of a `ψ^S_0`-argument. -/
def bcArg (Ps Pt : List Term) (a : Term) : Term :=
  if Ps.isPrefixOf (bcSl a) = true then bcApp Pt (bcSig Ps Pt (bcDrop Ps.length a))
  else bcSig Ps Pt a

section Sig

variable {Ps Pt : List Term}

@[simp] theorem bcSig_zero : bcSig Ps Pt zero = zero := by rw [bcSig]
@[simp] theorem bcSig_inacc (n : ℕ) : bcSig Ps Pt (inacc n) = inacc n := by rw [bcSig]
@[simp] theorem bcSig_inaccW : bcSig Ps Pt inaccW = inaccW := by rw [bcSig]
@[simp] theorem bcSig_add (a b : Term) :
    bcSig Ps Pt (add a b) = add (bcSig Ps Pt a) (bcSig Ps Pt b) := by rw [bcSig]
@[simp] theorem bcSig_phi (a b : Term) :
    bcSig Ps Pt (phi a b) = phi (bcSig Ps Pt a) (bcSig Ps Pt b) := by rw [bcSig]
@[simp] theorem bcSig_om (a : Term) : bcSig Ps Pt (om a) = om (bcSig Ps Pt a) := by rw [bcSig]
@[simp] theorem bcSig_psiI (n : ℕ) (a : Term) :
    bcSig Ps Pt (psiI n a) = psiI n (bcSig Ps Pt a) := by rw [bcSig]

theorem bcSig_psiS_zero (a : Term) : bcSig Ps Pt (psiS zero a) = psiS zero (bcArg Ps Pt a) := by
  rw [bcSig, bcArg]
  by_cases h : Ps.isPrefixOf (bcSl a) = true
  · rw [if_pos ⟨rfl, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h, bcSig_zero]

theorem bcSig_psiS_ne {s : Term} (hs : s ≠ zero) (a : Term) :
    bcSig Ps Pt (psiS s a) = psiS (bcSig Ps Pt s) (bcSig Ps Pt a) := by
  rw [bcSig, if_neg (fun h' => hs h'.1)]

/-- `bcSig` of a collapse `ψ^S_s(a)`: subscript image, and the argument image `bcArg` when
`s = 0`. -/
theorem bcSig_psiS (s a : Term) : bcSig Ps Pt (psiS s a) =
    psiS (bcSig Ps Pt s) (if s = zero then bcArg Ps Pt a else bcSig Ps Pt a) := by
  by_cases hs : s = zero
  · subst hs; rw [bcSig_psiS_zero, if_pos rfl, bcSig_zero]
  · rw [bcSig_psiS_ne hs, if_neg hs]

theorem bcArg_of_not {a : Term} (h : ¬ Ps.isPrefixOf (bcSl a) = true) :
    bcArg Ps Pt a = bcSig Ps Pt a := by rw [bcArg, if_neg h]

theorem bcArg_of_pre {a : Term} (h : Ps.isPrefixOf (bcSl a) = true) :
    bcArg Ps Pt a = bcApp Pt (bcSig Ps Pt (bcDrop Ps.length a)) := by rw [bcArg, if_pos h]

theorem bcSig_eq_zero_iff {t : Term} : bcSig Ps Pt t = zero ↔ t = zero := by
  cases t <;> simp [bcSig_psiS]

theorem bcSig_ne_zero {t : Term} (h : t ≠ zero) : bcSig Ps Pt t ≠ zero :=
  fun e => h (bcSig_eq_zero_iff.1 e)

theorem isF_bcSig (t : Term) : (bcSig Ps Pt t).isF = t.isF := by
  cases t <;> simp [bcSig_psiS, isF]

theorem isSC_bcSig (t : Term) : (bcSig Ps Pt t).isSC = t.isSC := by
  cases t <;> simp [bcSig_psiS, isSC]

theorem isPrin_bcSig (t : Term) : (bcSig Ps Pt t).isPrin = t.isPrin := by
  cases t <;> simp [bcSig_psiS, isPrin, isSC]

theorem isK_bcSig (t : Term) : (bcSig Ps Pt t).isK = t.isK := by
  cases t <;> simp [bcSig_psiS, isK, isF]

theorem head_bcSig (t : Term) : head (bcSig Ps Pt t) = bcSig Ps Pt (head t) := by
  cases t <;> simp [bcSig_psiS, head]

theorem cardT_bcSig (s : Term) : cardT (bcSig Ps Pt s) = bcSig Ps Pt (cardT s) := by
  unfold cardT
  by_cases h0 : s = zero
  · subst h0; simp
  · rw [if_neg (bcSig_ne_zero h0), if_neg h0, isF_bcSig]
    split_ifs <;> simp

end Sig

end Googology.Trans.PoR.InaccPsi.R2.Bc
