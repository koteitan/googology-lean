import Googology.Trans.BMS.TrioCofPsi

/-!
# Trio cofinality at a successor

`TrioCofPsi.trioPsi_fs` relates the fundamental sequence of `ψ_0(Ω_α)` to the
expansions of its trio matrix `M(α) = omegaIndexMatrix α` at a limit `α`, where
the members are again `ψ_0(Ω_γ)`.  At a successor `α = β + 1` they are not:

  `ψ_0(Ω_{β+1})[n] = ψ_0(ψ_β^{n+1}(0))`   (`fs_psiOmega_succ`),

that is `ψ_0(Ω_β)`, `ψ_0(ψ_β(Ω_β))`, `ψ_0(ψ_β(ψ_β(Ω_β)))`, …  (for `β ≥ 1`,
`ψ_β(Ω_β) = Ω_β^2` and then `Ω_β^{Ω_β}`, `Ω_β^{Ω_β^{Ω_β}}`, …).  This file
extends the map to these terms and proves the two-way cofinality.

**The expansions.**  `M(β+1)` is `M(β)` and one add unit `1`; its last two
columns are `(x, y, 0)(x+1, y+1, 0)`, whose expansion is a ladder
(`expandRL_ladder`):

  `(A ++ (x,y,0)(x+1,y+1,0))[N] = A ++ (x,y,0)(x+1,y,0)⋯(x+N,y,0)`.

**The map on the members** (`towerMatrix β n`, the matrix of
`ψ_0(ψ_β^{n+1}(0))`):

* `β = 0`: `(0)(1)⋯(n+1)`, which is `M(1)[n+1]` (`towerMatrix_zero`);
* `β` ends in `1`: `M(β+1)[n]` itself (`towerMatrix_pz`);
* `β ≠ 0` ends in `ω^c`, `c ≠ 0`: `M(β)` for `n = 0`, and for `n ≥ 1` the
  expansion `M(β+1)[n-1]` followed by the root and the multiply units of the
  last add unit of `M(β)`, unchanged.  So `M(β+1)[n-1] < towerMatrix β n <
  M(β+1)[n]` (`expand_lt_towerMatrix`, `towerMatrix_lt_expand`).

The first two cases are forced: the member's matrix is an expansion.  The
third is a reading of `Ω_β^2 = Ω_β·Ω_β`, `Ω_β^{Ω_β}`, …: the ladder climbs
past `Ω_β` at its level, and the root and multiply units that spell `Ω_β` in
`M(β)` are written once more.  The `#guard`s at the end check the published
rows for `v = 0, 1`.

**What is proved** (`trioPsi_fs_succ`), for standard `α = β + 1 < ε₀`:

* `ψ_0(Ω_α)[n] = ψ_0(ψ_β^{n+1}(0))`;
* `M(α)[k] < M(α)`, and `towerMatrix β n < M(α)`;
* `∀ n, ∃ k, towerMatrix β n ≤ M(α)[k]`;
* `∀ k, ∃ n, M(α)[k] ≤ towerMatrix β n`.

Also `towerMatrix β n < towerMatrix β (n+1)` (`towerMatrix_lt_succ`), and
`towerMatrix β n` is in the trio fragment except when `β` is a limit and
`n ≥ 1` (`trioStdL_towerMatrix`).  On the members the map is
order-preserving: both sides increase in `n` (`towerMatrix_lt_iff`), and
`M(β) ≤ towerMatrix β n` (`omegaIndexMatrix_le_towerMatrix`).
-/

namespace Googology.Trans.BMS
namespace TrioSucc

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open TrioStd
open TrioCofPsi (psiOmega)

/-! ### A ladder -/

/-- `n` columns `(x, y, 0), (x+1, y, 0), …` climbing in row `0` at level `y`. -/
def ladder (x y n : Nat) : List (List Nat) := (List.range n).map (fun t => [x + t, y, 0])

theorem m0L_three_one {l : List (List Nat)} (h1 : (parAtR l 1 (l.length - 1)).isSome = true)
    (h2 : parAtR l 2 (l.length - 1) = none) : m0L 3 l = 1 := by
  rw [m0L, show 3 - 1 = 1 + 1 from rfl, Nat.findGreatest_of_not (by rw [h2]; simp)]
  exact Nat.findGreatest_eq h1

/-- **`(a, y, 0)(a+1, y+1, 0)` expands to a ladder at level `y`.** -/
theorem expandRL_ladder (N a y : Nat) (A : List (List Nat)) :
    expandRL 3 N (A ++ [[a, y, 0], [a + 1, y + 1, 0]]) = A ++ ladder a y (N + 1) := by
  set B : List (List Nat) := [[a, y, 0], [a + 1, y + 1, 0]] with hB
  have h0 : ParR B 0 0 1 := ⟨by omega, by simp [hB], fun j' h1 h2 => by omega⟩
  have h1 : ParR B 1 0 1 := ⟨by omega, .single h0, by simp [hB], fun j' h1 h2 => by omega⟩
  have hp1 : parAtR B 1 (B.length - 1) = some 0 := (parAtR_eq_some _ _ _ _).mpr h1
  have hn2 : parAtR B 2 (B.length - 1) = none := parAtR_none_of_zero (k := 1) (by simp [hB])
  have hm : m0L 3 B = 1 := m0L_three_one (by rw [hp1]; rfl) hn2
  have hb : badRootR 3 B = some 0 := by
    rw [badRootR_eq (by simp [hB]), hm]; exact hp1
  have hlen : (A ++ B).length - 1 = A.length + (B.length - 1) := by simp [hB]
  have hmA : m0L 3 (A ++ B) = 1 := by
    apply m0L_three_one
    · rw [hlen, parAtR_shift hp1]; rfl
    · exact parAtR_none_of_zero (k := 1) (by rw [hlen, getElem!_append_right]; simp [hB])
  rw [expandRL_append_local 3 N A B 0 hb (by rw [hm, hmA])]
  congr 1
  rw [expandRL_some 3 N B 0 hb, hm]
  simp [hB, ladder, List.range_succ, List.flatten]
  exact flatten_map_single _ _

/-! ### The fundamental sequence of `ψ_0(Ω_{β+1})` -/

/-- `ψ_β^n(0)`: `0`, `Ω_β`, `ψ_β(Ω_β)`, … -/
def towerT (β : Term) : Nat → Term
  | 0 => nil
  | n + 1 => psi β (towerT β n)

theorem addT_one_cons (t : Term) : ∃ c d u, addT t t1 = cons c d u := by
  cases t with
  | nil => exact ⟨nil, nil, nil, rfl⟩
  | cons a b u => exact ⟨a, b, addT u t1, rfl⟩

theorem fs_addT_one : ∀ (β Y : Term), fs (addT β t1) Y = β := by
  intro β Y
  induction β with
  | nil => rw [addT_nil_left, fs]; simp
  | cons a b t _ _ iht =>
    obtain ⟨c, d, u, hc⟩ := addT_one_cons t
    rw [addT_cons, hc, fs, ← hc, iht]

theorem dom_addT_one : ∀ β : Term, dom (addT β t1) = t1 := by
  intro β
  induction β with
  | nil => rfl
  | cons a b t _ _ iht =>
    obtain ⟨c, d, u, hc⟩ := addT_one_cons t
    rw [addT_cons, hc, dom, ← hc, iht]
    simp

theorem addT_one_ne_nil (β : Term) : addT β t1 ≠ nil := by
  cases β <;> simp

theorem dom_psi_succ (β : Term) : dom (psi (addT β t1) nil) = psi (addT β t1) nil := by
  rw [dom]
  simp [dom_addT_one]

theorem psi_succ_not_lt (β : Term) : ¬ psi (addT β t1) nil < psiOmega (addT β t1) := by
  rw [psi_lt_psi_iff]
  rintro (h | ⟨h, -⟩)
  · exact absurd h (by
      intro h'
      have := TrioMono.eq_nil_of_le_nil (le_of_lt h')
      exact addT_one_ne_nil β this)
  · exact addT_one_ne_nil β h

theorem psi_succ_not_cmp (β : Term) :
    ¬ Term.cmp (psi (addT β t1) nil) (psiOmega (addT β t1)) = Ordering.lt :=
  psi_succ_not_lt β

theorem isNum_numeral : ∀ n : Nat, isNum (numeral n) = true := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih => simpa [numeral, repeatPrin, isNum] using ih

theorem dom_psiOmega_succ (β : Term) : dom (psiOmega (addT β t1)) = tw := by
  rw [dom]
  have hne : psi (addT β t1) nil ≠ t1 := by simp [addT_one_ne_nil]
  have hne2 : psi (addT β t1) nil ≠ tw := by simp
  simp [dom_psi_succ, hne, hne2, psi_succ_not_cmp]

theorem idx_psiOmega_succ (β : Term) (n : Nat) :
    idx (psiOmega (addT β t1)) n = numeral n := by
  rw [idx, dom_psiOmega_succ]
  simp

theorem fs_psi_succ (β Y : Term) : fs (psi (addT β t1) nil) Y = Y := by
  rw [fs]
  simp [dom_addT_one]

/-- **At a successor `α = β + 1`, `ψ_0(Ω_α)[n] = ψ_0(ψ_β^{n+1}(0))`**: the
members are `ψ_0(Ω_β)`, `ψ_0(ψ_β(Ω_β))`, `ψ_0(ψ_β(ψ_β(Ω_β)))`, …, for any
term `β`. -/
theorem fs_psiOmega_succ (β : Term) : ∀ n : Nat,
    fs (psiOmega (addT β t1)) (idx (psiOmega (addT β t1)) n) = psi nil (towerT β (n + 1)) := by
  intro n
  rw [idx_psiOmega_succ]
  induction n with
  | zero =>
    rw [fs]
    have hne : psi (addT β t1) nil ≠ t1 := by simp [addT_one_ne_nil]
    have hne2 : psi (addT β t1) nil ≠ tw := by simp
    simp [dom_psi_succ, hne, hne2, psi_succ_not_cmp, subOf, fs_addT_one, fs_psi_succ, towerT,
      numeral, repeatPrin]
  | succ m ih =>
    rw [fs]
    have hne : psi (addT β t1) nil ≠ t1 := by simp [addT_one_ne_nil]
    have hne2 : psi (addT β t1) nil ≠ tw := by simp
    have hnum : numeral (m + 1) ≠ nil ∧ isNum (numeral (m + 1)) = true :=
      ⟨by simp [numeral, repeatPrin], isNum_numeral _⟩
    have hpred : numPred (numeral (m + 1)) = numeral m := rfl
    simp [dom_psi_succ, hne, hne2, psi_succ_not_cmp, hnum, hpred, ih, subOf, fs_addT_one,
      fs_psi_succ, towerT]

/-! ### The trio matrix of `ψ_0(Ω_{β+1})` -/

/-- The state `(rp1, lastX, pz, i)` of `addUnits` after the summands of a term. -/
def auState : Nat → Nat → Bool → Nat → Term → Nat × Nat × Bool × Nat
  | rp1, lastX, pz, i, nil => (rp1, lastX, pz, i)
  | rp1, lastX, pz, i, cons _ b t =>
      if b == nil then
        (if pz then auState rp1 (lastX + 1) true (i + 1) t
         else auState rp1 (rp1 + 1) true (i + 1) t)
      else auState (rp1 + 2) (rp1 + 1) false (i + 1) t

/-- **The add units of a sum** are those of the first part, then those of the
second from the state the first leaves. -/
theorem addUnits_addT (γ : Term) : ∀ (β : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    addUnits rp1 lastX pz i (addT β γ) = addUnits rp1 lastX pz i β ++
      addUnits (auState rp1 lastX pz i β).1 (auState rp1 lastX pz i β).2.1
        (auState rp1 lastX pz i β).2.2.1 (auState rp1 lastX pz i β).2.2.2 γ := by
  intro β
  induction β with
  | nil => intro _ _ _ _; rfl
  | cons a b t _ _ iht =>
    intro rp1 lastX pz i
    rw [addT_cons, addUnits, addUnits, auState]
    by_cases hb : (b == nil) = true
    · rw [if_pos hb, if_pos hb, if_pos hb]
      cases pz with
      | true => simp only [if_true]; rw [iht]; rfl
      | false => simp only [Bool.false_eq_true, if_false]; rw [iht]; rfl
    · rw [if_neg hb, if_neg hb, if_neg hb, iht, List.append_assoc]

theorem auState_i_ge : ∀ (β : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat),
    i ≤ (auState rp1 lastX pz i β).2.2.2 := by
  intro β
  induction β with
  | nil => intro _ _ _ _; exact le_refl _
  | cons a b t _ _ iht =>
    intro rp1 lastX pz i
    rw [auState]
    split
    · split
      · exact le_trans (Nat.le_succ i) (iht _ _ _ _)
      · exact le_trans (Nat.le_succ i) (iht _ _ _ _)
    · exact le_trans (Nat.le_succ i) (iht _ _ _ _)

theorem auState_i_pos : ∀ (β : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat), β ≠ nil →
    1 ≤ (auState rp1 lastX pz i β).2.2.2 := by
  intro β rp1 lastX pz i hβ
  cases β with
  | nil => exact absurd rfl hβ
  | cons a b t =>
    rw [auState]
    split
    · split
      · exact le_trans (by omega) (auState_i_ge t _ _ _ (i + 1))
      · exact le_trans (by omega) (auState_i_ge t _ _ _ (i + 1))
    · exact le_trans (by omega) (auState_i_ge t _ _ _ (i + 1))

/-- **When the last summand is `1`, the last column is `(lastX, i-1, 0)`.** -/
theorem addUnits_last_pz : ∀ (β : Term) (rp1 lastX : Nat) (pz : Bool) (i : Nat), β ≠ nil →
    (auState rp1 lastX pz i β).2.2.1 = true →
    ∃ Q, addUnits rp1 lastX pz i β
      = Q ++ [[(auState rp1 lastX pz i β).2.1, (auState rp1 lastX pz i β).2.2.2 - 1, 0]] := by
  intro β
  induction β with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons a b t _ _ iht =>
    intro rp1 lastX pz i _ hz
    by_cases ht : t = nil
    · subst ht
      rw [auState] at hz ⊢
      rw [addUnits]
      by_cases hb : (b == nil) = true
      · rw [if_pos hb] at hz ⊢
        rw [if_pos hb]
        cases pz with
        | true => exact ⟨[], by simp [auState, addUnits]⟩
        | false => exact ⟨[[rp1, i - 1, 0]], by simp [auState, addUnits]⟩
      · rw [if_neg hb] at hz ⊢
        simp [auState] at hz
    · rw [auState] at hz ⊢
      rw [addUnits]
      by_cases hb : (b == nil) = true
      · rw [if_pos hb] at hz ⊢
        rw [if_pos hb]
        cases pz with
        | true =>
          obtain ⟨Q, hQ⟩ := iht rp1 (lastX + 1) true (i + 1) ht hz
          exact ⟨[lastX + 1, i, 0] :: Q, by rw [hQ]; rfl⟩
        | false =>
          obtain ⟨Q, hQ⟩ := iht rp1 (rp1 + 1) true (i + 1) ht hz
          exact ⟨[rp1, i - 1, 0] :: [rp1 + 1, i, 0] :: Q, by rw [hQ]; rfl⟩
      · rw [if_neg hb] at hz ⊢
        rw [if_neg hb]
        obtain ⟨Q, hQ⟩ := iht (rp1 + 2) (rp1 + 1) false (i + 1) ht hz
        exact ⟨([rp1, i - 1, 0] :: bodyU b (rp1 + 1) i) ++ Q, by rw [hQ, List.append_assoc]⟩

/-- The state after the add units of `β`, read from the start of `M(β)`. -/
abbrev sR (β : Term) : Nat := (auState 0 0 false 1 β).1
abbrev sX (β : Term) : Nat := (auState 0 0 false 1 β).2.1
abbrev sZ (β : Term) : Bool := (auState 0 0 false 1 β).2.2.1
abbrev sI (β : Term) : Nat := (auState 0 0 false 1 β).2.2.2

/-- **`M(β+1)` is `M(β)` and one more add unit `1`.** -/
theorem omegaIndexMatrix_succ (β : Term) :
    omegaIndexMatrix (addT β t1) = omegaIndexMatrix β ++
      (if sZ β then [[sX β + 1, sI β, 0]] else [[sR β, sI β - 1, 0], [sR β + 1, sI β, 0]]) := by
  rw [omegaIndexMatrix, addUnits_addT, omegaIndexMatrix]
  congr 1

theorem ladder_succ_left (x y n : Nat) : ladder x y (n + 1) = [x, y, 0] :: ladder (x + 1) y n := by
  rw [ladder, map_range_succ', ladder]
  refine congrArg₂ List.cons (by simp) (List.map_congr_left (fun t _ => ?_))
  exact list3_eq (by omega) rfl rfl

theorem ladder_succ_right (x y n : Nat) : ladder x y (n + 1) = ladder x y n ++ [[x + n, y, 0]] := by
  rw [ladder, List.range_succ, List.map_append, ladder]
  rfl

/-- **`M(1)[N]`**: `(0,0,0)(1,0,0)⋯(N,0,0)`. -/
theorem expand_one (N : Nat) : expandRL 3 N (omegaIndexMatrix (addT nil t1)) = ladder 0 0 (N + 1) := by
  have := expandRL_ladder N 0 0 []
  simpa [omegaIndexMatrix, addUnits] using this

/-- **`M(β+1)[N]` when `β` ends in `1`**: `M(β)` and `N` more columns of the
ladder its last column starts. -/
theorem expand_succ_pz {β : Term} (hβ : β ≠ nil) (hz : sZ β = true) (N : Nat) :
    expandRL 3 N (omegaIndexMatrix (addT β t1))
      = omegaIndexMatrix β ++ ladder (sX β + 1) (sI β - 1) N := by
  obtain ⟨Q, hQ⟩ := addUnits_last_pz β 0 0 false 1 hβ hz
  have hi : 1 ≤ sI β := auState_i_pos β 0 0 false 1 hβ
  rw [omegaIndexMatrix_succ, if_pos hz, omegaIndexMatrix, hQ, List.append_assoc]
  have := expandRL_ladder N (sX β) (sI β - 1) Q
  rw [show sI β - 1 + 1 = sI β by omega] at this
  simp only [List.cons_append, List.nil_append] at this ⊢
  rw [this, ladder_succ_left, List.append_assoc]
  rfl

/-- **`M(β+1)[N]` when `β ≠ 0` ends in `ω^c`, `c ≠ 0`**: `M(β)` and a ladder of
`N + 1` columns from the new anchor. -/
theorem expand_succ_lim {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) (N : Nat) :
    expandRL 3 N (omegaIndexMatrix (addT β t1))
      = omegaIndexMatrix β ++ ladder (sR β) (sI β - 1) (N + 1) := by
  have hi : 1 ≤ sI β := auState_i_pos β 0 0 false 1 hβ
  rw [omegaIndexMatrix_succ, if_neg (by simp [hz])]
  have := expandRL_ladder N (sR β) (sI β - 1) (omegaIndexMatrix β)
  rwa [show sI β - 1 + 1 = sI β by omega] at this

/-! ### The trio matrix of `ψ_0(ψ_β^{n+1}(0))` -/

/-- The exponent of the last summand. -/
def lastExp : Term → Term
  | nil => nil
  | cons _ b t => if t == nil then b else lastExp t

/-- The limit case of `towerMatrix`. -/
def towerLim (β : Term) : Nat → List (List Nat)
  | 0 => omegaIndexMatrix β
  | k + 1 => omegaIndexMatrix β ++ ladder (sR β) (sI β - 1) (k + 1)
      ++ bodyU (lastExp β) (sR β - 1) (sI β - 1)

/-- **The trio matrix of `ψ_0(ψ_β^{n+1}(0))`**, the `n`-th member of the
fundamental sequence of `ψ_0(Ω_{β+1})`:

* `β = 0`: `ψ_0(ψ_0^{n+1}(0)) = ω↑↑(n+1)` is the one-row matrix `(0)(1)⋯(n+1)`;
* `β` ends in `1` (its last column is a `z0` column `(x, y, 0)`): `M(β)` and a
  ladder `(x+1, y, 0) ⋯ (x+n, y, 0)`;
* `β ≠ 0` ends in `ω^c`, `c ≠ 0` (its last add unit is an anchor `(a, y-1, 0)`,
  a root `(a+1, y, 1)` and multiply units): `M(β)` for `n = 0`; otherwise
  `M(β)`, a ladder `(a+2, y, 0) ⋯ (a+1+n, y, 0)` of `n` columns at the root's
  level, and the root and the multiply units of the last add unit again. -/
def towerMatrix (β : Term) (n : Nat) : List (List Nat) :=
  match β with
  | nil => ladder 0 0 (n + 2)
  | cons _ _ _ =>
    if sZ β then omegaIndexMatrix β ++ ladder (sX β + 1) (sI β - 1) n
    else towerLim β n

/-- `β = 0`: the member is an expansion of `M(1)`, one bracket up. -/
theorem towerMatrix_zero (n : Nat) :
    towerMatrix nil n = expandRL 3 (n + 1) (omegaIndexMatrix (addT nil t1)) := by
  rw [expand_one]; rfl

/-- `β` ends in `1`: **the member is the expansion `M(β+1)[n]` itself.** -/
theorem towerMatrix_pz {β : Term} (hβ : β ≠ nil) (hz : sZ β = true) (n : Nat) :
    towerMatrix β n = expandRL 3 n (omegaIndexMatrix (addT β t1)) := by
  rw [expand_succ_pz hβ hz]
  cases β with
  | nil => exact absurd rfl hβ
  | cons a b t => rw [towerMatrix, if_pos hz]

theorem towerMatrix_lim_zero {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) :
    towerMatrix β 0 = omegaIndexMatrix β := by
  cases β with
  | nil => exact absurd rfl hβ
  | cons a b t => rw [towerMatrix, if_neg (by simp [hz]), towerLim]

theorem towerMatrix_lim_succ {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) (n : Nat) :
    towerMatrix β (n + 1) = omegaIndexMatrix β ++ ladder (sR β) (sI β - 1) (n + 1)
      ++ bodyU (lastExp β) (sR β - 1) (sI β - 1) := by
  cases β with
  | nil => exact absurd rfl hβ
  | cons a b t => rw [towerMatrix, if_neg (by simp [hz]), towerLim]

theorem lt_append_cons (P : List (List Nat)) (c : List Nat) (S : List (List Nat)) :
    P < P ++ c :: S := by
  have := TrioMono.append_lt_append_left P (List.nil_lt_cons c S)
  rwa [List.append_nil] at this

/-- `β` a limit, `n = 0`: `M(β) < M(β+1)[0]`. -/
theorem towerMatrix_lim_zero_lt {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) :
    towerMatrix β 0 < expandRL 3 0 (omegaIndexMatrix (addT β t1)) := by
  rw [towerMatrix_lim_zero hβ hz, expand_succ_lim hβ hz, ladder_succ_left]
  exact lt_append_cons _ _ _

/-- `β` a limit: **`M(β+1)[n] < ψ_0(ψ_β^{n+2}(0))`'s matrix**, a proper prefix. -/
theorem expand_lt_towerMatrix {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) (n : Nat) :
    expandRL 3 n (omegaIndexMatrix (addT β t1)) < towerMatrix β (n + 1) := by
  rw [towerMatrix_lim_succ hβ hz, expand_succ_lim hβ hz, bodyU]
  exact lt_append_cons _ _ _

/-- `β` a limit: **the matrix of `ψ_0(ψ_β^{n+2}(0))` is below `M(β+1)[n+1]`**: the
root copied after the ladder is below the next rung. -/
theorem towerMatrix_lt_expand {β : Term} (hβ : β ≠ nil) (hz : sZ β = false) (n : Nat) :
    towerMatrix β (n + 1) < expandRL 3 (n + 1) (omegaIndexMatrix (addT β t1)) := by
  rw [towerMatrix_lim_succ hβ hz, expand_succ_lim hβ hz, ladder_succ_right (sR β) _ (n + 1),
    bodyU, List.append_assoc]
  refine TrioMono.append_lt_append_left _ (TrioMono.append_lt_append_left _ ?_)
  exact List.cons_lt_cons_iff.mpr (Or.inl (TrioMono.col_lt (Or.inl (by omega))))

/-- A successor, `dom α = 1`, is `β + 1`. -/
theorem eq_addT_one_of_dom : ∀ α : Term, dom α = t1 → ∃ β, α = addT β t1 := by
  intro α
  induction α with
  | nil => intro h; simp at h
  | cons a b t _ _ iht =>
    intro h
    cases t with
    | nil =>
      refine ⟨nil, ?_⟩
      rw [dom] at h
      split_ifs at h <;> simp_all
    | cons c d u =>
      rw [dom_cons_cons] at h
      obtain ⟨β, hβ⟩ := iht h
      exact ⟨cons a b β, by rw [hβ]; rfl⟩

/-! ### Cofinal in each other -/

/-- **Each member's matrix is at or below an expansion of `M(β+1)`.** -/
theorem towerMatrix_le_expand (β : Term) (n : Nat) :
    ∃ k, towerMatrix β n = expandRL 3 k (omegaIndexMatrix (addT β t1)) ∨
      towerMatrix β n < expandRL 3 k (omegaIndexMatrix (addT β t1)) := by
  by_cases hβ : β = nil
  · subst hβ; exact ⟨n + 1, Or.inl (towerMatrix_zero n)⟩
  · cases hz : sZ β with
    | true => exact ⟨n, Or.inl (towerMatrix_pz hβ hz n)⟩
    | false =>
      cases n with
      | zero => exact ⟨0, Or.inr (towerMatrix_lim_zero_lt hβ hz)⟩
      | succ m => exact ⟨m + 1, Or.inr (towerMatrix_lt_expand hβ hz m)⟩

/-- **Each expansion of `M(β+1)` is at or below a member's matrix.** -/
theorem expand_le_towerMatrix (β : Term) (k : Nat) :
    ∃ n, expandRL 3 k (omegaIndexMatrix (addT β t1)) = towerMatrix β n ∨
      expandRL 3 k (omegaIndexMatrix (addT β t1)) < towerMatrix β n := by
  by_cases hβ : β = nil
  · subst hβ
    cases k with
    | zero =>
      refine ⟨0, Or.inr ?_⟩
      rw [expand_one, show towerMatrix nil 0 = ladder 0 0 (0 + 1 + 1) from rfl,
        ladder_succ_right 0 0 (0 + 1)]
      exact lt_append_cons _ _ _
    | succ m => exact ⟨m, Or.inl (towerMatrix_zero m).symm⟩
  · cases hz : sZ β with
    | true => exact ⟨k, Or.inl (towerMatrix_pz hβ hz k).symm⟩
    | false => exact ⟨k + 1, Or.inr (expand_lt_towerMatrix hβ hz k)⟩

/-- **The members' matrices increase.** -/
theorem towerMatrix_lt_succ (β : Term) (n : Nat) : towerMatrix β n < towerMatrix β (n + 1) := by
  by_cases hβ : β = nil
  · subst hβ
    rw [show towerMatrix nil (n + 1) = ladder 0 0 (n + 2 + 1) from rfl,
      ladder_succ_right 0 0 (n + 2)]
    exact lt_append_cons _ _ _
  · cases hz : sZ β with
    | true =>
      rw [towerMatrix_pz hβ hz, towerMatrix_pz hβ hz, expand_succ_pz hβ hz, expand_succ_pz hβ hz,
        ladder_succ_right, ← List.append_assoc]
      exact lt_append_cons _ _ _
    | false =>
      cases n with
      | zero =>
        rw [towerMatrix_lim_zero hβ hz, towerMatrix_lim_succ hβ hz, ladder_succ_left,
          List.append_assoc]
        exact lt_append_cons _ _ _
      | succ m =>
        exact lt_trans (towerMatrix_lt_expand hβ hz m) (expand_lt_towerMatrix hβ hz (m + 1))

/-- **At a successor, the fundamental sequence of `ψ_0(Ω_α)` and the expansions
of its trio matrix are cofinal in each other**, for standard `α = β + 1 < ε₀`.

* `ψ_0(Ω_α)[n] = ψ_0(ψ_β^{n+1}(0))`;
* every `M(α)[k]` is below `M(α)`, and so is the matrix of every member;
* the matrix of every member is at or below some `M(α)[k]`;
* every `M(α)[k]` is at or below the matrix of some member.

Here `M` is `omegaIndexMatrix`, `A[k]` is `expandRL 3 k A`, the matrix of
`ψ_0(ψ_β^{n+1}(0))` is `towerMatrix β n`, and the order is the dictionary order
on the matrices. -/
theorem trioPsi_fs_succ (α : exbE0.State) (β : Term) (hα : α.1 = addT β t1) :
    (∀ n, fs (psiOmega α.1) (idx (psiOmega α.1) n) = psi nil (towerT β (n + 1))) ∧
    (∀ k, expandRL 3 k (omegaIndexMatrix α.1) < omegaIndexMatrix α.1) ∧
    (∀ n, towerMatrix β n < omegaIndexMatrix α.1) ∧
    (∀ n, ∃ k, towerMatrix β n = expandRL 3 k (omegaIndexMatrix α.1) ∨
      towerMatrix β n < expandRL 3 k (omegaIndexMatrix α.1)) ∧
    (∀ k, ∃ n, expandRL 3 k (omegaIndexMatrix α.1) = towerMatrix β n ∨
      expandRL 3 k (omegaIndexMatrix α.1) < towerMatrix β n) := by
  have hne : α.1 ≠ nil := by rw [hα]; exact addT_one_ne_nil β
  have hexp := TrioCofPsi.trioPsi_expand_lt α hne
  refine ⟨fun n => ?_, hexp, fun n => ?_, fun n => ?_, fun k => ?_⟩
  · rw [hα]; exact fs_psiOmega_succ β n
  · obtain ⟨k, hk⟩ := towerMatrix_le_expand β n
    rw [← hα] at hk
    rcases hk with h | h
    · rw [h]; exact hexp k
    · exact lt_trans h (hexp k)
  · rw [hα]; exact towerMatrix_le_expand β n
  · rw [hα]; exact expand_le_towerMatrix β k

/-! ### Order-preserving on the members -/

theorem towerT_lt_succ (β : Term) : ∀ n, towerT β n < towerT β (n + 1) := by
  intro n
  induction n with
  | zero => exact nil_lt_cons _ _ _
  | succ m ih =>
    show psi β (towerT β m) < psi β (towerT β (m + 1))
    exact psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ih⟩)

/-- The members `ψ_0(ψ_β^{n+1}(0))` increase. -/
theorem member_lt (β : Term) {m n : Nat} (h : m < n) :
    psi nil (towerT β (m + 1)) < psi nil (towerT β (n + 1)) := by
  induction h with
  | refl => exact psi_lt_psi_iff.mpr (Or.inr ⟨rfl, towerT_lt_succ β (m + 1)⟩)
  | step _ ih => exact Term.lt_trans ih (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, towerT_lt_succ β _⟩))

theorem towerMatrix_strictMono (β : Term) : StrictMono (towerMatrix β) :=
  strictMono_nat_of_lt_succ (towerMatrix_lt_succ β)

/-- **The map is order-preserving on the members**: the matrices compare as the
terms do. -/
theorem towerMatrix_lt_iff (β : Term) (m n : Nat) :
    towerMatrix β m < towerMatrix β n ↔
      psi nil (towerT β (m + 1)) < psi nil (towerT β (n + 1)) := by
  rw [(towerMatrix_strictMono β).lt_iff_lt]
  refine ⟨member_lt β, fun h => ?_⟩
  by_contra hmn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hmn) with h' | rfl
  · exact Term.lt_asymm h (member_lt β h')
  · exact Term.lt_irrefl _ h

/-- `M(β)`, the matrix of `ψ_0(Ω_β) = ψ_0(Ω_{β+1})[0]`, is at or below every
member's matrix. -/
theorem omegaIndexMatrix_le_towerMatrix {β : Term} (hβ : β ≠ nil) (n : Nat) :
    omegaIndexMatrix β = towerMatrix β n ∨ omegaIndexMatrix β < towerMatrix β n := by
  cases hz : sZ β with
  | true =>
    rw [towerMatrix_pz hβ hz, expand_succ_pz hβ hz]
    cases n with
    | zero => left; simp [ladder]
    | succ m => right; rw [ladder_succ_left]; exact lt_append_cons _ _ _
  | false =>
    cases n with
    | zero => left; rw [towerMatrix_lim_zero hβ hz]
    | succ m =>
      right
      rw [towerMatrix_lim_succ hβ hz, ladder_succ_left, List.append_assoc]
      exact lt_append_cons _ _ _

/-! ### In the trio fragment -/

/-- The members' matrices are in the trio fragment, except where `β` is a limit
and `n ≥ 1`: there they are expansions of `M(β+1)`, or `M(β)`, a prefix of one. -/
theorem trioStdL_towerMatrix (α : exbE0.State) (β : Term) (hα : α.1 = addT β t1) (n : Nat)
    (hlim : β ≠ nil → sZ β = false → n = 0) : TrioCofinal.TrioStdL (towerMatrix β n) := by
  have hS := TrioCofPsi.trioStdL_omegaIndexMatrix α
  rw [hα] at hS
  by_cases hβ : β = nil
  · subst hβ
    rw [towerMatrix_zero]
    exact TrioCofinal.TrioStdL.step _ hS
  · cases hz : sZ β with
    | true =>
      rw [towerMatrix_pz hβ hz]
      exact TrioCofinal.TrioStdL.step _ hS
    | false =>
      rw [hlim hβ hz, towerMatrix_lim_zero hβ hz]
      have h0 := TrioCofinal.TrioStdL.step 0 hS
      rw [expand_succ_lim hβ hz, ladder_succ_left] at h0
      exact TrioCofPsi.trioStdL_prefix _ _ h0

/-! ### Values

`β = 0` and `β = 1` against the
[table for `M ≤ ψ_0(Ω_ω)`](https://github.com/koteitan/trio/blob/main/ebp2bms/sheet/0/README-en.md):
`ψ_0(Ω_1)[n]` is `ω`, `ω^ω`, `ω^{ω^ω}`, and `ψ_0(Ω_2)[n]` is `ε₀ = ψ_0(Ω)`,
`ζ₀ = ψ_0(Ω^2)`, `Γ₀ = ψ_0(Ω^Ω)`, the LVO `ψ_0(Ω^{Ω^Ω})` (with `ψ_1(Ω) = Ω^2`,
`ψ_1(Ω^2) = Ω^Ω`, `ψ_1(Ω^Ω) = Ω^{Ω^Ω}`). -/

#guard towerMatrix nil 0 = [[0,0,0],[1,0,0]]
#guard towerMatrix nil 1 = [[0,0,0],[1,0,0],[2,0,0]]
#guard towerMatrix nil 2 = [[0,0,0],[1,0,0],[2,0,0],[3,0,0]]
#guard towerMatrix t1 0 = [[0,0,0],[1,1,0]]
#guard towerMatrix t1 1 = [[0,0,0],[1,1,0],[2,1,0]]
#guard towerMatrix t1 2 = [[0,0,0],[1,1,0],[2,1,0],[3,1,0]]
#guard towerMatrix t1 3 = [[0,0,0],[1,1,0],[2,1,0],[3,1,0],[4,1,0]]

/-! At a limit `β` the member after `ψ_0(Ω_β)` repeats the root and the
multiply units of `β`'s last add unit after the ladder: `ψ_0(Ω_ω^2)`,
`ψ_0(Ω_ω^{Ω_ω})`, `ψ_0(Ω_{ω·2}^2)`, `ψ_0(Ω_{ω^2}^2)`, `ψ_0(Ω_{ω^ω}^2)`. -/

#guard towerMatrix (opowT t1) 1 = [[0,0,0],[1,1,1],[2,1,0],[1,1,1]]
#guard towerMatrix (opowT t1) 2 = [[0,0,0],[1,1,1],[2,1,0],[3,1,0],[1,1,1]]
#guard towerMatrix (addT (opowT t1) (opowT t1)) 1
  = [[0,0,0],[1,1,1],[2,1,0],[3,2,1],[4,2,0],[3,2,1]]
#guard towerMatrix (opowT (addT t1 t1)) 1 = [[0,0,0],[1,1,1],[2,1,1],[2,1,0],[1,1,1],[2,1,1]]
#guard towerMatrix (opowT (opowT t1)) 1
  = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[2,1,0],[1,1,1],[2,1,1],[3,0,0]]

end TrioSucc
end Googology.Trans.BMS
