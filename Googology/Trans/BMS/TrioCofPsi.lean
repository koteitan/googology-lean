import Googology.Trans.BMS.TrioStd
import Googology.Trans.BMS.TrioMono
import Googology.Trans.BMS.TrioCofinal
import Googology.Notation.ExBuchholz

/-!
# Trio cofinality, stated with the ψ terms

`TrioCofinal.lean` proves that expansion is cofinal on the trio fragment
(`trio_cofinal`, `trioStd_cofinal`), with trio's own terms `Three` as the only
term side (`trio_cofinal_term`).  This file states it on the side of this
library's extended Buchholz terms and their fundamental sequences, through the
trio map `α ↦ M(α) = omegaIndexMatrix α` of `ψ_0(Ω_α)`, for standard `α < ε₀`
(the states of `exbE0`).  `psiOmega α` is the term `ψ_0(Ω_α) = ψ_0(ψ_α(0))`.

What is proved:

* `trioStdL_omegaIndexMatrix`: `M(α)` lies in the trio fragment `TrioStdL`
  (reachable from `(0,0,0)(1,1,1)(2,2,1)⋯(v,v,1)`), not only among the
  standard three-row matrices (`TrioStd.omegaIndexMatrix_std`).  The proof is
  the one of `TrioStd`, run with `TrioStdL` in place of `Reach3`.
* `trioPsi_cofinal`: `ψ_0(Ω_β) < ψ_0(Ω_α) → ∃ k, M(β) ≤ M(α)[k]`, and
  `trioPsi_cofinal_val` the same with `val ψ_0(Ω_β) < val ψ_0(Ω_α)`;
  `OT_psiOmega` says `ψ_0(Ω_α)` is a standard form, and
  `val_psiOmega_lt_iff` that its value order is the order of the matrices.
* `trioPsi_expand_lt`: `M(α)[k] < M(α)` for `α ≠ 0`.
* At a limit (`dom α = ω`) the fundamental sequence of `ψ_0(Ω_α)` stays in
  the image: `ψ_0(Ω_α)[n] = ψ_0(Ω_{α[n]})` (`fs_psiOmega`, `idx_psiOmega`).
  `trioPsi_expand_prefix`: each `M(α)[k]` is a **prefix** of some
  `M(α[n+1])`.  `trioPsi_fs` puts it together: the sequences
  `M(α)[k]` and `M(ψ_0(Ω_α)[n+1])` are below `M(α)` and cofinal in each other.

The prefix statement is the new part.  It is read off the local expansion
lemmas of `TrioStd` (`expandRL_anchor_root`, `expandRL_digit_unit`,
`expandRL_copy_block`, `expandRL_embed`), which compute `M(α)[N]` exactly:

* the last summand is `ω`: `M(α)[N] ⊑ M(α)[N+1] = M(exT N α)`;
* the last summand is `ω^{X'+1}`, `X' ≠ 0`: `M(α)[N] = M(exT N α)`;
* the exponent is a limit: `M(α)[N]` is the anchor, the root and the multiply
  units of `exT N X`, and `M(exT (N+1) α)` those of `peelOne (exT (N+1) X)`;
  when `exT (N+1) X` is finite, peeling its leading `1` gives `exT N X`
  (`exT_finite`), otherwise `M(α)[N] ⊑ M(α)[N+1]` (`expandRL_prefix_succ`).

`exT N α` is `α[N+1]`, the step of `exbE0` (`exT_eq_step`).

At a successor `α = β + 1` the members of the fundamental sequence of
`ψ_0(Ω_α)` are `ψ_0(ψ_α(⋯))`, outside the terms `ψ_0(Ω_γ)` the map reads, so
only `trioPsi_cofinal` is stated there.
-/

namespace Googology.Trans.BMS
namespace TrioCofPsi

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open TrioStd
open TrioCofinal (TrioStdL trioGen)

/-! ### Expansion grows with the bracket -/

/-- `A[N]` is a prefix of `A[N+1]`, at any number of rows. -/
theorem expandRL_prefix_succ (r N : Nat) (l : List (List Nat)) :
    expandRL r N l <+: expandRL r (N + 1) l := by
  unfold expandRL
  split
  · exact List.prefix_refl _
  · rename_i p _
    rw [show (N + 1 + 1) * (l.length - 1 - p)
        = (N + 1) * (l.length - 1 - p) + (l.length - 1 - p) by ring,
      List.range_add, List.map_append, ← List.append_assoc]
    exact List.prefix_append _ _

theorem expandRL_prefix_le (r : Nat) (l : List (List Nat)) {N M : Nat} (h : N ≤ M) :
    expandRL r N l <+: expandRL r M l := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (expandRL_prefix_succ r _ l)

/-- A prefix is at or below in the dictionary order. -/
theorem eq_or_lt_of_prefix {a b : List (List Nat)} (h : a <+: b) : a = b ∨ a < b := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => exact Or.inl (List.append_nil a).symm
  | cons c t =>
    right
    have := TrioMono.append_lt_append_left a (List.nil_lt_cons c t)
    rwa [List.append_nil] at this

/-! ### The trio fragment is closed under prefixes -/

theorem trioStdL_wf {l : List (List Nat)} (h : TrioStdL l) : ∀ c ∈ l, c.length = 3 :=
  reach3_wf (TrioCofinal.trioStdL_std h)

theorem trioStdL_prefix : ∀ (m l : List (List Nat)), TrioStdL (l ++ m) → TrioStdL l := by
  intro m
  induction m with
  | nil => intro l h; rwa [List.append_nil] at h
  | cons c m ih =>
    intro l h
    have h1 : TrioStdL (l ++ [c]) := ih (l ++ [c]) (by rwa [List.append_assoc])
    have h2 := TrioStdL.step 0 h1
    rwa [expandRL_zero 3 _ (trioStdL_wf h1), List.dropLast_concat] at h2

theorem wf_of_WF3 {m : List (List Nat)} (h : WF3 m) : ∀ c ∈ m, c.length = 3 :=
  fun c hc => (h c hc).1

theorem wf_append {A B : List (List Nat)} (hA : ∀ c ∈ A, c.length = 3)
    (hB : ∀ c ∈ B, c.length = 3) : ∀ c ∈ A ++ B, c.length = 3 := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hA c h
  · exact hB c h

/-! ### Inside the multiply units the expansion is exact -/

/-- **One expansion inside the multiply units is `exT` on the terms**, with
nothing cut off. -/
theorem mul_exact (N x0 y : Nat) : ∀ X : Term, AllNil X → X ≠ nil → lastOne X = false →
    ∀ P : List (List Nat), (∀ c ∈ P, c.length = 3) →
      expandRL 3 N (P ++ mulUnits x0 y X) = P ++ mulUnits x0 y (exT N X) := by
  intro X
  induction X with
  | nil => intro _ h; exact absurd rfl h
  | cons a γ t _ _ iht =>
    intro hA _ hl P hP
    by_cases ht : t = nil
    · subst ht
      simp only [lastOne, beq_self_eq_true, if_true, beq_eq_false_iff_ne] at hl
      have hγb : (γ == nil) = false := by simpa using hl
      have hm : mulUnits x0 y (cons a γ nil) = [x0 + 1, y, 1] :: prSS (x0 + 2) γ := by
        rw [mulUnits, mulUnits, List.append_nil]
      have hw : ∀ c ∈ P ++ ([x0 + 1, y, 1] :: prSS (x0 + 2) γ), c.length = 3 :=
        wf_append hP (wf_of_WF3 (WF3_cons ⟨rfl, by simp⟩ (WF3_prSS (x0 + 2) γ)))
      rw [exT, hm]
      simp only [beq_self_eq_true, if_true, hγb, Bool.false_eq_true, if_false]
      split
      · rename_i h1
        rw [mulUnits_repT]
        rw [prSS_snoc (x0 + 2) h1, ← List.cons_append] at hw ⊢
        exact expandRL_copy_block N P [x0 + 1, y, 1] (prSS (x0 + 2) (dropLastT γ)) (x0 + 2)
          hw (by simp) (prSS_ge _ _)
      · rename_i h1
        have h1' : lastOne γ = false := by simpa using h1
        have hwA : ∀ c ∈ P ++ [[x0 + 1, y, 1]], c.length = 3 :=
          wf_append hP (by intro c hc; simp at hc; subst hc; rfl)
        have hE := expandRL_embed N (x0 + 2) (P ++ [[x0 + 1, y, 1]]) (unread 0 γ)
          (col_unread γ hA.2.1 0) (unread_last_pos hl h1') hwA
        rw [mulUnits, show mulUnits x0 y nil = [] from rfl, List.append_nil, prSS, prSS]
        rw [expandL_unread N γ 0] at hE
        simpa using hE
    · have htb : (t == nil) = false := by simpa using ht
      simp only [lastOne, htb, Bool.false_eq_true, if_false] at hl
      rw [exT]
      simp only [htb, Bool.false_eq_true, if_false]
      rw [mulUnits, mulUnits, ← List.append_assoc, ← List.append_assoc]
      exact iht hA.2.2 ht hl _
        (wf_append hP (wf_of_WF3 (WF3_cons ⟨rfl, by simp⟩ (WF3_prSS (x0 + 2) γ))))


/-! ### The trio matrices lie in the trio fragment -/

/-- The add unit of a last summand `ω^X` with `X ≠ 0`: the anchor, the root and
the multiply units. -/
theorem addUnits_last (rp1 lastX : Nat) (pz : Bool) (j : Nat) (a X : Term) (hX : X ≠ nil) :
    addUnits rp1 lastX pz (j + 1) (cons a X nil)
      = [rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: mulUnits (rp1 + 1) (j + 1) (peelOne X) := by
  have hXb : (X == nil) = false := by simpa using hX
  rw [addUnits]
  simp only [hXb, Bool.false_eq_true, if_false]
  rw [show addUnits (rp1 + 2) (rp1 + 1) false (j + 1 + 1) nil = [] from rfl,
    List.append_nil, Nat.add_sub_cancel, bodyU]

/-- **`step_add` for the trio fragment**: the proof of `TrioStd.step_add` with
`Reach3` replaced by `TrioStdL`. -/
theorem add_std (N : Nat) : ∀ α : Term, AllNil α → ZT α →
    ∀ (rp1 lastX : Nat) (pz : Bool) (j : Nat), (pz = true → AllOne α) →
    ∀ P : List (List Nat), TrioStdL (P ++ addUnits rp1 lastX pz (j + 1) α) →
      TrioStdL (P ++ addUnits rp1 lastX pz (j + 1) (exT N α)) := by
  intro α
  induction α with
  | nil => intro _ _ _ _ _ _ _ _ h; exact h
  | cons a X Y _ _ ihY =>
    intro hA hZ rp1 lastX pz j hpz P hR
    by_cases hY : Y = nil
    · subst hY
      rw [exT]
      simp only [beq_self_eq_true, if_true]
      by_cases hX : X = nil
      · subst hX
        simp only [beq_self_eq_true, if_true]
        obtain ⟨U, r', l', hU⟩ := addUnits_cons_split rp1 lastX pz (j + 1) a nil
        rw [hU, show addUnits r' l' (nil == nil) (j + 1 + 1) nil = [] from rfl,
          List.append_nil] at hR
        rw [show addUnits rp1 lastX pz (j + 1) nil = [] from rfl, List.append_nil]
        exact trioStdL_prefix U P hR
      · have hXb : (X == nil) = false := by simpa using hX
        simp only [hXb, Bool.false_eq_true, if_false]
        have hpzf : pz = false := by
          cases pz with
          | false => rfl
          | true => exact absurd (hpz rfl).1 hX
        subst hpzf
        rw [addUnits_last _ _ _ _ _ _ hX] at hR
        split
        · rename_i h1
          by_cases h0 : dropLastT X = nil
          · rw [peelOne_of_dropLast_nil h1 h0, show mulUnits (rp1 + 1) (j + 1) nil = []
              from rfl] at hR
            rw [h0]
            have := TrioStdL.step (N + 1) hR
            rw [expandRL_anchor_root] at this
            rw [addUnits_ones]
            exact this
          · rw [mulUnits_peel_snoc _ _ h1 h0] at hR
            have hE := expandRL_digit_unit N rp1 j P (mulUnits (rp1 + 1) (j + 1)
              (peelOne (dropLastT X))) (mulUnits_tail rp1 j _)
            have := TrioStdL.step N hR
            rw [show [rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: (mulUnits (rp1 + 1) (j + 1)
                (peelOne (dropLastT X)) ++ [[rp1 + 1 + 1, j + 1, 1]])
                = ([rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: mulUnits (rp1 + 1) (j + 1)
                  (peelOne (dropLastT X))) ++ [[rp1 + 2, j + 1, 1]] by simp, hE] at this
            rw [addUnits_repT _ h0]
            convert this using 3
            refine List.map_congr_left (fun c _ => ?_)
            rw [bodyU, List.map_cons, mulUnits_asc c _ _ (by omega)]
            simp [ascCol]
        · rename_i h1
          have h1' : lastOne X = false := by simpa using h1
          rw [addUnits_last _ _ _ _ _ _ (exT_ne_nil N hX h1')]
          rw [peelOne_of_not_lastOne hX h1'] at hR
          have hR' : TrioStdL ((P ++ [[rp1, j, 0], [rp1 + 1, j + 1, 1]])
              ++ mulUnits (rp1 + 1) (j + 1) X) := by simpa using hR
          have hwP : ∀ c ∈ P ++ [[rp1, j, 0], [rp1 + 1, j + 1, 1]], c.length = 3 :=
            fun c hc => trioStdL_wf hR' c (List.mem_append_left _ hc)
          have h2 := TrioStdL.step N hR'
          rw [mul_exact N (rp1 + 1) (j + 1) X hA.2.1 hX h1' _ hwP] at h2
          obtain ⟨S, hS⟩ := mulUnits_prefix (rp1 + 1) (j + 1) (exT N X)
          rw [hS, ← List.append_assoc] at h2
          have := trioStdL_prefix _ _ h2
          simpa using this
    · have hYb : (Y == nil) = false := by simpa using hY
      rw [exT]
      simp only [hYb, Bool.false_eq_true, if_false]
      obtain ⟨U, r', l', hU⟩ := addUnits_cons_split rp1 lastX pz (j + 1) a X
      rw [hU] at hR ⊢
      rw [← List.append_assoc] at hR ⊢
      exact ihY hA.2.2 hZ.2 r' l' (X == nil) (j + 1)
        (fun h => hZ.1 (by simpa using h)) _ hR

/-- `ψ_0(Ω_{ε₀})`, `(0,0,0)(1,1,1)(2,1,1)(3,0,0)(4,1,0)`, is in the trio
fragment: the steps of `TrioStd.reach3_topE0` from the generator
`(0,0,0)(1,1,1)(2,2,1)`. -/
theorem trioStdL_topE0 : TrioStdL topE0 := by
  have s1 : TrioStdL [[0,0,0],[1,1,1],[2,2,1]] := by
    have := TrioStdL.gen 2
    rwa [show trioGen 2 = [[0,0,0],[1,1,1],[2,2,1]] by decide] at this
  have s2 : TrioStdL [[0,0,0],[1,1,1],[2,2,0]] := by
    have := TrioStdL.step 1 s1
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,2,1]] = [[0,0,0],[1,1,1],[2,2,0],[3,3,1]]
      by decide] at this
    exact trioStdL_prefix [[3,3,1]] _ this
  have s3 : TrioStdL [[0,0,0],[1,1,1],[2,1,1],[3,1,1]] := by
    have := TrioStdL.step 2 s2
    rwa [show expandRL 3 2 [[0,0,0],[1,1,1],[2,2,0]] = [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      by decide] at this
  have s4 : TrioStdL [[0,0,0],[1,1,1],[2,1,1],[3,1,0]] := by
    have := TrioStdL.step 1 s3
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,1]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,1,0],[4,2,1],[5,2,1]] by decide] at this
    exact trioStdL_prefix [[4,2,1],[5,2,1]] _ this
  have s5 : TrioStdL [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]] := by
    have := TrioStdL.step 1 s4
    rw [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,1,0]]
      = [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1],[5,1,1]] by decide] at this
    exact trioStdL_prefix [[5,1,1]] _ this
  have := TrioStdL.step 1 s5
  rwa [show expandRL 3 1 [[0,0,0],[1,1,1],[2,1,1],[3,0,0],[4,1,1]] = topE0 by decide] at this

/-- The one-row matrices whose trio matrix is in the trio fragment. -/
def RTrioL (l : List Nat) : Prop := ZT (read 0 l) ∧ TrioStdL (omegaIndexMatrix (read 0 l))

theorem rTrioL_gen (n : Nat) : RTrioL (List.range (n + 1)) := by
  rw [RTrioL, read_range_eq_twr]
  refine ⟨⟨fun _ => trivial, trivial⟩, ?_⟩
  match n with
  | 0 =>
    have := TrioStdL.step 1 (TrioStdL.gen 1)
    rwa [show expandRL 3 1 (trioGen 1) = omegaIndexMatrix (twr (0 + 1)) by decide] at this
  | 1 =>
    have := TrioStdL.gen 1
    rwa [show trioGen 1 = omegaIndexMatrix (twr (1 + 1)) by decide] at this
  | k + 2 =>
    have := TrioStdL.step k trioStdL_topE0
    rwa [expandRL_topE0, ← omegaIndexMatrix_twr] at this

theorem rTrioL_step {m : List Nat} (hc : Col 0 m) (h : RTrioL m) (N : Nat) :
    RTrioL (expandL N 0 m) := by
  rw [RTrioL, read_expandL_exT N hc]
  refine ⟨zt_exT N _ h.1, ?_⟩
  have := add_std N (read 0 m) (allNil_read 0 m) h.1 0 0 false 0
    (fun h => absurd h (by simp)) [] (by simpa [omegaIndexMatrix] using h.2)
  simpa [omegaIndexMatrix] using this

/-- **The trio matrix of every standard `α < ε₀` is in the trio fragment**, and
`α` has the Cantor shape `ZT`. -/
theorem trioStdL_omegaIndexMatrix' (α : exbE0.State) :
    ZT α.1 ∧ TrioStdL (omegaIndexMatrix α.1) := by
  have hA := allNil_of_state α
  have h := reach_gen RTrioL (fun hc hR N => rTrioL_step hc hR N) rTrioL_gen
    (col_unread α.1 hA 0) (by rw [read_unread α.1 hA 0]; exact α.2.1)
  rw [RTrioL, read_unread α.1 hA 0] at h
  exact h

theorem trioStdL_omegaIndexMatrix (α : exbE0.State) : TrioStdL (omegaIndexMatrix α.1) :=
  (trioStdL_omegaIndexMatrix' α).2


/-! ### At a limit, each expansion is a prefix of the matrix of a smaller index -/

theorem prefix_append_left (P : List (List Nat)) {a b : List (List Nat)} (h : a <+: b) :
    P ++ a <+: P ++ b := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t, by rw [List.append_assoc]⟩

theorem prefix_of_eq {a b : List (List Nat)} (h : a = b) : a <+: b := h ▸ List.prefix_refl a

theorem map_range_prefix_succ {β : Type} (f : Nat → β) (n : Nat) :
    (List.range n).map f <+: (List.range (n + 1)).map f := by
  rw [List.range_succ, List.map_append]
  exact List.prefix_append _ _

/-- `exT` at a last summand `ω^X` with `X ≠ 0`. -/
theorem exT_last (N : Nat) (a X : Term) (hX : X ≠ nil) :
    exT N (cons a X nil)
      = if lastOne X then repT (dropLastT X) (N + 1) else cons a (exT N X) nil := by
  have hXb : (X == nil) = false := by simpa using hX
  rw [exT]
  simp only [beq_self_eq_true, if_true, hXb, Bool.false_eq_true, if_false]

theorem isFiniteT_repT {Z : Term} {n : Nat} (h : isFiniteT (repT Z (n + 1)) = true) :
    Z = nil := by
  rw [repT, isFiniteT, Bool.and_eq_true] at h
  simpa using h.1

theorem dropLastT_repT (Z : Term) : ∀ n : Nat, dropLastT (repT Z (n + 1)) = repT Z n := by
  intro n
  induction n with
  | zero => simp [repT, dropLastT]
  | succ m ih =>
    rw [repT, dropLastT, ih]
    simp [repT]

/-- When `exT (N+1) X` is finite it is `exT N X` and one more `1`. -/
theorem exT_finite (N : Nat) : ∀ X : Term, X ≠ nil → lastOne X = false →
    isFiniteT (exT (N + 1) X) = true → exT N X = dropLastT (exT (N + 1) X) := by
  intro X
  induction X with
  | nil => intro h; exact absurd rfl h
  | cons a γ t _ _ iht =>
    intro _ hl hf
    by_cases ht : t = nil
    · subst ht
      have hγ : γ ≠ nil := by
        intro h; subst h; simp [lastOne] at hl
      rw [exT_last N a γ hγ]
      rw [exT_last (N + 1) a γ hγ] at hf ⊢
      by_cases h1 : lastOne γ = true
      · rw [if_pos h1] at hf ⊢
        rw [if_pos h1, isFiniteT_repT hf, dropLastT_repT]
      · rw [if_neg h1] at hf
        have h1' : lastOne γ = false := by simpa using h1
        rw [isFiniteT, Bool.and_eq_true] at hf
        exact absurd (by simpa using hf.1) (exT_ne_nil (N + 1) hγ h1')
    · have htb : (t == nil) = false := by simpa using ht
      simp only [lastOne, htb, Bool.false_eq_true, if_false] at hl
      rw [exT, exT]
      rw [exT] at hf
      simp only [htb, Bool.false_eq_true, if_false] at hf ⊢
      rw [isFiniteT, Bool.and_eq_true] at hf
      have hne : (exT (N + 1) t == nil) = false := by
        simpa using exT_ne_nil (N + 1) ht hl
      rw [dropLastT, hne, if_neg (by simp), iht ht hl hf.2]

/-- **At a limit, an expansion of the trio matrix is a prefix of the trio
matrix of `exT N'`**, for some `N'`. -/
theorem add_lim (N : Nat) : ∀ α : Term, AllNil α → ZT α → α ≠ nil → lastOne α = false →
    ∀ (rp1 lastX : Nat) (pz : Bool) (j : Nat), (pz = true → AllOne α) →
    ∀ P : List (List Nat), (∀ c ∈ P, c.length = 3) →
      ∃ N', expandRL 3 N (P ++ addUnits rp1 lastX pz (j + 1) α)
        <+: P ++ addUnits rp1 lastX pz (j + 1) (exT N' α) := by
  intro α
  induction α with
  | nil => intro _ _ h; exact absurd rfl h
  | cons a X Y _ _ ihY =>
    intro hA hZ _ hl rp1 lastX pz j hpz P hP
    by_cases hY : Y = nil
    · subst hY
      have hX : X ≠ nil := by
        intro h; subst h; simp [lastOne] at hl
      have hpzf : pz = false := by
        cases pz with
        | false => rfl
        | true => exact absurd (hpz rfl).1 hX
      subst hpzf
      rw [addUnits_last _ _ _ _ _ _ hX]
      by_cases h1 : lastOne X = true
      · by_cases h0 : dropLastT X = nil
        · -- the last summand is `ω`: `M(α)[N]` is a prefix of `M(α)[N+1] = M(exT N α)`
          refine ⟨N, ?_⟩
          rw [exT_last N a X hX, if_pos h1, h0, addUnits_ones, peelOne_of_dropLast_nil h1 h0,
            show mulUnits (rp1 + 1) (j + 1) nil = [] from rfl, expandRL_anchor_root]
          exact prefix_append_left P (map_range_prefix_succ _ _)
        · -- the last summand is `ω^{X'+1}`, `X' ≠ 0`: `M(α)[N] = M(exT N α)`
          refine ⟨N, ?_⟩
          have hE := expandRL_digit_unit N rp1 j P (mulUnits (rp1 + 1) (j + 1)
            (peelOne (dropLastT X))) (mulUnits_tail rp1 j _)
          rw [mulUnits_peel_snoc _ _ h1 h0,
            show [rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: (mulUnits (rp1 + 1) (j + 1)
              (peelOne (dropLastT X)) ++ [[rp1 + 1 + 1, j + 1, 1]])
              = ([rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: mulUnits (rp1 + 1) (j + 1)
                (peelOne (dropLastT X))) ++ [[rp1 + 2, j + 1, 1]] by simp, hE,
            exT_last N a X hX, if_pos h1, addUnits_repT _ h0]
          refine prefix_append_left P (prefix_of_eq ?_)
          congr 1
          refine List.map_congr_left (fun c _ => ?_)
          rw [bodyU, List.map_cons, mulUnits_asc c _ _ (by omega)]
          simp [ascCol]
      · -- the exponent is a limit: the expansion is inside the multiply units
        have h1' : lastOne X = false := by simpa using h1
        refine ⟨N + 1, ?_⟩
        have hP' : ∀ c ∈ P ++ [[rp1, j, 0], [rp1 + 1, j + 1, 1]], c.length = 3 :=
          wf_append hP (by intro c hc; simp at hc; rcases hc with rfl | rfl <;> rfl)
        have e1 := mul_exact N (rp1 + 1) (j + 1) X hA.2.1 hX h1' _ hP'
        have e2 := mul_exact (N + 1) (rp1 + 1) (j + 1) X hA.2.1 hX h1' _ hP'
        rw [exT_last (N + 1) a X hX, if_neg h1, addUnits_last _ _ _ _ _ _
          (exT_ne_nil (N + 1) hX h1'), peelOne_of_not_lastOne hX h1']
        have hs : ∀ (m : List (List Nat)), P ++ [rp1, j, 0] :: [rp1 + 1, j + 1, 1] :: m
            = (P ++ [[rp1, j, 0], [rp1 + 1, j + 1, 1]]) ++ m := by intro m; simp
        rw [hs (mulUnits (rp1 + 1) (j + 1) X),
          hs (mulUnits (rp1 + 1) (j + 1) (peelOne (exT (N + 1) X))), e1]
        by_cases hf : isFiniteT (exT (N + 1) X) = true
        · rw [peelOne, if_pos hf, ← exT_finite N X hX h1' hf]
        · rw [peelOne, if_neg hf, ← e1, ← e2]
          exact expandRL_prefix_succ 3 N _
    · have hYb : (Y == nil) = false := by simpa using hY
      have hlY : lastOne Y = false := by
        simpa only [lastOne, hYb, Bool.false_eq_true, if_false] using hl
      obtain ⟨U, r', l', hU⟩ := addUnits_cons_split rp1 lastX pz (j + 1) a X
      have hwU : ∀ c ∈ U, c.length = 3 := by
        have := WF3_addUnits (cons a X nil) rp1 lastX pz (j + 1)
        rw [hU, show addUnits r' l' (X == nil) (j + 1 + 1) nil = [] from rfl,
          List.append_nil] at this
        exact wf_of_WF3 this
      obtain ⟨N', hN'⟩ := ihY hA.2.2 hZ.2 hY hlY r' l' (X == nil) (j + 1)
        (fun h => hZ.1 (by simpa using h)) (P ++ U) (wf_append hP hwU)
      refine ⟨N', ?_⟩
      rw [exT]
      simp only [hYb, Bool.false_eq_true, if_false]
      rw [hU, hU, ← List.append_assoc, ← List.append_assoc]
      exact hN'

/-! ### The ψ side -/

/-- `ψ_0(Ω_α)` as a term, with `Ω_α = ψ_α(0)`. -/
abbrev psiOmega (α : Term) : Term := psi nil (psi α nil)

/-- **`ψ_0(Ω_β) < ψ_0(Ω_α)` exactly when `β < α`.** -/
theorem psiOmega_lt_iff {α β : Term} : psiOmega β < psiOmega α ↔ β < α := by
  rw [psi_lt_psi_iff, psi_lt_psi_iff]
  simp

theorem dom_psi_sub {α : Term} (h : dom α = tw) : dom (psi α nil) = tw := by
  rw [dom]
  simp [h]

/-- At a limit `α` of cofinality `ω`, `ψ_0(Ω_α)` is one too. -/
theorem dom_psiOmega {α : Term} (h : dom α = tw) : dom (psiOmega α) = tw := by
  rw [dom]
  simp [dom_psi_sub h]

/-- **At a limit `α` of cofinality `ω`, `ψ_0(Ω_α)[Y] = ψ_0(Ω_{α[Y]})`**: the
fundamental sequence of `ψ_0(Ω_α)` stays in the terms the trio map reads. -/
theorem fs_psiOmega {α : Term} (h : dom α = tw) (Y : Term) :
    fs (psiOmega α) Y = psiOmega (fs α Y) := by
  have h2 := dom_psi_sub h
  have hin : fs (psi α nil) Y = psi (fs α Y) nil := by
    rw [fs]
    simp [h]
  rw [fs]
  simp [h2, hin]

theorem idx_psiOmega {α : Term} (h : dom α = tw) (n : Nat) :
    idx (psiOmega α) n = idx α n := by
  rw [idx_of_dom_tw (dom_psiOmega h), idx_of_dom_tw h]

/-- A limit `α` with every subscript `0` is not `0` and does not end in `1`. -/
theorem lim_of_dom : ∀ α : Term, AllNil α → dom α = tw → α ≠ nil ∧ lastOne α = false := by
  intro α
  induction α with
  | nil => intro _ h; simp at h
  | cons a b t _ _ iht =>
    intro hA h
    refine ⟨by simp, ?_⟩
    cases t with
    | nil =>
      obtain ⟨ha, _, _⟩ := hA
      subst ha
      simp only [lastOne, beq_self_eq_true, if_true]
      by_contra hb
      have hb' : b = nil := by simpa using hb
      subst hb'
      rw [dom_t1] at h
      simp at h
    | cons c d u =>
      rw [dom_cons_cons] at h
      have := (iht hA.2.2 h).2
      simpa [lastOne] using this

/-- `exT`, one step of the one-row expansion on the terms, is the step of
`exbE0`: `exT N α = α[N+1]`. -/
theorem exT_eq_step (α : exbE0.State) (N : Nat) : exT N α.1 = (exbE0.step α N).1 := by
  have hA := allNil_of_state α
  have hc := col_unread α.1 hA 0
  have h1 := read_expandL_exT N hc
  have h2 := read_expandL N (unread 0 α.1) 0 hc
  rw [read_unread α.1 hA 0] at h1 h2
  rw [← h1, h2]
  rfl

theorem omegaIndexMatrix_ne_nil {α : Term} (h : α ≠ nil) : omegaIndexMatrix α ≠ [] := by
  cases α with
  | nil => exact absurd rfl h
  | cons a X Y =>
    rw [omegaIndexMatrix, addUnits]
    split
    · simp
    · simp

/-! ### The theorems -/

/-- **Cofinality, stated with the ψ terms**: for standard `α, β < ε₀` with
`ψ_0(Ω_β) < ψ_0(Ω_α)`, the trio matrix of `ψ_0(Ω_β)` is at or below some
expansion of the trio matrix of `ψ_0(Ω_α)`. -/
theorem trioPsi_cofinal (α β : exbE0.State) (h : psiOmega β.1 < psiOmega α.1) :
    ∃ k, omegaIndexMatrix β.1 = expandRL 3 k (omegaIndexMatrix α.1) ∨
      omegaIndexMatrix β.1 < expandRL 3 k (omegaIndexMatrix α.1) :=
  TrioCofinal.trio_cofinal (trioStdL_omegaIndexMatrix α) (trioStdL_omegaIndexMatrix β)
    (omegaIndexMatrix_strictMono β α (psiOmega_lt_iff.mp h))

/-- **Every expansion of the trio matrix of `ψ_0(Ω_α)` is below it**, for
standard `0 < α < ε₀`. -/
theorem trioPsi_expand_lt (α : exbE0.State) (hne : α.1 ≠ nil) (k : Nat) :
    expandRL 3 k (omegaIndexMatrix α.1) < omegaIndexMatrix α.1 :=
  TrioCofinal.trio_expand_lt (trioStdL_omegaIndexMatrix α) (omegaIndexMatrix_ne_nil hne) k

/-- **At a limit, each expansion is a prefix of the trio matrix of a member of
the fundamental sequence.**  For standard `α < ε₀` with `dom α = ω`,
`M(α)[k]` is a prefix of `M(α[n+1])` for some `n`. -/
theorem trioPsi_expand_prefix (α : exbE0.State) (hd : dom α.1 = tw) (k : Nat) :
    ∃ n, expandRL 3 k (omegaIndexMatrix α.1) <+: omegaIndexMatrix (exbE0.step α n).1 := by
  have hA := allNil_of_state α
  obtain ⟨hne, hl⟩ := lim_of_dom α.1 hA hd
  have hZ := (trioStdL_omegaIndexMatrix' α).1
  obtain ⟨n, hn⟩ := add_lim k α.1 hA hZ hne hl 0 0 false 0 (fun h => absurd h (by simp)) []
    (by simp)
  refine ⟨n, ?_⟩
  rw [← exT_eq_step]
  simpa [omegaIndexMatrix] using hn

/-- **The fundamental sequence of `ψ_0(Ω_α)` and the expansions of its trio
matrix are cofinal in each other**, for standard `α < ε₀` with `dom α = ω`.

* `ψ_0(Ω_α)[n+1] = ψ_0(Ω_{α[n+1]})`, and `α[n+1]` is again standard below `ε₀`;
* every `M(α)[k]` is below `M(α)`, and so is every `M(α[n+1])`;
* every `M(α[n+1])` is at or below some `M(α)[k]`;
* every `M(α)[k]` is at or below some `M(α[n+1])`.

Here `M` is `omegaIndexMatrix`, `A[k]` is `expandRL 3 k A`, `α[n+1]` is the
step of `exbE0`, and the order is the dictionary order on the matrices. -/
theorem trioPsi_fs (α : exbE0.State) (hd : dom α.1 = tw) :
    (∀ n, fs (psiOmega α.1) (idx (psiOmega α.1) (n + 1)) = psiOmega (exbE0.step α n).1) ∧
    (∀ k, expandRL 3 k (omegaIndexMatrix α.1) < omegaIndexMatrix α.1) ∧
    (∀ n, omegaIndexMatrix (exbE0.step α n).1 < omegaIndexMatrix α.1) ∧
    (∀ n, ∃ k, omegaIndexMatrix (exbE0.step α n).1 = expandRL 3 k (omegaIndexMatrix α.1) ∨
      omegaIndexMatrix (exbE0.step α n).1 < expandRL 3 k (omegaIndexMatrix α.1)) ∧
    (∀ k, ∃ n, expandRL 3 k (omegaIndexMatrix α.1) = omegaIndexMatrix (exbE0.step α n).1 ∨
      expandRL 3 k (omegaIndexMatrix α.1) < omegaIndexMatrix (exbE0.step α n).1) := by
  have hA := allNil_of_state α
  obtain ⟨hne, _⟩ := lim_of_dom α.1 hA hd
  have hlt : ∀ n, (exbE0.step α n).1 < α.1 := fun n =>
    fs_lt (idx_lt_dom α.2.1 (lt_trans α.2.2 te0_lt_tW) hne (n + 1))
  refine ⟨fun n => ?_, trioPsi_expand_lt α hne, fun n => ?_, fun n => ?_, fun k => ?_⟩
  · rw [idx_psiOmega hd, fs_psiOmega hd]
    rfl
  · exact omegaIndexMatrix_strictMono _ α (hlt n)
  · exact trioPsi_cofinal α (exbE0.step α n) (psiOmega_lt_iff.mpr (hlt n))
  · obtain ⟨n, hn⟩ := trioPsi_expand_prefix α hd k
    exact ⟨n, eq_or_lt_of_prefix hn⟩

/-! ### The same in the ordinals -/

theorem allNil_of_mem_G : ∀ t : Term, AllNil t → ∀ z ∈ G nil t, AllNil z := by
  intro t
  induction t with
  | nil => intro _ z hz; simp [G] at hz
  | cons c d u _ ihd ihu =>
    intro hA z hz
    obtain ⟨hc, hd, hu⟩ := hA
    subst hc
    rw [G, List.mem_append] at hz
    rcases hz with hz | hz
    · rw [if_pos (le_refl _), List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · exact hd
      · simp [G] at hz
      · exact ihd hd z hz
    · exact ihu hu z hz

theorem allNil_lt_psi {α : Term} (hne : α ≠ nil) : ∀ x : Term, AllNil x → x < psi α nil := by
  intro x hx
  cases x with
  | nil => exact nil_lt_cons _ _ _
  | cons a b t =>
    obtain ⟨ha, -, -⟩ := hx
    subst ha
    rw [cons_lt_psi_iff, psi_lt_psi_iff]
    left
    cases α with
    | nil => exact absurd rfl hne
    | cons p q r => exact nil_lt_cons _ _ _

/-- **`ψ_0(Ω_α)` is a standard form** when `α` is one with every subscript `0`. -/
theorem OT_psiOmega {α : Term} (hOT : OT α) (hA : AllNil α) : OT (psiOmega α) := by
  have hG : ∀ z ∈ G nil α, z < psi α nil := by
    intro z hz
    have hne : α ≠ nil := by rintro rfl; simp [G] at hz
    exact allNil_lt_psi hne z (allNil_of_mem_G α hA z hz)
  have hn : nil < psi α nil := nil_lt_cons _ _ _
  unfold OT at hOT ⊢
  simp only [isOT, descHead, head?, G, hOT, Bool.true_and, Bool.and_true]
  have hle : nil ≤ α := by
    cases α with
    | nil => exact le_refl _
    | cons p q r => exact le_of_lt (nil_lt_cons _ _ _)
  rw [if_pos hle]
  simp only [List.all_nil, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
  intro x hx
  simp only [List.mem_cons, List.append_nil] at hx
  rcases hx with rfl | hx
  · exact hn
  · exact hG x hx

theorem OT_psiOmega_state (α : exbE0.State) : OT (psiOmega α.1) :=
  OT_psiOmega α.2.1 (allNil_of_state α)

/-- **Cofinality in the ordinals**: for standard `α, β < ε₀` with
`val ψ_0(Ω_β) < val ψ_0(Ω_α)`, the trio matrix of `β` is at or below some
expansion of the trio matrix of `α`. -/
theorem trioPsi_cofinal_val (α β : exbE0.State)
    (h : val (psiOmega β.1) < val (psiOmega α.1)) :
    ∃ k, omegaIndexMatrix β.1 = expandRL 3 k (omegaIndexMatrix α.1) ∨
      omegaIndexMatrix β.1 < expandRL 3 k (omegaIndexMatrix α.1) :=
  trioPsi_cofinal α β
    ((lt_iff_val_lt (OT_psiOmega_state β) (OT_psiOmega_state α)).mpr h)

/-- The ordinal order of `ψ_0(Ω_α)` is the order of the trio matrices. -/
theorem val_psiOmega_lt_iff (α β : exbE0.State) :
    val (psiOmega β.1) < val (psiOmega α.1) ↔ omegaIndexMatrix β.1 < omegaIndexMatrix α.1 := by
  rw [← lt_iff_val_lt (OT_psiOmega_state β) (OT_psiOmega_state α), psiOmega_lt_iff,
    omegaIndexMatrix_lt_iff]

end TrioCofPsi
end Googology.Trans.BMS
