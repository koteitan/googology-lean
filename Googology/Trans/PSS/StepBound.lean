import Googology.Trans.PSS.Steps
import «8».«8.6-diagSeq-Trans-fseq»

/-!
# Pair sequences → extended Buchholz's ψ: the number of ψ steps has no bound

`Steps.lean` proves that one expansion step of the pair sequences goes to one
or more steps `X ↦ X[idx X k]` of extended Buchholz's ψ.  This file proves that
the number of those steps is not bounded by a constant.

## The family

For `p ≥ 1` and `n ≥ 0` (pss-proof's `runSeq`):

```
famA p n = (0,0)(1,1)⋯(p,p)(p+1,p)⋯(p+n+1,p)   = gen (p+1), bracket n + 1
famB p n = famA p n with its last column dropped = famA p n, bracket 0
```

pss-proof's `runSeq_Trans` gives their terms: `ψ_0(ψ_p^{n+2}(0))` and
`ψ_0(ψ_p^{n+1}(0))`.  At `n = 0` this is the family
`(0,0)(1,1)⋯(p,p)(p+1,p) → (0,0)(1,1)⋯(p,p)`.

## The invariant

`lastSub X` is the subscript at the end of the rightmost path of `X`: go to the
last summand, then into its argument, until the argument is `0`.  For example
`lastSub (ψ_0(ψ_3(ψ_2(0)))) = 2`.

* `lastSub_fs_idx`: if a countable standard form `X` has `lastSub X = m + 1`,
  then `lastSub (X[idx X k]) = m` for **every** `k`.  (`dom X` is `ω` there, and
  every member of the fundamental sequence replaces the final `Ω_{m+1}` by a
  term that ends in `Ω_m`.)
* `steps_ge_of_lastSub`: so a chain of `s ≤ p` steps from `A` with
  `lastSub A = p` ends at `lastSub = p - s`.  If `lastSub B = p` too and
  `A ≠ B`, every chain from `A` to `B` has at least `p + 1` steps.

Both terms of the family have `lastSub = p`.

## Results

* `Steps r s a b`: `b` is reached from `a` in exactly `s` steps of `r`
  (`steps_iff_iterate`: it is `(Relation.Comp (flip r))^[s] Eq a b`).
* `famA_famB_steps_ge`: every chain from `pairToExbOT (famA p n)` to
  `pairToExbOT (famB p n)` has at least `p + 1` steps.
* `famA_famB_min_steps`: at `n = 0` the least number is exactly `p + 1`, with
  the indices `0, …, 0, 1`.
* `pairToExbOT_steps_unbounded`: no `K` bounds the number of ψ steps of one
  pair step.
-/

namespace Googology.Trans.PSS.StepBound

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.PSS (numeral_succ)

/-- The subscript at the end of the rightmost path. -/
def lastSub : Term → Term
  | nil => nil
  | cons _ _ (cons c d u) => lastSub (cons c d u)
  | cons a nil nil => a
  | cons _ (cons c d u) nil => lastSub (cons c d u)

theorem lastSub_cons_of_ne {a b t : Term} (ht : t ≠ nil) : lastSub (cons a b t) = lastSub t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons c d u => rfl

theorem lastSub_psi_of_ne {a b : Term} (hb : b ≠ nil) : lastSub (psi a b) = lastSub b := by
  cases b with
  | nil => exact absurd rfl hb
  | cons c d u => rfl

@[simp] theorem lastSub_psi_nil (a : Term) : lastSub (psi a nil) = a := rfl

/-- `Ω_m` as a term. -/
abbrev Om (m : Nat) : Term := psi (numeral m) nil

theorem cons_ne_nil' (a b t : Term) : cons a b t ≠ nil := fun h => Term.noConfusion h

theorem numeral_succ_ne_nil (m : Nat) : numeral (m + 1) ≠ nil := fun h => Term.noConfusion h

theorem dom_numeral_succ : ∀ m : Nat, dom (numeral (m + 1)) = t1
  | 0 => rfl
  | m + 1 => by
    rw [numeral_succ, numeral_succ]
    show dom (cons nil nil (numeral m)) = t1
    rw [← numeral_succ]
    exact dom_numeral_succ m

theorem fs_numeral_succ_nil : ∀ m : Nat, fs (numeral (m + 1)) nil = numeral m
  | 0 => by
    show fs (cons nil nil nil) nil = nil
    rw [fs]; simp only [dom_nil, if_true]
  | m + 1 => by
    rw [numeral_succ, numeral_succ, fs, ← numeral_succ, fs_numeral_succ_nil m]
    rfl

theorem Om_ne_t1 (m : Nat) : Om (m + 1) ≠ t1 := by
  intro h
  injection h with h1 _ _
  exact numeral_succ_ne_nil m h1

theorem Om_ne_tw (m : Nat) : Om (m + 1) ≠ tw := by
  intro h
  injection h with h1 _ _
  exact numeral_succ_ne_nil m h1

theorem tw_ne_t1 : tw ≠ t1 := by decide

/-- **The shape of `dom`**: a term whose rightmost path ends in `Ω_{m+1}` has
`dom` equal to `Ω_{m+1}` or `ω`. -/
theorem dom_of_lastSub (m : Nat) : ∀ X : Term, lastSub X = numeral (m + 1) →
    dom X = Om (m + 1) ∨ dom X = tw := by
  intro X
  induction X with
  | nil => intro h; exact absurd h.symm (numeral_succ_ne_nil m)
  | cons a b t _ ihb iht =>
    intro h
    cases t with
    | cons c d u => exact iht h
    | nil =>
      cases b with
      | nil =>
        have ha : a = numeral (m + 1) := h
        subst ha
        left
        rw [dom, dom_nil, if_pos rfl, if_neg (by rw [dom_numeral_succ]; decide),
          if_pos (dom_numeral_succ m)]
      | cons c d u =>
        have hb := ihb h
        rw [dom]
        have hne : dom (cons c d u) ≠ nil := dom_ne_nil (fun h => Term.noConfusion h)
        rw [if_neg hne]
        rcases hb with hb | hb
        · rw [if_neg (by rw [hb]; exact Om_ne_t1 m), if_neg (by rw [hb]; exact Om_ne_tw m)]
          split
          · left; exact hb
          · right; rfl
        · rw [if_neg (by rw [hb]; exact tw_ne_t1), if_pos hb]
          right; rfl

theorem fs_cons_cons (a b c d u Y : Term) :
    fs (cons a b (cons c d u)) Y = cons a b (fs (cons c d u) Y) := by
  rw [fs]

/-- When `dom X = Ω_{m+1}`, `X[Q]` puts `Q` at the end of the rightmost path. -/
theorem fs_of_dom_Om (m : Nat) (Q : Term) (hQ : Q ≠ nil) : ∀ X : Term,
    lastSub X = numeral (m + 1) → dom X = Om (m + 1) →
    fs X Q ≠ nil ∧ lastSub (fs X Q) = lastSub Q := by
  intro X
  induction X with
  | nil => intro h; exact absurd h.symm (numeral_succ_ne_nil m)
  | cons a b t _ ihb iht =>
    intro h hd
    cases t with
    | cons c d u =>
      obtain ⟨h1, h2⟩ := iht h hd
      rw [fs_cons_cons]
      exact ⟨cons_ne_nil' _ _ _, by rw [lastSub_cons_of_ne h1, h2]⟩
    | nil =>
      cases b with
      | nil =>
        have ha : a = numeral (m + 1) := h
        subst ha
        rw [fs, dom_nil, if_pos rfl, if_neg (by rw [dom_numeral_succ]; decide),
          if_pos (dom_numeral_succ m)]
        exact ⟨hQ, rfl⟩
      | cons c d u =>
        have hne : dom (cons c d u) ≠ nil := dom_ne_nil (fun h => Term.noConfusion h)
        rcases dom_of_lastSub m (cons c d u) h with hb | hb
        · have hlt : dom (cons c d u) < cons a (cons c d u) nil := by
            by_contra hn
            rw [dom, if_neg hne, if_neg (by rw [hb]; exact Om_ne_t1 m),
              if_neg (by rw [hb]; exact Om_ne_tw m), if_neg hn] at hd
            exact Om_ne_tw m hd.symm
          rw [fs, if_neg hne, if_neg (by rw [hb]; exact Om_ne_t1 m),
            if_neg (by rw [hb]; exact Om_ne_tw m), if_pos hlt]
          obtain ⟨h1, h2⟩ := ihb h hb
          exact ⟨cons_ne_nil' _ _ _, by rw [lastSub_psi_of_ne h1, h2]⟩
        · rw [dom, if_neg hne, if_neg (by rw [hb]; exact tw_ne_t1), if_pos hb] at hd
          exact absurd hd.symm (Om_ne_tw m)

/-- `ψ_m(Γ)` ends in `Ω_m` when `Γ` does, or when `Γ = 0`. -/
theorem lastSub_psi_numeral {m : Nat} {x Γ : Term} (h : lastSub (psi x Γ) = numeral m) :
    lastSub (psi (numeral m) Γ) = numeral m := by
  by_cases hΓ : Γ = nil
  · subst hΓ; rfl
  · rw [lastSub_psi_of_ne hΓ] at h ⊢; exact h

/-- **When `dom X = ω`, every member `X[k]` ends in `Ω_m`**, if `X` ends in `Ω_{m+1}`. -/
theorem fs_of_dom_tw (m : Nat) : ∀ X : Term,
    lastSub X = numeral (m + 1) → dom X = tw → ∀ k : Nat,
    fs X (numeral k) ≠ nil ∧ lastSub (fs X (numeral k)) = numeral m := by
  intro X
  induction X with
  | nil => intro h; exact absurd h.symm (numeral_succ_ne_nil m)
  | cons a b t _ ihb iht =>
    intro h hd k
    cases t with
    | cons c d u =>
      obtain ⟨h1, h2⟩ := iht h hd k
      rw [fs_cons_cons]
      exact ⟨cons_ne_nil' _ _ _, by rw [lastSub_cons_of_ne h1, h2]⟩
    | nil =>
      cases b with
      | nil =>
        have ha : a = numeral (m + 1) := h
        subst ha
        rw [dom, dom_nil, if_pos rfl, if_neg (by rw [dom_numeral_succ]; decide),
          if_pos (dom_numeral_succ m)] at hd
        exact absurd hd (Om_ne_tw m)
      | cons c d u =>
        have hne : dom (cons c d u) ≠ nil := dom_ne_nil (fun h => Term.noConfusion h)
        rcases dom_of_lastSub m (cons c d u) h with hb | hb
        · -- `dom b = Ω_{m+1}` and `X` diagonalizes
          have hnlt : ¬ dom (cons c d u) < cons a (cons c d u) nil := by
            intro hlt
            rw [dom, if_neg hne, if_neg (by rw [hb]; exact Om_ne_t1 m),
              if_neg (by rw [hb]; exact Om_ne_tw m), if_pos hlt, hb] at hd
            exact Om_ne_tw m hd
          have hsub : fs (subOf (dom (cons c d u))) nil = numeral m := by
            rw [hb]; exact fs_numeral_succ_nil m
          have base0 : cons a (fs (cons c d u) (psi (numeral m) nil)) nil ≠ nil ∧
              lastSub (cons a (fs (cons c d u) (psi (numeral m) nil)) nil) = numeral m := by
            obtain ⟨h1, h2⟩ := fs_of_dom_Om m _ (cons_ne_nil' _ _ _) (cons c d u) h hb
            exact ⟨cons_ne_nil' _ _ _, by rw [lastSub_psi_of_ne h1, h2]; rfl⟩
          induction k with
          | zero =>
            rw [fs, if_neg hne, if_neg (by rw [hb]; exact Om_ne_t1 m),
              if_neg (by rw [hb]; exact Om_ne_tw m), if_neg hnlt,
              dif_neg (by rintro ⟨h0, _⟩; exact h0 rfl), hsub]
            exact base0
          | succ k ihk =>
            have hc : numeral (k + 1) ≠ nil ∧ isNum (numeral (k + 1)) = true := by
              refine ⟨numeral_succ_ne_nil k, ?_⟩
              clear ihk
              induction k with
              | zero => rfl
              | succ k ih => rw [numeral_succ]; exact ih
            have hp : numPred (numeral (k + 1)) = numeral k := by rw [numeral_succ]; rfl
            rw [fs, if_neg hne, if_neg (by rw [hb]; exact Om_ne_t1 m),
              if_neg (by rw [hb]; exact Om_ne_tw m), if_neg hnlt, dif_pos hc]
            simp only [hp, hsub]
            obtain ⟨_, hk2⟩ := ihk
            split
            · rename_i x Γ heq
              rw [heq] at hk2
              split
              · obtain ⟨h1, h2⟩ := fs_of_dom_Om m _ (cons_ne_nil' _ _ _) (cons c d u) h hb
                exact ⟨cons_ne_nil' _ _ _,
                  by rw [lastSub_psi_of_ne h1, h2, lastSub_psi_numeral hk2]⟩
              · exact base0
            · exact base0
        · rw [fs, if_neg hne, if_neg (by rw [hb]; exact tw_ne_t1), if_pos hb]
          obtain ⟨h1, h2⟩ := ihb h hb k
          exact ⟨cons_ne_nil' _ _ _, by rw [lastSub_psi_of_ne h1, h2]⟩

/-! ## One step on a countable standard form -/

/-- **One step lowers the end subscript by exactly one**: if a countable
standard form `X` ends in `Ω_{m+1}`, then `X[idx X k]` ends in `Ω_m`, for every
`k`. -/
theorem lastSub_fs_idx {X : Term} (hOT : OT X) (hlt : X < tW) {m : Nat}
    (h : lastSub X = numeral (m + 1)) (k : Nat) :
    lastSub (fs X (idx X k)) = numeral m := by
  have hne : X ≠ nil := by rintro rfl; exact numeral_succ_ne_nil m h.symm
  have hd : dom X = tw := by
    rcases dom_eq_one_or_tw X hOT hlt hne with h1 | h1
    · rcases dom_of_lastSub m X h with h2 | h2
      · exact absurd (h2.symm.trans h1) (Om_ne_t1 m)
      · exact h2
    · exact h1
  have hi : idx X k = numeral k := by rw [idx, if_neg (by rw [hd]; exact tw_ne_t1)]
  rw [hi]
  exact (fs_of_dom_tw m X h hd k).2

/-! ## Counting steps -/

/-- `b` is reached from `a` by exactly `s` steps of `r`, where `r c a` means
that `c` is one step from `a` (the convention of `Rewrite.Rel`). -/
def Steps {α : Type} (r : α → α → Prop) : Nat → α → α → Prop
  | 0, a, b => a = b
  | s + 1, a, b => ∃ c, r c a ∧ Steps r s c b

/-- `Steps` is the `s`-th power of the one-step relation, written with
`Nat.iterate` and `Relation.Comp`. -/
theorem steps_iff_iterate {α : Type} (r : α → α → Prop) :
    ∀ (s : Nat) (a b : α), Steps r s a b ↔ (Relation.Comp (flip r))^[s] Eq a b
  | 0, a, b => Iff.rfl
  | s + 1, a, b => by
    rw [Function.iterate_succ_apply']
    show (∃ c, r c a ∧ Steps r s c b) ↔ ∃ c, flip r a c ∧ (Relation.Comp (flip r))^[s] Eq c b
    exact exists_congr fun c => and_congr Iff.rfl (steps_iff_iterate r s c b)

theorem steps_pos_transGen {α : Type} {r : α → α → Prop} :
    ∀ {s : Nat} {a b : α}, Steps r (s + 1) a b → Relation.TransGen r b a
  | 0, _, _, ⟨c, hc, rfl⟩ => Relation.TransGen.single hc
  | _ + 1, _, _, ⟨_, hc, hs⟩ => Relation.TransGen.tail (steps_pos_transGen hs) hc

theorem transGen_steps {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r b a) : ∃ s, Steps r (s + 1) a b := by
  induction h with
  | single h => exact ⟨0, _, h, rfl⟩
  | tail _ h ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨s + 1, _, h, hs⟩

/-- Along `s ≤ q` steps of `exbOT`, the end subscript goes from `q` to `q - s`. -/
theorem lastSub_of_steps : ∀ (s q : Nat) (A B : exbOT.State),
    lastSub A.1 = numeral q → s ≤ q → Steps exbOT.Rel s A B → lastSub B.1 = numeral (q - s)
  | 0, q, A, B, hA, _, hs => by rw [← hs, hA]; rfl
  | s + 1, q, A, B, hA, hsq, ⟨C, ⟨_, k, hC⟩, hs⟩ => by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hC' : lastSub C.1 = numeral q' := by
      rw [hC]; exact lastSub_fs_idx A.2.1 A.2.2 hA k
    rw [lastSub_of_steps s q' C B hC' (by omega) hs]
    congr 1; omega

/-- **The lower bound**: if `A ≠ B` both end in `Ω_p`, every chain of steps
from `A` to `B` has at least `p + 1` steps. -/
theorem steps_ge_of_lastSub {A B : exbOT.State} {p s : Nat}
    (hA : lastSub A.1 = numeral p) (hB : lastSub B.1 = numeral p) (hAB : A ≠ B)
    (hs : Steps exbOT.Rel s A B) : p + 1 ≤ s := by
  by_contra hlt
  have h := lastSub_of_steps s p A B hA (by omega) hs
  rw [hB] at h
  have hs0 : s = 0 := by have := Googology.Trans.PSS.numeral_injective h; omega
  subst hs0
  exact hAB hs

end Googology.Trans.PSS.StepBound

namespace Googology.Trans.PSS.StepBound

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Googology.Trans.BMS (pairL PairState pairStd expand2L badRootL)
open Googology.Trans.PSS (pairOrdTerm pairTerm pairToExbOT numeral_injective)

/-! ## The pair sequences `(0,0)(1,1)⋯(p,p)(p+1,p)⋯` -/

/-- **Bracket `0` drops the last column**, for every list. -/
theorem expand2L_zero (l : List (Nat × Nat)) : expand2L 0 l = l.dropLast := by
  unfold expand2L
  split
  · rfl
  · rename_i p m1 hbr
    have hp : p < l.length - 1 := by
      unfold badRootL at hbr
      split_ifs at hbr with he
      split at hbr
      · rename_i q hq
        simp only [Option.some.injEq, Prod.mk.injEq] at hbr
        rw [← hbr.1]
        exact ((Googology.Trans.BMS.parAt1_eq_some _ _ _).mp hq).1
      · split at hbr
        · rename_i q hq
          simp only [Option.some.injEq, Prod.mk.injEq] at hbr
          rw [← hbr.1]
          exact ((Googology.Trans.BMS.parAt_eq_some _ _ _).mp hq).1
        · exact absurd hbr (by simp)
    set L := l.length - 1 - p with hL
    have hmap : (List.range ((0 + 1) * L)).map (fun t =>
        if m1 && ((p == p + t % L) || Googology.Trans.BMS.ancAtB (l.map Prod.fst) p (p + t % L)) then
          ((l[p + t % L]!).1 + (t / L) * ((l[l.length - 1]!).1 - (l[p]!).1), (l[p + t % L]!).2)
        else l[p + t % L]!) = (List.range L).map (fun t => l[p + t]!) := by
      rw [Nat.zero_add, Nat.one_mul]
      apply List.map_congr_left
      intro t ht
      have htL : t < L := List.mem_range.mp ht
      rw [Nat.mod_eq_of_lt htL, Nat.div_eq_of_lt htL]
      split <;> simp
    rw [hmap]
    have hrange : List.range (p + L) = List.range p ++ (List.range L).map (p + ·) :=
      List.range_add
    have hpl : p + L = l.length - 1 := by omega
    rw [show (List.range L).map (fun t => l[p + t]!) =
        ((List.range L).map (p + ·)).map (fun i => l[i]!) by rw [List.map_map]; rfl,
      ← List.map_append, ← hrange, hpl]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_dropLast]
      rw [getElem!_pos l i (by simp at h2; omega)]

/-- `ψ_p(ψ_p(⋯ψ_p(0)⋯))` with `n` copies of `ψ_p`. -/
def tower (p : Nat) : Nat → Term
  | 0 => nil
  | n + 1 => psi (numeral p) (tower p n)

theorem toTerm_const2ndTower (p : Nat) :
    ∀ n, Googology.Trans.PSS.toTerm (_root_.PSS.const2ndTower p n) = tower p n
  | 0 => Googology.Trans.PSS.toTerm_BZero
  | n + 1 => by
    show Googology.Trans.PSS.toTerm (_root_.PSS.Dprin (p : ℕ∞) (_root_.PSS.const2ndTower p n)) = _
    rw [Googology.Trans.PSS.toTerm_Dprin, Googology.Trans.PSS.sub_coe, toTerm_const2ndTower p n]
    rfl

theorem tower_succ_ne_nil (p n : Nat) : tower p (n + 1) ≠ nil := cons_ne_nil' _ _ _

theorem lastSub_tower (p : Nat) : ∀ n, lastSub (tower p (n + 1)) = numeral p
  | 0 => rfl
  | n + 1 => by
    show lastSub (psi (numeral p) (tower p (n + 1))) = _
    rw [lastSub_psi_of_ne (tower_succ_ne_nil p n)]
    exact lastSub_tower p n

theorem tower_succ_ne (p : Nat) : ∀ n, tower p (n + 1) ≠ tower p n
  | 0 => cons_ne_nil' _ _ _
  | n + 1 => fun h => by
    injection h with _ h2 _
    exact tower_succ_ne p n h2

/-- **The term of `(0,0)(1,1)⋯(p,p)(p+1,p)⋯(p+n-1,p)`** is `ψ_0(ψ_p^n(0))`,
from pss-proof's `runSeq_Trans`. -/
theorem pairOrdTerm_runSeq {p n : Nat} (hp : 0 < p) (hn : 0 < n) :
    pairOrdTerm (_root_.PSS.runSeq 0 p n) = psi nil (tower p n) := by
  have hne : _root_.PSS.runSeq 0 p n ≠ [] := by
    simp only [_root_.PSS.runSeq, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  unfold pairOrdTerm
  rw [if_neg hne]
  unfold pairTerm
  rw [_root_.PSS.runSeq_Trans 0 p n hp hn]
  unfold _root_.PSS.runTower
  rw [Googology.Trans.PSS.toTerm_Dprin, Googology.Trans.PSS.sub_coe, toTerm_const2ndTower]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  show addNF t1 (psi nil (tower p (n' + 1))) = psi nil (tower p (n' + 1))
  rw [show tower p (n' + 1) = psi (numeral p) (tower p n') from rfl, addNF, if_pos]
  exact psi_lt_psi_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)

theorem lastSub_pairOrdTerm_runSeq {p n : Nat} (hp : 0 < p) :
    lastSub (pairOrdTerm (_root_.PSS.runSeq 0 p (n + 1))) = numeral p := by
  rw [pairOrdTerm_runSeq hp (Nat.succ_pos n), lastSub_psi_of_ne (tower_succ_ne_nil p n)]
  exact lastSub_tower p n

/-- The state `(0,0)(1,1)⋯(p,p)(p+1,p)⋯(p+n+1,p)`: the generator
`(0,0)⋯(p+1,p+1)` expanded at bracket `n + 1`. -/
def famA (p n : Nat) : PairState := pairL.step (pairStd.gen (p + 1)) (n + 1)

/-- `famA p n` expanded at bracket `0`: its last column dropped. -/
def famB (p n : Nat) : PairState := pairL.step (famA p n) 0

theorem famA_val {p : Nat} (hp : 0 < p) (n : Nat) :
    (famA p n).1 = _root_.PSS.runSeq 0 p (n + 2) := by
  have hlen : 2 ≤ (pairStd.gen (p + 1)).1.length := by
    rw [Googology.Trans.PSS.pairStd_gen]
    simp [_root_.PSS.diagSeq]
  unfold famA
  rw [Googology.Trans.PSS.pairL_step_eq_oper _ _ hlen, Googology.Trans.PSS.pairStd_gen,
    _root_.PSS.oper_diagSeq_eq_runSeq 0 (p + 1) (n + 2) (by omega), Nat.add_sub_cancel]

theorem famB_val {p : Nat} (hp : 0 < p) (n : Nat) :
    (famB p n).1 = _root_.PSS.runSeq 0 p (n + 1) := by
  unfold famB
  rw [Googology.Trans.BMS.pairL_step_val, expand2L_zero, famA_val hp]
  simp only [_root_.PSS.runSeq, show p - 0 + (n + 2) = (p - 0 + (n + 1)) + 1 by omega,
    List.range_succ, List.map_append, List.map_cons, List.map_nil, List.dropLast_concat]

/-- `famB p n` is one expansion step from `famA p n`. -/
theorem famB_rel {p : Nat} (hp : 0 < p) (n : Nat) : pairL.Rel (famB p n) (famA p n) := by
  refine ⟨?_, 0, rfl⟩
  show ¬ (famA p n).1 = []
  rw [famA_val hp]
  simp only [_root_.PSS.runSeq, List.map_eq_nil_iff, List.range_eq_nil]
  omega

/-- **The step `famA p n → famB p n` takes at least `p + 1` steps of extended
Buchholz's ψ**: `ψ_0(ψ_p^{n+2}(0))` to `ψ_0(ψ_p^{n+1}(0))`, whatever the
indices. -/
theorem famA_famB_steps_ge {p : Nat} (hp : 0 < p) (n s : Nat)
    (hs : Steps exbOT.Rel s (pairToExbOT (famA p n)) (pairToExbOT (famB p n))) :
    p + 1 ≤ s := by
  have hA : lastSub (pairToExbOT (famA p n)).1 = numeral p := by
    show lastSub (pairOrdTerm (famA p n).1) = _
    rw [famA_val hp]; exact lastSub_pairOrdTerm_runSeq hp
  have hB : lastSub (pairToExbOT (famB p n)).1 = numeral p := by
    show lastSub (pairOrdTerm (famB p n).1) = _
    rw [famB_val hp]; exact lastSub_pairOrdTerm_runSeq hp
  have hAB : pairToExbOT (famA p n) ≠ pairToExbOT (famB p n) := by
    intro h
    have h1 : pairOrdTerm (famA p n).1 = pairOrdTerm (famB p n).1 := congrArg Subtype.val h
    rw [famA_val hp, famB_val hp, pairOrdTerm_runSeq hp (by omega),
      pairOrdTerm_runSeq hp (by omega)] at h1
    injection h1 with _ h2 _
    exact tower_succ_ne p (n + 1) h2
  exact steps_ge_of_lastSub hA hB hAB hs

/-- **The number of ψ steps for one pair step has no bound.** -/
theorem pairToExbOT_steps_unbounded :
    ¬ ∃ K : Nat, ∀ a b : PairState, pairL.Rel b a →
      ∃ s ≤ K, Steps exbOT.Rel s (pairToExbOT a) (pairToExbOT b) := by
  rintro ⟨K, hK⟩
  obtain ⟨s, hsK, hs⟩ := hK _ _ (famB_rel (Nat.succ_pos K) 0)
  have := famA_famB_steps_ge (Nat.succ_pos K) 0 s hs
  omega

/-! ## The upper bound: `p + 1` steps suffice -/

/-- `ψ_0(ψ_p(Ω_j))`, with `Ω_0 = ψ_0(0) = 1`. -/
abbrev Yj (p j : Nat) : Term := psi nil (psi (numeral p) (Om j))

theorem dom_Om_succ (i : Nat) : dom (Om (i + 1)) = Om (i + 1) := by
  rw [dom, dom_nil, if_pos rfl, if_neg (by rw [dom_numeral_succ]; decide),
    if_pos (dom_numeral_succ i)]

theorem fs_Om_succ (i : Nat) (Q : Term) : fs (Om (i + 1)) Q = Q := by
  rw [fs, dom_nil, if_pos rfl, if_neg (by rw [dom_numeral_succ]; decide),
    if_pos (dom_numeral_succ i)]

theorem not_Om_lt_psi_nil (i : Nat) (W : Term) : ¬ Om (i + 1) < psi nil W := by
  intro h
  rcases psi_lt_psi_iff.mp h with h1 | ⟨h1, _⟩
  · exact not_lt_nil _ h1
  · exact numeral_succ_ne_nil i h1

/-- `ψ_0(ψ_p(Ω_{i+1}))[0] = ψ_0(ψ_p(Ω_i))` when `i + 1 ≤ p`. -/
theorem fs_Yj_succ {p i : Nat} (hi : i + 1 ≤ p) :
    fs (Yj p (i + 1)) (idx (Yj p (i + 1)) 0) = Yj p i := by
  have hlt : Om (i + 1) < psi (numeral p) (Om (i + 1)) := by
    apply psi_lt_psi_iff.mpr
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact Or.inl ((Googology.Trans.PSS.numeral_lt_numeral_iff _ _).mpr h)
    · exact Or.inr ⟨by rw [h], nil_lt_cons _ _ _⟩
  have hne : Om (i + 1) ≠ nil := cons_ne_nil' _ _ _
  have hdW : dom (psi (numeral p) (Om (i + 1))) = Om (i + 1) := by
    rw [dom, dom_Om_succ, if_neg hne, if_neg (Om_ne_t1 i), if_neg (Om_ne_tw i), if_pos hlt]
  have hfW : ∀ Q, fs (psi (numeral p) (Om (i + 1))) Q = psi (numeral p) Q := by
    intro Q
    rw [fs, dom_Om_succ, if_neg hne, if_neg (Om_ne_t1 i), if_neg (Om_ne_tw i), if_pos hlt,
      fs_Om_succ]
  have hdY : dom (Yj p (i + 1)) = tw := by
    rw [dom, hdW, if_neg hne, if_neg (Om_ne_t1 i), if_neg (Om_ne_tw i),
      if_neg (not_Om_lt_psi_nil i _)]
  have hidx : idx (Yj p (i + 1)) 0 = nil := by
    rw [idx, if_neg (by rw [hdY]; exact tw_ne_t1)]; rfl
  rw [hidx, fs, hdW, if_neg hne, if_neg (Om_ne_t1 i), if_neg (Om_ne_tw i),
    if_neg (not_Om_lt_psi_nil i _), dif_neg (by rintro ⟨h0, _⟩; exact h0 rfl)]
  show psi nil (fs (psi (numeral p) (Om (i + 1))) (psi (fs (numeral (i + 1)) nil) nil)) = _
  rw [fs_numeral_succ_nil, hfW]

/-- `ψ_0(ψ_p(1))[1] = ψ_0(ψ_p(0))`. -/
theorem fs_Yj_zero (p : Nat) : fs (Yj p 0) (idx (Yj p 0) 1) = psi nil (psi (numeral p) nil) := by
  have hd1 : dom t1 = t1 := by decide
  have hdW : dom (psi (numeral p) t1) = tw := by
    rw [dom, hd1, if_neg (by decide), if_pos rfl]
  have hdY : dom (Yj p 0) = tw := by
    show dom (psi nil (psi (numeral p) t1)) = tw
    rw [dom, hdW, if_neg (by decide), if_neg (by decide), if_pos rfl]
  have hidx : idx (Yj p 0) 1 = numeral 1 := by
    rw [idx, if_neg (by rw [hdY]; exact tw_ne_t1)]
  rw [hidx]
  show fs (psi nil (psi (numeral p) t1)) (numeral 1) = _
  rw [fs, hdW, if_neg (by decide), if_neg (by decide), if_pos rfl, fs, hd1,
    if_neg (by decide), if_pos rfl, if_pos (by rfl)]
  rw [show fs t1 nil = nil by rw [fs]; simp only [dom_nil, if_true]]
  rfl

/-- From `ψ_0(ψ_p(Ω_j))` (`j ≤ p`) to `ψ_0(ψ_p(0))` in `j + 1` steps. -/
theorem steps_Yj {p : Nat} (B : exbOT.State) (hB : B.1 = psi nil (psi (numeral p) nil)) :
    ∀ j, j ≤ p → ∀ A : exbOT.State, A.1 = Yj p j → Steps exbOT.Rel (j + 1) A B
  | 0, _, A, hA => by
    refine ⟨exbOT.step A 1, ⟨by show ¬ A.1 = nil; rw [hA]; exact cons_ne_nil' _ _ _, 1, rfl⟩, ?_⟩
    apply Subtype.ext
    show fs A.1 (idx A.1 1) = B.1
    rw [hA, fs_Yj_zero, hB]
  | i + 1, hi, A, hA => by
    refine ⟨exbOT.step A 0, ⟨by show ¬ A.1 = nil; rw [hA]; exact cons_ne_nil' _ _ _, 0, rfl⟩, ?_⟩
    apply steps_Yj B hB i (by omega)
    show fs A.1 (idx A.1 0) = Yj p i
    rw [hA, fs_Yj_succ hi]

/-- **`p + 1` steps suffice**: `ψ_0(ψ_p(ψ_p(0))) →[0] ψ_0(ψ_p(Ω_{p-1})) →[0] ⋯
→[0] ψ_0(ψ_p(1)) →[1] ψ_0(ψ_p(0))`. -/
theorem famA_famB_steps {p : Nat} (hp : 0 < p) :
    Steps exbOT.Rel (p + 1) (pairToExbOT (famA p 0)) (pairToExbOT (famB p 0)) := by
  apply steps_Yj _ _ p le_rfl
  · show pairOrdTerm (famA p 0).1 = _
    rw [famA_val hp, pairOrdTerm_runSeq hp (by omega)]
    rfl
  · show pairOrdTerm (famB p 0).1 = _
    rw [famB_val hp, pairOrdTerm_runSeq hp (by omega)]
    rfl

/-- **The least number of ψ steps for `famA p 0 → famB p 0` is exactly `p + 1`.** -/
theorem famA_famB_min_steps {p : Nat} (hp : 0 < p) :
    Steps exbOT.Rel (p + 1) (pairToExbOT (famA p 0)) (pairToExbOT (famB p 0)) ∧
    ∀ s, Steps exbOT.Rel s (pairToExbOT (famA p 0)) (pairToExbOT (famB p 0)) → p + 1 ≤ s :=
  ⟨famA_famB_steps hp, fun s hs => famA_famB_steps_ge hp 0 s hs⟩

end Googology.Trans.PSS.StepBound
