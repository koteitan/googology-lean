/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossKinds

set_option backward.do.legacy false

/-!
# `CutPred` along a list: the predecessor of every cut emit

`CutPred es` (`CrossKinds.lean`) asks that every cut emit of `es` (origin `clean r true`) is
immediately preceded by an emit with origin `clean r b` and the same emitted leg column.
The emitted list of a column is the concatenation of the lists of the items of the rule,
so this file states the condition relative to the last emit before a list (`CutSeq p L`,
`p` the emit before `L`, if any) and proves the bookkeeping:

* `cutSeq_append`: `CutSeq p (A ++ B) ↔ CutSeq p A ∧ CutSeq (lastOr p A) B`;
* `cutPred_of_cutSeq`: `CutSeq none es → CutPred es`;
* `cutSeq_flatten_range'`: an invariant carried over consecutive indices through a
  flattened list of outputs.
-/

namespace OmegaY.Official.Recon

open Canonical Official Classification

abbrev EO := Emit × Origin

/-- The emit `e` may follow `p`: if `e` is a cut copy of `r`, then `p` is a copy of `r` with
the same emitted leg column. -/
def Follows (p : Option EO) (e : EO) : Prop :=
  ∀ r, e.2 = .clean r true →
    ∃ e', p = some e' ∧ ∃ b, e'.2 = .clean r b ∧ e'.1.leftColumn = e.1.leftColumn

/-- Every cut emit of `L` follows its predecessor; the predecessor of the first element is
`p`. -/
def CutSeq : Option EO → List EO → Prop
  | _, [] => True
  | p, e :: L => Follows p e ∧ CutSeq (some e) L

/-- The last emit after `L`, starting from `p`. -/
def lastOr (p : Option EO) (L : List EO) : Option EO :=
  match L.getLast? with
  | some e => some e
  | none => p

@[simp] theorem lastOr_nil (p : Option EO) : lastOr p [] = p := rfl

theorem lastOr_cons (p : Option EO) (e : EO) (L : List EO) :
    lastOr p (e :: L) = lastOr (some e) L := by
  unfold lastOr
  cases L with
  | nil => simp
  | cons a L =>
    rw [List.getLast?_cons_cons]
    simp [List.getLast?_cons]

theorem lastOr_append (p : Option EO) (A B : List EO) :
    lastOr p (A ++ B) = lastOr (lastOr p A) B := by
  induction A generalizing p with
  | nil => rfl
  | cons a A ih =>
    rw [List.cons_append, lastOr_cons, ih, lastOr_cons]

theorem cutSeq_append (p : Option EO) (A B : List EO) :
    CutSeq p (A ++ B) ↔ CutSeq p A ∧ CutSeq (lastOr p A) B := by
  induction A generalizing p with
  | nil => simp [CutSeq]
  | cons a A ih =>
    rw [List.cons_append]
    simp only [CutSeq]
    rw [ih, lastOr_cons]
    tauto

theorem cutSeq_of_noCut : ∀ (p : Option EO) (L : List EO),
    (∀ e ∈ L, ∀ r, e.2 ≠ .clean r true) → CutSeq p L
  | _, [], _ => trivial
  | _, e :: L, h => by
    refine ⟨fun r hr => absurd hr (h e List.mem_cons_self r), ?_⟩
    exact cutSeq_of_noCut _ L (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem cutSeq_getElem : ∀ (p : Option EO) (L : List EO), CutSeq p L →
    ∀ j (hj : j < L.length) r, L[j].2 = .clean r true →
      (j = 0 → ∃ e', p = some e' ∧ ∃ b, e'.2 = .clean r b ∧
        e'.1.leftColumn = L[j].1.leftColumn) ∧
      ∀ (h0 : 0 < j), ∃ b, L[j - 1].2 = .clean r b ∧ L[j - 1].1.leftColumn = L[j].1.leftColumn
  | _, [], _, j, hj, _, _ => absurd hj (by simp)
  | p, e :: L, ⟨hf, hL⟩, j, hj, r, hr => by
    cases j with
    | zero =>
      refine ⟨fun _ => hf r hr, fun h0 => absurd h0 (by omega)⟩
    | succ j =>
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have hj' : j < L.length := by simp at hj; omega
      obtain ⟨h1, h2⟩ := cutSeq_getElem (some e) L hL j hj' r (by simpa using hr)
      cases j with
      | zero =>
        obtain ⟨e', he', b, hb, hlc⟩ := h1 rfl
        obtain rfl := Option.some.inj he'
        exact ⟨b, by simpa using hb, by simpa using hlc⟩
      | succ j =>
        obtain ⟨b, hb, hlc⟩ := h2 (by omega)
        exact ⟨b, by simpa using hb, by simpa using hlc⟩

/-- **`CutPred` from `CutSeq`.** -/
theorem cutPred_of_cutSeq {es : List EO} (h : CutSeq none es) : CutPred es := by
  intro j hj r hr
  obtain ⟨h1, h2⟩ := cutSeq_getElem none es h j hj r hr
  by_cases h0 : j = 0
  · obtain ⟨e', he', _⟩ := h1 h0
    cases he'
  · exact ⟨by omega, h2 (by omega)⟩

/-! ## Flattened lists of outputs -/

theorem forall₂_of_mapM {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok ys' =>
        rw [hxs] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons hx (forall₂_of_mapM hxs)

/-- An invariant `I j` on the emit before the output of the `j`-th item, carried over the
consecutive indices `a, a + 1, …, a + m - 1`. -/
theorem cutSeq_flatten_range' {α : Type} (run : α → Except Error (List EO)) (f : Nat → α)
    (I : Nat → Option EO → Prop) :
    ∀ (m a : Nat) (outs : List (List EO)),
      List.Forall₂ (fun j out => run (f j) = .ok out) (List.range' a m) outs →
      (∀ j, a ≤ j → j < a + m → ∀ out, run (f j) = .ok out → ∀ p, I j p →
        CutSeq p out ∧ I (j + 1) (lastOr p out)) →
      ∀ p, I a p → CutSeq p outs.flatten ∧ I (a + m) (lastOr p outs.flatten)
  | 0, a, outs, h, _, p, hp => by
    simp only [List.range'_zero] at h
    cases h
    exact ⟨trivial, by simpa using hp⟩
  | m + 1, a, outs, h, hstep, p, hp => by
    rw [List.range'_succ] at h
    cases h with
    | cons hout hrest =>
      rename_i out outs'
      obtain ⟨h1, h2⟩ := hstep a le_rfl (by omega) out hout p hp
      obtain ⟨h3, h4⟩ := cutSeq_flatten_range' run f I m (a + 1) outs' hrest
        (fun j hj1 hj2 => hstep j (by omega) (by omega)) _ h2
      rw [List.flatten_cons, cutSeq_append, lastOr_append]
      exact ⟨⟨h1, h3⟩, by rw [show a + (m + 1) = a + 1 + m by omega]; exact h4⟩

theorem filter_range_eq_range' (a : Nat) : ∀ n : Nat,
    (List.range n).filter (fun j => decide (a ≤ j)) = List.range' a (n - a)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_eq_range' a n]
    by_cases h : a ≤ n
    · rw [show n + 1 - a = (n - a) + 1 by omega, List.range'_concat]
      simp [h, show a + (n - a) = n by omega]
    · simp [h, show n + 1 - a = 0 by omega, show n - a = 0 by omega]

end OmegaY.Official.Recon
