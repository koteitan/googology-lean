/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Trace.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyColumn_emitsT`, in the proof passed to `mapM_map_fst` for the upper emits, the goal is beta-reduced before `cases leftColumn p.2`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Shape

set_option backward.do.legacy false

/-!
# The official rule with the origin of every emitted node

`Official.copyColumn` builds a column from a list of emitted nodes (`Official.Emit`)
and assembles it. This file runs the same rule and records, for every emitted node,
the node of the source mountain `M(s)` it comes from (`Origin`):

* `plain src`: a level-1 item without a copied root row (notes/03 §2.3, `C = ⊥`);
  `src` is the node `(x, σ)` of the source row `σ`.
* `clean src cut`: a level-1 item that copies the root row `C` (`C ≠ ⊥`); `src` is
  the node `(x, C)` whose leg is copied; `cut` is the flag `b` of the item.
* `upper src`: the upper part (rows `≥ τ`, notes/03 §2.5); `src` is the node of
  column `x'` at the same row.

`copyColumn_emitsT` shows that the traced rule emits exactly the nodes of the real
rule: if `copyColumn ctx τ = .ok col` then the traced emits `es` exist and
`assemble ctx (es.map Prod.fst) = .ok col`.

The origin is the witness that classifies the leg atom of the emitted node in the
numerical tests (`Witness.lean`).
-/

namespace OmegaY.Official.Classification

open Canonical Official

/-- The node of `M(s)` an emitted node comes from. -/
inductive Origin where
  | plain (src : Ref)
  | clean (src : Ref) (cut : Bool)
  | upper (src : Ref)
  deriving DecidableEq, Repr

def Origin.src : Origin → Ref
  | .plain r => r
  | .clean r _ => r
  | .upper r => r

/-- `levelOne` with origins. -/
def levelOneT (ctx : Context) (it : Item) : Result (List (Emit × Origin)) := do
  match nodeAt ctx.source ctx.x it.source with
  | none => return []
  | some (srcRef, src) =>
    match it.clean with
    | some C =>
      match nodeAt ctx.source ctx.x C with
      | none => throw .missingCleanSource
      | some (csRef, cs) => return [(⟨it.target, some (← leftColumn cs)⟩, .clean csRef it.cutBottom)]
    | none =>
      if it.source = 0 then return [(⟨it.target, none⟩, .plain srcRef)]
      else return [(⟨it.target, some (← leftColumn src)⟩, .plain srcRef)]

/-- `runItem` with origins. -/
def runItemT (ctx : Context) : Nat → Item → Result (List (Emit × Origin))
  | 0, _ => pure []
  | 1, it => levelOneT ctx it
  | d + 2, it => do
      let children ← childItems ctx (d + 2) it
      let outs ← children.mapM (runItemT ctx (d + 1))
      return outs.flatten

/-- The lower part (rows below `τ`) with origins. -/
def lowerT (ctx : Context) (τ : Row) : Result (List (Emit × Origin)) := do
  let outs ← (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2)
  return outs.flatten

/-- The column `x'` read by the upper part. -/
def upperColumn (ctx : Context) : Nat :=
  if ctx.x = ctx.lastColumn then ctx.rootColumn else ctx.x

/-- The upper part (rows `≥ τ`) with origins. -/
def upperT (ctx : Context) (τ : Row) : Result (List (Emit × Origin)) :=
  ((realNodes ctx.source (upperColumn ctx)).filter
      (fun p => decide (τ ≤ official p.2.row))).mapM fun p => do
    return (⟨official p.2.row, some (← leftColumn p.2)⟩, .upper p.1)

/-- All emitted nodes of the column, with origins, bottom to top. -/
def emitsT (ctx : Context) (τ : Row) : Result (List (Emit × Origin)) := do
  let l ← lowerT ctx τ
  let u ← upperT ctx τ
  return l ++ u

/-! ## The traced rule emits the nodes of the rule -/

/-- Mapping the results of `mapM`. -/
theorem mapM_map_fst {α β γ ε : Type} (f : α → Except ε β) (g : α → Except ε γ) (h : γ → β)
    (hfg : ∀ a, Functor.map h (g a) = f a) :
    ∀ xs : List α, Functor.map (List.map h) (xs.mapM g) = xs.mapM f := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.mapM_cons]
      rw [← hfg a, ← ih]
      cases g a with
      | error e => rfl
      | ok b =>
          cases as.mapM g with
          | error e => rfl
          | ok bs => rfl

theorem levelOneT_fst (ctx : Context) (it : Item) :
    Functor.map (List.map Prod.fst) (levelOneT ctx it) = levelOne ctx it := by
  unfold levelOneT levelOne
  cases nodeAt ctx.source ctx.x it.source with
  | none => rfl
  | some p =>
      obtain ⟨srcRef, src⟩ := p
      cases it.clean with
      | some C =>
          simp only
          cases nodeAt ctx.source ctx.x C with
          | none => rfl
          | some q =>
              obtain ⟨csRef, cs⟩ := q
              simp only
              cases leftColumn cs <;> rfl
      | none =>
          simp only
          split
          · rfl
          · cases leftColumn src <;> rfl

theorem runItemT_fst (ctx : Context) :
    ∀ (d : Nat) (it : Item), Functor.map (List.map Prod.fst) (runItemT ctx d it) = runItem ctx d it
  | 0, _ => rfl
  | 1, it => by simp only [runItemT, runItem]; exact levelOneT_fst ctx it
  | d + 2, it => by
      simp only [runItemT, runItem]
      cases childItems ctx (d + 2) it with
      | error e => rfl
      | ok children =>
          have hm := mapM_map_fst (runItem ctx (d + 1)) (runItemT ctx (d + 1)) (List.map Prod.fst)
            (fun c => runItemT_fst ctx (d + 1) c) children
          show (List.map Prod.fst <$> (List.mapM (runItemT ctx (d + 1)) children >>=
              fun outs => pure outs.flatten)) =
            (List.mapM (runItem ctx (d + 1)) children >>= fun outs => pure outs.flatten)
          rw [← hm]
          cases children.mapM (runItemT ctx (d + 1)) with
          | error e => rfl
          | ok outs =>
              show Except.ok (List.map Prod.fst outs.flatten) =
                Except.ok (List.map (List.map Prod.fst) outs).flatten
              rw [List.map_flatten]

/-- The accumulating loop of the lower part is a `mapM` followed by `flatten`. -/
theorem forIn_acc_ok {α β ε : Type} (f : α → Except ε (List β)) :
    ∀ (xs : List α) (acc r : List β),
      forIn xs acc (fun x s => Except.bind (f x) (fun v => Except.ok (ForInStep.yield (s ++ v))))
        = Except.ok r →
      ∃ vs, xs.mapM f = Except.ok vs ∧ r = acc ++ vs.flatten := by
  intro xs
  induction xs with
  | nil =>
      intro acc r h
      simp only [List.forIn_nil] at h
      exact ⟨[], rfl, by cases h; simp⟩
  | cons a as ih =>
      intro acc r h
      simp only [List.forIn_cons] at h
      cases hfa : f a with
      | error e => rw [hfa] at h; cases h
      | ok v =>
          rw [hfa] at h
          obtain ⟨vs, hvs, hr⟩ := ih (acc ++ v) r h
          refine ⟨v :: vs, ?_, by simp [hr]⟩
          simp only [List.mapM_cons, hfa, hvs]
          rfl

/-- The filtering loop of the upper part. -/
theorem forIn_filter_ok {α β γ ε : Type} (P : α → Prop) [DecidablePred P]
    (g : α → Except ε γ) (k : α → γ → β) :
    ∀ (xs : List α) (acc r : List β),
      forIn xs acc (fun x s => if P x then
          Except.bind (g x) (fun v => Except.ok (ForInStep.yield (s ++ [k x v])))
        else Except.ok (ForInStep.yield s)) = Except.ok r →
      ∃ vs, (xs.filter (fun x => decide (P x))).mapM
          (fun x => Except.bind (g x) (fun v => Except.ok (k x v))) = Except.ok vs ∧
        r = acc ++ vs := by
  intro xs
  induction xs with
  | nil =>
      intro acc r h
      simp only [List.forIn_nil] at h
      exact ⟨[], rfl, by cases h; simp⟩
  | cons a as ih =>
      intro acc r h
      simp only [List.forIn_cons] at h
      by_cases hP : P a
      · rw [if_pos hP] at h
        cases hga : g a with
        | error e => rw [hga] at h; cases h
        | ok v =>
            rw [hga] at h
            obtain ⟨vs, hvs, hr⟩ := ih (acc ++ [k a v]) r h
            refine ⟨k a v :: vs, ?_, by simp [hr]⟩
            simp only [List.filter_cons, hP, decide_true, if_true, List.mapM_cons, hga, hvs]
            rfl
      · rw [if_neg hP] at h
        obtain ⟨vs, hvs, hr⟩ := ih acc r h
        refine ⟨vs, ?_, hr⟩
        simp only [List.filter_cons, hP, decide_false]
        exact hvs

theorem map_eq_ok {α β ε : Type} {f : α → β} {x : Except ε α} {b : β}
    (h : Functor.map f x = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem copyColumn_emitsT {ctx : Context} {τ : Row} {col : Column}
    (h : copyColumn ctx τ = .ok col) :
    ∃ es, emitsT ctx τ = .ok es ∧ assemble ctx (es.map Prod.fst) = .ok col := by
  unfold copyColumn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    obtain ⟨vs, hvs, hlow⟩ := forIn_acc_ok (fun x : Nat × Item => runItem ctx x.1 x.2) _ _ _ hlower
    split at h
    · cases h
    · rename_i all hall
      obtain ⟨us, hus, hup⟩ := forIn_filter_ok (fun x : Ref × Cell => τ ≤ official x.2.row)
        (fun x => leftColumn x.2) (fun x v => (⟨official x.2.row, some v⟩ : Emit)) _ _ _ hall
      have hL := mapM_map_fst (fun x : Nat × Item => runItem ctx x.1 x.2)
        (fun p => runItemT ctx p.1 p.2) (List.map Prod.fst) (fun p => runItemT_fst ctx p.1 p.2)
        (lowerItems τ)
      rw [hvs] at hL
      obtain ⟨vsT, hvsT, hvsEq⟩ := map_eq_ok hL
      have hU := mapM_map_fst
        (fun x : Ref × Cell => Except.bind (leftColumn x.2)
          (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit)))
        (fun p : Ref × Cell => (do
          return ((⟨official p.2.row, some (← leftColumn p.2)⟩ : Emit), Origin.upper p.1) :
            Result (Emit × Origin)))
        Prod.fst (fun p => by beta_reduce; cases leftColumn p.2 <;> rfl)
        ((realNodes ctx.source (upperColumn ctx)).filter
          (fun p => decide (τ ≤ official p.2.row)))
      have hus' : List.mapM (fun x : Ref × Cell => Except.bind (leftColumn x.2)
          (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit)))
          ((realNodes ctx.source (upperColumn ctx)).filter
            (fun p => decide (τ ≤ official p.2.row))) = Except.ok us := hus
      rw [hus'] at hU
      obtain ⟨usT, husT, husEq⟩ := map_eq_ok hU
      refine ⟨vsT.flatten ++ usT, ?_, ?_⟩
      · simp only [emitsT, lowerT, upperT]
        rw [hvsT]
        show (do let u ← upperT ctx τ; pure (vsT.flatten ++ u)) = _
        simp only [upperT]
        rw [husT]
        rfl
      · rw [List.map_append, List.map_flatten, hvsEq, husEq, ← h, hup, hlow, List.nil_append]

end OmegaY.Official.Classification
