/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredItems.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Regions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Regions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyWitness

set_option backward.do.legacy false

/-!
# `CutPred` item by item

The emitted list of the lower part of a column is the depth-first concatenation of the
outputs of the items of the rule (`runItemT`). This file proves, by induction on the level,
what the output of each kind of item contributes to `CutPred` (`Spec`):

* a *plain* item (`C = ⊥`, `b = 0`) is self-contained: `CutSeq p out` for every `p`;
* a *gap* item (`C = ⊥`, `b = 1`, case 3 of the rule) needs the emit before it to be a copy
  of the root-row node `ρ = top_S(c_r)` of its region, unless column `x` has no node on the
  row of `ρ`;
* a *cut* item (`C ≠ ⊥`, `b = 1`) emits only cut copies of `C`;
* a *clean* item (`C ≠ ⊥`, `b = 0`, whose region has `C` as the top of the root column) is
  self-contained, and when column `x` has a node on row `C` its output ends with a copy of
  `C`.

Two facts about the run are used as hypotheses on the context (`LiftPos`, `CleanGap`); both
are proved for the contexts of every run (`CutPredMD.liftPosHolds`, `CutPredMD.cleanGapHolds`):

* `LiftPos`: in a region of level `d ≥ 3` below `τ`, for `i ≠ 0`, if column `x` ascends and
  has a node on the row of `ρ = top_S(c_r)`, then `h_κ > h_ρ` (the lift `Δ` is positive);
* `CleanGap`: for a clean item of level `≥ 2` with `i ≠ 0` that is reached by the rule and
  whose boundary column has a node in the target region, `h_ρ ≤ h_B + g` (the copies of the
  root row reach the height of `ρ`).
-/

namespace OmegaY.Official.Recon
open Canonical Official Classification

/-! ## Copies of a root-row node -/

/-- Column `x` has a node on row `C`. -/
def Nd (ctx : Context) (C : Row) : Prop := ∃ q, nodeAt ctx.source ctx.x C = some q

/-- `e` is a copy of the node `(x, C)` (a clean emit of `C`). -/
def CleanOf (ctx : Context) (C : Row) (e : EO) : Prop :=
  ∃ csRef cs lc b, nodeAt ctx.source ctx.x C = some (csRef, cs) ∧ leftColumn cs = .ok lc ∧
    e.1.leftColumn = some lc ∧ e.2 = .clean csRef b

/-- `e` is a cut copy of the node `(x, C)`. -/
def CutOf (ctx : Context) (C : Row) (e : EO) : Prop :=
  ∃ csRef cs lc, nodeAt ctx.source ctx.x C = some (csRef, cs) ∧ leftColumn cs = .ok lc ∧
    e.1.leftColumn = some lc ∧ e.2 = .clean csRef true

/-- The emit before is a copy of `(x, C)`. -/
def Ready (ctx : Context) (C : Row) (p : Option EO) : Prop := ∃ e, p = some e ∧ CleanOf ctx C e

theorem CutOf.clean {ctx : Context} {C : Row} {e : EO} (h : CutOf ctx C e) : CleanOf ctx C e := by
  obtain ⟨a, b, c, h1, h2, h3, h4⟩ := h
  exact ⟨a, b, c, true, h1, h2, h3, h4⟩

theorem CutOf.nd {ctx : Context} {C : Row} {e : EO} (h : CutOf ctx C e) : Nd ctx C := by
  obtain ⟨a, b, _, h1, _⟩ := h
  exact ⟨_, h1⟩

theorem follows_of_ready {ctx : Context} {C : Row} {p : Option EO} {e : EO}
    (hp : Ready ctx C p) (he : CutOf ctx C e) : Follows p e := by
  intro r hr
  obtain ⟨e', rfl, csRef, cs, lc, b, h1, h2, h3, h4⟩ := hp
  obtain ⟨csRef', cs', lc', h1', h2', h3', h4'⟩ := he
  rw [h1] at h1'
  have hq := Option.some.inj h1'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
  rw [h2] at h2'
  obtain rfl := Except.ok.inj h2'
  rw [h4'] at hr
  obtain ⟨rfl, -⟩ := Origin.clean.inj hr
  exact ⟨e', rfl, b, h4, by rw [h3, h3']⟩

/-- A run of cut copies of `C` after a copy of `C`. -/
theorem cut_run {ctx : Context} {C : Row} : ∀ (out : List EO) (p : Option EO),
    (∀ e ∈ out, CutOf ctx C e) → (Nd ctx C → Ready ctx C p) →
    CutSeq p out ∧ (Nd ctx C → Ready ctx C (lastOr p out))
  | [], _, _, hp => ⟨trivial, hp⟩
  | e :: out, p, h, hp => by
    have he := h e List.mem_cons_self
    have hr : Ready ctx C p := hp he.nd
    obtain ⟨h1, h2⟩ := cut_run out (some e) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
      (fun _ => ⟨e, rfl, he.clean⟩)
    exact ⟨⟨follows_of_ready hr he, h1⟩, by rw [lastOr_cons]; exact h2⟩

theorem cutSeq_flatten_all : ∀ (outs : List (List EO)), (∀ o ∈ outs, ∀ p, CutSeq p o) →
    ∀ p, CutSeq p outs.flatten
  | [], _, _ => trivial
  | o :: outs, h, p => by
    rw [List.flatten_cons, cutSeq_append]
    exact ⟨h o List.mem_cons_self p,
      cutSeq_flatten_all outs (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')) _⟩

theorem ready_lastOr {ctx : Context} {C : Row} {L : List EO} (h : Ready ctx C L.getLast?)
    (p : Option EO) : lastOr p L = L.getLast? := by
  obtain ⟨e, he, _⟩ := h
  unfold lastOr
  rw [he]

theorem lastOr_none (L : List EO) : lastOr none L = L.getLast? := by
  unfold lastOr
  cases L.getLast? <;> rfl

/-! ## Regions -/

/-- The region of level `d` with base `S` lies below `τ`, with the first difference at an
exponent `≥ d - 1`. -/
def LowerRegion (τ : Row) (d : Nat) (S : Row) : Prop :=
  ∃ k, d - 1 ≤ k ∧ S.coeff k < τ.coeff k ∧ ∀ k', k < k' → S.coeff k' = τ.coeff k'

theorem topIn_slot_self {M : Mountain} {c D : Nat} {S : Row} {r : Ref} {cl : Cell}
    (h : topIn M c D S = some (r, cl)) (hD : 2 ≤ D) :
    topIn M c (D - 1) (slot D S (height D (official cl.row))) = some (r, cl) := by
  refine topIn_sub h (fun r' h' => Classification.inRegion_slot hD h') ?_
  have hin := Classification.topIn_inRegion h
  rw [Classification.inRegion_iff] at hin ⊢
  intro k hk
  by_cases hk2 : k = D - 2
  · subst hk2
    rw [Classification.coeff_slot_at hD]
    rfl
  · rw [hin k (by omega), Classification.coeff_slot_high hD (by omega)]

theorem topIn_some_of_nd {M : Mountain} {c D : Nat} {S C : Row} {q : Ref × Cell}
    (hq : nodeAt M c C = some q) (hin : inRegion D S C = true) :
    ∃ a, topIn M c D S = some a := by
  have hmem : q ∈ realNodes M c := by
    unfold nodeAt at hq
    exact List.mem_of_find?_eq_some hq
  have hrow := (Classification.nodeAt_spec hq).2.2.2
  unfold topIn
  exact filter_last_exists hmem (by simp only [hrow]; exact hin)

/-! ## Items reached by the rule -/

/-- The items processed by the rule in the context `ctx` with top row `τ`: the first items
and the children of the items of level `≥ 2`. -/
inductive Reached (ctx : Context) (τ : Row) : Nat → Item → Prop
  | root {d : Nat} {it : Item} : (d, it) ∈ lowerItems τ → Reached ctx τ d it
  | child {d : Nat} {it c : Item} {cs : List Item} : Reached ctx τ (d + 2) it →
      childItems ctx (d + 2) it = .ok cs → c ∈ cs → Reached ctx τ (d + 1) c

theorem Reached.pos {ctx : Context} {τ : Row} {d : Nat} {it : Item}
    (h : Reached ctx τ d it) : 1 ≤ d := by
  cases h with
  | root hm =>
    simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
      List.mem_map] at hm
    obtain ⟨k, _, j, _, he⟩ := hm
    have := congrArg Prod.fst he
    simp only at this
    omega
  | child _ _ _ => omega

theorem Reached.lower {ctx : Context} {τ : Row} {d : Nat} {it : Item}
    (h : Reached ctx τ d it) : LowerRegion τ d it.source := by
  induction h with
  | root hm =>
    simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
      List.mem_map] at hm
    obtain ⟨k, _, j, hj, he⟩ := hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he.symm
    refine ⟨k, by omega, ?_, ?_⟩
    · have := Classification.coeff_slot_at (d := k + 2) (base := τ) (j := j) (by omega)
      simp only [show k + 2 - 2 = k by omega] at this
      simp only
      rw [this]
      exact hj
    · intro k' hk'
      exact Classification.coeff_slot_high (by omega) (by omega)
  | child _ hch hc ih =>
    obtain ⟨⟨j, hj⟩, _⟩ := childItems_ok hch _ hc
    obtain ⟨k, hk, hlt, hhi⟩ := ih
    refine ⟨k, by omega, ?_, ?_⟩
    · rw [hj, Classification.coeff_slot_high (by omega) (by omega)]
      exact hlt
    · intro k' hk'
      rw [hj, Classification.coeff_slot_high (by omega) (by omega)]
      exact hhi k' hk'

/-! ## The two facts used -/

/-- **Positive lift** (on the context). In a region `S` of level `d ≥ 3` below `τ`, for
`i ≠ 0`: if column `x` ascends and has a node on the row of `ρ = top_S(c_r)`, then
`h_ρ < h_κ`. -/
def LiftPos (ctx : Context) (τ : Row) : Prop :=
  ∀ (d : Nat) (S : Row) (r : Ref) (cl : Cell), 3 ≤ d → ctx.block ≠ 0 → LowerRegion τ d S →
    topIn ctx.source ctx.rootColumn d S = some (r, cl) → Nd ctx (official cl.row) →
    ascends ctx (some (r, cl)) = .ok true →
    heightOf d (some (r, cl)) < heightOf d (topIn ctx.source ctx.lastColumn d S)

/-- **Clean gap** (on the context). A reached clean item of level `d + 2` with `i ≠ 0` that
reaches case 4: `h_ρ ≤ h_q + g`. -/
def CleanGap (ctx : Context) (τ : Row) : Prop :=
  ∀ (d : Nat) (it : Item) (C : Row) (csRef : Ref) (cs : Cell) (g : Nat),
    Reached ctx τ (d + 2) it → it.clean = some C → it.cutBottom = false → ctx.block ≠ 0 →
    (topIn ctx.source ctx.x (d + 2) it.source).isSome →
    (topIn ctx.result ctx.boundary (d + 2) it.target).isSome →
    ascends ctx (topIn ctx.source ctx.rootColumn (d + 2) it.source) = .ok true →
    nodeAt ctx.source ctx.x C = some (csRef, cs) →
    generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g →
    heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
      heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g

/-! ## What an item contributes -/

/-- The top of the root column in the source region of `it` has row `C`. -/
def RootTop (ctx : Context) (d : Nat) (it : Item) (C : Row) : Prop :=
  ∃ r cl, topIn ctx.source ctx.rootColumn d it.source = some (r, cl) ∧ official cl.row = C

structure Spec (ctx : Context) (d : Nat) (it : Item) (out : List EO) : Prop where
  plain : it.clean = none → it.cutBottom = false → ∀ p, CutSeq p out
  gap : it.clean = none → it.cutBottom = true → ∀ r cl,
    topIn ctx.source ctx.rootColumn d it.source = some (r, cl) →
    ∀ p, (Ready ctx (official cl.row) p ∨ ¬ Nd ctx (official cl.row)) → CutSeq p out
  cut : ∀ C, it.clean = some C → it.cutBottom = true → ∀ e ∈ out, CutOf ctx C e
  clean : ∀ C, it.clean = some C → it.cutBottom = false → RootTop ctx d it C →
    (2 ≤ d → ctx.block ≠ 0) → (∀ p, CutSeq p out) ∧ (Nd ctx C → Ready ctx C out.getLast?)

/-! ### Level 1 -/

theorem spec_one {ctx : Context} {it : Item} {out : List EO} (h : levelOneT ctx it = .ok out) :
    Spec ctx 1 it out := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
    simp only [hsrc, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ e he => by simp at he,
      ?_⟩
    intro C _ _ hroot _
    refine ⟨fun _ => trivial, ?_⟩
    rintro ⟨q, hq⟩
    obtain ⟨r, cl, htop, hrow⟩ := hroot
    have hin := Classification.topIn_inRegion htop
    rw [hrow] at hin
    have hCs := Classification.inRegion_one hin
    rw [hCs, hsrc] at hq
    cases hq
  | some q =>
    obtain ⟨srcRef, src⟩ := q
    simp only [hsrc] at h
    cases hC : it.clean with
    | some C =>
      simp only [hC] at h
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
      | some q' =>
        obtain ⟨csRef, cs⟩ := q'
        cases hlc : leftColumn cs with
        | error err => simp [hcs, hlc, bind, Except.bind] at h
        | ok lc =>
          simp only [hcs, hlc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          refine ⟨(fun h' => by rw [hC] at h'; cases h'), (fun h' => by rw [hC] at h'; cases h'), ?_, ?_⟩
          · intro C' hC' hcb e he
            rw [hC] at hC'
            obtain rfl := Option.some.inj hC'
            simp only [List.mem_singleton] at he
            subst he
            exact ⟨csRef, cs, lc, hcs, hlc, rfl, by rw [hcb]⟩
          · intro C' hC' hcb _ _
            rw [hC] at hC'
            obtain rfl := Option.some.inj hC'
            refine ⟨fun p => ?_, fun _ => ⟨_, rfl, csRef, cs, lc, it.cutBottom, hcs, hlc, rfl, rfl⟩⟩
            apply cutSeq_of_noCut
            intro e he r hr
            simp only [List.mem_singleton] at he
            subst he
            simp [hcb] at hr
    | none =>
      have hno : ∀ e ∈ out, ∀ r, e.2 ≠ .clean r true := by
        simp only [hC] at h
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp
        · cases hl : leftColumn src with
          | error _ => simp [hl, bind, Except.bind] at h
          | ok lc =>
            simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp
      refine ⟨fun _ _ p => cutSeq_of_noCut p out hno,
        fun _ _ _ _ _ p _ => cutSeq_of_noCut p out hno, fun C hC' => ?_, fun C hC' => ?_⟩
      · rw [hC] at hC'; cases hC'
      · rw [hC] at hC'; cases hC'

/-! ### Level `≥ 2`: the runs of children -/

theorem runItemT_succ_succ {ctx : Context} {d : Nat} {it : Item} {out : List EO}
    (h : runItemT ctx (d + 2) it = .ok out) :
    ∃ cs outs, childItems ctx (d + 2) it = .ok cs ∧
      List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o) cs outs ∧ out = outs.flatten := by
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i cs hcs
    split at h
    · cases h
    · rename_i outs houts
      cases h
      exact ⟨cs, outs, hcs, forall₂_of_mapM houts, rfl⟩

theorem mem_map_range' {f : Nat → Item} {a m j : Nat} (h1 : a ≤ j) (h2 : j < a + m) :
    f j ∈ (List.range' a m).map f :=
  List.mem_map_of_mem (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem e_cases (d : Nat) : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
    ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ d ≠ 0) := by
  by_cases hd : d = 0
  · left; simp [hd]
  · right; simp [hd]

/-- **Case 2.** -/
theorem fold_case2 {ctx : Context} {d : Nat} {S T : Row} {i hR N : Nat} {lift : Int} {C : Row}
    {r : Ref} {cl : Cell} {outs : List (List EO)}
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o)
      ((List.range N).map (c2 (d + 2) S T i hR lift C)) outs)
    (IH : ∀ j < N, ∀ o, runItemT ctx (d + 1) (c2 (d + 2) S T i hR lift C j) = .ok o →
      Spec ctx (d + 1) (c2 (d + 2) S T i hR lift C j) o)
    (hroot : topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) S hR) = some (r, cl))
    (hC : official cl.row = C) (hi : ctx.block = i) (hlift0 : i = 0 → lift = 0)
    (hpos : Nd ctx C → d ≠ 0 → i ≠ 0 → 0 < lift) :
    ∀ p, CutSeq p outs.flatten := by
  intro p
  subst hC
  refine (cutSeq_flatten_range' (runItemT ctx (d + 1)) (c2 (d + 2) S T i hR lift (official cl.row))
    (fun j q => Nd ctx (official cl.row) → hR < j → (j : Int) ≤ hR + lift →
      Ready ctx (official cl.row) q) N 0 outs ?_ ?_ p (fun _ h => absurd h (by omega))).1
  · rw [← List.range_eq_range']
    exact List.forall₂_map_left_iff.mp hF
  · intro j _ hj out hrun q hq
    have hs := IH j (by omega) out hrun
    unfold c2 at hs
    have he := e_cases d
    by_cases h1 : j < hR
    · rw [if_pos h1] at hs
      exact ⟨hs.plain rfl rfl q, fun _ h2 _ => absurd h2 (by omega)⟩
    · rw [if_neg h1] at hs
      by_cases h2 : (j : Int) < hR + lift + (if d + 2 = 2 then 1 else 0)
      · rw [if_pos h2] at hs
        by_cases h3 : hR < j
        · have hcut := hs.cut _ rfl (by simp [h3])
          obtain ⟨hA, hB⟩ := cut_run out q hcut (fun hN => hq hN h3 (by omega))
          exact ⟨hA, fun hN _ _ => hB hN⟩
        · have hj : j = hR := by omega
          subst hj
          have hcl := hs.clean _ rfl (by simp) ⟨r, cl, hroot, rfl⟩ (by
            intro hd
            rw [hi]
            intro hi0
            have := hlift0 hi0
            omega)
          refine ⟨hcl.1 q, fun hN _ _ => ?_⟩
          have hR' := hcl.2 hN
          rw [ready_lastOr hR' q]
          exact hR'
      · rw [if_neg h2] at hs
        by_cases h4 : i ≠ 0 ∧ (j : Int) = hR + lift
        · have hsrc : ((j : Int) - lift).toNat = hR := by omega
          rw [hsrc] at hs
          have hd0 : d ≠ 0 := by
            intro hd0
            subst hd0
            simp at h2
            omega
          refine ⟨hs.gap rfl (by simp [h4]) r cl hroot q ?_, fun _ _ h5 => absurd h5 (by omega)⟩
          by_cases hN : Nd ctx (official cl.row)
          · have := hpos hN hd0 h4.1
            exact Or.inl (hq hN (by omega) (by omega))
          · exact Or.inr hN
        · have hcb : decide (i ≠ 0 ∧ (j : Int) = hR + lift) = false := by simp only [decide_eq_false_iff_not]; exact h4
          rw [hcb] at hs
          exact ⟨hs.plain rfl rfl q, fun _ _ h5 => absurd h5 (by omega)⟩

/-- **Case 3.** -/
theorem fold_case3 {ctx : Context} {d : Nat} {S T : Row} {hR hB m : Nat} {C : Row}
    {r : Ref} {cl : Cell} {outs : List (List EO)}
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o)
      ((List.range' hR m).map (c3 (d + 2) S T hR hB C)) outs)
    (IH : ∀ j, hR ≤ j → j < hR + m → ∀ o, runItemT ctx (d + 1) (c3 (d + 2) S T hR hB C j) = .ok o →
      Spec ctx (d + 1) (c3 (d + 2) S T hR hB C j) o)
    (hroot : topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) S hR) = some (r, cl))
    (hC : official cl.row = C) :
    ∀ p, (Ready ctx C p ∨ ¬ Nd ctx C) → CutSeq p outs.flatten := by
  intro p hp
  subst hC
  refine (cutSeq_flatten_range' (runItemT ctx (d + 1)) (c3 (d + 2) S T hR hB (official cl.row))
    (fun j q => j ≤ hB + hR → (Ready ctx (official cl.row) q ∨ ¬ Nd ctx (official cl.row)))
    m hR outs (List.forall₂_map_left_iff.mp hF) ?_ p (fun _ => hp)).1
  intro j hj1 hj2 out hrun q hq
  have hs := IH j hj1 hj2 out hrun
  unfold c3 at hs
  have he := e_cases d
  by_cases h2 : (j : Int) < (hB : Int) + (hR : Int) + (if d + 2 = 2 then 1 else 0)
  · rw [if_pos h2] at hs
    have hcut := hs.cut _ rfl rfl
    have hq' := hq (by omega)
    obtain ⟨hA, hB'⟩ := cut_run out q hcut (fun hN => by
      rcases hq' with h | h
      · exact h
      · exact absurd hN h)
    refine ⟨hA, fun _ => ?_⟩
    by_cases hN : Nd ctx (official cl.row)
    · exact Or.inl (hB' hN)
    · exact Or.inr hN
  · rw [if_neg h2] at hs
    by_cases h5 : j = hB + hR
    · have hsrc : j - hB = hR := by omega
      rw [hsrc] at hs
      exact ⟨hs.gap rfl (by simp [h5]) r cl hroot q (hq (by omega)),
        fun h6 => absurd h6 (by omega)⟩
    · have hcb : decide (j = hB + hR) = false := by simp only [decide_eq_false_iff_not]; exact h5
      rw [hcb] at hs
      exact ⟨hs.plain rfl rfl q, fun h6 => absurd h6 (by omega)⟩

/-- **Case 4 without a cut bottom.** -/
theorem fold_case4 {ctx : Context} {d : Nat} {S T : Row} {hR hB N : Nat} {C : Row}
    {r : Ref} {cl : Cell} {outs : List (List EO)}
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o)
      ((List.range N).map (c4 (d + 2) S T hR hB 0 false C)) outs)
    (IH : ∀ j < N, ∀ o, runItemT ctx (d + 1) (c4 (d + 2) S T hR hB 0 false C j) = .ok o →
      Spec ctx (d + 1) (c4 (d + 2) S T hR hB 0 false C j) o)
    (hroot : topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) S hR) = some (r, cl))
    (hC : official cl.row = C) (hi : ctx.block ≠ 0) (hN : Nd ctx C → hR < N) :
    (∀ p, CutSeq p outs.flatten) ∧ (Nd ctx C → Ready ctx C outs.flatten.getLast?) := by
  have hF' : List.Forall₂ (fun j o => runItemT ctx (d + 1) (c4 (d + 2) S T hR hB 0 false C j) = .ok o)
      (List.range' 0 N) outs := by
    rw [← List.range_eq_range']
    exact List.forall₂_map_left_iff.mp hF
  have hstep : ∀ j, 0 ≤ j → j < 0 + N → ∀ out,
      runItemT ctx (d + 1) (c4 (d + 2) S T hR hB 0 false C j) = .ok out → ∀ q,
      (Nd ctx C → hR < j → Ready ctx C q) →
      CutSeq q out ∧ (Nd ctx C → hR < j + 1 → Ready ctx C (lastOr q out)) := by
    intro j _ hj out hrun q hq
    have hs := IH j (by omega) out hrun
    unfold c4 at hs
    simp only [Bool.false_eq_true, if_false] at hs
    by_cases h1 : j < hR
    · rw [if_pos h1] at hs
      exact ⟨hs.plain rfl rfl q, fun _ h2 => absurd h2 (by omega)⟩
    · rw [if_neg h1] at hs
      by_cases h3 : hR < j
      · have hcut := hs.cut _ rfl (by simp [h3])
        obtain ⟨hA, hB'⟩ := cut_run out q hcut (fun hN' => hq hN' h3)
        exact ⟨hA, fun hN' _ => hB' hN'⟩
      · have hj : j = hR := by omega
        subst hj
        have hcl := hs.clean _ rfl (by simp) ⟨r, cl, hroot, hC⟩ (fun _ => hi)
        refine ⟨hcl.1 q, fun hN' _ => ?_⟩
        have hR' := hcl.2 hN'
        rw [ready_lastOr hR' q]
        exact hR'
  have key : ∀ p, CutSeq p outs.flatten ∧
      (Nd ctx C → hR < N → Ready ctx C (lastOr p outs.flatten)) := by
    intro p
    have := cutSeq_flatten_range' (runItemT ctx (d + 1)) (c4 (d + 2) S T hR hB 0 false C)
      (fun j q => Nd ctx C → hR < j → Ready ctx C q) N 0 outs hF' hstep p
      (fun _ h => absurd h (by omega))
    simpa only [Nat.zero_add] using this
  refine ⟨fun p => (key p).1, fun hNd => ?_⟩
  have := (key none).2 hNd (hN hNd)
  rwa [lastOr_none] at this

/-! ### Level `≥ 2`: the four kinds -/

section steps
variable {ctx : Context} {τ : Row} {d : Nat} {it : Item} {cs : List Item}
  {outs : List (List EO)}

theorem step_plain (H2 : LiftPos ctx τ) (hreach : Reached ctx τ (d + 2) it)
    (hch : childItems ctx (d + 2) it = .ok cs)
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o) cs outs)
    (IH : ∀ c ∈ cs, ∀ o, runItemT ctx (d + 1) c = .ok o → Spec ctx (d + 1) c o)
    (hcl : it.clean = none) (hcb : it.cutBottom = false) : ∀ p, CutSeq p outs.flatten := by
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
    rw [childItems_none hch hx] at hF
    cases hF
    intro p
    trivial
  | some a =>
    obtain ⟨b, hasc⟩ := childItems_asc hch hx
    cases b with
    | false =>
      obtain ⟨_, _, hall⟩ := childItems_case1 hch hx hasc
      apply cutSeq_flatten_all
      intro o ho p
      obtain ⟨c, hc, hco⟩ := forall₂_mem_right hF o ho
      exact (IH c hc o hco).plain (hall c hc).1 (hall c hc).2 p
    | true =>
      cases hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source with
      | none =>
        rw [hrho] at hasc
        simp [ascends, pure, Except.pure] at hasc
      | some rc =>
        obtain ⟨r, cl⟩ := rc
        have hasc' := hasc
        rw [hrho] at hasc'
        have hcs := childItems_case2 hch hcl hcb hx hrho hasc'
        subst hcs
        refine fold_case2 hF (fun j hj o ho => IH _ (List.mem_map_of_mem (List.mem_range.mpr hj)) o ho)
          (topIn_slot_self hrho (by omega)) rfl rfl (fun h0 => by rw [h0]; simp) ?_
        intro hN hd0 hi0
        have hlow := hreach.lower
        have := H2 (d + 2) it.source r cl (by omega) hi0 hlow hrho hN hasc'
        have hh : heightOf (d + 2) (some (r, cl)) = height (d + 2) (official cl.row) := rfl
        rw [hh] at this
        have hb : (0 : Int) < ctx.block := by omega
        exact Int.mul_pos (by omega) hb

theorem step_gap (hch : childItems ctx (d + 2) it = .ok cs)
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o) cs outs)
    (IH : ∀ c ∈ cs, ∀ o, runItemT ctx (d + 1) c = .ok o → Spec ctx (d + 1) c o)
    (hcl : it.clean = none) (hcb : it.cutBottom = true) {r : Ref} {cl : Cell}
    (hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl)) :
    ∀ p, (Ready ctx (official cl.row) p ∨ ¬ Nd ctx (official cl.row)) →
      CutSeq p outs.flatten := by
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
    rw [childItems_none hch hx] at hF
    cases hF
    intro p _
    trivial
  | some a =>
    obtain ⟨b, hasc⟩ := childItems_asc hch hx
    cases b with
    | false =>
      obtain ⟨_, h2, _⟩ := childItems_case1 hch hx hasc
      rw [hcb] at h2
      cases h2
    | true =>
      rw [hrho] at hasc
      have hcs := childItems_case3 hch hcl hcb hx hrho hasc
      rw [filter_range_eq_range'] at hcs
      subst hcs
      exact fold_case3 hF (fun j h1 h2 o ho => IH _ (mem_map_range' h1 h2) o ho)
        (topIn_slot_self hrho (by omega)) rfl

theorem step_cut (hch : childItems ctx (d + 2) it = .ok cs)
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o) cs outs)
    (IH : ∀ c ∈ cs, ∀ o, runItemT ctx (d + 1) c = .ok o → Spec ctx (d + 1) c o)
    {C : Row} (hcl : it.clean = some C) (hcb : it.cutBottom = true) :
    ∀ e ∈ outs.flatten, CutOf ctx C e := by
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
    rw [childItems_none hch hx] at hF
    cases hF
    intro e he
    simp at he
  | some a =>
    obtain ⟨b, hasc⟩ := childItems_asc hch hx
    cases b with
    | false =>
      obtain ⟨h1, _, _⟩ := childItems_case1 hch hx hasc
      rw [hcl] at h1
      cases h1
    | true =>
      cases hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source with
      | none =>
        rw [hrho] at hasc
        simp [ascends, pure, Except.pure] at hasc
      | some rc =>
        obtain ⟨r, cl⟩ := rc
        rw [hrho] at hasc
        obtain ⟨_, _, _, _, _, _, hcs⟩ := childItems_case4 hch hcl hx hrho hasc
        intro e he
        obtain ⟨o, ho, heo⟩ := List.mem_flatten.mp he
        obtain ⟨c, hc, hco⟩ := forall₂_mem_right hF o ho
        have hs := IH c hc o hco
        rw [hcs] at hc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
        unfold c4 at hs
        rw [hcb] at hs
        simp only [if_true] at hs
        exact hs.cut C rfl rfl e heo

theorem step_clean (H1 : CleanGap ctx τ) (hreach : Reached ctx τ (d + 2) it)
    (hch : childItems ctx (d + 2) it = .ok cs)
    (hF : List.Forall₂ (fun c o => runItemT ctx (d + 1) c = .ok o) cs outs)
    (IH : ∀ c ∈ cs, ∀ o, runItemT ctx (d + 1) c = .ok o → Spec ctx (d + 1) c o)
    {C : Row} (hcl : it.clean = some C) (hcb : it.cutBottom = false)
    (hroot : RootTop ctx (d + 2) it C) (hi : ctx.block ≠ 0) :
    (∀ p, CutSeq p outs.flatten) ∧ (Nd ctx C → Ready ctx C outs.flatten.getLast?) := by
  obtain ⟨r, cl, hrho, hC⟩ := hroot
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
    rw [childItems_none hch hx] at hF
    cases hF
    refine ⟨fun _ => trivial, ?_⟩
    rintro ⟨q, hq⟩
    have hin := Classification.topIn_inRegion hrho
    rw [hC] at hin
    obtain ⟨a, ha⟩ := topIn_some_of_nd hq hin
    rw [hx] at ha
    cases ha
  | some a =>
    obtain ⟨b, hasc⟩ := childItems_asc hch hx
    cases b with
    | false =>
      obtain ⟨h1, _, _⟩ := childItems_case1 hch hx hasc
      rw [hcl] at h1
      cases h1
    | true =>
      have hasc' := hasc
      rw [hrho] at hasc'
      obtain ⟨csRef, csc, g, hnode, hgen, hbd, hcs⟩ := childItems_case4 hch hcl hx hrho hasc'
      obtain ⟨hbsome, hoff⟩ := hbd hcb
      rw [hcb, hoff] at hcs
      simp only [hi, if_false] at hcs
      subst hcs
      have hgap := H1 d it C csRef csc g hreach hcl hcb hi (by rw [hx]; rfl) hbsome hasc hnode hgen
      rw [hrho] at hgap
      have hh : heightOf (d + 2) (some (r, cl)) = height (d + 2) (official cl.row) := rfl
      rw [hh] at hgap
      refine fold_case4 hF (fun j hj o ho => IH _ (List.mem_map_of_mem (List.mem_range.mpr hj)) o ho)
        (topIn_slot_self hrho (by omega)) hC hi (fun _ => by omega)

end steps

/-! ### The induction -/

theorem spec_all {ctx : Context} {τ : Row} (H1 : CleanGap ctx τ) (H2 : LiftPos ctx τ) :
    ∀ (d : Nat) (it : Item) (out : List EO), Reached ctx τ d it → runItemT ctx d it = .ok out →
      Spec ctx d it out
  | 0, _, _, hreach, _ => absurd hreach.pos (by omega)
  | 1, it, out, _, h => spec_one (by simpa [runItemT] using h)
  | d + 2, it, out, hreach, h => by
    obtain ⟨cs, outs, hch, hF, rfl⟩ := runItemT_succ_succ h
    have IH : ∀ c ∈ cs, ∀ o, runItemT ctx (d + 1) c = .ok o → Spec ctx (d + 1) c o :=
      fun c hc o ho => spec_all H1 H2 (d + 1) c o (Reached.child hreach hch hc) ho
    refine ⟨fun hcl hcb => step_plain H2 hreach hch hF IH hcl hcb,
      fun hcl hcb r cl hrho => step_gap hch hF IH hcl hcb hrho,
      fun C hcl hcb => step_cut hch hF IH hcl hcb,
      fun C hcl hcb hroot hi => step_clean H1 hreach hch hF IH hcl hcb hroot (hi (by omega))⟩

end OmegaY.Official.Recon
