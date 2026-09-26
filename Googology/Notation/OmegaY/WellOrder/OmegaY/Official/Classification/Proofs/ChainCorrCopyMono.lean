/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrCopyMono.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `case2_ok`, `case3_ok` and `case4_ok` the goal is beta-reduced after `unfold TagOK`, before `split_ifs`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartCopy
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Regions

set_option backward.do.legacy false

/-!
# `CopyMono`: the origin rows of a copied column do not decrease

`CopyMono` (`ChainCorrStartCopy.lean`) says that in a copied column the rows of the origins
of the emitted nodes do not decrease. This is a property of the rule alone: it holds for
every column of every block and needs no fact about the source mountain besides validity.

## The origin range of an item

Every item `(S, T, C, o, b)` of level `d` emits nodes whose origins lie in a range `Rg` of
official rows:

* `C = ⊥`, `b = 0` (plain): the source region `S`;
* `C = ⊥`, `b = 1` (cut bottom): the rows of `S` at or above the top `ρ` of the root column
  in `S`;
* `C ≠ ⊥`, `b = 0` (clean): the rows of `S` at or below `C`;
* `C ≠ ⊥`, `b = 1` (gap copy): the row `C` itself.

A copied row `C` is always the row of the top of the root column in the current region
(`Inv`). The children of an item (notes/03 §2.4, cases 1 to 4) take slots `S[σ]` with `σ`
not decreasing, and the only children that share a slot are, in the slot `h_ρ` of the root
top, a clean child, then gap-copy children, then a cut-bottom child. So consecutive
children have ordered ranges (`childItems_mono`), and the emits of an item have
non-decreasing origin rows (`runItemT_mono`). The lower part runs the regions `L_{k,j}`
below `τ` in increasing order, and the upper part copies nodes at or above `τ` in column
order (`emitsT_mono`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

namespace CopyMonoProof

/-! ## Regions and slots -/

theorem slot_coeff_high {d : Nat} {S : Row} {σ k : Nat} (hk : d + 1 ≤ k) :
    (slot (d + 2) S σ).coeff k = S.coeff k :=
  coeff_slot_high (by omega) (by omega)

theorem slot_coeff_at {d : Nat} {S : Row} {σ : Nat} : (slot (d + 2) S σ).coeff d = σ := by
  have := coeff_slot_at (d := d + 2) (base := S) (j := σ) (by omega)
  simpa using this

/-- Rows of a lower slot are below rows of a higher slot. -/
theorem lt_of_slot_lt {d : Nat} {S a b : Row} {σ1 σ2 : Nat}
    (ha : inRegion (d + 1) (slot (d + 2) S σ1) a = true)
    (hb : inRegion (d + 1) (slot (d + 2) S σ2) b = true) (h : σ1 < σ2) : a < b := by
  rw [inRegion_iff] at ha hb
  refine Row.lt_iff.mpr ⟨d, fun m hm => ?_, ?_⟩
  · rw [ha m (by omega), hb m (by omega), slot_coeff_high (by omega), slot_coeff_high (by omega)]
  · rw [ha d (by omega), hb d (by omega), slot_coeff_at, slot_coeff_at]
    exact h

/-- A row of a region lies in the slot of its height. -/
theorem mem_slot_height {d : Nat} {S r : Row} (h : inRegion (d + 2) S r = true) :
    inRegion (d + 1) (slot (d + 2) S (height (d + 2) r)) r = true := by
  rw [inRegion_iff] at h ⊢
  intro k hk
  rcases Nat.lt_or_eq_of_le (show d ≤ k by omega) with hk' | hk'
  · rw [slot_coeff_high (by omega)]
    exact h k (by omega)
  · subst hk'
    rw [slot_coeff_at]
    simp [height]

theorem mem_of_slot {d : Nat} {S r : Row} {σ : Nat}
    (h : inRegion (d + 1) (slot (d + 2) S σ) r = true) : inRegion (d + 2) S r = true :=
  inRegion_slot (d := d + 2) (by omega) (by simpa using h)

/-! ## Ranges and invariants -/

/-- The official row of the top of the root column in a region. -/
def rootTop (ctx : Context) (d : Nat) (S : Row) : Option Row :=
  (topIn ctx.source ctx.rootColumn d S).map fun p => official p.2.row

/-- The range of the origin rows of an item. -/
def Rg (ctx : Context) (d : Nat) (it : Item) (r : Row) : Prop :=
  match it.clean with
  | some C => if it.cutBottom then r = C else inRegion d it.source r = true ∧ r ≤ C
  | none => inRegion d it.source r = true ∧
      (it.cutBottom = true → ∀ ρ, rootTop ctx d it.source = some ρ → ρ ≤ r)

/-- A copied row is the row of the top of the root column in the source region. -/
def Inv (ctx : Context) (d : Nat) (it : Item) : Prop :=
  ∀ C, it.clean = some C → rootTop ctx d it.source = some C

theorem rootTop_mem {ctx : Context} {d : Nat} {S C : Row} (h : rootTop ctx d S = some C) :
    inRegion d S C = true := by
  unfold rootTop at h
  cases hp : topIn ctx.source ctx.rootColumn d S with
  | none => rw [hp] at h; cases h
  | some p =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact topIn_inRegion hp

/-- The top of the root column in a region is also the top in the slot containing it. -/
theorem rootTop_slot {ctx : Context} {d : Nat} {S C : Row}
    (h : rootTop ctx (d + 2) S = some C) :
    rootTop ctx (d + 1) (slot (d + 2) S (height (d + 2) C)) = some C := by
  unfold rootTop at h ⊢
  cases hp : topIn ctx.source ctx.rootColumn (d + 2) S with
  | none => rw [hp] at h; cases h
  | some p =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hin := topIn_inRegion hp
      have hsub : ∀ r, inRegion (d + 1) (slot (d + 2) S (height (d + 2) C)) r = true →
          inRegion (d + 2) S r = true := fun r hr => mem_of_slot hr
      rw [Recon.topIn_sub hp hsub (by rw [h]; exact mem_slot_height (h ▸ hin))]
      simp [h]

/-- The emits of an item: origins in its range and non-decreasing origin rows. -/
def OLe (M : Mountain) (p q : Emit × Origin) : Prop :=
  ∀ c c', cell? M p.2.src = some c → cell? M q.2.src = some c' → official c.row ≤ official c'.row

def InRg (ctx : Context) (d : Nat) (it : Item) (ps : List (Emit × Origin)) : Prop :=
  ∀ p ∈ ps, ∃ c, cell? ctx.source p.2.src = some c ∧ Rg ctx d it (official c.row)

/-! ## Tags of children -/

/-- A child range: the slot `σ` of `S`, and a mode: `0` plain, `1` at or below `C`, `2`
exactly `C`, `3` at or above `C`. -/
def InTag (d : Nat) (S C : Row) (σ m : Nat) (r : Row) : Prop :=
  inRegion (d + 1) (slot (d + 2) S σ) r = true ∧ (m = 1 → r ≤ C) ∧ (m = 2 → r = C) ∧
    (m = 3 → C ≤ r)

/-- The order of two child ranges. -/
def TagOK (hR : Nat) (σ1 m1 σ2 m2 : Nat) : Prop :=
  σ1 < σ2 ∨ (σ1 = hR ∧ σ2 = hR ∧ (m1 = 1 ∨ m1 = 2) ∧ (m2 = 2 ∨ m2 = 3))

theorem tag_le {d : Nat} {S C a b : Row} {hR σ1 m1 σ2 m2 : Nat}
    (ha : InTag d S C σ1 m1 a) (hb : InTag d S C σ2 m2 b) (h : TagOK hR σ1 m1 σ2 m2) :
    a ≤ b := by
  rcases h with h | ⟨_, _, hm1, hm2⟩
  · exact le_of_lt (lt_of_slot_lt ha.1 hb.1 h)
  · have haC : a ≤ C := by
      rcases hm1 with h1 | h1
      · exact ha.2.1 h1
      · exact le_of_eq (ha.2.2.1 h1)
    have hCb : C ≤ b := by
      rcases hm2 with h2 | h2
      · exact le_of_eq (hb.2.2.1 h2).symm
      · exact hb.2.2.2 h2
    exact le_trans haC hCb

theorem tag_below {d : Nat} {S C r : Row} {hR σ m : Nat} (hr : InTag d S C σ m r)
    (hC : inRegion (d + 1) (slot (d + 2) S hR) C = true) (h : σ < hR) : r < C :=
  lt_of_slot_lt hr.1 hC h

theorem tag_above {d : Nat} {S C r : Row} {hR σ m : Nat} (hr : InTag d S C σ m r)
    (hC : inRegion (d + 1) (slot (d + 2) S hR) C = true) (h : hR < σ) : C < r :=
  lt_of_slot_lt hC hr.1 h

/-! ## Level `1` -/

theorem levelOneT_mono {ctx : Context} {it : Item} (hI : Inv ctx 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    InRg ctx 1 it ps ∧ ps.Pairwise (OLe ctx.source) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      exact ⟨fun p hp => by simp at hp, List.Pairwise.nil⟩
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hscell hsrow
      simp only [hsrc] at h
      have hsingle : ∀ (ps : List (Emit × Origin)) (e : Emit × Origin), ps = [e] →
          (∃ c, cell? ctx.source e.2.src = some c ∧ Rg ctx 1 it (official c.row)) →
          InRg ctx 1 it ps ∧ ps.Pairwise (OLe ctx.source) := by
        intro ps e hps he
        subst hps
        exact ⟨fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact he,
          List.pairwise_singleton _ _⟩
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only at hccell hcrow
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                refine hsingle _ _ rfl ⟨cs, by simpa [Origin.src] using hccell, ?_⟩
                simp only [Rg, hC, hcrow]
                split
                · trivial
                · exact ⟨rootTop_mem (hI C hC), le_refl _⟩
      | none =>
          simp only [hC] at h
          have hRg : Rg ctx 1 it (official src.row) := by
            simp only [Rg, hC, hsrow]
            refine ⟨inRegion_self 1 _, fun _ ρ hρ => ?_⟩
            rw [inRegion_one (rootTop_mem hρ)]
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            exact hsingle _ _ h.symm ⟨src, by simpa [Origin.src] using hscell, hRg⟩
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              exact hsingle _ _ rfl ⟨src, by simpa [Origin.src] using hscell, hRg⟩

/-! ## Children -/

/-- What an item needs from its children. -/
def ChildrenOK (ctx : Context) (d : Nat) (it : Item) (cs : List Item) : Prop :=
  (∀ c ∈ cs, Inv ctx (d + 1) c ∧ ∀ r, Rg ctx (d + 1) c r → Rg ctx (d + 2) it r) ∧
  cs.Pairwise (fun c c' => ∀ a b, Rg ctx (d + 1) c a → Rg ctx (d + 1) c' b → a ≤ b)

theorem childrenOK_of_tags {ctx : Context} {d : Nat} {it : Item} {js : List Nat}
    (hjs : js.Pairwise (· < ·)) (f : Nat → Item) (C : Row) (hR : Nat) (σ m : Nat → Nat)
    (hinv : ∀ j ∈ js, Inv ctx (d + 1) (f j))
    (htag : ∀ j ∈ js, ∀ r, Rg ctx (d + 1) (f j) r → InTag d it.source C (σ j) (m j) r)
    (hpar : ∀ j ∈ js, ∀ r, InTag d it.source C (σ j) (m j) r → Rg ctx (d + 2) it r)
    (hord : ∀ j ∈ js, ∀ j' ∈ js, j < j' → TagOK hR (σ j) (m j) (σ j') (m j')) :
    ChildrenOK ctx d it (js.map f) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact ⟨hinv j hj, fun r hr => hpar j hj r (htag j hj r hr)⟩
  · rw [List.pairwise_map]
    refine hjs.imp_of_mem ?_
    intro j j' hj hj' hlt a b ha hb
    exact tag_le (htag j hj a ha) (htag j' hj' b hb) (hord j hj j' hj' hlt)

/-! ## The four cases -/

/-- The children of case 2 (lift). -/
def c2 (S T C0 : Row) (d hR : Nat) (L e : Int) (blk : Nat) (j : Nat) : Item :=
  if j < hR then ⟨slot (d + 2) S j, slot (d + 2) T j, none, 0, false⟩
  else if (j : Int) < hR + L + e then
    ⟨slot (d + 2) S hR, slot (d + 2) T j, some C0, 0, decide (hR < j)⟩
  else ⟨slot (d + 2) S ((j : Int) - L).toNat, slot (d + 2) T j, none, 0,
    decide (blk ≠ 0 ∧ (j : Int) = hR + L)⟩

theorem case2_ok {ctx : Context} {d : Nat} {it : Item} (hcl : it.clean = none)
    (hcb : it.cutBottom = false) {C0 : Row} {hR : Nat} {L e : Int} (he : e = 0 ∨ e = 1)
    (hL0 : ctx.block = 0 → L = 0)
    (hC0slot : inRegion (d + 1) (slot (d + 2) it.source hR) C0 = true)
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) it.source hR) = some C0) (N : Nat) :
    ChildrenOK ctx d it ((List.range N).map (c2 it.source it.target C0 d hR L e ctx.block)) := by
  refine childrenOK_of_tags List.pairwise_lt_range _ C0 hR
    (fun j => if j < hR then j else if (j : Int) < hR + L + e then hR else ((j : Int) - L).toNat)
    (fun j => if j < hR then 0 else if (j : Int) < hR + L + e then (if hR < j then 2 else 1)
      else (if ctx.block ≠ 0 ∧ (j : Int) = hR + L then 3 else 0)) ?_ ?_ ?_ ?_
  · intro j _ C' hC'
    unfold c2 at hC'
    by_cases h1 : j < hR
    · rw [if_pos h1] at hC'
      cases hC'
    · rw [if_neg h1] at hC'
      by_cases h2 : (j : Int) < hR + L + e
      · rw [if_pos h2] at hC'
        cases hC'
        unfold c2
        rw [if_neg h1, if_pos h2]
        exact hinvC0
      · rw [if_neg h2] at hC'
        cases hC'
  · intro j _ r hr
    unfold c2 at hr
    by_cases h1 : j < hR
    · rw [if_pos h1] at hr
      simp only [Rg] at hr
      simp only [h1, if_true]
      exact ⟨hr.1, by simp, by simp, by simp⟩
    · rw [if_neg h1] at hr
      by_cases h2 : (j : Int) < hR + L + e
      · rw [if_pos h2] at hr
        simp only [Rg] at hr
        simp only [h1, h2, if_false, if_true]
        by_cases h3 : hR < j
        · simp only [h3, decide_true, if_true] at hr ⊢
          subst hr
          exact ⟨hC0slot, by simp, fun _ => rfl, by simp⟩
        · simp only [h3, decide_false, if_false, Bool.false_eq_true] at hr ⊢
          exact ⟨hr.1, fun _ => hr.2, by simp, by simp⟩
      · rw [if_neg h2] at hr
        simp only [Rg] at hr
        simp only [h1, h2, if_false]
        by_cases h3 : ctx.block ≠ 0 ∧ (j : Int) = hR + L
        · have hσ : ((j : Int) - L).toNat = hR := by omega
          rw [if_pos h3, hσ]
          rw [hσ] at hr
          exact ⟨hr.1, by simp, by simp, fun _ => hr.2 (by simpa using h3) _ hinvC0⟩
        · simp only [h3, if_false]
          exact ⟨hr.1, by simp, by simp, by simp⟩
  · intro j _ r hr
    simp only [Rg, hcl, hcb]
    exact ⟨mem_of_slot hr.1, by simp⟩
  · intro j _ j' _ hjj
    unfold TagOK
    beta_reduce
    split_ifs <;> omega

/-- The children of case 3 (cut bottom). -/
def c3 (S T C0 : Row) (d hR hB : Nat) (e : Int) (j : Nat) : Item :=
  if (j : Int) < hB + hR + e then ⟨slot (d + 2) S hR, slot (d + 2) T (j - hR), some C0, 0, true⟩
  else ⟨slot (d + 2) S (j - hB), slot (d + 2) T (j - hR), none, 0, decide (j = hB + hR)⟩

theorem case3_ok {ctx : Context} {d : Nat} {it : Item} (hcl : it.clean = none)
    (hcb : it.cutBottom = true) {C0 : Row} {hR hB : Nat} {e : Int} (he : e = 0 ∨ e = 1)
    (hrt : rootTop ctx (d + 2) it.source = some C0)
    (hC0slot : inRegion (d + 1) (slot (d + 2) it.source hR) C0 = true)
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) it.source hR) = some C0) (N : Nat) :
    ChildrenOK ctx d it
      (((List.range N).filter (fun x => decide (hR ≤ x))).map (c3 it.source it.target C0 d hR hB e)) := by
  refine childrenOK_of_tags (List.pairwise_lt_range.filter _) _ C0 hR
    (fun j => if (j : Int) < hB + hR + e then hR else j - hB)
    (fun j => if (j : Int) < hB + hR + e then 2 else if j = hB + hR then 3 else 0) ?_ ?_ ?_ ?_
  · intro j _ C' hC'
    unfold c3 at hC'
    by_cases h2 : (j : Int) < hB + hR + e
    · rw [if_pos h2] at hC'
      cases hC'
      unfold c3
      rw [if_pos h2]
      exact hinvC0
    · rw [if_neg h2] at hC'
      cases hC'
  · intro j hj r hr
    have hjR : hR ≤ j := by simpa using (List.mem_filter.mp hj).2
    unfold c3 at hr
    by_cases h2 : (j : Int) < hB + hR + e
    · rw [if_pos h2] at hr
      simp only [Rg, if_true] at hr
      simp only [h2, if_true]
      subst hr
      exact ⟨hC0slot, by simp, fun _ => rfl, by simp⟩
    · rw [if_neg h2] at hr
      simp only [Rg] at hr
      simp only [h2, if_false]
      by_cases h3 : j = hB + hR
      · have hσ : j - hB = hR := by omega
        simp only [h3, if_true]
        rw [← h3, hσ] at hr ⊢
        refine ⟨hr.1, by simp, by simp, fun _ => hr.2 ?_ _ hinvC0⟩
        simp [h3]
      · simp only [h3, if_false]
        exact ⟨hr.1, by simp, by simp, by simp⟩
  · intro j hj r hr
    have hjR : hR ≤ j := by simpa using (List.mem_filter.mp hj).2
    simp only [Rg, hcl, hcb]
    refine ⟨mem_of_slot hr.1, fun _ ρ hρ => ?_⟩
    rw [hrt] at hρ
    cases hρ
    by_cases h2 : (j : Int) < hB + hR + e
    · simp only [h2, if_true] at hr
      exact le_of_eq (hr.2.2.1 rfl).symm
    · simp only [h2, if_false] at hr
      by_cases h3 : j = hB + hR
      · simp only [h3, if_true] at hr
        exact hr.2.2.2 rfl
      · simp only [h3, if_false] at hr
        exact le_of_lt (tag_above hr hC0slot (by omega))
  · intro j hj j' hj' hjj
    have hjR : hR ≤ j := by simpa using (List.mem_filter.mp hj).2
    have hjR' : hR ≤ j' := by simpa using (List.mem_filter.mp hj').2
    unfold TagOK
    beta_reduce
    split_ifs <;> omega

/-- The children of case 4 (a copied root row). -/
def c4 (S T C : Row) (d hR hB off : Nat) (cut : Bool) (j : Nat) : Item :=
  if cut = true then
    ⟨slot (d + 2) S hR, slot (d + 2) T j, some C, ((j : Int) - hB + off).toNat, true⟩
  else if j < hR then ⟨slot (d + 2) S j, slot (d + 2) T j, none, 0, false⟩
  else ⟨slot (d + 2) S hR, slot (d + 2) T j, some C, ((j : Int) - hB + off).toNat, decide (hR < j)⟩

theorem case4_ok {ctx : Context} {d : Nat} {it : Item} {C : Row} (hcl : it.clean = some C)
    {hR hB : Nat}
    (hC0slot : inRegion (d + 1) (slot (d + 2) it.source hR) C = true)
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) it.source hR) = some C) (N : Nat) :
    ChildrenOK ctx d it
      ((List.range N).map (c4 it.source it.target C d hR hB it.offset it.cutBottom)) := by
  refine childrenOK_of_tags List.pairwise_lt_range _ C hR
    (fun j => if it.cutBottom = true then hR else if j < hR then j else hR)
    (fun j => if it.cutBottom = true then 2 else if j < hR then 0 else if hR < j then 2 else 1)
    ?_ ?_ ?_ ?_
  · intro j _ C' hC'
    unfold c4 at hC'
    by_cases h0 : it.cutBottom = true
    · rw [if_pos h0] at hC'
      cases hC'
      unfold c4
      rw [if_pos h0]
      exact hinvC0
    · rw [if_neg h0] at hC'
      by_cases h1 : j < hR
      · rw [if_pos h1] at hC'
        cases hC'
      · rw [if_neg h1] at hC'
        cases hC'
        unfold c4
        rw [if_neg h0, if_neg h1]
        exact hinvC0
  · intro j _ r hr
    unfold c4 at hr
    by_cases h0 : it.cutBottom = true
    · rw [if_pos h0] at hr
      simp only [Rg, if_true] at hr
      simp only [h0, if_true]
      subst hr
      exact ⟨hC0slot, by simp, fun _ => rfl, by simp⟩
    · rw [if_neg h0] at hr
      simp only [h0]
      by_cases h1 : j < hR
      · rw [if_pos h1] at hr
        simp only [Rg] at hr
        simp only [h1, if_true]
        exact ⟨hr.1, by simp, by simp, by simp⟩
      · rw [if_neg h1] at hr
        simp only [Rg] at hr
        simp only [h1, if_false]
        by_cases h3 : hR < j
        · simp only [h3, decide_true, if_true] at hr ⊢
          subst hr
          exact ⟨hC0slot, by simp, fun _ => rfl, by simp⟩
        · simp only [h3, decide_false, if_false, Bool.false_eq_true] at hr ⊢
          exact ⟨hr.1, fun _ => hr.2, by simp, by simp⟩
  · intro j _ r hr
    simp only [Rg, hcl]
    by_cases h0 : it.cutBottom = true
    · simp only [h0, if_true] at hr ⊢
      exact hr.2.2.1 rfl
    · simp only [h0, if_false, Bool.false_eq_true] at hr ⊢
      refine ⟨mem_of_slot hr.1, ?_⟩
      by_cases h1 : j < hR
      · simp only [h1, if_true] at hr
        exact le_of_lt (tag_below hr hC0slot h1)
      · simp only [h1, if_false] at hr
        by_cases h3 : hR < j
        · simp only [h3, if_true] at hr
          exact le_of_eq (hr.2.2.1 rfl)
        · simp only [h3, if_false] at hr
          exact hr.2.1 rfl
  · intro j _ j' _ hjj
    unfold TagOK
    beta_reduce
    split_ifs <;> omega

theorem childItems_mono {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (hI : Inv ctx (d + 2) it) (h : childItems ctx (d + 2) it = .ok cs) :
    ChildrenOK ctx d it cs := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have hrt : ∀ r cl, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl) →
      rootTop ctx (d + 2) it.source = some (official cl.row) := by
    intro r cl h'
    simp [rootTop, h']
  generalize topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h hrt
  split at h
  · obtain rfl := Except.ok.inj h
    exact ⟨by simp, List.Pairwise.nil⟩
  · rename_i aRef aCell hA
    split at h
    · cases h
    · rename_i asc hasc
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hflags
          have hcl : it.clean = none := by
            cases hc : it.clean with
            | none => rfl
            | some _ => exact absurd (Or.inl (by simp [hc])) hflags
          have hcb : it.cutBottom = false := by
            cases hb : it.cutBottom with
            | false => rfl
            | true => exact absurd (Or.inr (Or.inr hb)) hflags
          obtain rfl := Except.ok.inj h
          refine childrenOK_of_tags List.pairwise_lt_range _ 0 0 id (fun _ => 0) ?_ ?_ ?_ ?_
          · intro j _ C hC
            simp at hC
          · intro j _ r hr
            simp only [Rg] at hr
            exact ⟨hr.1, by simp, by simp, by simp⟩
          · intro j _ r hr
            simp only [Rg, hcl, hcb]
            exact ⟨mem_of_slot hr.1, by simp⟩
          · intro j _ j' _ hjj
            exact Or.inl hjj
      · -- ascending
        rename_i hnasc
        have hasc_true : asc = true := by simpa using hnasc
        subst hasc_true
        obtain ⟨ρRef, ρCell, rfl⟩ : ∃ r c, rho = some (r, c) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hasc
          | some p => exact ⟨p.1, p.2, rfl⟩
        have hrt' := hrt ρRef ρCell rfl
        have hC0slot : inRegion (d + 1) (slot (d + 2) it.source (height (d + 2)
            (official ρCell.row))) (official ρCell.row) = true :=
          mem_slot_height (rootTop_mem hrt')
        have hinvC0 := rootTop_slot hrt'
        have hHO : heightOf (d + 2) (some (ρRef, ρCell)) = height (d + 2) (official ρCell.row) := rfl
        simp only [hHO] at h
        generalize hhR : height (d + 2) (official ρCell.row) = hR at h hC0slot hinvC0
        generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hC at h
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        have he : ∀ (e : Int), (if d + 2 = 2 then (1 : Int) else 0) = e → e = 0 ∨ e = 1 := by
          intro e he
          split at he <;> omega
        split at h
        · rename_i hcl
          split at h
          · -- case 2: lift
            rename_i hcb
            have hcb' : it.cutBottom = false := by simpa using hcb
            generalize hLdef : ((hC : Int) - hR) * (ctx.block : Int) = L at h
            have hL0 : ctx.block = 0 → L = 0 := by intro h0; rw [← hLdef, h0]; simp
            generalize hedef : (if d + 2 = 2 then (1 : Int) else 0) = e at h
            obtain rfl := Except.ok.inj h
            exact case2_ok hcl hcb' (he e hedef) hL0 hC0slot hinvC0 _
          · -- case 3: cut bottom
            rename_i hcb
            have hcb' : it.cutBottom = true := by simpa using hcb
            generalize hedef : (if d + 2 = 2 then (1 : Int) else 0) = e at h
            obtain rfl := Except.ok.inj h
            exact case3_ok hcl hcb' (he e hedef) hrt' hC0slot hinvC0 _
        · -- case 4: a copied root row
          rename_i C hcl
          have hCC : official ρCell.row = C := by
            have := hI C hcl
            rw [hrt'] at this
            exact Option.some.inj this
          rw [hCC] at hC0slot hinvC0
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                exact case4_ok hcl hC0slot hinvC0 _

/-! ## Runs of items -/

/-- Flattening the results of `mapM` keeps a pairwise relation when the inputs are ordered. -/
theorem flatten_mapM_pairwise {α β ε : Type} {g : α → Except ε (List β)} (R : β → β → Prop)
    (Rng : α → β → Prop) :
    ∀ (xs : List α) (ys : List (List β)), xs.mapM g = .ok ys →
      (∀ x ∈ xs, ∀ l, g x = .ok l → l.Pairwise R ∧ ∀ b ∈ l, Rng x b) →
      xs.Pairwise (fun x x' => ∀ b b', Rng x b → Rng x' b' → R b b') →
      ys.flatten.Pairwise R ∧ ∀ b ∈ ys.flatten, ∃ x ∈ xs, Rng x b := by
  intro xs
  induction xs with
  | nil =>
      intro ys h _ _
      simp only [List.mapM_nil, pure, Except.pure] at h
      cases h
      simp
  | cons x xs ih =>
      intro ys h hone hpw
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i l hl
        split at h
        · cases h
        · rename_i ls hls
          cases h
          obtain ⟨hlR, hlRng⟩ := hone x (by simp) l hl
          obtain ⟨hpx, hpw'⟩ := List.pairwise_cons.mp hpw
          obtain ⟨ihR, ihRng⟩ := ih ls hls (fun x' hx' => hone x' (by simp [hx'])) hpw'
          refine ⟨?_, ?_⟩
          · rw [List.flatten_cons, List.pairwise_append]
            refine ⟨hlR, ihR, fun a ha b hb => ?_⟩
            obtain ⟨x', hx', hb'⟩ := ihRng b hb
            exact hpx x' hx' a b (hlRng a ha) hb'
          · intro b hb
            rw [List.flatten_cons, List.mem_append] at hb
            rcases hb with hb | hb
            · exact ⟨x, by simp, hlRng b hb⟩
            · obtain ⟨x', hx', hb'⟩ := ihRng b hb
              exact ⟨x', by simp [hx'], hb'⟩

theorem ole_of_rg {M : Mountain} {p q : Emit × Origin} {a b : Row → Prop}
    (hab : ∀ r r', a r → b r' → r ≤ r')
    (hp : ∃ c, cell? M p.2.src = some c ∧ a (official c.row))
    (hq : ∃ c, cell? M q.2.src = some c ∧ b (official c.row)) : OLe M p q := by
  intro c c' hc hc'
  obtain ⟨c1, hc1, ha⟩ := hp
  obtain ⟨c2, hc2, hb⟩ := hq
  rw [hc1] at hc
  rw [hc2] at hc'
  cases hc
  cases hc'
  exact hab _ _ ha hb

/-- **The emits of an item** have origins in its range and non-decreasing origin rows. -/
theorem runItemT_mono (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), Inv ctx d it →
      runItemT ctx d it = .ok ps → InRg ctx d it ps ∧ ps.Pairwise (OLe ctx.source)
  | 0, _, ps, _, h => by
      simp [runItemT, pure, Except.pure] at h
      subst h
      exact ⟨fun p hp => by simp at hp, List.Pairwise.nil⟩
  | 1, it, ps, hI, h => levelOneT_mono hI (by simpa [runItemT] using h)
  | d + 2, it, ps, hI, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hcs, hpw⟩ := childItems_mono hI hch
          obtain ⟨hR, hRng⟩ := flatten_mapM_pairwise (OLe ctx.source)
            (fun c p => ∃ cl, cell? ctx.source p.2.src = some cl ∧ Rg ctx (d + 1) c (official cl.row))
            children outs houts
            (fun c hc l hl => by
              obtain ⟨h1, h2⟩ := runItemT_mono ctx (d + 1) c l (hcs c hc).1 hl
              exact ⟨h2, h1⟩)
            (hpw.imp fun hab b b' hb hb' => ole_of_rg hab hb hb')
          refine ⟨fun p hp => ?_, hR⟩
          obtain ⟨c, hc, cl, hcl, hrg⟩ := hRng p hp
          exact ⟨cl, hcl, (hcs c hc).2 _ hrg⟩

/-! ## The lower items -/

theorem lowerItems_ordered (τ : Row) :
    (lowerItems τ).Pairwise (fun p q => ∀ a b, inRegion p.1 p.2.source a = true →
      inRegion q.1 q.2.source b = true → a < b) := by
  unfold lowerItems
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro k _
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro j j' hjj a b ha hb
    exact lt_of_slot_lt (d := k) ha hb hjj
  · rw [List.pairwise_reverse]
    refine List.pairwise_lt_range.imp ?_
    intro k' k hkk p hp q hq a b ha hb
    simp only [List.mem_map, List.mem_range] at hp hq
    obtain ⟨j, hj, rfl⟩ := hp
    obtain ⟨j', _, rfl⟩ := hq
    simp only at ha hb
    rw [inRegion_iff] at ha hb
    refine Row.lt_iff.mpr ⟨k, fun m hm => ?_, ?_⟩
    · rw [ha m (by omega), hb m (by omega), slot_coeff_high (by omega),
        slot_coeff_high (d := k') (by omega)]
    · rw [ha k (by omega), hb k (by omega), slot_coeff_at, slot_coeff_high (d := k') (by omega)]
      exact hj

/-- The lower part: origins below `τ`, non-decreasing origin rows. -/
theorem lowerT_mono {ctx : Context} {τ : Row} {ls : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok ls) :
    ls.Pairwise (OLe ctx.source) ∧
      ∀ p ∈ ls, ∃ c, cell? ctx.source p.2.src = some c ∧ official c.row < τ := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    obtain ⟨hR, hRng⟩ := flatten_mapM_pairwise (OLe ctx.source)
      (fun q p => ∃ cl, cell? ctx.source p.2.src = some cl ∧
        inRegion q.1 q.2.source (official cl.row) = true)
      (lowerItems τ) outs houts
      (fun q hq l hl => by
        have hinv : Inv ctx q.1 q.2 := by
          intro C hC
          simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
            List.mem_map] at hq
          obtain ⟨_, _, _, _, rfl⟩ := hq
          cases hC
        obtain ⟨h1, h2⟩ := runItemT_mono ctx q.1 q.2 l hinv hl
        refine ⟨h2, fun p hp => ?_⟩
        obtain ⟨cl, hcl, hrg⟩ := h1 p hp
        have hcl0 : q.2.clean = none := by
          simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
            List.mem_map] at hq
          obtain ⟨_, _, _, _, rfl⟩ := hq
          rfl
        refine ⟨cl, hcl, ?_⟩
        unfold Rg at hrg
        rw [hcl0] at hrg
        exact hrg.1)
      ((lowerItems_ordered τ).imp fun hab b b' hb hb' =>
        ole_of_rg (fun r r' hr hr' => le_of_lt (hab r r' hr hr')) hb hb')
    refine ⟨hR, fun p hp => ?_⟩
    obtain ⟨q, hq, cl, hcl, hin⟩ := hRng p hp
    exact ⟨cl, hcl, (lowerItems_below τ q hq).1 _ hin⟩

/-! ## The upper part and the whole column -/

theorem official_lt_of_index {M : Mountain} (hV : MountainValid M) {c a b : Nat} {x y : Cell}
    (hx : cell? M ⟨c, a⟩ = some x) (hy : cell? M ⟨c, b⟩ = some y) (ha : 1 ≤ a) (hab : a < b) :
    official x.row < official y.row :=
  Recon.official_strictMono (one_le_row hV hx ha) (cell_row_lt hV hx hy hab)

theorem upperT_mono {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    {us : List (Emit × Origin)} (h : upperT ctx τ = .ok us) :
    us.Pairwise (OLe ctx.source) ∧
      ∀ p ∈ us, ∃ c, cell? ctx.source p.2.src = some c ∧ τ ≤ official c.row := by
  unfold upperT at h
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ h
  set xs := (realNodes ctx.source (upperColumn ctx)).filter
    (fun p => decide (τ ≤ official p.2.row)) with hxs
  have hsrc : ∀ i (hi : i < us.length) (hi' : i < xs.length), us[i].2.src = xs[i].1 := by
    intro i hi hi'
    have := hall i hi' hi
    simp only [bind, Except.bind, pure, Except.pure] at this
    split at this
    · cases this
    · rw [← Except.ok.inj this]
      rfl
  have hmem : ∀ i (hi' : i < xs.length), xs[i] ∈ realNodes ctx.source (upperColumn ctx) ∧
      τ ≤ official xs[i].2.row := by
    intro i hi'
    have := List.mem_filter.mp (List.getElem_mem hi')
    exact ⟨this.1, by simpa using this.2⟩
  have hxpw : xs.Pairwise (fun p q => p.1.index < q.1.index) :=
    (Recon.realNodes_pairwise ctx.source (upperColumn ctx)).filter _
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij c c' hc hc'
    have hi' : i < xs.length := by omega
    have hj' : j < xs.length := by omega
    rw [hsrc i hi hi'] at hc
    rw [hsrc j hj hj'] at hc'
    obtain ⟨hci, hi1, hcelli⟩ := mem_realNodes (hmem i hi').1
    obtain ⟨hcj, _, hcellj⟩ := mem_realNodes (hmem j hj').1
    rw [hcelli] at hc
    rw [hcellj] at hc'
    cases hc
    cases hc'
    have hidx := List.pairwise_iff_getElem.mp hxpw i j hi' hj' hij
    have hx : cell? ctx.source ⟨upperColumn ctx, xs[i].1.index⟩ = some xs[i].2 := by
      rw [← hci]; exact hcelli
    have hy : cell? ctx.source ⟨upperColumn ctx, xs[j].1.index⟩ = some xs[j].2 := by
      rw [← hcj]; exact hcellj
    exact le_of_lt (official_lt_of_index hV hx hy hi1 hidx)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hi' : i < xs.length := by omega
    obtain ⟨_, _, hcelli⟩ := mem_realNodes (hmem i hi').1
    exact ⟨xs[i].2, by rw [hsrc i hi hi']; exact hcelli, (hmem i hi').2⟩

/-- **The origin rows of a copied column do not decrease.** -/
theorem emitsT_mono {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) : es.Pairwise (OLe ctx.source) := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i ls hls
    split at h
    · cases h
    · rename_i us hus
      cases h
      obtain ⟨hl, hlb⟩ := lowerT_mono hls
      obtain ⟨hu, hub⟩ := upperT_mono hV hus
      rw [List.pairwise_append]
      exact ⟨hl, hu, fun a ha b hb => ole_of_rg (fun r r' hr hr' => le_of_lt (lt_of_lt_of_le hr hr'))
        (hlb a ha) (hub b hb)⟩

end CopyMonoProof

open CopyMonoProof in
/-- **`CopyMono` holds.** -/
theorem copyMono : CopyMono := by
  intro s n D M out ρ R t hdat i _ _ y es _ _ hes k k' hk hk' hkk c c' hc hc'
  have hV := build_valid_of_success hdat.splice.build
  have hpw := emitsT_mono (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    hV hes
  rcases Nat.lt_or_eq_of_le hkk with hlt | heq
  · have hole := List.pairwise_iff_getElem.mp hpw k k' hk hk' hlt c c' hc hc'
    obtain ⟨_, hidx, _⟩ := emitsT_good hes es[k'] (List.getElem_mem hk')
    by_contra hn
    have hlt' := Recon.official_strictMono (one_le_row hV hc' hidx) (lt_of_not_ge hn)
    exact absurd hole (not_le.mpr hlt')
  · subst heq
    rw [hc] at hc'
    cases hc'
    exact le_refl _

/-- **`StartCopy` from the four open parts of the block profile.** -/
theorem startCopy_of_open (hA : CopyOrder) (hB : CopyEmitted) (hC2 : CopyFirst) (hT : CutTop) :
    StartCopy :=
  startCopy_of_parts hA hB copyMono hC2 hT

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.copyMono
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.startCopy_of_open
