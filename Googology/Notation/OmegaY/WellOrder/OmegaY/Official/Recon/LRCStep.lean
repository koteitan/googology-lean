/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCKids

set_option backward.do.legacy false

/-!
# One step of the simulation of the tree of `X` by the tree of `Y`

Two copy contexts `cX`, `cY` that differ only in the source column (`Pair`). An item `A` of the
tree of `X` and an item `B` of the tree of `Y` with the same target are *similar* (`Sim`) when
they are equal, or when one is plain and the other copies the root row `ρ` of its region
without a cut bottom, the plain one's column not ascending at `ρ` and the other's ascending
(`RPX`, `RPY`).

`step`: given similar items, the `j`-th child of `A` has a similar `j`-th child in `B`, when a
row `w` of the column of `Y` lies in its source region and the node `θ` (emitted by the child
`j' ∈ {j, j+1}` of `A`, with origin row `a`) satisfies `EmitOK`. If `j < j'` the children are
equal.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- Two copy contexts that differ only in the source column. -/
structure Pair (cX cY : Context) : Prop where
  src : cY.source = cX.source
  root : cY.rootColumn = cX.rootColumn
  block : cY.block = cX.block
  last : cY.lastColumn = cX.lastColumn
  bnd : ∀ d T, topIn cY.result cY.boundary d T = topIn cX.result cX.boundary d T
  blk : cX.block ≠ 0

/-- `X` plain, `Y` copies the root row. -/
def RPX (cX cY : Context) (d : Nat) (A B : Item) : Prop :=
  A.clean = none ∧ A.cutBottom = false ∧ B.source = A.source ∧ B.target = A.target ∧
    B.cutBottom = false ∧ ∃ ρr ρc, topIn cX.source cX.rootColumn d A.source = some (ρr, ρc) ∧
      B.clean = some (official ρc.row) ∧ ascends cX (some (ρr, ρc)) = .ok false ∧
      ascends cY (some (ρr, ρc)) = .ok true

/-- `X` copies the root row, `Y` plain. -/
def RPY (cX cY : Context) (d : Nat) (A B : Item) : Prop :=
  B.clean = none ∧ B.cutBottom = false ∧ B.source = A.source ∧ B.target = A.target ∧
    A.cutBottom = false ∧ ∃ ρr ρc, topIn cX.source cX.rootColumn d A.source = some (ρr, ρc) ∧
      A.clean = some (official ρc.row) ∧ ascends cX (some (ρr, ρc)) = .ok true ∧
      ascends cY (some (ρr, ρc)) = .ok false

def Sim (cX cY : Context) (d : Nat) (A B : Item) : Prop :=
  A = B ∨ RPX cX cY d A B ∨ RPY cX cY d A B

theorem Sim.source {cX cY : Context} {d : Nat} {A B : Item} (h : Sim cX cY d A B) :
    B.source = A.source := by
  rcases h with rfl | h | h
  · rfl
  · exact h.2.2.1
  · exact h.2.2.1

theorem Sim.target {cX cY : Context} {d : Nat} {A B : Item} (h : Sim cX cY d A B) :
    B.target = A.target := by
  rcases h with rfl | h | h
  · rfl
  · exact h.2.2.2.1
  · exact h.2.2.2.1

/-- The facts about the anchor row `a` (the origin row of `θ`) that the step uses. -/
structure Anch (cX cY : Context) (a : Row) : Prop where
  eq : ∀ d S ρr ρc, topIn cX.source cX.rootColumn (d + 2) S = some (ρr, ρc) →
    official ρc.row < a →
      (ascends cX (some (ρr, ρc)) = .ok true ↔ ascends cY (some (ρr, ρc)) = .ok true)
  le : ∀ d S ρr ρc, topIn cX.source cX.rootColumn (d + 2) S = some (ρr, ρc) →
    official ρc.row ≤ a → ascends cX (some (ρr, ρc)) = .ok true →
      ascends cY (some (ρr, ρc)) = .ok true
  gen : ∀ refx cx gx refy cy gy, nodeAt cX.source cX.x a = some (refx, cx) →
    generations cX.source cX.rootColumn a (cX.x + 1) refx cx 0 = .ok gx →
    nodeAt cX.source cY.x a = some (refy, cy) →
    generations cX.source cX.rootColumn a (cY.x + 1) refy cy 0 = .ok gy → gx = gy + 1

/-! ## Small facts -/

theorem ascends_bool {ctx : Context} {ρ : Option (Ref × Cell)} {b : Bool}
    (h : ascends ctx ρ = .ok b) : (ascends ctx ρ = .ok true ↔ b = true) := by
  rw [h]
  constructor
  · intro h'; exact Except.ok.inj h'
  · intro h'; rw [h']

theorem ascends_none' (ctx : Context) : ascends ctx none = .ok false := rfl

/-- A row in the slot `j` of `S` has coefficient `j`. -/
theorem coeff_of_slot {d : Nat} {S r : Row} {j : Nat}
    (h : inRegion (d + 1) (slot (d + 2) S j) r = true) : r.coeff d = j :=
  (inRegion_slot_iff.mp h).2

theorem region_of_slot {d : Nat} {S r : Row} {j : Nat}
    (h : inRegion (d + 1) (slot (d + 2) S j) r = true) : inRegion (d + 2) S r = true :=
  (inRegion_slot_iff.mp h).1

/-- Rows of a region compare by the height coefficient when it differs. -/
theorem lt_of_coeff_lt {d : Nat} {S r r' : Row} (hr : inRegion (d + 2) S r = true)
    (hr' : inRegion (d + 2) S r' = true) (h : r.coeff d < r'.coeff d) : r < r' := by
  refine Row.lt_iff.mpr ⟨d, ?_, h⟩
  intro q hq
  rw [inRegion_iff'.mp hr q (by omega), inRegion_iff'.mp hr' q (by omega)]

theorem slot_eq_of {d : Nat} {S : Row} {a b : Nat} (h : a = b) : slot d S a = slot d S b := by
  rw [h]

/-- What `EmitOK` says about an emit whose origin cell is `cθ`. -/
theorem eok_parts {M : Mountain} {cr d : Nat} {it : Item} {p : Emit × Origin} {cθ : Cell}
    (h : Inner.EmitOK M cr d it p) (hc : cell? M p.2.src = some cθ) :
    inRegion d it.source (official cθ.row) = true ∧
    (∀ C, it.clean = some C → it.cutBottom = false →
      official cθ.row ≤ C ∧ (Inner.isPlainO p.2 = true → official cθ.row < C)) ∧
    (∀ C, it.clean = some C → it.cutBottom = true →
      official cθ.row = C ∧ Inner.isCleanO p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → 2 ≤ d → ∀ r ρc,
      topIn M cr d it.source = some (r, ρc) →
        official ρc.row ≤ official cθ.row ∧
          (Inner.isPlainO p.2 = true → official ρc.row < official cθ.row)) := by
  obtain ⟨_, c, hc', h1, h2, h3, h4⟩ := h
  rw [hc] at hc'
  cases hc'
  exact ⟨h1, h2, h3, h4⟩

/-- The source region of a child is a slot of the source region. -/
theorem child_src {ctx : Context} {d : Nat} {A : Item} {cs : List Item}
    (h : childItems ctx (d + 2) A = .ok cs) {j : Nat} (hj : j < cs.length) :
    ∃ σ, cs[j].source = slot (d + 2) A.source σ :=
  LegJump.childItems_source h _ (List.getElem_mem hj)

/-- The top of the column of `Y` in a region holding one of its rows. -/
theorem topY {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c d : Nat} {S : Row}
    {wq : Ref × Cell} (hwq : wq ∈ realNodes M c) (hw : inRegion (d + 2) S (official wq.2.row) = true) :
    ∃ ay : Ref × Cell, topIn M c (d + 2) S = some ay ∧
      (official wq.2.row).coeff d ≤ height (d + 2) (official ay.2.row) := by
  obtain ⟨r, c', h1, h2⟩ := LowerLeftProof.top_ge hb hwq hw
  exact ⟨(r, c'), h1, h2⟩

/-- The source index of a child of case 2. -/
theorem c2_source (d : Nat) (S T : Row) (i hR : Nat) (lift : Int) (C : Row) (j : Nat) :
    (j < hR ∧ (c2 d S T i hR lift C j).source = slot d S j) ∨
    (hR ≤ j ∧ (j : Int) < hR + lift + (if d = 2 then 1 else 0) ∧
      (c2 d S T i hR lift C j).source = slot d S hR) ∨
    (hR ≤ j ∧ hR + lift + (if d = 2 then 1 else 0) ≤ (j : Int) ∧
      (c2 d S T i hR lift C j).source = slot d S ((j : Int) - lift).toNat) := by
  unfold c2
  by_cases h1 : j < hR
  · left; simp [h1]
  · by_cases h2 : (j : Int) < hR + lift + (if d = 2 then 1 else 0)
    · right; left; simp [h1, h2]; omega
    · right; right; simp [h1, h2]; omega

theorem c2_low {d : Nat} {S T : Row} {i hR : Nat} {lift : Int} {C : Row} {j : Nat} (h : j < hR) :
    c2 d S T i hR lift C j = k1 d S T j := by
  unfold c2 k1; simp [h]

theorem c2_root {d : Nat} {S T : Row} {i hR : Nat} {lift : Int} {C : Row}
    (h : 0 < lift + (if d = 2 then 1 else 0)) :
    c2 d S T i hR lift C hR = ⟨slot d S hR, slot d T hR, some C, 0, false⟩ := by
  unfold c2
  have h2 : (hR : Int) < hR + lift + (if d = 2 then 1 else 0) := by omega
  simp [h2]

theorem e_val' (d : Nat) : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
    ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · left; subst h; simp
  · right; refine ⟨?_, h⟩; rw [if_neg (by omega)]

/-- The three kinds of children of case 2. -/
theorem c2_cases {d : Nat} {S T : Row} {i hR : Nat} {lift : Int} {C : Row} (j : Nat) :
    (j < hR ∧ c2 d S T i hR lift C j = k1 d S T j) ∨
    (hR ≤ j ∧ (j : Int) < hR + lift + (if d = 2 then 1 else 0) ∧
      c2 d S T i hR lift C j = ⟨slot d S hR, slot d T j, some C, 0, decide (hR < j)⟩) ∨
    (hR ≤ j ∧ hR + lift + (if d = 2 then 1 else 0) ≤ (j : Int) ∧
      ((c2 d S T i hR lift C j).source = slot d S ((j : Int) - lift).toNat ∧
        (c2 d S T i hR lift C j).clean = none ∧
        (c2 d S T i hR lift C j).cutBottom = decide (i ≠ 0 ∧ (j : Int) = hR + lift))) := by
  unfold c2 k1
  by_cases h1 : j < hR
  · left; simp [h1]
  · by_cases h2 : (j : Int) < hR + lift + (if d = 2 then 1 else 0)
    · right; left; simp [h1, h2]; omega
    · right; right; simp [h1, h2]; omega

/-- **Step, equal plain items without a cut bottom.** -/
theorem step_eq_plain {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A : Item} {csX csY : List Item} (hcl : A.clean = none) (hcb : A.cutBottom = false)
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) A = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj1 : j' ≤ j + 1) (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true)
    (hMDY : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDX : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source)) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨σ, hσ⟩ := child_src hcsX hj
  have hw' := hw
  rw [hσ] at hw'
  have hwA := region_of_slot hw'
  have hwσ := coeff_of_slot hw'
  obtain ⟨ay, hay, hayh⟩ := topY hb hwq hwA
  have hayY : topIn cY.source cY.x (d + 2) A.source = some ay := by rw [P.src]; exact hay
  obtain ⟨bX, hbX⟩ := childItems_asc hcsX hax
  obtain ⟨bY, hbY⟩ := childItems_asc hcsY hayY
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) A.source =
      topIn cX.source cX.rootColumn (d + 2) A.source := by rw [P.src, P.root]
  rw [hrhoY] at hbY
  obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
  rw [hθa] at haReg
  have hblk := P.blk
  cases bX with
  | false =>
    obtain ⟨_, _, hlX, hgX⟩ := kids1 hcsX hax hbX
    have hjσ : σ = j := by
      have := hgX j hj
      rw [this] at hσ
      exact (LowerLeftProof.slot_inj hσ).symm
    have hj'a : a.coeff d = j' := by
      have := hgX j' hj'
      rw [this] at haReg
      exact coeff_of_slot haReg
    cases bY with
    | false =>
      have hbY' : ascends cY (topIn cY.source cY.rootColumn (d + 2) A.source) = .ok false := by
        rw [hrhoY]; exact hbY
      obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY'
      have hjY : j < csY.length := by
        rw [hlY]; have : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
        omega
      refine ⟨hjY, Or.inl ?_, fun _ => ?_⟩ <;>
      · rw [hgX j hj, hgY j hjY]
    | true =>
      -- `Y` ascends, `X` does not: the root top is at or above `a`
      cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
      | none => rw [hρ] at hbY; cases hbY
      | some ρ =>
        obtain ⟨r, cl⟩ := ρ
        rw [hρ] at hbX hbY
        have hle : a ≤ official cl.row := by
          by_contra hn
          have := (H.eq d A.source r cl hρ (lt_of_not_ge hn)).mpr hbY
          rw [hbX] at this; cases this
        have hρin := topIn_inRegion hρ
        have haA : inRegion (d + 2) A.source a = true := by
          have := hgX j' hj'
          rw [this] at haReg
          exact region_of_slot haReg
        have hjR : j' ≤ height (d + 2) (official cl.row) := by
          have := coeff_le_of_inRegion haA hρin hle
          show j' ≤ (official cl.row).coeff d
          omega
        have hMD := hMDY r cl hρ hbY
        have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
          rw [hrhoY]; exact hρ
        obtain ⟨hlY, hgY⟩ := kids2 hcsY hcl hcb hayY hrhoY' hbY
        have hlast : topIn cY.source cY.lastColumn (d + 2) A.source =
            topIn cX.source cX.lastColumn (d + 2) A.source := by rw [P.src, P.last]
        rw [hlast, P.block] at hlY hgY
        have hlift : (1 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
            A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
              (cX.block : Int) := by
          have h1 : (1 : Int) ≤ (cX.block : Int) := by omega
          have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
              A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int) := by
            omega
          have := Int.mul_le_mul h2 h1 (by omega) (by omega)
          simpa using this
        have hjY : j < csY.length := by
          rw [hlY]
          have : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
          omega
        refine ⟨hjY, ?_, fun hlt => ?_⟩
        · rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
          · left
            rw [hgX j hj, hgY j hjY, c2_low hjr]
          · have hjeq : j = height (d + 2) (official cl.row) := by omega
            right; left
            rw [hgX j hj, hgY j hjY]
            subst hjeq
            rw [c2_root (by split <;> omega)]
            refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, ?_, ?_⟩
            · exact Inner.topIn_slot hρ
            · exact hbX
            · exact hbY
        · have hjr : j < height (d + 2) (official cl.row) := by omega
          rw [hgX j hj, hgY j hjY, c2_low hjr]
  | true =>
    cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
    | none => rw [hρ] at hbX; cases hbX
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hbX hbY
      have hρin := topIn_inRegion hρ
      have hMD := hMDX r cl hρ hbX
      obtain ⟨hlX, hgX⟩ := kids2 hcsX hcl hcb hax hρ hbX
      have hlast : topIn cY.source cY.lastColumn (d + 2) A.source =
          topIn cX.source cX.lastColumn (d + 2) A.source := by rw [P.src, P.last]
      have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
        rw [hrhoY]; exact hρ
      have hay' : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
      have hHR : height (d + 2) (official cl.row) = (official cl.row).coeff d := rfl
      have hlift : (1 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
          A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
            (cX.block : Int) := by
        have h1 : (1 : Int) ≤ (cX.block : Int) := by omega
        have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
            A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int) := by
          omega
        have := Int.mul_le_mul h2 h1 (by omega) (by omega)
        simpa using this
      have hee := e_val' d
      -- name the parameters
      generalize hLf : (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat)
        : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) * (cX.block : Int) = lift
        at hlX hgX hlift
      cases bY with
      | true =>
        obtain ⟨hlY, hgY⟩ := kids2 hcsY hcl hcb hayY hrhoY' hbY
        rw [hlast, P.block, hLf] at hlY hgY
        have hjY : j < csY.length := by
          rw [hlY]
          have hs := hgX j hj
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · have e : slot (d + 2) A.source j = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h2]; rfl
            have := LowerLeftProof.slot_inj e; omega
          · have e : slot (d + 2) A.source (height (d + 2) (official cl.row)) =
                slot (d + 2) A.source σ := by rw [← hσ, hs, h3]
            have := LowerLeftProof.slot_inj e
            rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h2 <;> omega
          · have e : slot (d + 2) A.source ((j : Int) - lift).toNat = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h3.1]
            have := LowerLeftProof.slot_inj e; omega
        refine ⟨hjY, Or.inl ?_, fun _ => ?_⟩ <;>
        · rw [hgX j hj, hgY j hjY]
      | false =>
        -- `X` ascends, `Y` does not: the root top is above `a`
        have hlt : a < official cl.row := by
          by_contra hn
          have := H.le d A.source r cl hρ (not_lt.mp hn) hbX
          rw [hbY] at this; cases this
        have haA : inRegion (d + 2) A.source a = true := by
          obtain ⟨σ', hσ'⟩ := child_src hcsX hj'
          rw [hσ'] at haReg
          exact region_of_slot haReg
        have haρ : a.coeff d ≤ (official cl.row).coeff d := coeff_le_of_inRegion haA hρin hlt.le
        obtain ⟨_, _, hcut, hcb'⟩ := eok_parts hEc hcθ
        rw [hθa] at hcut hcb'
        have hj'R : j' ≤ height (d + 2) (official cl.row) := by
          by_contra hn
          have hs := hgX j' hj'
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j' with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · omega
          · -- a gap copy of `ρ`
            have hcl3 : csX[j'].clean = some (official cl.row) := by rw [hs, h3]
            have hcb3 : csX[j'].cutBottom = true := by rw [hs, h3]; simp; omega
            have := (hcut _ hcl3 hcb3).1
            rw [this] at hlt; exact lt_irrefl _ hlt
          · rw [← hs] at h3
            obtain ⟨hs3, hcl3, hcb3⟩ := h3
            by_cases hq : (j' : Int) = height (d + 2) (official cl.row) + lift
            · -- the lifted slot of `ρ`: its root top is `ρ`
              have hd1 : 2 ≤ d + 1 := by
                rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
                · rw [he1] at h2; omega
                · omega
              have hcbt : csX[j'].cutBottom = true := by rw [hcb3]; simp; omega
              have hjeq : ((j' : Int) - lift).toNat = height (d + 2) (official cl.row) := by omega
              rw [hjeq] at hs3
              have htop : topIn cX.source cX.rootColumn (d + 1) csX[j'].source = some (r, cl) := by
                rw [hs3]; exact Inner.topIn_slot hρ
              have := (hcb' hcl3 hcbt hd1 r cl htop).1
              exact absurd hlt (not_lt.mpr this)
            · rw [hs3] at haReg
              have := coeff_of_slot haReg
              rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
              · rw [he1] at h2; omega
              · rw [he1] at h2; omega
        have hbY' : ascends cY (topIn cY.source cY.rootColumn (d + 2) A.source) = .ok false := by
          rw [hrhoY, hρ]; exact hbY
        obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY'
        have hjR : j ≤ height (d + 2) (official cl.row) := by omega
        have hσj : σ = j := by
          have hs := hgX j hj
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · have e : slot (d + 2) A.source j = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h2]; rfl
            exact (LowerLeftProof.slot_inj e).symm
          · have e : slot (d + 2) A.source (height (d + 2) (official cl.row)) =
                slot (d + 2) A.source σ := by rw [← hσ, hs, h3]
            have := LowerLeftProof.slot_inj e; omega
          · rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
            · rw [he1] at h2; omega
            · rw [he1] at h2; omega
        have hjY : j < csY.length := by rw [hlY]; omega
        refine ⟨hjY, ?_, fun hlt' => ?_⟩
        · rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
          · left
            rw [hgX j hj, hgY j hjY, c2_low hjr]
          · have hjeq : j = height (d + 2) (official cl.row) := by omega
            right; right
            rw [hgX j hj, hgY j hjY]
            subst hjeq
            rw [c2_root (by rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] <;> omega)]
            refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, hbX, hbY⟩
            exact Inner.topIn_slot hρ
        · have hjr : j < height (d + 2) (official cl.row) := by omega
          rw [hgX j hj, hgY j hjY, c2_low hjr]

/-- The two kinds of children of case 3. -/
theorem c3_cases {d : Nat} {S T : Row} {hR hB : Nat} {C : Row} (j : Nat) :
    ((j : Int) < hB + hR + (if d = 2 then 1 else 0) ∧
      c3 d S T hR hB C j = ⟨slot d S hR, slot d T (j - hR), some C, 0, true⟩) ∨
    (hB + hR + (if d = 2 then 1 else 0) ≤ (j : Int) ∧
      c3 d S T hR hB C j = ⟨slot d S (j - hB), slot d T (j - hR), none, 0, decide (j = hB + hR)⟩) := by
  unfold c3
  by_cases h : (j : Int) < hB + hR + (if d = 2 then 1 else 0)
  · left; simp [h]
  · right; simp [h]; omega

/-- The kinds of children of case 4 without a cut bottom. -/
theorem c4_cases {d : Nat} {S T : Row} {hR hB off : Nat} {C : Row} (j : Nat) :
    (j < hR ∧ c4 d S T hR hB off false C j = k1 d S T j) ∨
    (j = hR ∧ c4 d S T hR hB off false C j =
      ⟨slot d S hR, slot d T hR, some C, ((j : Int) - hB + off).toNat, false⟩) ∨
    (hR < j ∧ (c4 d S T hR hB off false C j).clean = some C ∧
      (c4 d S T hR hB off false C j).cutBottom = true) := by
  unfold c4 k1
  rcases Nat.lt_trichotomy j hR with h | h | h
  · left; simp [h]
  · right; left; subst h; simp
  · right; right; simp [show ¬ j < hR by omega, h]

theorem c4_cut {d : Nat} {S T : Row} {hR hB off : Nat} {C : Row} (j : Nat) :
    (c4 d S T hR hB off true C j).clean = some C ∧ (c4 d S T hR hB off true C j).cutBottom = true := by
  unfold c4; simp

/-- **Step, equal plain items with a cut bottom.** -/
theorem step_eq_cb {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source)
    {d : Nat} {A : Item} {csX csY : List Item} (hcl : A.clean = none) (hcb : A.cutBottom = true)
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) A = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j : Nat} (hj : j < csX.length)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) csX[j].source (official wq.2.row) = true) :
    ∃ hjY : j < csY.length, csX[j] = csY[j] := by
  obtain ⟨σ, hσ⟩ := child_src hcsX hj
  have hw' := hw
  rw [hσ] at hw'
  have hwA := region_of_slot hw'
  have hwσ := coeff_of_slot hw'
  obtain ⟨ay, hay, hayh⟩ := topY hb hwq hwA
  have hayY : topIn cY.source cY.x (d + 2) A.source = some ay := by rw [P.src]; exact hay
  have hbX := asc_true_of_kind hcsX hax (Or.inr hcb)
  have hbY := asc_true_of_kind hcsY hayY (Or.inr hcb)
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) A.source =
      topIn cX.source cX.rootColumn (d + 2) A.source := by rw [P.src, P.root]
  rw [hrhoY] at hbY
  cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
  | none => rw [hρ] at hbX; cases hbX
  | some ρ =>
    obtain ⟨r, cl⟩ := ρ
    rw [hρ] at hbX hbY
    have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
      rw [hrhoY]; exact hρ
    have hblkY : cY.block ≠ 0 := by rw [P.block]; exact P.blk
    obtain ⟨hlX, hgX⟩ := kids3 hcsX hcl hcb P.blk hax hρ hbX
    obtain ⟨hlY, hgY⟩ := kids3 hcsY hcl hcb hblkY hayY hrhoY' hbY
    rw [P.bnd] at hlY hgY
    have hay' : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
    have hee := e_val' d
    have hjY : j < csY.length := by
      rw [hlY]
      have hs := hgX j hj
      rcases c3_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official cl.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (C := official cl.row) (j + height (d + 2) (official cl.row)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e : slot (d + 2) A.source (height (d + 2) (official cl.row)) =
            slot (d + 2) A.source σ := by rw [← hσ, hs, h2]
        have := LowerLeftProof.slot_inj e
        rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h1 <;> omega
      · have e : slot (d + 2) A.source (j + height (d + 2) (official cl.row) -
            heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target)) =
            slot (d + 2) A.source σ := by rw [← hσ, hs, h2]
        have := LowerLeftProof.slot_inj e
        rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h1 <;> omega
    exact ⟨hjY, by rw [hgX j hj, hgY j hjY]⟩

/-- **Step, equal items that copy a root row.** -/
theorem step_eq_clean {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A : Item} {csX csY : List Item} {C : Row} (hcl : A.clean = some C)
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) A = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEA : Inner.EmitOK cX.source cX.rootColumn (d + 2) A θp)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 2) A.source (official wq.2.row) = true)
    (hnt : C = a → j + 1 < csX.length)
    (hMHY : ∀ r cl csRef csc g, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      A.cutBottom = false → nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target) + g) :
    ∃ hjY : j < csY.length, csX[j]'(by omega) = csY[j] := by
  have hj : j < csX.length := by omega
  obtain ⟨ay, hay, _⟩ := topY hb hwq hw
  have hayY : topIn cY.source cY.x (d + 2) A.source = some ay := by rw [P.src]; exact hay
  have hbX := asc_true_of_kind hcsX hax (Or.inl (by rw [hcl]; simp))
  have hbY := asc_true_of_kind hcsY hayY (Or.inl (by rw [hcl]; simp))
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) A.source =
      topIn cX.source cX.rootColumn (d + 2) A.source := by rw [P.src, P.root]
  rw [hrhoY] at hbY
  cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
  | none => rw [hρ] at hbX; cases hbX
  | some ρ =>
    obtain ⟨r, cl⟩ := ρ
    rw [hρ] at hbX hbY
    have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
      rw [hrhoY]; exact hρ
    have hblkY : cY.block ≠ 0 := by rw [P.block]; exact P.blk
    obtain ⟨xr, xc, gx, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hcl P.blk hax hρ hbX
    obtain ⟨yr, yc, gy, hyn, hyg, hyb, hlY, hgY⟩ := kids4 hcsY hcl hblkY hayY hrhoY' hbY
    rw [P.bnd] at hyb hlY hgY
    rw [P.src] at hyn
    rw [P.src, P.root] at hyg
    by_cases hCa : C = a
    · subst hCa
      have hg := H.gen xr xc gx yr yc gy hxn hxg hyn hyg
      have hjY : j < csY.length := by
        have := hnt rfl
        rw [hlX] at this; rw [hlY]; omega
      exact ⟨hjY, by rw [hgX j hj, hgY j hjY]⟩
    · -- `θ` is not a copy of `C`: `A` has no cut bottom and `θ` is in a child `≤ h_ρ`
      obtain ⟨_, _, hcutA, _⟩ := eok_parts hEA hcθ
      have hcbA : A.cutBottom = false := by
        cases h : A.cutBottom with
        | false => rfl
        | true => exact absurd ((hcutA C hcl h).1.symm.trans hθa) hCa
      obtain ⟨_, _, hcutc, _⟩ := eok_parts hEc hcθ
      have hj'R : j' ≤ height (d + 2) (official cl.row) := by
        by_contra hn
        have hs := hgX j' hj'
        rw [hcbA] at hs
        rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
          (hR := height (d + 2) (official cl.row))
          (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
          (off := A.offset) (C := C) j' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2, h3⟩
        · omega
        · omega
        · rw [← hs] at h2 h3
          exact hCa ((hcutc C h2 h3).1.symm.trans hθa)
      have hoff := (hyb hcbA).2
      have hMH := hMHY r cl yr yc gy hρ hcbA hyn hyg
      have hjY : j < csY.length := by
        rw [hlY, hoff]; omega
      exact ⟨hjY, by rw [hgX j hj, hgY j hjY]⟩

/-- **Step, `X` plain and `Y` copying the root row.** -/
theorem step_rpx {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hrp : RPX cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 2) A.source (official wq.2.row) = true)
    (hMHY : ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨hAcl, hAcb, hBs, hBt, hBcb, r, cl, hρ, hBcl, haX, haY⟩ := hrp
  have hρin := topIn_inRegion hρ
  have hle : a ≤ official cl.row := by
    by_contra hn
    have := (H.eq d A.source r cl hρ (lt_of_not_ge hn)).mpr haY
    rw [haX] at this; cases this
  have hbX : ascends cX (topIn cX.source cX.rootColumn (d + 2) A.source) = .ok false := by
    rw [hρ]; exact haX
  obtain ⟨_, _, hlX, hgX⟩ := kids1 hcsX hax hbX
  obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
  rw [hθa, hgX j' hj'] at haReg
  have haj' : a.coeff d = j' := coeff_of_slot haReg
  have haA := region_of_slot haReg
  have hj'R : j' ≤ height (d + 2) (official cl.row) := by
    have := coeff_le_of_inRegion haA hρin hle
    show j' ≤ (official cl.row).coeff d
    omega
  obtain ⟨ay, hay, _⟩ := topY hb hwq hw
  have hayY : topIn cY.source cY.x (d + 2) B.source = some ay := by rw [P.src, hBs]; exact hay
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) B.source = some (r, cl) := by
    rw [P.src, P.root, hBs]; exact hρ
  have hblkY : cY.block ≠ 0 := by rw [P.block]; exact P.blk
  obtain ⟨yr, yc, gy, hyn, hyg, hyb, hlY, hgY⟩ := kids4 hcsY hBcl hblkY hayY hrhoY haY
  rw [P.bnd] at hyb hlY hgY
  rw [P.src] at hyn
  rw [P.src, P.root] at hyg
  have hoff := (hyb hBcb).2
  have hMH := hMHY _ r cl yr yc gy hBcl hBcb (by rw [hBs]; exact hρ) hyn hyg
  have hjY : j < csY.length := by rw [hlY, hoff]; omega
  rw [hBcb, hoff, hBs, hBt] at hgY
  have hkj : ∀ hjr : j < height (d + 2) (official cl.row), csX[j] = csY[j] := by
    intro hjr
    rw [hgX j hj, hgY j hjY]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := 0) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h2.symm
    · omega
    · omega
  refine ⟨hjY, ?_, fun hlt => hkj (by omega)⟩
  rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
  · exact Or.inl (hkj hjr)
  · have hjeq : j = height (d + 2) (official cl.row) := by omega
    right; left
    have hY := hgY j hjY
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := 0) (C := official cl.row) j with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · rw [hgX j hj, hY, h2]
      subst hjeq
      refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, haX, haY⟩
      exact Inner.topIn_slot hρ
    · omega

/-- **Step, `X` copying the root row and `Y` plain.** -/
theorem step_rpy {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hrp : RPY cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨hBcl, hBcb, hBs, hBt, hAcb, r, cl, hρ, hAcl, haX, haY⟩ := hrp
  have hlt : a < official cl.row := by
    by_contra hn
    have := H.le d A.source r cl hρ (not_lt.mp hn) haX
    rw [haY] at this; cases this
  obtain ⟨xr, xc, gx, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hAcl P.blk hax hρ haX
  rw [hAcb] at hgX
  have hxoff := (hxb hAcb).2
  obtain ⟨_, _, hcutc, _⟩ := eok_parts hEc hcθ
  have hj'R : j' ≤ height (d + 2) (official cl.row) := by
    by_contra hn
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2, h3⟩
    · omega
    · omega
    · rw [← hgX j' hj'] at h2 h3
      have := (hcutc _ h2 h3).1
      rw [hθa] at this
      rw [this] at hlt; exact lt_irrefl _ hlt
  -- the source slot of the child `j` is `j`
  have hsj : csX[j].source = slot (d + 2) A.source j := by
    rw [hgX j hj]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [h2]; rfl
    · rw [h2, h1]
    · omega
  have hw' := hw
  rw [hsj] at hw'
  have hwA := region_of_slot hw'
  have hwj := coeff_of_slot hw'
  obtain ⟨ay, hay, hayh⟩ := topY hb hwq hwA
  have hayY : topIn cY.source cY.x (d + 2) B.source = some ay := by rw [P.src, hBs]; exact hay
  have hbY : ascends cY (topIn cY.source cY.rootColumn (d + 2) B.source) = .ok false := by
    rw [P.src, P.root, hBs, hρ]; exact haY
  obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY
  rw [hBs, hBt] at hgY
  have hay' : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
  have hjY : j < csY.length := by rw [hlY]; omega
  have hkj : ∀ hjr : j < height (d + 2) (official cl.row), csX[j] = csY[j] := by
    intro hjr
    rw [hgX j hj, hgY j hjY]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h2
    · omega
    · omega
  refine ⟨hjY, ?_, fun hlt' => hkj (by omega)⟩
  rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
  · exact Or.inl (hkj hjr)
  · have hjeq : j = height (d + 2) (official cl.row) := by omega
    right; right
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · rw [hgX j hj, hgY j hjY, h2]
      subst hjeq
      refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, haX, haY⟩
      exact Inner.topIn_slot hρ
    · omega

/-- **One step of the simulation.** -/
theorem step {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hsim : Sim cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj1 : j' ≤ j + 1) (hj' : j' < csX.length)
    (hEA : Inner.EmitOK cX.source cX.rootColumn (d + 2) A θp)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true)
    (hnt : ∀ C, A.clean = some C → C = a → j + 1 < csX.length)
    (hMDX : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDY : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMHY : ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  have hwA : inRegion (d + 2) A.source (official wq.2.row) = true := by
    obtain ⟨σ, hσ⟩ := child_src hcsX hj
    rw [hσ] at hw
    exact region_of_slot hw
  rcases hsim with rfl | hrp | hrp
  · cases hcl : A.clean with
    | none =>
      cases hcb : A.cutBottom with
      | false =>
        exact step_eq_plain P hb H hcθ hθa hcl hcb hcsX hcsY hax hjj hj1 hj' hEc hwq hw hMDY hMDX
      | true =>
        obtain ⟨hjY, he⟩ := step_eq_cb P hb hcl hcb hcsX hcsY hax hj hwq hw
        exact ⟨hjY, Or.inl he, fun _ => he⟩
    | some C =>
      obtain ⟨hjY, he⟩ := step_eq_clean P hb H hcθ hθa hcl hcsX hcsY hax hjj hj' hEA hEc hwq hwA
        (hnt C hcl) (fun r cl csRef csc g hρ hcb' hn hg =>
          hMHY C r cl csRef csc g hcl hcb' hρ hn hg)
      exact ⟨hjY, Or.inl he, fun _ => he⟩
  · exact step_rpx P hb H hcθ hθa hrp hcsX hcsY hax hjj hj' hEc hwq hwA hMHY
  · exact step_rpy P hb H hcθ hθa hrp hcsX hcsY hax hjj hj' hEc hwq hw

end OmegaY.Official.Recon.LRC
