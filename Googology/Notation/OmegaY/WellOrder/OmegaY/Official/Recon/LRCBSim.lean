/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBSim.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCCopy

set_option backward.do.legacy false

/-!
# The boundary column holds the aligned lifting items of `X`

For the boundary case of the lower row law, the parent column is the boundary column
`B = c_r + w·(i+1)` of the block `i + 1` of `X`, the copy of `x₀` in block `i`. This file shows
that every lifting item `K` of the tree of `X` (plain, no cut bottom, `x` ascending at the root
top, hence aligned) is an item of the tree of `B` as well (`simB_chain`), so that the top of `B`
in the target of `K` has height `h_κ + (h_κ - h_ρ)·i` (`bnd_lift`, in `LRCBLift.lean`).

The simulation `SimB` along the aligned path of `K`: equal items, two copies of the same root
row (offsets may differ), `X` plain and `B` copying the root row `ρ` (`x` does not ascend at
`ρ`, `x₀` always does: `x0_asc`), or `X` copying `ρ` and `B` plain (block `0`, no lift).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- **The last column ascends at every node of the root column below `τ`** (the argument of
`LowerBndSrc.x0_ascends`). -/
theorem x0_asc {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hT : Top s M t root)
    {ctx : Context} (hsrc : ctx.source = M) (hx : ctx.x = M.size - 1)
    (hrc : ctx.rootColumn = root.column) {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M root.column)
    (hlt : official ρ.2.row < official t.row) : ascends ctx (some ρ) = .ok true := by
  have hb := hT.build
  obtain ⟨q, hq, hqt⟩ := top_mem hT
  have hne : official q.2.row ≠ 0 := by rw [hqt]; exact hT.real
  have hlq : leftColumn q.2 = .ok root.column := by rw [hqt]; exact leftColumn_of hT.left
  obtain ⟨σ, l, ps, _, _, _, hl', _, hps, _, _⟩ := source_edge hb hq hne
  rw [hlq] at hl'
  obtain rfl := Except.ok.inj hl'
  have hq' : q ∈ realNodes M ctx.x := by rw [hx]; exact hq
  refine ascends_of_root_leg hb hsrc hq' hne (by rw [hrc]; exact hlq) (by rw [hrc]; exact hps)
    (by rw [hrc]; exact hρ) ?_
  apply hps.2.2 _ (List.mem_map.mpr ⟨ρ, hρ, rfl⟩)
  rw [hqt]
  exact hlt

/-- **Case 4 in any block.** -/
theorem kids4b {ctx : Context} {d : Nat} {A : Item} {cs : List Item} {C : Row}
    (h : childItems ctx d A = .ok cs) (hcl : A.clean = some C)
    {a : Ref × Cell} (hx : topIn ctx.source ctx.x d A.source = some a)
    {r : Ref} {cl : Cell} (hrho : topIn ctx.source ctx.rootColumn d A.source = some (r, cl))
    (hasc : ascends ctx (some (r, cl)) = .ok true) :
    ∃ csRef csc g, nodeAt ctx.source ctx.x C = some (csRef, csc) ∧
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef csc 0 = .ok g ∧
      (A.cutBottom = false →
        (topIn ctx.result ctx.boundary d A.target).isSome ∧ A.offset = 0) ∧
      cs.length = ((if ctx.block = 0 then ((height d (official a.2.row) : Nat) : Int)
          else ((heightOf d (topIn ctx.result ctx.boundary d A.target) : Nat) : Int) + (g : Int)
            - (A.offset : Int)) + 1).toNat ∧
      ∀ j (hj : j < cs.length), cs[j] = c4 d A.source A.target (height d (official cl.row))
        (heightOf d (topIn ctx.result ctx.boundary d A.target)) A.offset A.cutBottom C j := by
  obtain ⟨csRef, csc, g, hn, hg, hb, hl⟩ := childItems_case4 h hcl hx hrho hasc
  subst hl
  exact ⟨csRef, csc, g, hn, hg, hb, by simp, fun j hj => by simp⟩

/-! ## The relation -/

/-- `X` and `B` items with the same target region along the aligned path. -/
def SimB (cX cB : Context) (d : Nat) (A A' : Item) : Prop :=
  A' = A ∨
  (A'.source = A.source ∧ A'.target = A.target ∧ A.cutBottom = false ∧ A'.cutBottom = false ∧
    ∃ C, A.clean = some C ∧ A'.clean = some C) ∨
  (A.clean = none ∧ A.cutBottom = false ∧ A'.source = A.source ∧ A'.target = A.target ∧
    A'.cutBottom = false ∧ ∃ ρr ρc, topIn cX.source cX.rootColumn d A.source = some (ρr, ρc) ∧
      A'.clean = some (official ρc.row) ∧ ascends cX (some (ρr, ρc)) = .ok false) ∨
  (A'.clean = none ∧ A'.cutBottom = false ∧ A'.source = A.source ∧ A'.target = A.target ∧
    A.cutBottom = false ∧ cB.block = 0 ∧ ∃ ρr ρc,
      topIn cX.source cX.rootColumn d A.source = some (ρr, ρc) ∧ A.clean = some (official ρc.row))

theorem SimB.source {cX cB : Context} {d : Nat} {A A' : Item} (h : SimB cX cB d A A') :
    A'.source = A.source := by
  rcases h with rfl | h | h | h
  · rfl
  · exact h.1
  · exact h.2.2.1
  · exact h.2.2.1

theorem SimB.target {cX cB : Context} {d : Nat} {A A' : Item} (h : SimB cX cB d A A') :
    A'.target = A.target := by
  rcases h with rfl | h | h | h
  · rfl
  · exact h.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.1

/-! ## One step -/

theorem k1_eq_c2_low {d : Nat} {S T : Row} {i hR : Nat} {lift : Int} {C : Row} {j : Nat}
    (h : j < hR) : k1 d S T j = c2 d S T i hR lift C j := (c2_low h).symm

theorem c2_target (d : Nat) (S T : Row) (i hR : Nat) (lift : Int) (C : Row) (j : Nat) :
    (c2 d S T i hR lift C j).target = slot d T j := by
  unfold c2; split_ifs <;> rfl

theorem c4_target (d : Nat) (S T : Row) (hR hB off : Nat) (cb : Bool) (C : Row) (j : Nat) :
    (c4 d S T hR hB off cb C j).target = slot d T j := by
  unfold c4; split_ifs <;> rfl

set_option maxHeartbeats 3000000 in
/-- **One step of the simulation of an aligned path by the tree of `B`.** -/
theorem stepB {cX cB : Context} (hsrc : cB.source = cX.source)
    (hroot : cB.rootColumn = cX.rootColumn) (hlast : cB.lastColumn = cX.lastColumn)
    (hbX : cX.block ≠ 0) {s : List Nat} (hb : Canonical.build s = .ok cX.source)
    {d : Nat} {A A' : Item} (hsim : SimB cX cB (d + 2) A A') (hAcb : A.cutBottom = false)
    {csX csB : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsB : childItems cB (d + 2) A' = .ok csB)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {bx : Ref × Cell} (hbx : topIn cX.source cB.x (d + 2) A.source = some bx)
    {j : Nat} (hj : j < csX.length) (hal : csX[j].source = csX[j].target)
    (hAal : A.source = A.target)
    {ρK : Ref × Cell} (hρK : ρK ∈ realNodes cX.source cX.rootColumn)
    (hρKin : inRegion (d + 1) csX[j].source (official ρK.2.row) = true)
    (hx0 : ∀ ρr ρc, topIn cX.source cX.rootColumn (d + 2) A.source = some (ρr, ρc) →
      ascends cB (some (ρr, ρc)) = .ok true)
    (hx0ρ : ∀ ρr ρc, topIn cX.source cX.rootColumn (d + 2) A.source = some (ρr, ρc) →
      height (d + 2) (official ρc.row) ≤ height (d + 2) (official bx.2.row))
    (hMDX : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDB : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cB (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMHB : ∀ C r cl csRef csc g, A'.clean = some C → A'.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) A'.source = some (r, cl) →
      nodeAt cX.source cB.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cB.x + 1) csRef csc 0 = .ok g → cB.block ≠ 0 →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cB.result cB.boundary (d + 2) A'.target) + g) :
    ∃ hjB : j < csB.length, SimB cX cB (d + 1) csX[j] csB[j] ∧ csX[j].cutBottom = false := by
  have hA'S := hsim.source
  have hbxB : topIn cB.source cB.x (d + 2) A'.source = some bx := by rw [hsrc, hA'S]; exact hbx
  have hee := e_val' d
  -- the root top of the region
  have hρKA : inRegion (d + 2) A.source (official ρK.2.row) = true := by
    obtain ⟨σ, hσ⟩ := child_src hcsX hj
    rw [hσ] at hρKin; exact region_of_slot hρKin
  obtain ⟨ρr, ρc, hρ, hρKle⟩ := LowerLeftProof.top_ge hb hρK hρKA
  have hρin := topIn_inRegion hρ
  have hHR : height (d + 2) (official ρc.row) = (official ρc.row).coeff d := rfl
  have hρB : topIn cB.source cB.rootColumn (d + 2) A'.source = some (ρr, ρc) := by
    rw [hsrc, hroot, hA'S]; exact hρ
  have hascB := hx0 ρr ρc hρ
  have hMB := hMDB ρr ρc hρ hascB
  have hx0ρ' := hx0ρ ρr ρc hρ
  have hlastB : topIn cB.source cB.lastColumn (d + 2) A'.source =
      topIn cX.source cX.lastColumn (d + 2) A.source := by rw [hsrc, hlast, hA'S]
  -- the source slot of an aligned child
  have hsl : ∀ (σ : Nat) (σ' : Nat), csX[j].source = slot (d + 2) A.source σ →
      csX[j].target = slot (d + 2) A.target σ' → σ = σ' := by
    intro σ σ' h1 h2
    rw [hal, h2, ← hAal] at h1
    exact (LowerLeftProof.slot_inj h1).symm
  have hjR : ∀ hsj : csX[j].source = slot (d + 2) A.source j, j ≤ height (d + 2) (official ρc.row) := by
    intro hsj
    rw [hsj] at hρKin
    have := coeff_of_slot hρKin
    omega
  -- the children of `B` at the root slot, depending on the lift
  have hnoLift : ∀ (hB0 : 0 < (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
      Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int) +
        (if d + 2 = 2 then 1 else 0) → False), cB.block = 0 ∧ 1 ≤ d := by
    intro h
    by_cases hbk : cB.block = 0
    · refine ⟨hbk, ?_⟩
      by_contra hd
      apply h
      rw [hbk]
      have : d = 0 := by omega
      subst this; simp
    · exfalso; apply h
      have h1 : (1 : Int) ≤ (cB.block : Int) := by omega
      have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
          Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int) := by omega
      have := Int.mul_le_mul h2 h1 (by omega) (by omega)
      rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] <;> simp at this ⊢ <;> omega
  -- `c2` at the root slot without a lift
  have hc2noL : ∀ {S T : Row} {C : Row} (lift : Int),
      ¬ (0 < lift + (if d + 2 = 2 then 1 else 0)) → 0 ≤ lift →
      c2 (d + 2) S T 0 (height (d + 2) (official ρc.row)) lift C
        (height (d + 2) (official ρc.row)) = k1 (d + 2) S T (height (d + 2) (official ρc.row)) := by
    intro S T C lift hn hl0
    unfold c2 k1
    have hl : lift = 0 := by
      rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at hn <;> omega
    subst hl
    rcases hee with ⟨he1, _⟩ | ⟨he1, hd1⟩
    · rw [he1] at hn; omega
    · have hd0 : d ≠ 0 := by omega
      simp [hd0]
  have hbxh : height (d + 2) (official bx.2.row) = (official bx.2.row).coeff d := rfl
  have hMBr : height (d + 2) (official ρc.row) < heightOf (d + 2)
      (topIn cX.source cX.lastColumn (d + 2) A.source) := hMB
  -- the lift of `B` is not negative
  have hlB0 : (0 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
      Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int) := by
    apply Int.mul_nonneg <;> omega
  -- `B` has the plain kind of case 2 at `A'` when `A'` is plain
  have hB2 : ∀ (hcl' : A'.clean = none) (hcb' : A'.cutBottom = false),
      csB.length = (((height (d + 2) (official bx.2.row) : Nat) : Int) +
        (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat) : Int) -
          ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int) + 1).toNat ∧
      ∀ j (hj : j < csB.length), csB[j] = c2 (d + 2) A.source A.target cB.block
        (height (d + 2) (official ρc.row))
        ((((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat) : Int) -
          ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int)) (official ρc.row) j := by
    intro hcl' hcb'
    obtain ⟨h1, h2⟩ := kids2 hcsB hcl' hcb' hbxB hρB hascB
    rw [hlastB] at h1 h2
    rw [hA'S, hsim.target] at h2
    exact ⟨h1, h2⟩
  -- `B` copies the root row at `A'`
  have hB4 : ∀ C (hcl' : A'.clean = some C) (hcb' : A'.cutBottom = false),
      j ≤ height (d + 2) (official ρc.row) → ∃ hjB : j < csB.length,
      csB[j] = c4 (d + 2) A.source A.target (height (d + 2) (official ρc.row))
        (heightOf (d + 2) (topIn cB.result cB.boundary (d + 2) A.target)) 0 false C j := by
    intro C hcl' hcb' hjle
    have hascB' : ascends cB (some (ρr, ρc)) = .ok true := hascB
    obtain ⟨yr, yc, gB, hyn, hyg, hyb, hlY, hgY⟩ := kids4b hcsB hcl' hbxB hρB hascB'
    have hoff := (hyb hcb').2
    rw [hcb', hoff, hA'S, hsim.target] at hgY
    rw [hoff, hsim.target] at hlY
    have hjB : j < csB.length := by
      rw [hlY]
      by_cases hbk : cB.block = 0
      · rw [if_pos hbk]; omega
      · rw [if_neg hbk]
        have := hMHB C ρr ρc yr yc gB hcl' hcb' (by rw [hA'S]; exact hρ) (by rw [← hsrc]; exact hyn)
          (by rw [← hsrc, ← hroot]; exact hyg) hbk
        rw [hsim.target] at this
        omega
    exact ⟨hjB, hgY j hjB⟩
  -- the step for two copies of the same root row
  have cleanStep : ∀ {C : Row} (hcl : A.clean = some C) (hcb : A.cutBottom = false)
      (hoff : A.offset = 0)
      (hgX : ∀ j (hj : j < csX.length), csX[j] = c4 (d + 2) A.source A.target
        (height (d + 2) (official ρc.row))
        (heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target)) A.offset A.cutBottom C j)
      (hcl' : A'.clean = some C) (hcb' : A'.cutBottom = false),
      ∃ hjB : j < csB.length, SimB cX cB (d + 1) csX[j] csB[j] ∧ csX[j].cutBottom = false := by
    intro C hcl hcb hoff hgX hcl' hcb'
    rw [hcb, hoff] at hgX
    have hjle : j ≤ height (d + 2) (official ρc.row) := by
      by_contra hn
      rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official ρc.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (off := 0) (C := C) j with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · omega
      · have := hsl (height (d + 2) (official ρc.row)) j
          (by rw [hgX j hj]; exact c4_src_hi (Or.inl h1.le))
          (by rw [hgX j hj]; exact c4_target _ _ _ _ _ _ _ _ _)
        omega
    obtain ⟨hjB, hgB⟩ := hB4 C hcl' hcb' hjle
    refine ⟨hjB, ?_, ?_⟩
    · rw [hgX j hj, hgB]
      rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official ρc.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (off := 0) (C := C) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
      · left
        rw [h2]
        rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
          (hR := height (d + 2) (official ρc.row))
          (hB := heightOf (d + 2) (topIn cB.result cB.boundary (d + 2) A.target))
          (off := 0) (C := C) j with ⟨_, g2⟩ | ⟨g1, _⟩ | ⟨g1, _⟩
        · rw [g2]
        · omega
        · omega
      · right; left
        rw [h2]
        rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
          (hR := height (d + 2) (official ρc.row))
          (hB := heightOf (d + 2) (topIn cB.result cB.boundary (d + 2) A.target))
          (off := 0) (C := C) j with ⟨g1, _⟩ | ⟨_, g2⟩ | ⟨g1, _⟩
        · omega
        · rw [g2]
          exact ⟨rfl, rfl, rfl, rfl, C, rfl, rfl⟩
        · omega
      · omega
    · rw [hgX j hj]
      rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official ρc.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (off := 0) (C := C) j with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [h2]; rfl
      · rw [h2]
      · omega
  rcases hsim with hEqA | ⟨hS', hT', _, hB'cb, C, hXC, hBC⟩ |
      ⟨hXn, hXcb, hS', hT', hB'cb, r1, c1, hρ1, hB'C, hascX⟩ |
      ⟨hB'n, hB'cb, hS', hT', hXcb, hblk0, r1, c1, hρ1, hXC⟩
  · -- equal items
    have hEqA' := hEqA.symm
    subst hEqA'
    cases hcl : A.clean with
    | none =>
      obtain ⟨bX, hbX⟩ := childItems_asc hcsX hax
      rw [hρ] at hbX
      obtain ⟨hlB, hgB⟩ := hB2 hcl hAcb
      cases bX with
      | false =>
        have hbX' : ascends cX (topIn cX.source cX.rootColumn (d + 2) A.source) = .ok false := by
          rw [hρ]; exact hbX
        obtain ⟨_, _, _, hgX⟩ := kids1 hcsX hax hbX'
        have hjle := hjR (by rw [hgX j hj]; rfl)
        have hjB : j < csB.length := by rw [hlB]; omega
        refine ⟨hjB, ?_, by rw [hgX j hj]; rfl⟩
        rcases Nat.lt_or_ge j (height (d + 2) (official ρc.row)) with hlt | hge
        · left; rw [hgX j hj, hgB j hjB, c2_low hlt]
        · have hjeq : j = height (d + 2) (official ρc.row) := by omega
          by_cases hpos : 0 < (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
              Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int) +
                (if d + 2 = 2 then 1 else 0)
          · right; right; left
            rw [hgX j hj, hgB j hjB]
            subst hjeq
            rw [c2_root hpos]
            exact ⟨rfl, rfl, rfl, rfl, rfl, ρr, ρc, Inner.topIn_slot hρ, rfl, hbX⟩
          · obtain ⟨hbk, _⟩ := hnoLift hpos
            left
            rw [hgX j hj, hgB j hjB]
            subst hjeq
            rw [hbk]
            have := hc2noL (S := A.source) (T := A.target) (C := official ρc.row)
              ((((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat) : Int) -
                ((height (d + 2) (official ρc.row) : Nat) : Int)) * ((0 : Nat) : Int))
              (by rw [hbk] at hpos; exact hpos) (by simp)
            rw [this]
      | true =>
        obtain ⟨hlX, hgX⟩ := kids2 hcsX hcl hAcb hax hρ hbX
        have hMX := hMDX ρr ρc hρ hbX
        have hliftX : (1 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
            A.source) : Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) *
              (cX.block : Int) := by
          have h1 : (1 : Int) ≤ (cX.block : Int) := by omega
          have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
              A.source) : Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int) := by
            omega
          have := Int.mul_le_mul h2 h1 (by omega) (by omega)
          simpa using this
        have hs := hgX j hj
        rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
          (hR := height (d + 2) (official ρc.row))
          (lift := (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat) :
            Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cX.block : Int))
          (C := official ρc.row) j with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have hjB : j < csB.length := by rw [hlB]; omega
          refine ⟨hjB, Or.inl ?_, by rw [hs, h2]; rfl⟩
          rw [hs, hgB j hjB, h2, c2_low h1]
        · -- the root slot: aligned only at `h_ρ`
          have hjeq : j = height (d + 2) (official ρc.row) := by
            have := hsl (height (d + 2) (official ρc.row)) j (by rw [hs, h3]) (by rw [hs, h3])
            omega
          have hjB : j < csB.length := by rw [hlB]; omega
          refine ⟨hjB, ?_, by rw [hs, h3]; simp [hjeq]⟩
          subst hjeq
          rw [hs, h3, hgB _ hjB]
          by_cases hpos : 0 < (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
              Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * (cB.block : Int) +
                (if d + 2 = 2 then 1 else 0)
          · left
            rw [c2_root hpos]; simp
          · obtain ⟨hbk, _⟩ := hnoLift hpos
            right; right; right
            rw [hbk]
            have := hc2noL (S := A.source) (T := A.target) (C := official ρc.row)
              ((((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat) : Int) -
                ((height (d + 2) (official ρc.row) : Nat) : Int)) * ((0 : Nat) : Int))
              (by rw [hbk] at hpos; exact hpos) (by simp)
            rw [this]
            exact ⟨rfl, rfl, rfl, rfl, by simp, rfl, ρr, ρc, Inner.topIn_slot hρ, by simp⟩
        · exfalso
          have := hsl _ j (by rw [hs]; exact h3.1) (by rw [hs]; exact c2_target _ _ _ _ _ _ _ _)
          rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h2 <;> omega
    | some C =>
      have hascXA := asc_true_of_kind hcsX hax (Or.inl (by rw [hcl]; simp))
      rw [hρ] at hascXA
      obtain ⟨xr, xc, gX, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hcl hbX hax hρ hascXA
      exact cleanStep hcl hAcb (hxb hAcb).2 hgX hcl hAcb
  · -- two copies of `C`
    have hA'cb := hB'cb
    have hascXA := asc_true_of_kind hcsX hax (Or.inl (by rw [hXC]; simp))
    rw [hρ] at hascXA
    obtain ⟨xr, xc, gX, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hXC hbX hax hρ hascXA
    obtain ⟨hA'cb', _⟩ : A.cutBottom = false ∧ True := ⟨hAcb, trivial⟩
    exact cleanStep hXC hAcb (hxb hAcb).2 hgX hBC hB'cb
  · -- `X` plain, `B` copies `ρ`
    have e1 : (r1, c1) = (ρr, ρc) := Option.some.inj (hρ1.symm.trans hρ)
    have e2 := (Prod.mk.inj e1).1.symm
    have e3 := (Prod.mk.inj e1).2.symm
    subst e2 e3
    have hbX' : ascends cX (topIn cX.source cX.rootColumn (d + 2) A.source) = .ok false := by
      rw [hρ]; exact hascX
    obtain ⟨_, _, _, hgX⟩ := kids1 hcsX hax hbX'
    have hjle := hjR (by rw [hgX j hj]; rfl)
    obtain ⟨hjB, hgB⟩ := hB4 _ hB'C hB'cb hjle
    refine ⟨hjB, ?_, by rw [hgX j hj]; rfl⟩
    rw [hgX j hj, hgB]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official ρc.row))
      (hB := heightOf (d + 2) (topIn cB.result cB.boundary (d + 2) A.target))
      (off := 0) (C := official ρc.row) j with ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · left; exact h2
    · right; right; left
      rw [h2]
      subst h1
      exact ⟨rfl, rfl, rfl, rfl, rfl, ρr, ρc, Inner.topIn_slot hρ, rfl, hascX⟩
    · omega
  · -- `X` copies `ρ`, `B` plain (block `0`)
    have e1 : (r1, c1) = (ρr, ρc) := Option.some.inj (hρ1.symm.trans hρ)
    have e2 := (Prod.mk.inj e1).1.symm
    have e3 := (Prod.mk.inj e1).2.symm
    subst e2 e3
    have hascXA := asc_true_of_kind hcsX hax (Or.inl (by rw [hXC]; simp))
    rw [hρ] at hascXA
    obtain ⟨xr, xc, gX, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hXC hbX hax hρ hascXA
    have hoffX := (hxb hXcb).2
    rw [hXcb, hoffX] at hgX
    have hjle : j ≤ height (d + 2) (official ρc.row) := by
      by_contra hn
      rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official ρc.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (off := 0) (C := official ρc.row) j with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · omega
      · have := hsl (height (d + 2) (official ρc.row)) j
          (by rw [hgX j hj]; exact c4_src_hi (Or.inl h1.le)) (by rw [hgX j hj]; exact c4_target _ _ _ _ _ _ _ _ _)
        omega
    obtain ⟨hlB, hgB⟩ := hB2 hB'n hB'cb
    rw [hblk0] at hlB hgB
    have hjB : j < csB.length := by rw [hlB]; simp; omega
    refine ⟨hjB, ?_, by
      rw [hgX j hj]
      rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
        (hR := height (d + 2) (official ρc.row))
        (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
        (off := 0) (C := official ρc.row) j with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [h2]; rfl
      · rw [h2]
      · omega⟩
    rw [hgX j hj, hgB j hjB]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official ρc.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := 0) (C := official ρc.row) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · left; rw [h2, c2_low h1]
    · rw [h2]
      subst h1
      by_cases hpos : 0 < (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) :
          Nat) : Int) - ((height (d + 2) (official ρc.row) : Nat) : Int)) * ((0 : Nat) : Int) +
            (if d + 2 = 2 then 1 else 0)
      · right; left
        rw [c2_root hpos]
        exact ⟨rfl, rfl, rfl, rfl, official ρc.row, rfl, rfl⟩
      · right; right; right
        rw [hc2noL _ hpos (by simp)]
        exact ⟨rfl, rfl, rfl, rfl, rfl, hblk0, ρr, ρc, Inner.topIn_slot hρ, rfl⟩
    · omega

end OmegaY.Official.Recon.LRC
