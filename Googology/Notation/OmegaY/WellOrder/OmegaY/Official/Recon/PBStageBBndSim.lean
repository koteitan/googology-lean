/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBBndSim.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBBndK

set_option backward.do.legacy false

/-!
# `BoundaryPos` holds (stage B)

For a root column `c_r ≥ 1` and a block `1 ≤ i ≤ n`, the hypothetical copy `K` of `c_r` in block
`i` runs (`kRun`, `PBStageBBndK.lean`) and emits every row below `τ` of the boundary column
`B = c_r + w·i` (`boundaryPos`).

## Proof

`B` is the copy of `x₀` in block `i - 1` (context `A`). We follow the items of `A` that emit a row
of `B` and relate each to the item of `K` with the same target region (`RelB`):

* `B1`: the item of `K` skips the bottom of its region (gap copy or cut-bottom item). It emits every
  row of `B` in its target (`coverAll`).
* `B2`: the same plain item (source = target), with a node of `c_r` in its region. `K` is in case 2
  (the root column ascends at its own top, `ascCr`) with the top of `K` equal to the root top `ρ`.
  The children of `A` and `K` agree below the slot of `ρ`; the child of `K` in the slot of `ρ` is a
  clean copy of `ρ` or a cut-bottom item; above it `K` has gap copies or a cut-bottom item. The
  ranges agree: `h_κ + (h_κ - h_ρ)(i - 1) = h_ρ + (h_κ - h_ρ)·i`.
* `B3`: a clean copy of the root top `C` in `K`, with a plain or clean item of `A`. The generations
  of the root column are `0`, so `K` has the children up to the height of `B`: below the slot of
  `C` plain, in it a clean copy (in `A` too, by fact MD when `i - 1 ≥ 1`), above it gap copies.

The first items are `B2`: every first region has a node of `c_r` (`firstRoot`, from `topBump` and
`fill`).

With `rootShadowZero` (`PBStageBRootZero.lean`) and `genLeg` (`PBStageBGenLeg.lean`) this gives
`RootShadowOut` (`rootShadowOut`) and **`LowerParentBelowHolds` with no hypothesis**
(`lowerParentBelowHolds`), hence `ParentBelowHolds` (`parentBelowHolds`).
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve
open Classification.Proofs Classification.Proofs.CopyShape.PBStageB
open Classification.Proofs.CopyShape Classification.Proofs.CopyShape.InnerRow
open Classification.Proofs.ChainCorr.CopyMonoProof

/-- **Every first region has a node of the root column.** -/
theorem firstRoot {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {q : Nat × Item} (hq : q ∈ lowerItems (official t.row)) :
    ∃ ρ, topIn M root.column q.1 q.2.source = some ρ := by
  have hb := hTop.build
  obtain ⟨rc, a, J, hrc, hri, hτ, hag, _⟩ := topBump hTop
  obtain ⟨k, j, _, hj, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
  simp only
  have hkJ : J ≤ k := by
    by_contra hn
    rw [hτ, Recon.RowLaw.bump_coeff_low (by omega)] at hj
    omega
  have hin : inRegion (k + 2) (official t.row) (official rc.row) = true := by
    rw [Recon.RowLaw.inRegion_iff']
    intro q hq'
    rw [hτ, Recon.RowLaw.bump_coeff_high (by omega), hag q (by omega)]
  have hjle : j ≤ (official rc.row).coeff k := by
    rw [hτ] at hj
    rcases Nat.lt_or_eq_of_le hkJ with hlt | heq
    · rw [Recon.RowLaw.bump_coeff_high hlt] at hj
      rw [← hag k hlt.le]; omega
    · subst heq
      rw [Recon.RowLaw.bump_coeff_at] at hj
      rw [← hag J le_rfl]; omega
  have hrc' : cell? M ⟨root.column, root.index⟩ = some rc := hrc
  obtain ⟨p, hp, hpin⟩ := fill hb root.index rc hri hrc' hin j hjle
  obtain ⟨hpc, hp1, hpcell⟩ := Classification.mem_realNodes hp
  cases h' : topIn M root.column (k + 1) (slot (k + 2) (official t.row) j) with
  | none => exact absurd h' (topIn_ne_none_of_node hpc hp1 hpcell hpin)
  | some ρ => exact ⟨ρ, rfl⟩

/-- The relation of an item of the copy `A` of `x₀` (block `i - 1`) and an item of the copy `K`
of `c_r` (block `i`) with the same target region. -/
def RelB (M : Mountain) (cr : Nat) (K : Context) (d : Nat) (a k : Item) : Prop :=
  (k.cutBottom = true ∧ a.target = k.target ∧ InvCov K M cr d k) ∨
  (a = k ∧ a.clean = none ∧ a.cutBottom = false ∧ a.source = a.target ∧ a.offset = 0 ∧
    ∃ ρ, topIn M cr d a.source = some ρ) ∨
  (∃ C, k = ⟨a.source, a.source, some C, 0, false⟩ ∧ rootTop K d a.source = some C ∧
    a.target = a.source ∧ a.cutBottom = false ∧ (a.clean = none ∨ a.clean = some C))

/-- The copy of `c_r` in block `i`. -/
def Kc (M R : Mountain) (cr i : Nat) : Context := ⟨M, R, cr, i, cr, M.size - 1 - cr, M.size - 1⟩

/-- The copy of `x₀` in block `i'` that makes the boundary column of block `i' + 1`. -/
def Ac (M R : Mountain) (cr i' i : Nat) : Context :=
  ctxAt M R (M.size - 1) i' cr (M.size - 1 - cr) (M.size - 1) (cr + (M.size - 1 - cr) * i)

theorem int_mul_succ (a : Int) (b : Nat) : a * ((b + 1 : Nat) : Int) = a * (b : Int) + a := by
  push_cast; rw [Int.mul_add, Int.mul_one]

/-- **The step of `B2`: the same plain item.** -/
theorem b2_step {s : List Nat} {M R : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i i' : Nat} (hii : i' + 1 = i) {d : Nat} {it : Item}
    {csA csK : List Item}
    (hcA : ChildCase (Ac M R root.column i' i) d it csA)
    (hcK : ChildCase (Kc M R root.column i) d it csK)
    (hcl : it.clean = none) (hcb : it.cutBottom = false) (hST : it.source = it.target)
    {ρ : Ref × Cell} (hρ : topIn M root.column (d + 2) it.source = some ρ)
    (hbel : ∀ r, inRegion (d + 2) it.source r = true → r < official t.row)
    {cA : Item} (hcAm : cA ∈ csA) :
    ∃ cK ∈ csK, RelB M root.column (Kc M R root.column i) (d + 1) cA cK := by
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  have hmemρ : ρ ∈ realNodes M root.column := (Recon.RowLaw.topIn_spec hρ).1
  have hasc := ascCr hb (ctx := Kc M R root.column i) rfl rfl rfl hmemρ
  -- the top of `x₀` is at least as high as the root top
  obtain ⟨κ, hκ, hκρ⟩ := RowLaw.Top.rootCut_region hTop hbel hρ
  have hCR : (official ρ.2.row).coeff d ≤ (official κ.2.row).coeff d :=
    Recon.RowLaw.coeff_le_of_inRegion (topIn_inRegion hρ) (topIn_inRegion hκ) hκρ
  obtain ⟨ρr, ρc⟩ := ρ
  simp only at hCR
  -- the case of `K`
  cases hcK with
  | none hn => exact absurd hn (by show topIn M root.column (d + 2) it.source ≠ none; rw [hρ]; simp)
  | case1 _ _ hasc' _ _ _ =>
      have : topIn (Kc M R root.column i).source (Kc M R root.column i).rootColumn (d + 2)
          it.source = some (ρr, ρc) := hρ
      rw [this, hasc] at hasc'; cases hasc'
  | case3 _ _ _ _ _ _ _ hcb' _ _ => rw [hcb] at hcb'; cases hcb'
  | case4 _ _ _ _ _ _ _ hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
  | case2 aK haK ρr' ρc' hρK hascK _ _ LK eK hLK heK =>
      have hρK' : topIn M root.column (d + 2) it.source = some (ρr', ρc') := hρK
      rw [hρ] at hρK'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρK')
      have haK' : topIn M root.column (d + 2) it.source = some aK := haK
      rw [hρ] at haK'
      obtain rfl := Option.some.inj haK'
      have he01 : 0 ≤ eK ∧ eK ≤ 1 := by rw [heK]; split <;> omega
      -- `L_K = (h_κ - h_ρ)·i`
      have hκ' : heightOf (d + 2) (topIn (Kc M R root.column i).source
          (Kc M R root.column i).lastColumn (d + 2) it.source) = (official κ.2.row).coeff d := by
        show heightOf (d + 2) (topIn M (M.size - 1) (d + 2) it.source) = _
        rw [hκ]; rfl
      rw [hκ'] at hLK
      have hLK' : LK = (((official κ.2.row).coeff d : Int) -
          (height (d + 2) (official ρc.row) : Int)) * (i : Int) := hLK
      -- common facts
      set hR := height (d + 2) (official ρc.row) with hhR
      set hC := (official κ.2.row).coeff d with hhC
      have hRC : hR ≤ hC := hCR
      have hLK0 : 0 ≤ LK := by rw [hLK']; exact Int.mul_nonneg (by omega) (by omega)
      have hLKge : (hC : Int) - hR ≤ LK := by
        rw [hLK', ← hii, int_mul_succ]
        have := Int.mul_nonneg (show (0 : Int) ≤ (hC : Int) - hR by omega)
          (show (0 : Int) ≤ (i' : Int) by omega)
        omega
      have hrts : rootTop (Kc M R root.column i) (d + 1) (slot (d + 2) it.source hR) =
          some (official ρc.row) :=
        rootTop_slot (rootTop_of_topIn (ctx := Kc M R root.column i) rfl rfl hρ)
      have htps : topIn M root.column (d + 1) (slot (d + 2) it.source hR) = some (ρr, ρc) :=
        ChainCorr.Inner.topIn_slot hρ
      have hXρ : XNode M (Kc M R root.column i).x (official ρc.row) := ⟨(ρr, ρc), hmemρ, rfl⟩
      have hmemρ' := hmemρ
      obtain ⟨hρc, hρ1, hρcell⟩ := Classification.mem_realNodes hmemρ'
      have hρcell' : cell? M ⟨root.column, ρr.index⟩ = some ρc := by
        have : ρr = ⟨root.column, ρr.index⟩ := by simp only at hρc; rw [← hρc]
        rw [← this]; exact hρcell
      have hfill : ∀ j, j < hR → ∃ ρ', topIn M root.column (d + 1) (slot (d + 2) it.source j) =
          some ρ' := by
        intro j hj
        obtain ⟨q, hq, hqin⟩ := fill hb ρr.index ρc hρ1 hρcell' (topIn_inRegion hρ) j hj.le
        obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
        cases h' : topIn M root.column (d + 1) (slot (d + 2) it.source j) with
        | none => exact absurd h' (topIn_ne_none_of_node hqc hq1 hqcell hqin)
        | some ρ' => exact ⟨ρ', rfl⟩
      have hST' : ∀ j, slot (d + 2) it.source j = slot (d + 2) it.target j := by
        intro j; rw [hST]
      have hmemK : ∀ j : Nat, (j : Int) ≤ hR + LK →
          ChainCorr.CopyMonoProof.c2 it.source it.target (official ρc.row) d hR LK eK
            (Kc M R root.column i).block j ∈
          (List.range (((height (d + 2) (official ρc.row) : Nat) : Int) + LK + 1).toNat).map
            (ChainCorr.CopyMonoProof.c2 it.source it.target (official ρc.row) d hR LK eK
              (Kc M R root.column i).block) := by
        intro j hj
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
      -- the relation for a child of `K`, by the slot
      have hrel : ∀ (j : Nat) (cA : Item), (j : Int) ≤ hR + LK →
          cA.target = slot (d + 2) it.target j →
          (j < hR → cA = ⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0, false⟩) →
          (j = hR → (hR : Int) < hR + LK + eK → cA.source = slot (d + 2) it.source hR ∧
            cA.cutBottom = false ∧ (cA.clean = none ∨ cA.clean = some (official ρc.row))) →
          RelB M root.column (Kc M R root.column i) (d + 1) cA
            (ChainCorr.CopyMonoProof.c2 it.source it.target (official ρc.row) d hR LK eK
              (Kc M R root.column i).block j) := by
        intro j cA hj htg hlow hmid
        unfold ChainCorr.CopyMonoProof.c2
        by_cases h1 : j < hR
        · rw [if_pos h1, hlow h1]
          refine Or.inr (Or.inl ⟨rfl, rfl, rfl, hST' j, rfl, hfill j h1⟩)
        · rw [if_neg h1]
          by_cases h2 : (j : Int) < hR + LK + eK
          · rw [if_pos h2]
            by_cases h3 : hR < j
            · have hd : decide (hR < j) = true := decide_eq_true h3
              rw [hd]
              exact Or.inl ⟨rfl, htg, Or.inl ⟨official ρc.row, rfl, rfl, hrts, hXρ,
                fun _ _ _ _ _ => Nat.zero_le _⟩⟩
            · have hjR : j = hR := by omega
              have hd : decide (hR < j) = false := decide_eq_false h3
              rw [hd]
              obtain ⟨hsrc, hcb', hcl'⟩ := hmid hjR (by omega)
              refine Or.inr (Or.inr ⟨official ρc.row, ?_, ?_, ?_, hcb', hcl'⟩)
              · rw [hsrc, hjR, hST']
              · rw [hsrc]; exact hrts
              · rw [htg, hsrc, hjR, hST']
          · rw [if_neg h2]
            have hjeq : (j : Int) = hR + LK := by omega
            have hidx : ((j : Int) - LK).toNat = hR := by omega
            have hd : decide ((Kc M R root.column i).block ≠ 0 ∧ (j : Int) = hR + LK) = true :=
              decide_eq_true ⟨by show i ≠ 0; omega, hjeq⟩
            rw [hd, hidx]
            exact Or.inl ⟨rfl, htg, Or.inr (Or.inl ⟨rfl, rfl, (ρr, ρc), htps, hXρ⟩)⟩
      -- the case of `A`
      cases hcA with
      | none _ => simp at hcAm
      | case3 _ _ _ _ _ _ _ hcb' _ _ => rw [hcb] at hcb'; cases hcb'
      | case4 _ _ _ _ _ _ _ hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
      | case1 aA haA _ _ _ _ =>
          have haA' : topIn M (M.size - 1) (d + 2) it.source = some aA := haA
          rw [hκ] at haA'
          obtain rfl := Option.some.inj haA'
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcAm
          have hj' : j ≤ (official κ.2.row).coeff d := by
            have := List.mem_range.mp hj; show j ≤ height (d + 2) (official κ.2.row); omega
          have hjK : (j : Int) ≤ hR + LK := by omega
          refine ⟨_, hmemK j hjK, hrel j _ hjK rfl (fun _ => rfl) (fun hjR _ => ?_)⟩
          exact ⟨by rw [hjR], rfl, Or.inl rfl⟩
      | case2 aA haA ρrA ρcA hρA hascA _ _ LA eA hLA heA =>
          have haA' : topIn M (M.size - 1) (d + 2) it.source = some aA := haA
          rw [hκ] at haA'
          obtain rfl := Option.some.inj haA'
          have hρA' : topIn M root.column (d + 2) it.source = some (ρrA, ρcA) := hρA
          rw [hρ] at hρA'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρA')
          have heAK : eA = eK := by rw [heA, heK]
          subst heAK
          have hLA' : LA = ((hC : Int) - hR) * (i' : Int) := by
            rw [hLA]
            show ((heightOf (d + 2) (topIn M (M.size - 1) (d + 2) it.source) : Nat) - (hR : Int)) *
              (i' : Int) = _
            rw [hκ]; rfl
          have hLKA : LK = LA + ((hC : Int) - hR) := by
            rw [hLK', hLA', ← hii, int_mul_succ]
          have hLA0 : 0 ≤ LA := by rw [hLA']; exact Int.mul_nonneg (by omega) (by omega)
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcAm
          have hj' : (j : Int) < hC + LA + 1 := by
            have := List.mem_range.mp hj
            have h2 : ((height (d + 2) (official κ.2.row) : Nat) : Int) + LA + 1 =
                (hC : Int) + LA + 1 := rfl
            omega
          have hjK : (j : Int) ≤ hR + LK := by omega
          refine ⟨_, hmemK j hjK, hrel j _ hjK ?_ ?_ ?_⟩
          · unfold ChainCorr.CopyMonoProof.c2; split_ifs <;> rfl
          · intro h1; unfold ChainCorr.CopyMonoProof.c2; rw [if_pos h1]
          · intro hjR hK
            subst hjR
            unfold ChainCorr.CopyMonoProof.c2
            rw [if_neg (lt_irrefl _)]
            by_cases h2A : ((height (d + 2) (official ρc.row) : Nat) : Int) <
                (height (d + 2) (official ρc.row) : Int) + LA + eA
            · rw [if_pos h2A]
              exact ⟨rfl, decide_eq_false (lt_irrefl _), Or.inr rfl⟩
            · rw [if_neg h2A]
              have hLA00 : LA = 0 := by omega
              have hidx : (((height (d + 2) (official ρc.row) : Nat) : Int) - LA).toNat =
                  height (d + 2) (official ρc.row) := by omega
              rw [hidx]
              refine ⟨rfl, decide_eq_false ?_, Or.inl rfl⟩
              rintro ⟨hi0, _⟩
              have hprod : ((hC : Int) - hR) * (i' : Int) = 0 := by rw [← hLA']; exact hLA00
              rcases Int.mul_eq_zero.mp hprod with h0 | h0
              · have : LK = 0 := by rw [hLKA, hLA00, h0]; rfl
                omega
              · exact hi0 (by show i' = 0; omega)

/-- **The step of `B3`: a clean copy of the root top in `K`.** -/
theorem b3_step {s : List Nat} {M R : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i i' : Nat} (hii : i' + 1 = i)
    (hBA : BCtx M R root.column (M.size - 1) i' (Ac M R root.column i' i))
    (hVR : MountainValid R) {d : Nat} {it : Item} {C : Row} {csA csK : List Item}
    (hcA : ChildCase (Ac M R root.column i' i) d it csA)
    (hcK : ChildCase (Kc M R root.column i) d ⟨it.source, it.source, some C, 0, false⟩ csK)
    (hrt : rootTop (Kc M R root.column i) (d + 2) it.source = some C)
    (hT : it.target = it.source) (hcb : it.cutBottom = false)
    (hclA : it.clean = none ∨ it.clean = some C)
    (hReA : Reach (Ac M R root.column i' i) (official t.row) (d + 2) it)
    {cA : Item} (hcAm : cA ∈ csA) {r : Row} (hr : inRegion (d + 1) cA.target r = true)
    (hrB : ∃ z ∈ realNodes R (root.column + (M.size - 1 - root.column) * i),
      official z.2.row = r) :
    ∃ cK ∈ csK, RelB M root.column (Kc M R root.column i) (d + 1) cA cK := by
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨ρ, hρ, hρC⟩ := topIn_of_rootTop (ctx := Kc M R root.column i) (M := M)
    (cr := root.column) rfl rfl hrt
  obtain ⟨ρr, ρc⟩ := ρ
  have hρC' : official ρc.row = C := hρC
  have hmemρ : (ρr, ρc) ∈ realNodes M root.column := (Recon.RowLaw.topIn_spec hρ).1
  have hXρ : XNode M (Kc M R root.column i).x (official ρc.row) := ⟨(ρr, ρc), hmemρ, rfl⟩
  have hrts : rootTop (Kc M R root.column i) (d + 1)
      (slot (d + 2) it.source (height (d + 2) (official ρc.row))) = some C := by
    have := rootTop_slot hrt; rw [← hρC'] at this ⊢; exact this
  -- the index of the child of `A`
  obtain ⟨j, hjt⟩ := children_target hcA cA hcAm
  rw [hT] at hjt
  rw [hjt] at hr
  have hrj : r.coeff d = j := (Recon.RowLaw.inRegion_slot_iff.mp hr).2
  have hrS : inRegion (d + 2) it.source r = true := (Recon.RowLaw.inRegion_slot_iff.mp hr).1
  obtain ⟨z, hzB, hzr⟩ := hrB
  obtain ⟨hzc, hz1, hzcell⟩ := Classification.mem_realNodes hzB
  have hzS : inRegion (d + 2) it.source (official z.2.row) = true := by rw [hzr]; exact hrS
  obtain ⟨b, hbt, hjb⟩ : ∃ b, topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2)
      it.source = some b ∧ j ≤ (official b.2.row).coeff d := by
    cases hb' : topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2) it.source with
    | none => exact absurd hb' (topIn_ne_none_of_node hzc hz1 hzcell hzS)
    | some b =>
        refine ⟨b, rfl, ?_⟩
        have hle := le_top_of_node hVR hzc hz1 hzcell hzS hb'
        rw [← hrj, ← hzr]
        exact Recon.RowLaw.coeff_le_of_inRegion hzS (topIn_inRegion hb') hle
  -- the case of `K`: a clean copy of `C`
  cases hcK with
  | none hn =>
      have : topIn M root.column (d + 2) it.source = none := hn
      rw [hρ] at this; cases this
  | case1 _ _ _ hcl' _ _ => cases hcl'
  | case2 _ _ _ _ _ _ hcl' _ _ _ _ _ => cases hcl'
  | case3 _ _ _ _ _ _ hcl' _ _ _ => cases hcl'
  | case4 aK haK ρr' ρc' hρK hascK C' hcl' csRef cs0 hcs g hg hbnd =>
      simp only [Option.some.injEq] at hcl'
      subst hcl'
      have hρK' : topIn M root.column (d + 2) it.source = some (ρr', ρc') := hρK
      rw [hρ] at hρK'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρK')
      obtain ⟨hcsc, _, _, _⟩ := Classification.nodeAt_spec hcs
      have hg0 : g = 0 := gen_root (M := M) (cr := root.column) (by simp only at hcsc; exact hcsc)
        hg
      subst hg0
      have hblkK : (Kc M R root.column i).block ≠ 0 := by
        show i ≠ 0; omega
      simp only at hbnd ⊢
      rw [if_neg hblkK]
      have hBeq : heightOf (d + 2) (topIn (Kc M R root.column i).result
          (Kc M R root.column i).boundary (d + 2) it.source) = (official b.2.row).coeff d := by
        show heightOf (d + 2) (topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2)
          it.source) = _
        rw [hbt]; rfl
      set hR := height (d + 2) (official ρc.row) with hhR
      set hB := heightOf (d + 2) (topIn (Kc M R root.column i).result
          (Kc M R root.column i).boundary (d + 2) it.source) with hhB
      have hjB : j ≤ hB := by rw [hBeq]; exact hjb
      -- the facts about the child of `A` in the slot `j`
      have hslotinj : ∀ j', slot (d + 2) it.source j' = slot (d + 2) it.source j → j' = j := by
        intro j' h'
        have := congrArg (fun r : Row => r.coeff d) h'
        simpa [ChainCorr.CopyMonoProof.slot_coeff_at] using this
      have hA : (j < hR → cA = ⟨slot (d + 2) it.source j, slot (d + 2) it.source j, none, 0,
          false⟩) ∧ (j = hR → cA.source = slot (d + 2) it.source hR ∧ cA.cutBottom = false ∧
          (cA.clean = none ∨ cA.clean = some C)) := by
        cases hcA with
        | none _ => simp at hcAm
        | case3 _ _ _ _ _ _ _ hcb' _ _ => rw [hcb] at hcb'; cases hcb'
        | case1 aA haA _ _ _ _ =>
            obtain ⟨j', _, rfl⟩ := List.mem_map.mp hcAm
            have hjj : j' = j := by
              apply hslotinj j'
              have h' : slot (d + 2) it.target j' = slot (d + 2) it.source j := hjt
              rw [hT] at h'; exact h'
            subst hjj
            refine ⟨fun _ => by rw [hT], fun hjR => ⟨?_, rfl, Or.inl rfl⟩⟩
            show slot (d + 2) it.source j' = slot (d + 2) it.source hR
            rw [hjR]
        | case2 aA haA ρrA ρcA hρA hascA _ _ LA eA hLA heA =>
            have hρA' : topIn M root.column (d + 2) it.source = some (ρrA, ρcA) := hρA
            rw [hρ] at hρA'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρA')
            obtain ⟨j', _, rfl⟩ := List.mem_map.mp hcAm
            have hjj : j' = j := by
              apply hslotinj j'
              rw [← hjt, hT]
              unfold ChainCorr.CopyMonoProof.c2; split_ifs <;> rfl
            subst hjj
            have he01 : 0 ≤ eA ∧ eA ≤ 1 := by rw [heA]; split <;> omega
            have hMD := CopyShape.Found.factMD_of_bctx hTop hBA d it hReA _ _ hρA hascA
            have hMD' : hR < heightOf (d + 2) (topIn M (M.size - 1) (d + 2) it.source) := hMD
            have hLA' : LA = ((heightOf (d + 2) (topIn M (M.size - 1) (d + 2) it.source) : Int) -
                (hR : Int)) * (i' : Int) := hLA
            have hLA0 : 0 ≤ LA := by rw [hLA']; exact Int.mul_nonneg (by omega) (by omega)
            refine ⟨fun h1 => ?_, fun hjR => ?_⟩
            · unfold ChainCorr.CopyMonoProof.c2; rw [if_pos h1, hT]
            · subst hjR
              unfold ChainCorr.CopyMonoProof.c2
              rw [if_neg (lt_irrefl _)]
              by_cases h2A : ((hR : Nat) : Int) < (hR : Int) + LA + eA
              · rw [if_pos h2A]
                exact ⟨rfl, decide_eq_false (lt_irrefl _), Or.inr (by rw [hρC'])⟩
              · rw [if_neg h2A]
                have hLA00 : LA = 0 := by omega
                have hidx : (((hR : Nat) : Int) - LA).toNat = hR := by omega
                rw [hidx]
                refine ⟨rfl, decide_eq_false ?_, Or.inl rfl⟩
                rintro ⟨hi0, _⟩
                have hprod : ((heightOf (d + 2) (topIn M (M.size - 1) (d + 2) it.source) : Int) -
                    (hR : Int)) * (i' : Int) = 0 := by rw [← hLA']; exact hLA00
                rcases Int.mul_eq_zero.mp hprod with h0 | h0
                · omega
                · exact hi0 (by show i' = 0; omega)
        | case4 aA haA ρrA ρcA hρA hascA CA hclA' csRA csA0 hcsA gA hgA hbndA =>
            have hρA' : topIn M root.column (d + 2) it.source = some (ρrA, ρcA) := hρA
            rw [hρ] at hρA'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρA')
            have hCA : CA = C := by
              rcases hclA with h0 | h0 <;> rw [hclA'] at h0
              · cases h0
              · exact Option.some.inj h0
            subst hCA
            obtain ⟨j', _, rfl⟩ := List.mem_map.mp hcAm
            have hjj : j' = j := by
              apply hslotinj j'
              rw [← hjt, hT]
              unfold ChainCorr.CopyMonoProof.c4; split_ifs <;> rfl
            subst hjj
            refine ⟨fun h1 => ?_, fun hjR => ?_⟩
            · unfold ChainCorr.CopyMonoProof.c4; rw [hcb]
              simp only [Bool.false_eq_true, if_false]; rw [if_pos h1, hT]
            · subst hjR
              unfold ChainCorr.CopyMonoProof.c4; rw [hcb]
              simp only [Bool.false_eq_true, if_false]
              rw [if_neg (lt_irrefl _)]
              exact ⟨rfl, decide_eq_false (lt_irrefl _), Or.inr rfl⟩
      obtain ⟨hAlow, hAmid⟩ := hA
      refine ⟨ChainCorr.CopyMonoProof.c4 it.source it.source C d hR hB 0 false j,
        List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
      have hXC : XNode M (Kc M R root.column i).x C := by rw [← hρC']; exact hXρ
      have hcAt : cA.target = slot (d + 2) it.source j := hjt
      unfold ChainCorr.CopyMonoProof.c4
      simp only [Bool.false_eq_true, if_false]
      by_cases h1 : j < hR
      · rw [if_pos h1, hAlow h1]
        obtain ⟨hρc, hρ1, hρcell⟩ := Classification.mem_realNodes hmemρ
        have hρcell' : cell? M ⟨root.column, ρr.index⟩ = some ρc := by
          have : ρr = ⟨root.column, ρr.index⟩ := by simp only at hρc; rw [← hρc]
          rw [← this]; exact hρcell
        obtain ⟨q, hq, hqin⟩ := fill hb ρr.index ρc hρ1 hρcell' (topIn_inRegion hρ) j h1.le
        obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
        refine Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩)
        cases h' : topIn M root.column (d + 1) (slot (d + 2) it.source j) with
        | none => exact absurd h' (topIn_ne_none_of_node hqc hq1 hqcell hqin)
        | some ρ' => exact ⟨ρ', rfl⟩
      · rw [if_neg h1]
        by_cases h3 : hR < j
        · have hd : decide (hR < j) = true := decide_eq_true h3
          rw [hd]
          refine Or.inl ⟨rfl, hcAt, Or.inl ⟨C, rfl, rfl, hrts, hXC, ?_⟩⟩
          intro _ _ _ _ _
          simp only
          omega
        · have hjR : j = hR := by omega
          have hd : decide (hR < j) = false := decide_eq_false h3
          rw [hd]
          obtain ⟨hsrc, hcbA, hclA2⟩ := hAmid hjR
          have hoff0 : (((j : Nat) : Int) - (hB : Int) + ((0 : Nat) : Int)).toNat = 0 := by omega
          refine Or.inr (Or.inr ⟨C, ?_, ?_, ?_, hcbA, hclA2⟩)
          · rw [hsrc, hoff0, hjR]
          · rw [hsrc]; exact hrts
          · rw [hcAt, hsrc, hjR]

/-- Every lower emit of a new column is a row of the column. -/
theorem lo_node {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {X i x : Nat} {lo us : List (Emit × Origin)} (hD : ColData s n R M t root X i x lo us) :
    ∀ p ∈ lo, ∃ z ∈ realNodes R X, official z.2.row = p.1.row := by
  intro p hp
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
  have hsz := hD.size
  have hk : m + 1 < (R[X]'hD.XR).size := by rw [hsz]; simp; omega
  obtain ⟨hk', hrow, _⟩ := hD.node hk (by omega)
  refine ⟨(⟨X, m + 1⟩, (R[X]'hD.XR)[m + 1]'hk), ?_, ?_⟩
  · exact CopyShape.mem_realNodes_of_cell' (p := ⟨X, m + 1⟩)
      (by simp [cell?, Array.getElem?_eq_getElem hD.XR, Array.getElem?_eq_getElem hk])
      (by show 1 ≤ m + 1; omega)
  · simp only
    rw [hrow, official_stored']
    simp only [Nat.add_sub_cancel]
    rw [List.getElem_append_left hm]

/-- **The parallel run of `A` (copy of `x₀`, block `i - 1`) and `K` (copy of `c_r`, block
`i`).** -/
theorem simB {s : List Nat} {M R : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i i' : Nat} (hii : i' + 1 = i)
    (hBA : BCtx M R root.column (M.size - 1) i' (Ac M R root.column i' i))
    (hVR : MountainValid R) :
    ∀ (d : Nat) (a k : Item) (psA psK : List (Emit × Origin)),
      RelB M root.column (Kc M R root.column i) (d + 1) a k →
      Reach (Ac M R root.column i' i) (official t.row) (d + 1) a →
      runItemT (Ac M R root.column i' i) (d + 1) a = .ok psA →
      runItemT (Kc M R root.column i) (d + 1) k = .ok psK →
      (∀ p ∈ psA, ∃ z ∈ realNodes R (root.column + (M.size - 1 - root.column) * i),
        official z.2.row = p.1.row) →
      ∀ p ∈ psA, ∃ q ∈ psK, q.1.row = p.1.row
  | 0, a, k, psA, psK, hrel, _, hA, hK, hZ => by
      intro p hp
      have hb := hTop.build
      have hVM := build_valid_of_success hb
      have hA1 : levelOneT (Ac M R root.column i' i) a = .ok psA := by simpa [runItemT] using hA
      have hK1 : levelOneT (Kc M R root.column i) k = .ok psK := by simpa [runItemT] using hK
      have hpr := levelOneT_target hA1 p hp
      rcases hrel with ⟨_, htg, hI⟩ | ⟨rfl, _, _, _, _, ρ, hρ⟩ | ⟨C, rfl, hrt, htg, _, _⟩
      · obtain ⟨z, hzB, hzr⟩ := hZ p hp
        obtain ⟨q, hq, hqr⟩ := coverAll hVM hVR (ctx := Kc M R root.column i) rfl rfl
          (by show i ≠ 0; omega) (fun _ _ => rfl) 0 k psK hK hI z hzB
          (by rw [hzr, hpr, htg]; exact inRegion_self 1 k.target)
        exact ⟨q, hq, hqr.trans hzr⟩
      · have hS := inRegion_one (topIn_inRegion hρ)
        obtain ⟨q', hq'⟩ := Recon.RowLaw.nodeAt_of_mem (Recon.RowLaw.topIn_spec hρ).1
        obtain ⟨q, hq, hqr⟩ := levelOne_emits_target hK1 ⟨q', by
          show nodeAt M root.column a.source = some q'; rw [← hS]; exact hq'⟩
        exact ⟨q, hq, hqr.trans hpr.symm⟩
      · obtain ⟨ρ, hρ, hρC⟩ := topIn_of_rootTop (ctx := Kc M R root.column i) (M := M)
          (cr := root.column) rfl rfl hrt
        have hS := inRegion_one (topIn_inRegion hρ)
        obtain ⟨q', hq'⟩ := Recon.RowLaw.nodeAt_of_mem (Recon.RowLaw.topIn_spec hρ).1
        obtain ⟨q, hq, hqr⟩ := levelOne_emits_target hK1 ⟨q', by
          show nodeAt M root.column a.source = some q'; rw [← hS]; exact hq'⟩
        exact ⟨q, hq, hqr.trans (hpr.trans htg).symm⟩
  | d + 1, a, k, psA, psK, hrel, hReA, hA, hK, hZ => by
      intro p hp
      have hb := hTop.build
      have hVM := build_valid_of_success hb
      obtain ⟨csA, outsA, hchA, hmA, rfl⟩ := runItemT_step' hA
      obtain ⟨csK, outsK, hchK, hmK, rfl⟩ := runItemT_step' hK
      obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
      obtain ⟨cA, hcAm, hcAout⟩ := mem_of_mapM hmA hout
      have hcA := childItems_cases hchA
      have hcK := childItems_cases hchK
      have hpt := runItemT_target _ d cA out hcAout p hpo
      rcases hrel with ⟨_, htg, hI⟩ | ⟨rfl, hcl, hcb, hST, _, ρ, hρ⟩ |
          ⟨C, rfl, hrt, htg, hcb, hclA⟩
      · -- `K` covers its target
        obtain ⟨z, hzB, hzr⟩ := hZ p hp
        have hpa := runItemT_target _ (d + 1) a _ hA p hp
        obtain ⟨q, hq, hqr⟩ := coverAll hVM hVR (ctx := Kc M R root.column i) rfl rfl
          (by show i ≠ 0; omega) (fun _ _ => rfl) (d + 1) k _ hK hI z hzB
          (by rw [hzr, ← htg]; exact hpa)
        exact ⟨q, hq, hqr.trans hzr⟩
      · obtain ⟨cK, hcKm, hrelK⟩ := b2_step hTop hii hcA hcK hcl hcb hST hρ
          (reach_below hReA).1 hcAm
        obtain ⟨outK, houtK, hcKout⟩ := mapM_ok_of_mem' hmK hcKm
        obtain ⟨q, hq, hqr⟩ := simB hTop hii hBA hVR d cA cK out outK hrelK
          (Reach.child hReA hchA hcAm) hcAout hcKout
          (fun p' hp' => hZ p' (List.mem_flatten.mpr ⟨out, hout, hp'⟩)) p hpo
        exact ⟨q, List.mem_flatten.mpr ⟨outK, houtK, hq⟩, hqr⟩
      · obtain ⟨cK, hcKm, hrelK⟩ := b3_step hTop hii hBA hVR hcA hcK hrt htg hcb hclA hReA
          hcAm hpt (hZ p hp)
        obtain ⟨outK, houtK, hcKout⟩ := mapM_ok_of_mem' hmK hcKm
        obtain ⟨q, hq, hqr⟩ := simB hTop hii hBA hVR d cA cK out outK hrelK
          (Reach.child hReA hchA hcAm) hcAout hcKout
          (fun p' hp' => hZ p' (List.mem_flatten.mpr ⟨out, hout, hp'⟩)) p hpo
        exact ⟨q, List.mem_flatten.mpr ⟨outK, houtK, hq⟩, hqr⟩

/-- **`BoundaryPos` holds.** -/
theorem boundaryPos : BoundaryPos := by
  intro s n R hrun M t root hTop hcr1 i hi1 hin
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨_, _, _, _, hBasic⟩ := run_basic hrun
  have hVR : MountainValid R := hBasic.valid
  have hcr := hTop.lt
  have hn0 : n ≠ 0 := by omega
  have hsize := CopyShape.Found.run_size hrun hTop hn0
  have hMs := Canonical.build_size hb
  have hwi : (M.size - 1 - root.column) * i ≤ n * (M.size - 1 - root.column) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hin
  have hw1 : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hBlt : root.column + (M.size - 1 - root.column) * i < R.size := by rw [hsize]; omega
  obtain ⟨col, hcol, htc⟩ : ∃ col, M[M.size - 1]? = some col ∧ col.back? = some t := by
    have := hTop.top
    cases h' : M[M.size - 1]? with
    | none => rw [h'] at this; cases this
    | some col => rw [h'] at this; exact ⟨col, rfl, this⟩
  have hBRR := CutPredMD.boundaryRootRowsHolds s n R hrun M col t root hb hcol htc hTop.left hcr i
    hi1 hBlt
  -- the run of the copy of `c_r`
  obtain ⟨es, hes⟩ := kRun hb (K := Kc M R root.column i) (cr := root.column)
    (B := root.column + (M.size - 1 - root.column) * i) rfl rfl rfl (by omega)
    (by show i ≠ 0; omega) (fun _ _ => rfl) hBRR
  refine ⟨es, hes, ?_⟩
  intro hB kz hkz hkz1 hzτ
  -- the boundary column is the copy of `x₀` in block `i - 1`
  obtain ⟨M1, col1, t1, root1, hM1, hcol1, ht1, hTop1, hCI, hI⟩ :=
    run_new_column hrun hBlt (show s.length - 1 ≤ root.column + (M.size - 1 - root.column) * i
      by omega)
  have hMM : M = M1 := Except.ok.inj (hb.symm.trans hM1)
  subst hMM
  have hcc : col = col1 := Option.some.inj (hcol.symm.trans hcol1)
  subst hcc
  have htt : t = t1 := Option.some.inj (htc.symm.trans ht1)
  subst htt
  have hrr : root = root1 := Option.some.inj (hTop.left.symm.trans hTop1.left)
  subst hrr
  obtain ⟨i', x', loA, usA, hDA⟩ := colData hrun hTop hCI hI hBlt (by omega)
  obtain ⟨hx', hii⟩ := CutPredMD.boundary_source hcr (by omega) hDA.xb hDA.Xeq.symm
  subst hx'
  -- the emit of the node
  obtain ⟨hk', hrow, _⟩ := hDA.node hkz hkz1
  have hrow' : official R[root.column + (M.size - 1 - root.column) * i][kz].row =
      (loA ++ usA)[kz - 1].1.row := by rw [hrow, official_stored']
  have hlo : kz - 1 < loA.length := by
    by_contra hn
    have hmem : (loA ++ usA)[kz - 1] ∈ usA := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := hDA.us_ge _ hmem
    rw [← hrow'] at this
    exact absurd hzτ (not_lt.mpr this)
  have hpmem : (loA ++ usA)[kz - 1] ∈ loA := by
    rw [List.getElem_append_left hlo]; exact List.getElem_mem _
  have hZall := lo_node hDA
  -- the first item of the emit
  have hlA := hDA.hlo
  unfold lowerT at hlA
  simp only [bind, Except.bind, pure, Except.pure] at hlA
  split at hlA
  · cases hlA
  · rename_i outsA houtsA
    cases hlA
    have hesK := hes
    unfold lowerT at hesK
    simp only [bind, Except.bind, pure, Except.pure] at hesK
    split at hesK
    · cases hesK
    · rename_i outsK houtsK
      cases hesK
      obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hpmem
      obtain ⟨q0, hq0, hq0out⟩ := mem_of_mapM houtsA hout
      obtain ⟨outK, houtK, hq0K⟩ := mapM_ok_of_mem' houtsK hq0
      obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq0
      have hRe : Reach (Ac M R root.column i' i) (official t.row) q0.1 q0.2 := Reach.top hq0
      obtain ⟨ρ, hρ⟩ := firstRoot hTop hq0
      subst hkj
      have hrel : RelB M root.column (Kc M R root.column i) (k + 1)
          ⟨slot (k + 2) (official t.row) j, slot (k + 2) (official t.row) j, none, 0, false⟩
          ⟨slot (k + 2) (official t.row) j, slot (k + 2) (official t.row) j, none, 0, false⟩ :=
        Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, ρ, hρ⟩)
      obtain ⟨q, hq, hqr⟩ := simB hTop hii hDA.bctx hVR k _ _ out outK hrel hRe hq0out hq0K
        (fun p hp => hZall p (List.mem_flatten.mpr ⟨out, hout, hp⟩)) _ hpo
      exact ⟨q, List.mem_flatten.mpr ⟨outK, houtK, hq⟩, by rw [hqr, hrow']⟩

/-- **`RootShadowOut` holds.** -/
theorem rootShadowOut : RootShadowOut :=
  rootShadowOut_of_boundaryPos' boundaryPos

/-- **`LowerParentBelowHolds` holds.** -/
theorem lowerParentBelowHolds : LowerParentBelowHolds :=
  lowerParentBelowHolds_of_genLeg CopyShape.PBStageB.genLeg rootShadowOut

/-- **`ParentBelowHolds` holds.** -/
theorem parentBelowHolds : ParentBelowHolds :=
  parentBelowHolds_of_lower lowerParentBelowHolds

end OmegaY.Official.Recon.LowerPB.StageB

#print axioms OmegaY.Official.Recon.LowerPB.StageB.boundaryPos
#print axioms OmegaY.Official.Recon.LowerPB.StageB.lowerParentBelowHolds
#print axioms OmegaY.Official.Recon.LowerPB.StageB.parentBelowHolds
