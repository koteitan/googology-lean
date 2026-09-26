/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerChildren.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerSplit

set_option backward.do.legacy false

/-!
# Every child of an item emits

`childSpec` (`RowLawChildren.lean`) says that the first child of an item emits when the
source column has a node in the source region. This file shows the same for **every** child
(`childSpecAll`): the sources of the children are slots `S[σ j]` with `σ j ≤ h_a`, the height
of the top `a` of the source column in `S` (in case 2 the lifted slots `j - Δ ≤ h_a`, in
case 3 `j - h_q ≤ h_a`, and the root slot `h_ρ ≤ h_a` because an ascending column has a node
at the reference row).

Consequences for the tree of a column (`run_top`): the output of an item of level `d + 2`
with a node in its source region contains a row of height (coefficient `d`) exactly
`n - 1`, `n` its number of children. So for a lower pair, `λ` has height `N_X(J) - 1`
(`lam_height`), and `LowerJHolds` is equivalent to asking for an item `J'` of `Y` with the
target of `J`, a node in its source region, and fewer children than `J`
(`LowerJFewer`, `lowerJ_of_fewer`).
-/

namespace OmegaY.Official.Recon.JumpLawLower

open Canonical Expansion Dimension RowLaw JumpLaw

/-- The children of an item, with every child emitting. -/
def ChildSpecAll (ctx : Context) (d : Nat) (it : Item) (children : List Item) : Prop :=
  ∃ (n : Nat) (F : Nat → Item) (σ : Nat → Nat),
    children = (List.range n).map F ∧
    (∀ j, (F j).target = slot (d + 2) it.target j) ∧
    (∀ j, (F j).source = slot (d + 2) it.source (σ j)) ∧
    (Has ctx (d + 2) it.source → ∀ j, j < n → Has ctx (d + 1) (F j).source)

theorem specAll_of {ctx : Context} {d : Nat} {it : Item} {hT : Nat}
    (hslot : ∀ h, h ≤ hT → Has ctx (d + 1) (slot (d + 2) it.source h))
    (n : Nat) (F : Nat → Item) (σ : Nat → Nat)
    (htgt : ∀ j, (F j).target = slot (d + 2) it.target j)
    (hsrc : ∀ j, (F j).source = slot (d + 2) it.source (σ j))
    (hbound : ∀ j, j < n → σ j ≤ hT) :
    ChildSpecAll ctx d it ((List.range n).map F) := by
  refine ⟨n, F, σ, rfl, htgt, hsrc, fun _ j hj => ?_⟩
  rw [hsrc j]
  exact hslot _ (hbound j hj)

/-- **Every child emits.** -/
theorem childSpecAll {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) (d + 2) it) :
    Ok (childItems ctx (d + 2) it) (ChildSpecAll ctx d it) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  unfold childItems
  dsimp only
  split
  · rename_i hnone
    refine ok_pure ⟨0, fun j => ⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0,
      false⟩, id, by simp, fun _ => rfl, fun _ => rfl, ?_⟩
    intro hH
    exact absurd hnone (has_iff_topIn.mp hH)
  · rename_i aRef aCell hA
    have hslot : ∀ h, h ≤ (official aCell.row).coeff d → Has ctx (d + 1) (slot (d + 2) it.source h) :=
      fun h hh => has_slot_of_top hb hA hh
    refine ok_bind (ok_eq _) (fun asc hasc => ?_)
    split
    · -- case 1
      split
      · exact ok_throw_bind _ _
      · refine ok_pure (specAll_of hslot _ _ id (fun _ => rfl) (fun _ => rfl) ?_)
        intro j hj
        simp only [height_eq] at hj
        simp only [id]
        omega
    · rename_i hasc'
      have hasc_true : asc = true := by simpa using hasc'
      subst hasc_true
      obtain ⟨⟨ρRef, ρCell⟩, hρ, p, hp, hprow⟩ := node_of_ascends hctx hasc
      obtain ⟨_, hρin, _⟩ := topIn_spec hρ
      have hpin : inRegion (d + 2) it.source (official p.2.row) = true := by
        rw [hprow]; exact hρin
      have hRT : (official ρCell.row).coeff d ≤ (official aCell.row).coeff d := by
        refine coeff_le_of_inRegion hρin (topIn_spec hA).2.1 ?_
        rw [← hprow]
        exact topIn_row_max hb hA hp hpin
      rw [hρ]
      generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
      simp only [heightOf, height_eq]
      split
      · rename_i hcl
        split
        · -- case 2
          rename_i hcut
          have hρ' : topIn ctx.source root.column (d + 2) it.source = some (ρRef, ρCell) := by
            rw [← hctx.rootc]; exact hρ
          obtain ⟨⟨κRef, κCell⟩, hκ, hle⟩ := Top.rootCut_region hctx.top hit.below hρ'
          have hκ' : topIn ctx.source ctx.lastColumn (d + 2) it.source = some (κRef, κCell) := by
            rw [hctx.last]; exact hκ
          have hRK : (official ρCell.row).coeff d ≤ (official κCell.row).coeff d :=
            coeff_le_of_inRegion hρin (topIn_spec hκ).2.1 hle
          rw [hκ']
          have hlift : (0 : Int) ≤ ((((official κCell.row).coeff d : Nat) : Int) -
              (((official ρCell.row).coeff d : Nat) : Int)) * ctx.block :=
            Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
          generalize ((((official κCell.row).coeff d : Nat) : Int) -
              (((official ρCell.row).coeff d : Nat) : Int)) * ctx.block = lift at hlift ⊢
          generalize (official ρCell.row).coeff d = hR at hRT hRK ⊢
          generalize (official aCell.row).coeff d = hT at hRT hslot ⊢
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          refine ok_pure (specAll_of hslot _ _ (fun j => if j < hR then j
            else if (j : Int) < hR + lift + e then hR else ((j : Int) - lift).toNat) ?_ ?_ ?_)
          · intro j
            try dsimp only
            split_ifs <;> rfl
          · intro j
            try dsimp only
            split_ifs <;> rfl
          · intro j hj
            try dsimp only
            split_ifs <;> omega
        · -- case 3
          generalize (official ρCell.row).coeff d = hR at hRT ⊢
          generalize (official aCell.row).coeff d = hT at hRT hslot ⊢
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          simp only [range_filter_ge, List.map_map]
          refine ok_pure (specAll_of hslot _ _ (fun m => if ((m + hR : Nat) : Int) < hB + hR + e
            then hR else m + hR - hB) ?_ ?_ ?_)
          · intro j
            simp only [Function.comp_apply]
            split_ifs <;> simp only [Nat.add_sub_cancel]
          · intro j
            simp only [Function.comp_apply]
            split_ifs <;> rfl
          · intro j hj
            try dsimp only
            split_ifs <;> split at hj <;> omega
      · -- case 4
        rename_i C hC
        split
        · exact ok_throw_bind _ _
        · rename_i q hq
          obtain ⟨csRef, cs⟩ := q
          simp only [pure, Except.pure, bind, Except.bind]
          cases hg : generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 with
          | error _ => intro _ h; cases h
          | ok g =>
            simp only
            split
            · intro _ h; cases h
            · generalize (official ρCell.row).coeff d = hR at hRT ⊢
              generalize (official aCell.row).coeff d = hT at hRT hslot ⊢
              intro children hch
              simp only [Except.ok.injEq] at hch
              subst hch
              refine specAll_of hslot _ _ (fun j => if it.cutBottom = true then hR
                else if j < hR then j else hR) ?_ ?_ ?_
              · intro j
                try dsimp only
                split_ifs <;> rfl
              · intro j
                try dsimp only
                split_ifs <;> rfl
              · intro j _
                try dsimp only
                split_ifs <;> omega

/-! ## The top of the output of an item -/

/-- **The output of an item with a node in its source region reaches the last slot.** -/
theorem run_top {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item}
    (hA : ItemOK ctx (official t.row) (d + 2) A) (hH : Has ctx (d + 2) A.source)
    {L : List Emit} (hL : runItem ctx (d + 2) A = .ok L) {cs : List Item}
    (hcs : childItems ctx (d + 2) A = .ok cs) :
    0 < cs.length ∧ ∃ em ∈ L, em.row.coeff d = cs.length - 1 := by
  obtain ⟨cs', outs, hcs', hF, rfl⟩ := runItem_children hL
  rw [hcs] at hcs'
  obtain rfl := Except.ok.inj hcs'
  obtain ⟨n, F, σ, hcsF, htgt, hsrc, hall⟩ := childSpecAll hctx hA cs hcs
  obtain ⟨hlen, hget⟩ := forall₂_getElem hF
  have hn : cs.length = n := by rw [hcsF]; simp
  obtain ⟨n', F', σ', hcsF', _, _, _, hfirst', _⟩ := childSpec hctx hA cs hcs
  have hn' : cs.length = n' := by rw [hcsF']; simp
  have hpos : 0 < n' := (hfirst' hH).1
  refine ⟨by omega, ?_⟩
  have hlast : cs.length - 1 < cs.length := by omega
  have hlo : cs.length - 1 < outs.length := by omega
  obtain ⟨hmOK, hmtgt⟩ := child_itemOK hctx hA hcs _ hlast
  have hgood := runItem_good hctx (d + 1) (by omega) cs[cs.length - 1] hmOK outs[cs.length - 1]
    (hget _ hlast hlo)
  have hHm : Has ctx (d + 1) cs[cs.length - 1].source := by
    have := hall hH (cs.length - 1) (by omega)
    have hce : cs[cs.length - 1] = F (cs.length - 1) := by
      simp only [hcsF, List.getElem_map, List.getElem_range]
    rw [hce]
    exact this
  obtain ⟨em, hem⟩ := List.exists_mem_of_ne_nil _ (hgood.2.mp hHm)
  have hin := hgood.1.2.1 em hem
  rw [hmtgt] at hin
  exact ⟨em, List.mem_flatten.mpr ⟨_, List.getElem_mem hlo, hem⟩, (inRegion_slot_iff.mp hin).2⟩

/-! ## The height of `λ` -/

/-- **`λ` lies in the last child of `J`.** For a lower pair with `e = d + 1`, the height
(coefficient `d`) of `λ` is the number of children of `J` minus one. -/
theorem lam_height {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    {lam θ : Row} {l d : Nat} {J : Item} (hP : LowerPair s n R M t root i x lam θ l (d + 1) J)
    {cs : List Item} (hcs : childItems (colCtx M R root i x) (d + 2) J = .ok cs) :
    lam.coeff d + 1 = cs.length := by
  have hctx := hP.nc.runCtx
  obtain ⟨vs, us, col, hvs, _, _, k, hk, hkL, hlam, _, _, ⟨LJ, hLJ, hlamJ⟩, hmax⟩ := hP.run
  obtain ⟨_, hJOK, LB, hLB, hLBsub, _⟩ := inTree_facts hctx hvs hP.tree
  have hLBJ : LB = LJ := Except.ok.inj (hLB.symm.trans hLJ)
  subst hLBJ
  have hgood := runItem_good hctx (d + 1 + 1) (by omega) J hJOK LB hLB
  have hH : Has (colCtx M R root i x) (d + 2) J.source := hgood.2.mpr (List.ne_nil_of_mem hlamJ)
  obtain ⟨_, em, hem, hemc⟩ := run_top hctx hJOK hH hLB hcs
  have hlt := run_coeff_lt hctx hJOK hLB hcs _ hlamJ
  have hemin := hgood.1.2.1 em hem
  have hle := hmax em (hLBsub em hem) hemin
  have hlamin := hgood.1.2.1 _ hlamJ
  rw [hlam] at hlt hlamin
  have := coeff_le_of_inRegion hemin hlamin hle
  omega

/-- **Open (tree form, children count).** For a lower pair with the item `J` of `X`, the item
tree of `Y = φ_i(l)` has an item `J'` with the target of `J`, a node of its source column in
its source region, and, when `e ≥ 1`, fewer children than `J`. -/
def LowerJFewer : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (lam θ : Row) (l e : Nat) (J : Item), LowerPair s n R M t root i x lam θ l e J →
    ∀ i' x', NewColumn s n R M t root i' x' →
      legCol (colCtx M R root i x) l = x' + (M.size - 1 - root.column) * i' →
      ∃ J', InTree (colCtx M R root i' x') (official t.row) (e + 1) J' ∧
        J'.target = J.target ∧ Has (colCtx M R root i' x') (e + 1) J'.source ∧
        ∀ d, e = d + 1 → ∀ cs cs', childItems (colCtx M R root i x) (d + 2) J = .ok cs →
          childItems (colCtx M R root i' x') (d + 2) J' = .ok cs' → cs'.length < cs.length

/-- **`LowerJHolds` from `LowerJFewer`.** -/
theorem lowerJ_of_fewer (hF : LowerJFewer) : LowerJHolds := by
  intro s n R M t root i x lam θ l e J hP i' x' hNC' hY
  obtain ⟨J', hJ', htgt, hHas, hfew⟩ := hF s n R M t root i x lam θ l e J hP i' x' hNC' hY
  refine ⟨J', hJ', htgt, hHas, ?_⟩
  intro d hd cs' hcs'
  subst hd
  obtain ⟨vs, us, col, hvs, _, _, k, hk, hkL, _, _, _, ⟨LJ, hLJ, _⟩, _⟩ := hP.run
  obtain ⟨cs, outs, hcs, _, _⟩ := runItem_children hLJ
  have h1 := lam_height hP hcs
  have h2 := hfew d rfl cs cs' hcs hcs'
  omega

end OmegaY.Official.Recon.JumpLawLower

#print axioms OmegaY.Official.Recon.JumpLawLower.childSpecAll
#print axioms OmegaY.Official.Recon.JumpLawLower.lam_height
#print axioms OmegaY.Official.Recon.JumpLawLower.lowerJ_of_fewer
