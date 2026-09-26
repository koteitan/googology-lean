/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawChildren.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawItems

set_option backward.do.legacy false

/-!
# The children of an item

`Official.childItems` replaces an item of level `d + 2` by its children (notes/03 §2.4,
cases 1 to 4). `childSpec` records what the chain argument needs about them:

* the children are `F 0, …, F (n - 1)`, with targets the slots `T[0], …, T[n-1]`;
* their sources are slots `S[σ j]` with `σ` monotone;
* if the source column has a node in `S`, then `n > 0` and it has a node in the source of
  the first child;
* every child satisfies the offset condition.

Two facts about the source mountain are used: an ascending column has a node at the row of
the root top (`node_of_ascends`, so `h_ρ ≤ h_a`), and the root top is not above the last
column top in the region (`Top.rootCut_region`, so the lift `Δ = (h_κ - h_ρ) i ≥ 0`).
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

/-- What the chain argument needs about the children of an item of level `d + 2`. -/
def ChildSpec (ctx : Context) (d : Nat) (it : Item) (children : List Item) : Prop :=
  ∃ (n : Nat) (F : Nat → Item) (σ : Nat → Nat),
    children = (List.range n).map F ∧
    (∀ j, (F j).target = slot (d + 2) it.target j) ∧
    (∀ j, (F j).source = slot (d + 2) it.source (σ j)) ∧
    (∀ j j', j ≤ j' → σ j ≤ σ j') ∧
    (Has ctx (d + 2) it.source → 0 < n ∧ Has ctx (d + 1) (F 0).source) ∧
    (∀ j, j < n → OffsetOK ctx (F j))

theorem ok_eq {ε α : Type} (x : Except ε α) : Ok x (fun a => x = .ok a) := fun _ h => h

theorem range_filter_ge (a h : Nat) :
    (List.range a).filter (fun x => decide (h ≤ x)) = (List.range (a - h)).map (· + h) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases hh : h ≤ a
    · rw [show a + 1 - h = (a - h) + 1 by omega, List.range_succ, List.map_append]
      simp [hh, show a - h + h = a by omega]
    · rw [show a + 1 - h = a - h by omega]
      simp [hh]

theorem offsetOK_of_none {ctx : Context} {it : Item} (h : it.clean = none) : OffsetOK ctx it := by
  intro C hC
  rw [h] at hC
  cases hC

theorem offsetOK_of_zero {ctx : Context} {it : Item} (h : it.offset = 0) : OffsetOK ctx it := by
  intro _ _ _ _ _ _ _ _
  rw [h]
  exact Nat.zero_le _

theorem spec_of {ctx : Context} {d : Nat} {it : Item} {hT : Nat}
    (hslot : ∀ h, h ≤ hT → Has ctx (d + 1) (slot (d + 2) it.source h))
    (n : Nat) (F : Nat → Item) (σ : Nat → Nat)
    (htgt : ∀ j, (F j).target = slot (d + 2) it.target j)
    (hsrc : ∀ j, (F j).source = slot (d + 2) it.source (σ j))
    (hmono : ∀ j j', j ≤ j' → σ j ≤ σ j')
    (hfirst : 0 < n ∧ σ 0 ≤ hT)
    (hoff : ∀ j, j < n → OffsetOK ctx (F j)) :
    ChildSpec ctx d it ((List.range n).map F) := by
  refine ⟨n, F, σ, rfl, htgt, hsrc, hmono, fun _ => ⟨hfirst.1, ?_⟩, hoff⟩
  rw [hsrc 0]
  exact hslot _ hfirst.2

/-- **The children of an item.** -/
theorem childSpec {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) (d + 2) it) :
    Ok (childItems ctx (d + 2) it) (ChildSpec ctx d it) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  unfold childItems
  dsimp only
  split
  · -- no node of column `x` in the region
    rename_i hnone
    refine ok_pure ⟨0, fun j => ⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0,
      false⟩, id, by simp, fun _ => rfl, fun _ => rfl, fun _ _ h => h, ?_, ?_⟩
    · intro hH
      exact absurd hnone (has_iff_topIn.mp hH)
    · intro j hj
      omega
  · rename_i aRef aCell hA
    have hslot : ∀ h, h ≤ (official aCell.row).coeff d → Has ctx (d + 1) (slot (d + 2) it.source h) :=
      fun h hh => has_slot_of_top hb hA hh
    have hTdef : height (d + 2) (official aCell.row) = (official aCell.row).coeff d := height_eq _ _
    refine ok_bind (ok_eq _) (fun asc hasc => ?_)
    split
    · -- case 1: not ascending
      split
      · exact ok_throw_bind _ _
      · rename_i hflags
        refine ok_pure ⟨_, _, id, rfl, fun _ => rfl, fun _ => rfl, fun _ _ h => h, ?_, ?_⟩
        · intro _
          exact ⟨by omega, hslot 0 (Nat.zero_le _)⟩
        · intro j _
          exact offsetOK_of_none rfl
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
        · -- case 2: lift
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
          have he : 0 ≤ e := by rw [← hedef]; split <;> omega
          refine ok_pure (spec_of hslot _ _ (fun j => if j < hR then j
            else if (j : Int) < hR + lift + e then hR else ((j : Int) - lift).toNat) ?_ ?_ ?_ ?_ ?_)
          · intro j
            try dsimp only
            split_ifs <;> rfl
          · intro j
            try dsimp only
            split_ifs <;> rfl
          · intro j j' hjj
            try dsimp only
            split_ifs <;> omega
          · refine ⟨by omega, ?_⟩
            try dsimp only
            split_ifs <;> omega
          · intro j _
            try dsimp only
            split_ifs
            · exact offsetOK_of_none rfl
            · exact offsetOK_of_zero rfl
            · exact offsetOK_of_none rfl
        · -- case 3: cut bottom
          generalize (official ρCell.row).coeff d = hR at hRT ⊢
          generalize (official aCell.row).coeff d = hT at hRT hslot ⊢
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          simp only [range_filter_ge, List.map_map]
          refine ok_pure (spec_of hslot _ _ (fun m => if ((m + hR : Nat) : Int) < hB + hR + e then hR
            else m + hR - hB) ?_ ?_ ?_ ?_ ?_)
          · intro j
            simp only [Function.comp_apply]
            split_ifs <;> simp only [Nat.add_sub_cancel]
          · intro j
            simp only [Function.comp_apply]
            split_ifs <;> rfl
          · intro j j' hjj
            try dsimp only
            split_ifs <;> omega
          · refine ⟨?_, ?_⟩
            · split <;> omega
            · try dsimp only
              split_ifs <;> omega
          · intro j _
            simp only [Function.comp_apply]
            split_ifs
            · exact offsetOK_of_zero rfl
            · exact offsetOK_of_none rfl
      · -- case 4: a copied root row
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
            · have hoff : ctx.block ≠ 0 → it.offset ≤ g :=
                fun hi => hit.offset C hC hi csRef cs g hq hg
              generalize (official ρCell.row).coeff d = hR at hRT ⊢
              generalize (official aCell.row).coeff d = hT at hRT hslot ⊢
              intro children hch
              simp only [Except.ok.injEq] at hch
              subst hch
              refine spec_of hslot _ _ (fun j => if it.cutBottom = true then hR
                else if j < hR then j else hR) ?_ ?_ ?_ ?_ ?_
              · intro j
                try dsimp only
                split_ifs <;> rfl
              · intro j
                try dsimp only
                split_ifs <;> rfl
              · intro j j' hjj
                try dsimp only
                split_ifs <;> omega
              · refine ⟨?_, ?_⟩
                · split
                  · omega
                  · rename_i hi
                    have := hoff hi
                    omega
                · try dsimp only
                  split_ifs <;> omega
              · intro j hj C' hC' hi csRef' cs' g' hq' hg'
                have hC'' : C' = C := by
                  try dsimp only at hC'
                  split_ifs at hC' <;> (cases hC'; rfl)
                subst hC''
                rw [hq] at hq'
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hq')
                rw [hg] at hg'
                obtain rfl := Except.ok.inj hg'
                have := hoff hi
                rw [if_neg hi] at hj
                try dsimp only
                split_ifs <;> (try simp only) <;> omega

end OmegaY.Official.Recon.RowLaw
