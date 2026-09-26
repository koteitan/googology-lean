/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeCutForm.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeProfileLegOrder

set_option backward.do.legacy false

/-!
# Where the gap copies of a copied column lie (the map `Ψ`)

A gap copy (`Origin.clean _ true`, `cutO = true`) of a copied column with origin row `C` lies
strictly above the images `Ψ(r)` of the rows `r ≤ C` and strictly below the images of the rows
`r > C` of its first item, where `Ψ = Ψ E (topA ctx)` is the row map of the column
(`LegRowMatchInnerMap.lean`), and `C` is the row of a node of the root column where the column
ascends.

* `CutΨ`: the statement for an item (for a clean item, only rows up to its root row count; for an
  item that skips the bottom of its region, only rows above the root top).
* `levelOneT_cut`, `childItems_cut`, `runItemT_cut`: the induction over the items (the case
  analysis of `InnerRow.childItems_formula`).
* `AscRow`, `childItems_invA`, `runItemT_asc`: the origin row of a gap copy is the row of a root
  top where the column ascends.
* `lowerT_cut`: the statement for a lower copy of a block context.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.LowerPB
open CopyShape.NoMA CopyShape.InnerRow

/-! ## The statement for an item -/

/-- The gap copies of an item lie between the images of the rows at or below their origin row
and the images of the rows above it. -/
def CutΨ (E : Env) (top : Nat → Row → Option (Ref × Cell)) (D : Nat) (it : Item)
    (p : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin p.2 = true → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
    inRegion D it.target p.1.row = true ∧
    (∀ C, it.clean = some C → it.cutBottom = true → official c0.row = C) ∧
    (it.clean = none → it.cutBottom = true → ∀ ρ, top D it.source = some ρ →
      official ρ.2.row ≤ official c0.row) ∧
    (it.clean = none →
      (∀ r, inRegion D it.source r = true → r ≤ official c0.row →
        (it.cutBottom = true → ∀ ρ, top D it.source = some ρ → official ρ.2.row < r) →
        Ψ E top it.cutBottom D it.source it.target r < p.1.row) ∧
      (∀ r, inRegion D it.source r = true → official c0.row < r →
        p.1.row < Ψ E top it.cutBottom D it.source it.target r)) ∧
    (∀ C, it.clean = some C → it.cutBottom = false →
      ∀ r, inRegion D it.source r = true → r ≤ C →
        (r ≤ official c0.row → Ψ E top false D it.source it.target r < p.1.row) ∧
        (official c0.row < r → p.1.row < Ψ E top false D it.source it.target r))

/-! ## Level one -/

theorem levelOneT_cut {ctx : Context} {R : Mountain} {B : Nat} {it : Item}
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, CutΨ (Env.ofCtx ctx R B) (topA ctx) 1 it p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp
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
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp hk c0 hc0
                simp only [List.mem_singleton] at hp
                subst hp
                have hcb : it.cutBottom = true := by
                  cases hb : it.cutBottom
                  · rw [hb] at hk; simp [ChainCorr.cutOrigin] at hk
                  · rfl
                have hcc : c0 = cs := by
                  simp only [Env.ofCtx_M, Origin.src] at hc0
                  exact Option.some.inj (hc0.symm.trans hccell)
                subst hcc
                refine ⟨inRegion_self 1 _, ?_, ?_, ?_, ?_⟩
                · intro C' hC' _
                  rw [hC] at hC'
                  cases hC'
                  exact hcrow
                · intro hn; rw [hC] at hn; cases hn
                · intro hn; rw [hC] at hn; cases hn
                · intro C' _ hb; rw [hcb] at hb; cases hb
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp hk
            simp only [List.mem_singleton] at hp
            subst hp
            simp [ChainCorr.cutOrigin] at hk
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp hk
              simp only [List.mem_singleton] at hp
              subst hp
              simp [ChainCorr.cutOrigin] at hk

/-! ## Comparisons through the slots of a region -/

theorem ΨF_slot_lt {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {T : Row}
    {m : Bool} {S' r : Row} {j j' : Nat} {x : Row}
    (hx : inRegion (d + 1) (slot (d + 2) T j') x = true) (h : j < j') :
    Ψ E top m (d + 1) S' (slot (d + 2) T j) r < x :=
  ChainCorr.Inner.slot_rows_lt (Ψ_mem E top d m S' _ r) hx h

theorem ΨF_slot_gt {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {T : Row}
    {m : Bool} {S' r : Row} {j j' : Nat} {x : Row}
    (hx : inRegion (d + 1) (slot (d + 2) T j) x = true) (h : j < j') :
    x < Ψ E top m (d + 1) S' (slot (d + 2) T j') r :=
  ChainCorr.Inner.slot_rows_lt hx (Ψ_mem E top d m S' _ r) h

/-! ## The step: from the children to the item -/

theorem childItems_cut {ctx : Context} {R : Mountain} {B : Nat} {d : Nat} {it : Item}
    {cs : List Item} (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx (d + 2) it = .ok cs)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) it)
    (hMD : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf (d + 2) (some (ρr, ρc)) <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source)) :
    ∀ c ∈ cs, ∀ p, EOKw (Env.ofCtx ctx R B) ctx.x (d + 1) c p →
      CutΨ (Env.ofCtx ctx R B) (topA ctx) (d + 1) c p →
      CutΨ (Env.ofCtx ctx R B) (topA ctx) (d + 2) it p := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · -- the column has no node in the region
    obtain rfl := Except.ok.inj h
    simp
  · rename_i _ aRef aCell hA
    split at h
    · cases h
    · rename_i _ v hv
      split at h
      · -- case 1: the region does not ascend
        rename_i hnv
        have hv0 : v = false := by simpa using hnv
        subst hv0
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hcond
          obtain rfl := Except.ok.inj h
          have hcl : it.clean = none := by
            cases hc : it.clean
            · rfl
            · exact absurd (Or.inl (by simp [hc])) hcond
          have hcb : it.cutBottom = false := by
            cases hb : it.cutBottom
            · rfl
            · exact absurd (Or.inr (Or.inr hb)) hcond
          have htop : topA ctx (d + 2) it.source = none := by
            apply topA_of_not_asc
            intro ρ hρ
            rw [hrho] at hρ
            subst hρ
            exact hv
          intro ch hch p hpw hpc hk c0 hc0
          simp only [List.mem_map] at hch
          obtain ⟨j, _, rfl⟩ := hch
          obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
          obtain ⟨hT, _, _, hnone, _⟩ := hpc hk c0 hc0
          obtain ⟨ha, hb⟩ := hnone rfl
          simp only at hreg hT ha hb
          have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
          have hCS := Recon.RowLaw.inRegion_of_slot hreg
          refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
            fun _ hb' => absurd hb' (by simp [hcb]),
            fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
          · intro r hr hrC _
            rw [hcb, ΨF_none htop]
            have hσ : r.coeff d ≤ j := by
              rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC
            rcases Nat.lt_or_eq_of_le hσ with hl | he
            · exact ΨF_slot_lt hT hl
            · have hrs : inRegion (d + 1) (slot (d + 2) it.source j) r = true := by
                rw [← he]; exact slot_mem hr
              rw [he]
              exact ha r hrs hrC (fun h => by cases h)
          · intro r hr hrC
            rw [hcb, ΨF_none htop]
            have hσ : j ≤ r.coeff d := by
              rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
            rcases Nat.lt_or_eq_of_le hσ with hl | he
            · exact ΨF_slot_gt hT hl
            · have hrs : inRegion (d + 1) (slot (d + 2) it.source j) r = true := by
                rw [he]; exact slot_mem hr
              rw [← he]
              exact hb r hrs hrC
      · -- the region ascends
        rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hhR : heightOf (d + 2) (some (ρr, ρc)) = (official ρc.row).coeff d := by
          simp [heightOf, Recon.RowLaw.height_eq]
        have hsub := ChainCorr.Inner.topIn_slot hrho
        rw [← hhR] at hsub
        have hρreg := topIn_inRegion hrho
        have hρslot : inRegion (d + 1) (slot (d + 2) it.source (heightOf (d + 2) (some (ρr, ρc))))
            (official ρc.row) = true :=
          Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρreg, hhR.symm⟩
        have hMD' := hMD ρr ρc hrho hv
        have htop : topA ctx (d + 2) it.source = some (ρr, ρc) := topA_of_asc hrho hv
        have htopsub : topA ctx (d + 1)
            (slot (d + 2) it.source (heightOf (d + 2) (some (ρr, ρc)))) = some (ρr, ρc) :=
          topA_of_asc hsub hv
        have hEL : (Env.ofCtx ctx R B).lift (d + 2) it.source =
            (heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) -
              heightOf (d + 2) (some (ρr, ρc))) * ctx.block := by
          unfold Env.lift
          simp only [Env.ofCtx_M, Env.ofCtx_x0, Env.ofCtx_cr, Env.ofCtx_i]
          rw [hrho]
          apply max_eq_left
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        have hLint : ((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) : Int) -
            (heightOf (d + 2) (some (ρr, ρc)) : Int)) * (ctx.block : Int) =
            (((Env.ofCtx ctx R B).lift (d + 2) it.source : Nat) : Int) := by
          rw [hEL, Nat.cast_mul, Nat.cast_sub hMD'.le]
        have hL1 := (Env.ofCtx ctx R B).one_le_lift (d + 2) it.source
        have hEB : (Env.ofCtx ctx R B).hB (d + 2) it.target =
            heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) := by
          unfold Env.hB
          rw [hbnd]
          rfl
        simp only at h
        rw [hLint] at h
        generalize hLdef : (Env.ofCtx ctx R B).lift (d + 2) it.source = L at h hL1
        generalize hRdef : heightOf (d + 2) (some (ρr, ρc)) = hR at h hhR hsub hρslot htopsub
        -- the slot of a row of the region, compared with the slot of `ρ`
        have hσle : ∀ r, inRegion (d + 2) it.source r = true → r ≤ official ρc.row →
            r.coeff d ≤ hR := fun r hr h => by
          rw [hhR]; exact Recon.RowLaw.coeff_le_of_inRegion hr hρreg h
        have hσge : ∀ r, inRegion (d + 2) it.source r = true → official ρc.row < r →
            hR ≤ r.coeff d := fun r hr h => by
          rw [hhR]; exact Recon.RowLaw.coeff_le_of_inRegion hρreg hr h.le
        -- at level 2 the slot of `ρ` holds only `ρ`
        have hlev2 : ∀ r, d = 0 → inRegion (d + 2) it.source r = true → official ρc.row < r →
            r.coeff d ≠ hR := by
          intro r hd hr hlt heq
          subst hd
          have h1 : inRegion (0 + 1) (slot (0 + 2) it.source hR) r = true := by
            rw [← heq]; exact slot_mem hr
          have e1 := inRegion_one h1
          have e2 := inRegion_one hρslot
          rw [e1, ← e2] at hlt
          exact lt_irrefl _ hlt
        split at h
        · -- clean = none
          rename_i hcl
          split at h
          · -- case 2: lift
            rename_i hcb'
            have hcb : it.cutBottom = false := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            obtain rfl := Except.ok.inj h
            intro ch hch p hpw hpc
            simp only [List.mem_map] at hch
            obtain ⟨j, _, rfl⟩ := hch
            split_ifs at hpw hpc with h1 h2
            · -- below the root top
              intro hk c0 hc0
              obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
              obtain ⟨hT, _, _, hnone, _⟩ := hpc hk c0 hc0
              obtain ⟨ha, hb⟩ := hnone rfl
              simp only at hreg hT ha hb
              have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
              have hCS := Recon.RowLaw.inRegion_of_slot hreg
              have hCρ : official c0.row < official ρc.row :=
                ChainCorr.Inner.slot_rows_lt hreg hρslot h1
              refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                fun _ hb' => absurd hb' (by simp [hcb]),
                fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
              · intro r hr hrC _
                rw [hcb, ΨF_low htop (hrC.trans hCρ.le)]
                have hσ : r.coeff d ≤ j := by
                  rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC
                rcases Nat.lt_or_eq_of_le hσ with hl | hq
                · exact ΨF_slot_lt hT hl
                · rw [hq]
                  exact ha r (by rw [← hq]; exact slot_mem hr) hrC (fun h => by cases h)
              · intro r hr hrC
                rw [hcb]
                have hσ : j ≤ r.coeff d := by
                  rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                by_cases hrρ : r ≤ official ρc.row
                · rw [ΨF_low htop hrρ]
                  rcases Nat.lt_or_eq_of_le hσ with hl | hq
                  · exact ΨF_slot_gt hT hl
                  · rw [← hq]; exact hb r (by rw [hq]; exact slot_mem hr) hrC
                · have hρr : official ρc.row < r := lt_of_not_ge hrρ
                  have hσR := hσge r hr hρr
                  by_cases hσe : r.coeff d = (official ρc.row).coeff d
                  · rw [ΨF_mid htop hρr hσe, hLdef]
                    exact ΨF_slot_gt hT (by omega)
                  · rw [ΨF_high htop hρr hσe, hLdef]
                    exact ΨF_slot_gt hT (by omega)
            · -- a copy of the root row
              by_cases hjR : hR < j
              · -- a gap copy: its origin is `ρ`
                have hdec : decide (hR < j) = true := decide_eq_true hjR
                simp only [hdec] at hpw hpc
                intro hk c0 hc0
                obtain ⟨hT, hcc, _, _, _⟩ := hpc hk c0 hc0
                simp only at hT hcc
                have hCeq : official c0.row = official ρc.row := hcc _ rfl trivial
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ hb' => absurd hb' (by simp [hcb]),
                  fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · intro r hr hrC _
                  rw [hCeq] at hrC
                  rw [hcb, ΨF_low htop hrC]
                  exact ΨF_slot_lt hT (by have := hσle r hr hrC; omega)
                · intro r hr hrC
                  rw [hCeq] at hrC
                  rw [hcb]
                  have hσR := hσge r hr hrC
                  by_cases hσe : r.coeff d = (official ρc.row).coeff d
                  · rw [ΨF_mid htop hrC hσe, hLdef]
                    apply ΨF_slot_gt hT
                    rcases he with ⟨he1, hd0⟩ | ⟨he0, _⟩
                    · exact absurd (hσe.trans hhR.symm) (hlev2 r hd0 hr hrC)
                    · omega
                  · rw [ΨF_high htop hrC hσe, hLdef]
                    apply ΨF_slot_gt hT
                    have : hR ≠ r.coeff d := fun h' => hσe (by rw [← h', hhR])
                    omega
              · -- the non-cut copy of the root slot
                have hjeq : j = hR := by omega
                subst hjeq
                have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                simp only [hdec] at hpw hpc
                intro hk c0 hc0
                obtain ⟨hreg, hcl0, -⟩ := eokw_cell hpw hc0
                obtain ⟨hT, _, _, _, hsome⟩ := hpc hk c0 hc0
                simp only at hreg hT hsome
                have hCρ : official c0.row ≤ official ρc.row := hcl0 _ rfl
                have hsm := hsome _ rfl trivial
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ hb' => absurd hb' (by simp [hcb]),
                  fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · intro r hr hrC _
                  rw [hcb, ΨF_low htop (hrC.trans hCρ)]
                  have hσ := hσle r hr (hrC.trans hCρ)
                  rcases Nat.lt_or_eq_of_le hσ with hl | hq
                  · exact ΨF_slot_lt hT hl
                  · rw [hq]
                    exact (hsm r (by rw [← hq]; exact slot_mem hr) (hrC.trans hCρ)).1 hrC
                · intro r hr hrC
                  rw [hcb]
                  have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  have hCS := Recon.RowLaw.inRegion_of_slot hreg
                  have hσ : j ≤ r.coeff d := by
                    rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                  by_cases hrρ : r ≤ official ρc.row
                  · rw [ΨF_low htop hrρ]
                    have hq : r.coeff d = j := le_antisymm (hσle r hr hrρ) hσ
                    rw [hq]
                    exact (hsm r (by rw [← hq]; exact slot_mem hr) hrρ).2 hrC
                  · have hρr : official ρc.row < r := lt_of_not_ge hrρ
                    have hσR := hσge r hr hρr
                    by_cases hσe : r.coeff d = (official ρc.row).coeff d
                    · rw [ΨF_mid htop hρr hσe, hLdef]
                      exact ΨF_slot_gt hT (by omega)
                    · rw [ΨF_high htop hρr hσe, hLdef]
                      exact ΨF_slot_gt hT (by omega)
            · -- a lifted slot
              by_cases hjc : (j : Int) = hR + L
              · -- the item that skips the bottom of the root slot
                have hσ : ((j : Int) - L).toNat = hR := by omega
                have he0 : e = 0 ∧ 1 ≤ d := by
                  rcases he with ⟨_, _⟩ | ⟨he0, hd⟩
                  · exfalso; omega
                  · exact ⟨he0, hd⟩
                have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = true :=
                  decide_eq_true ⟨by omega, hjc⟩
                simp only [hσ, hdec] at hpw hpc
                have hjN : j = hR + L := by omega
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                obtain ⟨hT, _, hgo, hnone, _⟩ := hpc hk c0 hc0
                obtain ⟨ha, hb⟩ := hnone rfl
                simp only at hreg hT hgo ha hb
                have hρC : official ρc.row ≤ official c0.row := hgo trivial trivial _ htopsub
                have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hCS := Recon.RowLaw.inRegion_of_slot hreg
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ hb' => absurd hb' (by simp [hcb]),
                  fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · intro r hr hrC _
                  rw [hcb]
                  by_cases hrρ : r ≤ official ρc.row
                  · rw [ΨF_low htop hrρ]
                    exact ΨF_slot_lt hT (by have := hσle r hr hrρ; omega)
                  · have hρr : official ρc.row < r := lt_of_not_ge hrρ
                    have hq : r.coeff d = hR := le_antisymm
                      (by rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC)
                      (hσge r hr hρr)
                    rw [ΨF_mid htop hρr (hq.trans hhR), hLdef, ← hhR, ← hjN, hq]
                    refine ha r (by rw [← hq]; exact slot_mem hr) hrC ?_
                    intro _ ρ' hρ'
                    rw [htopsub] at hρ'
                    cases hρ'
                    exact hρr
                · intro r hr hrC
                  rw [hcb]
                  have hρr : official ρc.row < r := lt_of_le_of_lt hρC hrC
                  have hσR := hσge r hr hρr
                  by_cases hσe : r.coeff d = (official ρc.row).coeff d
                  · have hq : r.coeff d = hR := hσe.trans hhR.symm
                    rw [ΨF_mid htop hρr hσe, hLdef, ← hhR, ← hjN, hq]
                    exact hb r (by rw [← hq]; exact slot_mem hr) hrC
                  · rw [ΨF_high htop hρr hσe, hLdef]
                    apply ΨF_slot_gt hT
                    have : hR ≠ r.coeff d := fun h' => hσe (by rw [← h', hhR])
                    omega
              · -- a plain lifted slot
                have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = false :=
                  decide_eq_false (fun h' => hjc h'.2)
                simp only [hdec] at hpw hpc
                have hσ : hR < ((j : Int) - L).toNat := by
                  rcases he with ⟨he1, _⟩ | ⟨he0, _⟩ <;> omega
                have hjN : j = ((j : Int) - L).toNat + L := by omega
                generalize hs' : ((j : Int) - L).toNat = s' at hσ hjN hpw hpc
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                obtain ⟨hT, _, _, hnone, _⟩ := hpc hk c0 hc0
                obtain ⟨ha, hb⟩ := hnone rfl
                simp only at hreg hT ha hb
                have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hCS := Recon.RowLaw.inRegion_of_slot hreg
                have hρC : official ρc.row < official c0.row :=
                  ChainCorr.Inner.slot_rows_lt hρslot hreg hσ
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ hb' => absurd hb' (by simp [hcb]),
                  fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · intro r hr hrC _
                  rw [hcb]
                  have hσC : r.coeff d ≤ s' := by
                    rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC
                  by_cases hrρ : r ≤ official ρc.row
                  · rw [ΨF_low htop hrρ]
                    exact ΨF_slot_lt hT (by have := hσle r hr hrρ; omega)
                  · have hρr : official ρc.row < r := lt_of_not_ge hrρ
                    by_cases hσe : r.coeff d = (official ρc.row).coeff d
                    · rw [ΨF_mid htop hρr hσe, hLdef]
                      exact ΨF_slot_lt hT (by omega)
                    · rw [ΨF_high htop hρr hσe, hLdef]
                      rcases Nat.lt_or_eq_of_le hσC with hl | hq
                      · exact ΨF_slot_lt hT (by omega)
                      · rw [hq, ← hjN]
                        exact ha r (by rw [← hq]; exact slot_mem hr) hrC (fun h => by cases h)
                · intro r hr hrC
                  rw [hcb]
                  have hρr : official ρc.row < r := lt_trans hρC hrC
                  have hσC : s' ≤ r.coeff d := by
                    rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                  have hσe : r.coeff d ≠ (official ρc.row).coeff d := by omega
                  rw [ΨF_high htop hρr hσe, hLdef]
                  rcases Nat.lt_or_eq_of_le hσC with hl | hq
                  · exact ΨF_slot_gt hT (by omega)
                  · rw [← hq, ← hjN]
                    exact hb r (by rw [hq]; exact slot_mem hr) hrC
          · -- case 3: the bottom of the region is skipped
            rename_i hcb'
            have hcb : it.cutBottom = true := by simpa using hcb'
            have he : ((if d + 2 = 2 then (1 : Int) else 0) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then (1 : Int) else 0) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then (1 : Int) else 0) = e at h he
            rw [← hEB] at h
            generalize hBdef : (Env.ofCtx ctx R B).hB (d + 2) it.target = hB at h
            have htgt : (if ctx.block = 0 then height (d + 2) (official aCell.row)
                else hB + height (d + 2) (official aCell.row)) =
                hB + height (d + 2) (official aCell.row) := if_neg (by omega)
            rw [htgt] at h
            obtain rfl := Except.ok.inj h
            intro ch hch p hpw hpc
            simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hch
            obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hch
            -- the parent statement for the rows above `ρ`, with the admissible rows only
            have hadm : ∀ r, (it.cutBottom = true → ∀ ρ, topA ctx (d + 2) it.source = some ρ →
                official ρ.2.row < r) → official ρc.row < r := fun r hadm =>
              hadm hcb _ htop
            split_ifs at hpw hpc with h1
            · -- a gap copy of `ρ`
              intro hk c0 hc0
              obtain ⟨hT, hcc, _, _, _⟩ := hpc hk c0 hc0
              simp only at hT hcc
              have hCeq : official c0.row = official ρc.row := hcc _ rfl trivial
              refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                fun _ _ ρ' hρ' => ?_, fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
              · rw [htop] at hρ'; cases hρ'; rw [hCeq]
              · intro r hr hrC hr'
                rw [hCeq] at hrC
                exact absurd (hadm r hr') (not_lt.mpr hrC)
              · intro r hr hrC
                rw [hCeq] at hrC
                rw [hcb]
                have hσR := hσge r hr hrC
                by_cases hσe : r.coeff d = (official ρc.row).coeff d
                · rw [ΨG_mid htop hσe, hBdef]
                  apply ΨF_slot_gt hT
                  rcases he with ⟨he1, hd0⟩ | ⟨he0, _⟩
                  · exact absurd (hσe.trans hhR.symm) (hlev2 r hd0 hr hrC)
                  · omega
                · rw [ΨG_high htop hσe, hBdef]
                  apply ΨF_slot_gt hT
                  have : hR ≠ r.coeff d := fun h' => hσe (by rw [← h', hhR])
                  omega
            · by_cases hjc : j = hB + hR
              · -- the item that skips the bottom of the root slot
                have hσ : j - hB = hR := by omega
                have hσ' : j - hR = hB := by omega
                have hdec : decide (j = hB + hR) = true := decide_eq_true hjc
                simp only [hσ, hσ', hdec] at hpw hpc
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                obtain ⟨hT, _, hgo, hnone, _⟩ := hpc hk c0 hc0
                obtain ⟨ha, hb⟩ := hnone rfl
                simp only at hreg hT hgo ha hb
                have hρC : official ρc.row ≤ official c0.row := hgo trivial trivial _ htopsub
                have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hCS := Recon.RowLaw.inRegion_of_slot hreg
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ _ ρ' hρ' => ?_, fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · rw [htop] at hρ'; cases hρ'; exact hρC
                · intro r hr hrC hr'
                  have hρr := hadm r hr'
                  rw [hcb]
                  have hq : r.coeff d = hR := le_antisymm
                    (by rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC)
                    (hσge r hr hρr)
                  rw [ΨG_mid htop (hq.trans hhR), hBdef, hq]
                  refine ha r (by rw [← hq]; exact slot_mem hr) hrC ?_
                  intro _ ρ' hρ'
                  rw [htopsub] at hρ'
                  cases hρ'
                  exact hρr
                · intro r hr hrC
                  rw [hcb]
                  have hρr : official ρc.row < r := lt_of_le_of_lt hρC hrC
                  have hσR := hσge r hr hρr
                  by_cases hσe : r.coeff d = (official ρc.row).coeff d
                  · have hq : r.coeff d = hR := hσe.trans hhR.symm
                    rw [ΨG_mid htop hσe, hBdef, hq]
                    exact hb r (by rw [← hq]; exact slot_mem hr) hrC
                  · rw [ΨG_high htop hσe, hBdef]
                    apply ΨF_slot_gt hT
                    have : hR ≠ r.coeff d := fun h' => hσe (by rw [← h', hhR])
                    omega
              · -- a plain slot above the root slot
                have hdec : decide (j = hB + hR) = false := decide_eq_false hjc
                simp only [hdec] at hpw hpc
                have hσ : hR < j - hB := by
                  rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                obtain ⟨hT, _, _, hnone, _⟩ := hpc hk c0 hc0
                obtain ⟨ha, hb⟩ := hnone rfl
                simp only at hreg hT ha hb
                have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hCS := Recon.RowLaw.inRegion_of_slot hreg
                have hρC : official ρc.row < official c0.row :=
                  ChainCorr.Inner.slot_rows_lt hρslot hreg hσ
                have hjj : j - hB + hB - hR = j - hR := by omega
                refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C hC => absurd hC (by simp [hcl]),
                  fun _ _ ρ' hρ' => ?_, fun _ => ⟨?_, ?_⟩, fun C hC => absurd hC (by simp [hcl])⟩
                · rw [htop] at hρ'; cases hρ'; exact hρC.le
                · intro r hr hrC hr'
                  have hρr := hadm r hr'
                  rw [hcb]
                  have hσR := hσge r hr hρr
                  have hσC : r.coeff d ≤ j - hB := by
                    rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC
                  by_cases hσe : r.coeff d = (official ρc.row).coeff d
                  · rw [ΨG_mid htop hσe, hBdef]
                    exact ΨF_slot_lt hT (by omega)
                  · rw [ΨG_high htop hσe, hBdef]
                    rcases Nat.lt_or_eq_of_le hσC with hl | hq
                    · exact ΨF_slot_lt hT (by rw [← hhR] at hσe ⊢; omega)
                    · rw [hq, ← hhR, hjj]
                      exact ha r (by rw [← hq]; exact slot_mem hr) hrC (fun h => by cases h)
                · intro r hr hrC
                  rw [hcb]
                  have hρr : official ρc.row < r := lt_trans hρC hrC
                  have hσC : j - hB ≤ r.coeff d := by
                    rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                  have hσe : r.coeff d ≠ (official ρc.row).coeff d := by omega
                  rw [ΨG_high htop hσe, hBdef]
                  rcases Nat.lt_or_eq_of_le hσC with hl | hq
                  · exact ΨF_slot_gt hT (by omega)
                  · rw [← hq, ← hhR, hjj]
                    exact hb r (by rw [hq]; exact slot_mem hr) hrC
        · -- case 4: a copy of the root row
          rename_i C hclC
          obtain ⟨r0, ρ0, hρ0, hρ0C⟩ := hinv C hclC
          rw [hrho] at hρ0
          cases hρ0
          subst hρ0C
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · rename_i nd hnd
            split at h
            · cases h
            · rename_i _ g hgen
              split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · rename_i hcond
                rw [← hEB] at h
                generalize hBdef : (Env.ofCtx ctx R B).hB (d + 2) it.target = hB at h
                have htgt : (if ctx.block = 0 then ((height (d + 2) (official aCell.row) : Nat) : Int)
                    else (hB : Int) + (g : Int) - (it.offset : Int)) =
                    (hB : Int) + (g : Int) - (it.offset : Int) := if_neg (by omega)
                rw [htgt] at h
                obtain rfl := Except.ok.inj h
                intro ch hch p hpw hpc
                simp only [List.mem_map] at hch
                obtain ⟨j, _, rfl⟩ := hch
                split_ifs at hpw hpc with hb h1
                · -- `b = 1`: gap copies of `ρ` only
                  intro hk c0 hc0
                  obtain ⟨hT, hcc, _, _, _⟩ := hpc hk c0 hc0
                  simp only at hT hcc
                  refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C' hC' _ => ?_,
                    fun hn => absurd hn (by simp [hclC]), fun hn => absurd hn (by simp [hclC]),
                    fun _ _ hb' => absurd hb' (by simp [hb])⟩
                  rw [hclC] at hC'
                  cases hC'
                  exact hcc _ rfl trivial
                · -- a slot below the root top
                  intro hk c0 hc0
                  obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                  obtain ⟨hT, _, _, hnone, _⟩ := hpc hk c0 hc0
                  obtain ⟨ha, hbb⟩ := hnone rfl
                  simp only at hreg hT ha hbb
                  have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  have hCS := Recon.RowLaw.inRegion_of_slot hreg
                  refine ⟨Recon.RowLaw.inRegion_of_slot hT, fun C' _ hb' => absurd hb' (by simp [hb]),
                    fun hn => absurd hn (by simp [hclC]), fun hn => absurd hn (by simp [hclC]), ?_⟩
                  intro C' hC' _ r hr hrC'
                  rw [hclC] at hC'
                  cases hC'
                  rw [ΨF_low htop hrC']
                  refine ⟨fun hrC => ?_, fun hrC => ?_⟩
                  · have hσ : r.coeff d ≤ j := by
                      rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hr hCS hrC
                    rcases Nat.lt_or_eq_of_le hσ with hl | hq
                    · exact ΨF_slot_lt hT hl
                    · rw [hq]
                      exact ha r (by rw [← hq]; exact slot_mem hr) hrC (fun h => by cases h)
                  · have hσ : j ≤ r.coeff d := by
                      rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                    rcases Nat.lt_or_eq_of_le hσ with hl | hq
                    · exact ΨF_slot_gt hT hl
                    · rw [← hq]; exact hbb r (by rw [hq]; exact slot_mem hr) hrC
                · by_cases hjR : hR < j
                  · -- a gap copy of `ρ`
                    have hdec : decide (hR < j) = true := decide_eq_true hjR
                    simp only [hdec] at hpw hpc
                    intro hk c0 hc0
                    obtain ⟨hT, hcc, _, _, _⟩ := hpc hk c0 hc0
                    simp only at hT hcc
                    have hCeq : official c0.row = official ρc.row := hcc _ rfl trivial
                    refine ⟨Recon.RowLaw.inRegion_of_slot hT,
                      fun C' _ hb' => absurd hb' (by simp [hb]),
                      fun hn => absurd hn (by simp [hclC]), fun hn => absurd hn (by simp [hclC]), ?_⟩
                    intro C' hC' _ r hr hrC'
                    rw [hclC] at hC'
                    cases hC'
                    rw [ΨF_low htop hrC']
                    refine ⟨fun _ => ΨF_slot_lt hT (by have := hσle r hr hrC'; omega),
                      fun hrC => ?_⟩
                    rw [hCeq] at hrC
                    exact absurd hrC' (not_le.mpr hrC)
                  · -- the non-cut copy of the root slot
                    have hjeq : j = hR := by omega
                    subst hjeq
                    have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                    simp only [hdec] at hpw hpc
                    intro hk c0 hc0
                    obtain ⟨hreg, hcl0, -⟩ := eokw_cell hpw hc0
                    obtain ⟨hT, _, _, _, hsome⟩ := hpc hk c0 hc0
                    simp only at hreg hT hsome
                    have hCρ : official c0.row ≤ official ρc.row := hcl0 _ rfl
                    have hsm := hsome _ rfl trivial
                    refine ⟨Recon.RowLaw.inRegion_of_slot hT,
                      fun C' _ hb' => absurd hb' (by simp [hb]),
                      fun hn => absurd hn (by simp [hclC]), fun hn => absurd hn (by simp [hclC]), ?_⟩
                    intro C' hC' _ r hr hrC'
                    rw [hclC] at hC'
                    cases hC'
                    rw [ΨF_low htop hrC']
                    have hCj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                    have hCS := Recon.RowLaw.inRegion_of_slot hreg
                    refine ⟨fun hrC => ?_, fun hrC => ?_⟩
                    · have hσ := hσle r hr hrC'
                      rcases Nat.lt_or_eq_of_le hσ with hl | hq
                      · exact ΨF_slot_lt hT hl
                      · rw [hq]
                        exact (hsm r (by rw [← hq]; exact slot_mem hr) hrC').1 hrC
                    · have hσ : j ≤ r.coeff d := by
                        rw [← hCj]; exact Recon.RowLaw.coeff_le_of_inRegion hCS hr hrC.le
                      have hq : r.coeff d = j := le_antisymm (hσle r hr hrC') hσ
                      rw [hq]
                      exact (hsm r (by rw [← hq]; exact slot_mem hr) hrC').2 hrC


/-! ## The induction over the items -/

theorem runItemT_cut (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMD : FactMD ctx τ) (hMH : FactMH ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      Reach ctx τ (d + 1) it → ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
      ∀ p ∈ ps, CutΨ (Env.ofCtx ctx R B) (topA ctx) (d + 1) it p
  | 0, it, ps, h, _, _ => levelOneT_cut (by simpa [runItemT] using h)
  | d + 1, it, ps, h, hRe, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, _, _⟩ := ChainCorr.Inner.childItems_order hch hinv
          have hcut := childItems_cut (R := R) (B := B) hi hbnd hch hinv (hMD d it hRe)
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem : children[a]'(by omega) ∈ children := List.getElem_mem _
          have hrun := hall a (by omega) ha
          have hRe' := Reach.child hRe hch hmem
          have hinv' := hinvc _ hmem
          have hw := (runItemT_shapeW ctx τ R B hV hi hbnd hMD hMH d _ _ hrun hRe' hinv').1 p hpl
          exact hcut _ hmem p hw
            (runItemT_cut ctx τ R B hV hi hbnd hMD hMH d _ _ hrun hRe' hinv' p hpl)

/-! ## The origin row of a gap copy is the row of an ascending root top -/

/-- `C` is the row of the top `ρ` of the root column in some region where the column ascends. -/
def AscRow (ctx : Context) (C : Row) : Prop :=
  ∃ d S ρ, topIn ctx.source ctx.rootColumn (d + 2) S = some ρ ∧ official ρ.2.row = C ∧
    ascends ctx (some ρ) = .ok true

/-- The root row copied by a clean item is an ascending root top. -/
def ItemInvA (ctx : Context) (it : Item) : Prop := ∀ C, it.clean = some C → AscRow ctx C

theorem childItems_invA {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hA : ItemInvA ctx it) :
    ∀ c ∈ cs, ItemInvA ctx c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i _ v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro ch hch C hC
          simp only [List.mem_map] at hch
          obtain ⟨j, _, rfl⟩ := hch
          cases hC
      · rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hasc : AscRow ctx (official ρc.row) := ⟨d, it.source, (ρr, ρc), hrho, rfl, hv⟩
        simp only at h
        split at h
        · split at h
          · obtain rfl := Except.ok.inj h
            intro ch hch C hC
            simp only [List.mem_map] at hch
            obtain ⟨j, _, rfl⟩ := hch
            split_ifs at hC <;>
              first
              | (simp only [Option.some.injEq] at hC; subst hC; exact hasc)
              | simp at hC
          · obtain rfl := Except.ok.inj h
            intro ch hch C hC
            simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hch
            obtain ⟨j, _, rfl⟩ := hch
            split_ifs at hC <;>
              first
              | (simp only [Option.some.injEq] at hC; subst hC; exact hasc)
              | simp at hC
        · rename_i C0 hclC
          have hAC := hA C0 hclC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro ch hch C hC
                simp only [List.mem_map] at hch
                obtain ⟨j, _, rfl⟩ := hch
                split_ifs at hC <;>
                  first
                  | (simp only [Option.some.injEq] at hC; subst hC; exact hAC)
                  | simp at hC

theorem levelOneT_asc {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) (hA : ItemInvA ctx it) :
    ∀ p ∈ ps, ChainCorr.cutOrigin p.2 = true → ∀ c0, cell? ctx.source p.2.src = some c0 →
      AscRow ctx (official c0.row) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp
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
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp _ c0 hc0
                simp only [List.mem_singleton] at hp
                subst hp
                have hcc : c0 = cs := by
                  simp only [Origin.src] at hc0
                  exact Option.some.inj (hc0.symm.trans hccell)
                subst hcc
                rw [hcrow]
                exact hA C hC
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp hk
            simp only [List.mem_singleton] at hp
            subst hp
            simp [ChainCorr.cutOrigin] at hk
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp hk
              simp only [List.mem_singleton] at hp
              subst hp
              simp [ChainCorr.cutOrigin] at hk

theorem runItemT_asc (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      ItemInvA ctx it → ∀ p ∈ ps, ChainCorr.cutOrigin p.2 = true →
        ∀ c0, cell? ctx.source p.2.src = some c0 → AscRow ctx (official c0.row)
  | 0, it, ps, h, hA => levelOneT_asc (by simpa [runItemT] using h) hA
  | d + 1, it, ps, h, hA => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem : children[a]'(by omega) ∈ children := List.getElem_mem _
          exact runItemT_asc ctx d _ _ (hall a (by omega) ha) (childItems_invA hch hA _ hmem) p hpl

/-! ## The lower gap copies of a block context -/

/-- **Where a lower gap copy lies.** In a context of a block `1 ≤ i ≤ n`, a gap copy with origin
row `C` lies in the first item `q` of `C`, strictly above the images of the rows `≤ C` of `q` and
strictly below the images of the rows `> C` of `q` (the map of the column); and `C` is the row of
an ascending root top. -/
theorem lowerT_cut {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx) {es : List (Emit × Origin)}
    (hes : lowerT ctx (official t.row) = .ok es) :
    ∀ e ∈ es, cutO e.2 = true → ∀ c0, cell? M e.2.src = some c0 →
      ∃ q ∈ lowerItems (official t.row), inRegion q.1 q.2.source (official c0.row) = true ∧
        inRegion q.1 q.2.source e.1.row = true ∧
        (∀ r, inRegion q.1 q.2.source r = true → r ≤ official c0.row →
          Ψ (blockEnv M R root.column i) (topA ctx) false q.1 q.2.source q.2.source r <
            e.1.row) ∧
        (∀ r, inRegion q.1 q.2.source r = true → official c0.row < r →
          e.1.row <
            Ψ (blockEnv M R root.column i) (topA ctx) false q.1 q.2.source q.2.source r) ∧
        AscRow ctx (official c0.row) := by
  intro e he hcut c0 hc0
  have hblk : 1 ≤ ctx.block := by rw [hB.block]; exact hi1
  have hV : MountainValid ctx.source := by
    rw [hB.source]; exact build_valid_of_success hTop.build
  have hMD := Found.factMD_of_bctx hTop hB
  have hMH := Found.factMH_of_bctx hrun hTop hi1 hin hB
  have hbd : ctx.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary
    rw [hB.root, hB.width, hB.block]
  have hbnd : ∀ d T, topIn ctx.result ctx.boundary d T =
      topIn R (root.column + (M.size - 1 - root.column) * i) d T := by
    intro d T
    rw [hbd]
    exact Found.topIn_congr hB.bnd
  have hcut' : ChainCorr.cutOrigin e.2 = true := by rw [← Found.cutO_eq]; exact hcut
  unfold lowerT at hes
  simp only [bind, Except.bind, pure, Except.pure] at hes
  split at hes
  · cases hes
  · rename_i outs houts
    cases hes
    obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp he
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
    obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
    have hmem := List.getElem_mem (l := lowerItems (official t.row))
      (by omega : a < (lowerItems (official t.row)).length)
    obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hmem
    have hrun' := hall a (by omega) ha
    rw [hkj] at hrun' hmem
    have hRe : Reach ctx (official t.row) (k + 1) _ := Reach.top hmem
    have hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (k + 1)
        ⟨slot (k + 2) (official t.row) j, slot (k + 2) (official t.row) j, none, 0, false⟩ :=
      fun C hC => by cases hC
    have hc0' : cell? ctx.source e.2.src = some c0 := by rw [hB.source]; exact hc0
    have hw := (runItemT_shapeW ctx (official t.row) R
      (root.column + (M.size - 1 - root.column) * i) hV hblk hbnd hMD hMH k _ _ hrun' hRe
      hinv).1 e hel
    have hcf := runItemT_cut ctx (official t.row) R
      (root.column + (M.size - 1 - root.column) * i) hV hblk hbnd hMD hMH k _ _ hrun' hRe hinv
      e hel hcut' c0 (by rw [Env.ofCtx_M]; exact hc0')
    have hasc := runItemT_asc ctx k _ _ hrun' (fun C hC => by cases hC) e hel hcut' c0 hc0'
    obtain ⟨_, _, c, hc, hreg, _⟩ := hw
    have hcc : c = c0 := by
      rw [Env.ofCtx_M] at hc
      exact Option.some.inj (hc.symm.trans hc0')
    subst hcc
    obtain ⟨hT, _, _, hnone, _⟩ := hcf
    obtain ⟨ha', hb'⟩ := hnone rfl
    rw [env_eq hB rfl] at ha' hb'
    refine ⟨_, hmem, hreg, hT, fun r hr hrC => ha' r hr hrC (fun h => by cases h),
      fun r hr hrC => hb' r hr hrC, hasc⟩

end OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.childItems_cut
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.lowerT_cut

