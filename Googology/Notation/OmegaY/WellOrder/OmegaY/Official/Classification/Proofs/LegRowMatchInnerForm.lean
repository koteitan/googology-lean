/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchInnerForm.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerMap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeNoMA

set_option backward.do.legacy false

/-!
# Every non-cut emit of a copied column has the row `Ψ` of its origin row

The row formula of `CopyShape` (the last part of `EOK`, with the map `Φ`) needs (MA), which is
false. With the map `Ψ E (topA ctx)` of `LegRowMatchInnerMap.lean`, which reads the root top of a
region only where the column of `ctx` ascends, the formula holds without (MA):

* `childItems_formula`: the formula passes from the children of an item to the item. The proof
  is the formula part of `CopyShape.childItems_shape`; in case 1 (the region does not ascend)
  `topA ctx` is `none`, so `Ψ` keeps the slot, as the children do.
* `runItemT_formula`, `emitsT_formula` (`LegRowMatchInnerRun.lean`): every non-cut emit of the lower part has the row
  `Ψ E (topA ctx) false (k + 1) L L σ`, where `(k + 1, L)` is the first item containing the
  origin row `σ`; an emit of the upper part has the row of its origin.

The other parts of `EOK` are `EOKw`, proved in `CopyShapeNoMA.lean` (`runItemT_shapeW`).
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

open Canonical Reserve Official Descent Classification Proofs
open CopyShape.NoMA

/-- The row formula for an emit `p` of an item `it` of level `d`. -/
def FormΨ (E : Env) (top : Nat → Row → Option (Ref × Cell)) (d : Nat) (it : Item)
    (p : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin p.2 = false → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
    p.1.row = Ψ E top (it.cutBottom && it.clean.isNone) d it.source it.target (official c0.row)

theorem eokw_cell {E : Env} {x d : Nat} {it : Item} {p : Emit × Origin} (hp : EOKw E x d it p)
    {c0 : Cell} (hc0 : cell? E.M p.2.src = some c0) :
    inRegion d it.source (official c0.row) = true ∧
    (∀ C, it.clean = some C → official c0.row ≤ C) ∧
    (∀ C, it.clean = some C → it.cutBottom = true → ChainCorr.cutOrigin p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → ChainCorr.cutOrigin p.2 = false → 2 ≤ d →
      ∀ ρr ρc, topIn E.M E.cr d it.source = some (ρr, ρc) → official ρc.row < official c0.row) := by
  obtain ⟨_, _, c, hc, hreg, h1, h2, h3⟩ := hp
  rw [hc0] at hc
  cases hc
  exact ⟨hreg, h1, h2, h3⟩

/-- **The formula passes from the children to the item.** -/
theorem childItems_formula {ctx : Context} {R : Mountain} {B : Nat} {d : Nat} {it : Item}
    {cs : List Item} (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx (d + 2) it = .ok cs)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) it)
    (hMD : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf (d + 2) (some (ρr, ρc)) <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source)) :
    ∀ c ∈ cs, ∀ p, EOKw (Env.ofCtx ctx R B) ctx.x (d + 1) c p →
      FormΨ (Env.ofCtx ctx R B) (topA ctx) (d + 1) c p →
      FormΨ (Env.ofCtx ctx R B) (topA ctx) (d + 2) it p := by
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
          intro ch hch p hpw hpf hk c0 hc0
          simp only [List.mem_map] at hch
          obtain ⟨j, _, rfl⟩ := hch
          obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
          have hj : (official c0.row).coeff d = j := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
          rw [hpf hk c0 hc0, hcb, hcl]
          simp only [Bool.false_and, bmode_ff]
          subst hj
          rw [ΨF_none htop]
      · -- the region ascends: the top of the root column exists
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
        have hrhoE : topIn (Env.ofCtx ctx R B).M (Env.ofCtx ctx R B).cr (d + 2) it.source =
            some (ρr, ρc) := hrho
        have htop : topA ctx (d + 2) it.source = some (ρr, ρc) := topA_of_asc hrho hv
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
        generalize hRdef : heightOf (d + 2) (some (ρr, ρc)) = hR at h hhR hsub hρslot
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
            intro ch hch p hpw hpf
            simp only [List.mem_map] at hch
            obtain ⟨j, _, rfl⟩ := hch
            split_ifs at hpw hpf with h1 h2
            · -- below the root top
              intro hk c0 hc0
              obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
              simp only at hreg
              have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
              have hlt := ChainCorr.Inner.slot_rows_lt hreg hρslot h1
              rw [hpf hk c0 hc0, hcb, hcl]
              simp only [bmode_ff, bmode_tf, bmode_some]
              rw [ΨF_low htop hlt.le, hj]
            · -- a copy of the root row
              by_cases hjR : hR < j
              · have hdec : decide (hR < j) = true := decide_eq_true hjR
                simp only [hdec] at hpw
                have hcut := cut_of_cleanCutW hpw
                intro hk; rw [hcut] at hk; cases hk
              · have hjeq : j = hR := by omega
                subst hjeq
                have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                simp only [hdec] at hpw hpf
                intro hk c0 hc0
                obtain ⟨hreg, hcl0, -⟩ := eokw_cell hpw hc0
                simp only at hreg
                have hle := hcl0 _ rfl
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                rw [hpf hk c0 hc0, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΨF_low htop hle, hj]
            · -- a lifted slot
              by_cases hjc : (j : Int) = hR + L
              · have hσ : ((j : Int) - L).toNat = hR := by omega
                have he0 : e = 0 ∧ 1 ≤ d := by
                  rcases he with ⟨_, _⟩ | ⟨he0, hd⟩
                  · exfalso; omega
                  · exact ⟨he0, hd⟩
                have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = true :=
                  decide_eq_true ⟨by omega, hjc⟩
                simp only [hσ, hdec] at hpw hpf
                intro hk c0 hc0
                obtain ⟨hreg, -, -, hup⟩ := eokw_cell hpw hc0
                simp only at hreg
                have hlt := hup rfl rfl hk (by omega) ρr ρc hsub
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hjN : j = hR + L := by omega
                rw [hpf hk c0 hc0, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΨF_mid htop hlt (hj.trans hhR), hj, ← hhR, hLdef, ← hjN]
              · have hdec : decide (ctx.block ≠ 0 ∧ (j : Int) = hR + L) = false :=
                  decide_eq_false (fun h' => hjc h'.2)
                simp only [hdec] at hpw hpf
                have hσ : hR < ((j : Int) - L).toNat := by
                  rcases he with ⟨he1, _⟩ | ⟨he0, _⟩ <;> omega
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                simp only at hreg
                have hlt := ChainCorr.Inner.slot_rows_lt hρslot hreg hσ
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hne : (official c0.row).coeff d ≠ (official ρc.row).coeff d := by omega
                have hjN : j = ((j : Int) - L).toNat + L := by omega
                rw [hpf hk c0 hc0, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΨF_high htop hlt hne, hj, hLdef, ← hjN]
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
            intro ch hch p hpw hpf
            simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hch
            obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hch
            split_ifs at hpw hpf with h1
            · have hcut := cut_of_cleanCutW hpw
              intro hk; rw [hcut] at hk; cases hk
            · by_cases hjc : j = hB + hR
              · have hσ : j - hB = hR := by omega
                have hσ' : j - hR = hB := by omega
                have hdec : decide (j = hB + hR) = true := decide_eq_true hjc
                simp only [hσ, hσ', hdec] at hpw hpf
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                simp only at hreg
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                rw [hpf hk c0 hc0, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΨG_mid htop (hj.trans hhR), hj, hBdef]
              · have hdec : decide (j = hB + hR) = false := decide_eq_false hjc
                simp only [hdec] at hpw hpf
                have hσ : hR < j - hB := by
                  rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                intro hk c0 hc0
                obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                simp only at hreg
                have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                have hne : (official c0.row).coeff d ≠ (official ρc.row).coeff d := by omega
                rw [hpf hk c0 hc0, hcb, hcl]
                simp only [bmode_ff, bmode_tf, bmode_some]
                rw [ΨG_high htop hne, hj, hBdef, ← hhR,
                  show j - hB + hB - hR = j - hR by omega]
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
                intro ch hch p hpw hpf
                simp only [List.mem_map] at hch
                obtain ⟨j, _, rfl⟩ := hch
                split_ifs at hpw hpf with hb h1
                · -- `b = 1`: gap copies only
                  have hcut := cut_of_cleanCutW hpw
                  intro hk; rw [hcut] at hk; cases hk
                · -- a slot below the root top
                  intro hk c0 hc0
                  obtain ⟨hreg, -⟩ := eokw_cell hpw hc0
                  simp only at hreg
                  have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                  have hlt := ChainCorr.Inner.slot_rows_lt hreg hρslot h1
                  rw [hpf hk c0 hc0, hclC]
                  simp only [bmode_ff, bmode_tf, bmode_some]
                  rw [ΨF_low htop hlt.le, hj]
                · by_cases hjR : hR < j
                  · have hdec : decide (hR < j) = true := decide_eq_true hjR
                    simp only [hdec] at hpw
                    have hcut := cut_of_cleanCutW hpw
                    intro hk; rw [hcut] at hk; cases hk
                  · have hjeq : j = hR := by omega
                    subst hjeq
                    have hdec : decide (j < j) = false := decide_eq_false (lt_irrefl _)
                    simp only [hdec] at hpw hpf
                    intro hk c0 hc0
                    obtain ⟨hreg, hcl0, -⟩ := eokw_cell hpw hc0
                    simp only at hreg
                    have hj := (Recon.RowLaw.inRegion_slot_iff.mp hreg).2
                    rw [hpf hk c0 hc0, hclC]
                    simp only [bmode_ff, bmode_tf, bmode_some]
                    rw [ΨF_low htop (hcl0 _ rfl), hj]

end OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.childItems_formula
