/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapFirst.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapItems

set_option backward.do.legacy false

/-!
# The first gap copy after a clean copy (`CutGap`)

In a copied column of a block `i ≥ 1`, every clean non-cut emit (origin `.clean r false`,
the copy of the root row with `b = 0`) is followed by a gap copy of the same origin at the next
row `bump θ 0` (`emitsT_firstGap`). The clean non-cut copies are made by level-1 children of a
level-2 item in case 2 (then the next child is a gap copy, since the lift is at least 1) or in
case 4 with `b = 0` (then the next child exists when `h_ρ + 1 ≤ h_q + g`, the fact
`FactFG`, a strict form of MH at level 2).

## Numerical tests

`FactFG` in the form `h_ρ ≤ h_q` (with `g ≥ 1` it gives `FactFG`) and the conclusion (the next
emit after every clean non-cut emit is a gap copy of the same origin one row up) were checked
by the scratch script `mhs.cjs` on the legal sequences of length ≤ 6 with entries ≤ 6, on the
64 sequences where `LegBelowTop` fails and on the larger samples of the final report: no
failure.
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-- (FG, proved: `fgHolds`, `CutGapFG.lean`) A reached level-2 item that copies the root row `C` with `b = 0` makes the
child `h_ρ + 1`: `h_ρ + 1 ≤ h_q + g`. -/
def FactFG (ctx : Context) (τ : Row) : Prop :=
  ∀ it C, Reach ctx τ 2 it → it.clean = some C → it.cutBottom = false →
    ∀ csRef cs g, nodeAt ctx.source ctx.x C = some (csRef, cs) →
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g →
      heightOf 2 (topIn ctx.source ctx.rootColumn 2 it.source) + 1 ≤
        heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) + g

/-- (FG, proved: `fgHolds`) `FactFG` for every copied column of every block `i ≥ 1`. -/
def FGHolds : Prop := BlockFact FactFG

/-- Every clean non-cut emit has a gap copy of the same origin at the next row. -/
def FirstGap (ps : List (Emit × Origin)) : Prop :=
  ∀ p ∈ ps, ∀ r, p.2 = .clean r false →
    ∃ q ∈ ps, q.2 = .clean r true ∧ q.1.row = Row.bump p.1.row 0

/-! ## Level 1 -/

/-- What a level-1 item emitting a clean copy looks like. -/
theorem levelOneT_clean {ctx : Context} {c : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx c = .ok ps) {p : Emit × Origin} (hp : p ∈ ps) {r : Ref} {b : Bool}
    (hpo : p.2 = .clean r b) :
    ∃ C cs0 lc, c.clean = some C ∧ b = c.cutBottom ∧
      (∃ q, nodeAt ctx.source ctx.x c.source = some q) ∧
      nodeAt ctx.source ctx.x C = some (r, cs0) ∧ leftColumn cs0 = .ok lc ∧
      p = (⟨c.target, some lc⟩, .clean r c.cutBottom) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x c.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp at hp
  | some q =>
      simp only [hsrc] at h
      cases hC : c.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · rename_i lc hlc
                cases h
                simp only [List.mem_singleton] at hp
                subst hp
                simp only [Origin.clean.injEq] at hpo
                obtain ⟨rfl, rfl⟩ := hpo
                exact ⟨C, cs, lc, rfl, rfl, ⟨q, rfl⟩, hcs, hlc, rfl⟩
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [List.mem_singleton] at hp
            subst hp
            cases hpo
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              cases hpo

/-- A level-1 item copying the root row `C` emits one clean copy. -/
theorem levelOneT_of_clean {ctx : Context} {c : Item} {q : Ref × Cell} {C : Row} {r : Ref}
    {cs0 : Cell} {lc : Nat} (hsrc : nodeAt ctx.source ctx.x c.source = some q)
    (hC : c.clean = some C) (hcs : nodeAt ctx.source ctx.x C = some (r, cs0))
    (hlc : leftColumn cs0 = .ok lc) :
    levelOneT ctx c = .ok [(⟨c.target, some lc⟩, .clean r c.cutBottom)] := by
  unfold levelOneT
  rw [hsrc]
  simp only [hC, hcs, bind, Except.bind, pure, Except.pure, hlc]

/-! ## Level 2 -/

/-- **At level 2 a clean non-cut child is followed by a gap-copy child with the same source,
one slot up.** -/
theorem childItems_two_next {ctx : Context} {it : Item} {cs : List Item}
    (hV : MountainValid ctx.source) (h : childItems ctx 2 it = .ok cs) (hi : 1 ≤ ctx.block)
    (hMD : ∀ ρr ρc, topIn ctx.source ctx.rootColumn 2 it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf 2 (some (ρr, ρc)) < heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source))
    (hFG : ∀ C, it.clean = some C → it.cutBottom = false →
      ∀ csRef cs0 g, nodeAt ctx.source ctx.x C = some (csRef, cs0) →
        generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs0 0 = .ok g →
        heightOf 2 (topIn ctx.source ctx.rootColumn 2 it.source) + 1 ≤
          heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) + g)
    {a : Nat} (ha : a < cs.length) {C : Row} (hcl : cs[a].clean = some C)
    (hb : cs[a].cutBottom = false) (hnode : ∃ q, nodeAt ctx.source ctx.x cs[a].source = some q) :
    ∃ ha' : a + 1 < cs.length, cs[a + 1].source = cs[a].source ∧ cs[a + 1].clean = some C ∧
      cs[a + 1].cutBottom = true ∧ cs[a].target = slot 2 it.target a ∧
      cs[a + 1].target = slot 2 it.target (a + 1) := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn 2 it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp at ha
  · rename_i _ aRef aCell hA
    split at h
    · cases h
    · rename_i _ v hv
      split at h
      · -- case 1: only plain children
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          simp only [List.getElem_map, List.getElem_range] at hcl
          cases hcl
      · rename_i hvt
        have hvt' : v = true := by simpa using hvt
        subst hvt'
        obtain ⟨ρr, ρc, rfl⟩ : ∃ a b, rho = some (a, b) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some q => exact ⟨q.1, q.2, rfl⟩
        have hMD' := hMD ρr ρc hrho hv
        simp only at h
        split at h
        · -- clean = none
          rename_i hcl0
          split at h
          · -- case 2
            simp only [↓reduceIte] at h
            obtain rfl := Except.ok.inj h
            simp only [List.length_map, List.length_range] at ha
            simp only [List.getElem_map, List.getElem_range] at hcl hb hnode
            have hL1 : (1 : Int) ≤ ((heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) : Int) -
                (heightOf 2 (some (ρr, ρc)) : Int)) * (ctx.block : Int) := by
              have h1 : (1 : Int) ≤ (heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) : Int) -
                (heightOf 2 (some (ρr, ρc)) : Int) := by omega
              have h2 : (1 : Int) ≤ (ctx.block : Int) := by omega
              have := Int.mul_le_mul h1 h2 (by decide) (by omega)
              simpa using this
            split_ifs at hcl hb hnode with h1 h2
            · have hb' : ¬ (heightOf 2 (some (ρr, ρc)) < a) := by simpa using hb
              have haR : a = heightOf 2 (some (ρr, ρc)) := by omega
              -- the column has a node in the slot of the root top
              obtain ⟨q, hq⟩ := hnode
              obtain ⟨hqc, hq1, hqcell, hqrow⟩ := Classification.nodeAt_spec hq
              have hslot : inRegion 1 (slot 2 it.source (heightOf 2 (some (ρr, ρc))))
                  (slot 2 it.source (heightOf 2 (some (ρr, ρc)))) = true :=
                inRegion_self 1 _
              have hin := (Recon.RowLaw.inRegion_slot_iff (d := 0)).mp hslot
              have hle := le_top_of_node hV hqc hq1 hqcell (by rw [hqrow]; exact hin.1) hA
              have hco := Recon.RowLaw.coeff_le_of_inRegion (d := 0) (by rw [hqrow]; exact hin.1)
                (topIn_inRegion hA) hle
              rw [hqrow, hin.2] at hco
              have hht : height 2 (official aCell.row) = (official aCell.row).coeff 0 :=
                Recon.RowLaw.height_eq 0 _
              have ha1 : a + 1 < (((height 2 (official aCell.row) : Nat) : Int) +
                  ((heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) : Int) -
                    (heightOf 2 (some (ρr, ρc)) : Int)) * (ctx.block : Int) + 1).toNat := by
                omega
              refine ⟨by simpa using ha1, ?_⟩
              have hn1 : ¬ a + 1 < heightOf 2 (some (ρr, ρc)) := by omega
              have hn2 : ((a + 1 : Nat) : Int) < (heightOf 2 (some (ρr, ρc)) : Int) +
                  ((heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) : Int) -
                    (heightOf 2 (some (ρr, ρc)) : Int)) * (ctx.block : Int) + 1 := by omega
              simp only [List.getElem_map, List.getElem_range, if_neg hn1, if_pos hn2, if_neg h1,
                if_pos h2]
              exact ⟨trivial, hcl, by simp; omega, trivial, trivial⟩
          · -- case 3: every clean child cuts the bottom
            exfalso
            have hmem := List.getElem_mem ha
            have hmem' := hmem
            obtain rfl := Except.ok.inj h
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hmem'
            obtain ⟨j, _, hj⟩ := hmem'
            rw [← hj] at hcl hb
            split_ifs at hcl hb
        · -- case 4
          rename_i C' hclC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · rename_i nd hnd
            split at h
            · cases h
            · rename_i _ g hgen
              split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · rename_i hcond
                have htgt : (if ctx.block = 0 then ((height 2 (official aCell.row) : Nat) : Int)
                    else (heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) : Int) + (g : Int) -
                      (it.offset : Int)) =
                    (heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) : Int) + (g : Int) -
                      (it.offset : Int) := if_neg (by omega)
                rw [htgt] at h
                obtain rfl := Except.ok.inj h
                simp only [List.length_map, List.length_range] at ha
                simp only [List.getElem_map, List.getElem_range] at hcl hb hnode
                by_cases hcb : it.cutBottom = true
                · simp only [hcb, if_true] at hb
                  cases hb
                · have hcbf : it.cutBottom = false := by simpa using hcb
                  have hoff : it.offset = 0 := by
                    by_contra hne
                    exact hcond ⟨by simp [hcbf], Or.inr hne⟩
                  have hF := hFG C' hclC hcbf nd.1 nd.2 g hnd hgen
                  rw [hrho] at hF
                  simp only [hcbf, Bool.false_eq_true, if_false] at hcl hb hnode
                  split_ifs at hcl hb hnode with h1
                  · have hb' : ¬ (heightOf 2 (some (ρr, ρc)) < a) := by simpa using hb
                    have haR : a = heightOf 2 (some (ρr, ρc)) := by omega
                    have ha1 : a + 1 < ((heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) : Int) +
                        (g : Int) - (it.offset : Int) + 1).toNat := by
                      rw [hoff]; omega
                    refine ⟨by simpa using ha1, ?_⟩
                    have hn1 : ¬ a + 1 < heightOf 2 (some (ρr, ρc)) := by omega
                    simp only [List.getElem_map, List.getElem_range, hcbf, Bool.false_eq_true,
                      if_false, if_neg hn1, if_neg h1]
                    refine ⟨trivial, by simpa using hcl, by simp; omega, trivial, trivial⟩

/-- **At level 2 every clean non-cut emit has its gap copy one row up.** -/
theorem runItemT_two_firstGap {ctx : Context} {τ : Row} {it : Item} {ps : List (Emit × Origin)}
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block) (hMD : FactMD ctx τ)
    (hFG : FactFG ctx τ) (hRe : Reach ctx τ 2 it) (h : runItemT ctx 2 it = .ok ps) :
    FirstGap ps := by
  rw [show (2 : Nat) = 0 + 2 from rfl] at h
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i children hch
    split at h
    · cases h
    · rename_i outs houts
      cases h
      intro p hp r hpr
      obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
      have hrun := hall a (by omega) ha
      have hlev : levelOneT ctx (children[a]'(by omega)) = .ok outs[a] := by
        simpa [runItemT] using hrun
      obtain ⟨C, cs0, lc, hC, hb, hsrcnode, hcs, hlc, rfl⟩ := levelOneT_clean hlev hpl hpr
      obtain ⟨ha1, hsrc1, hcl1, hcb1, htg0, htg1⟩ := childItems_two_next hV hch hi (hMD 0 it hRe)
        (fun C hC hb => hFG it C hRe hC hb) (a := a) (by omega) hC hb.symm hsrcnode
      obtain ⟨q0, hq0⟩ := hsrcnode
      have hlev1 := levelOneT_of_clean (ctx := ctx) (c := children[a + 1]) (q := q0)
        (by rw [hsrc1]; exact hq0) hcl1 hcs hlc
      have hrun1 := hall (a + 1) ha1 (by omega)
      have hout1 : outs[a + 1]'(by omega) =
          [(⟨(children[a + 1]).target, some lc⟩, .clean r (children[a + 1]).cutBottom)] := by
        have : levelOneT ctx (children[a + 1]) = .ok (outs[a + 1]'(by omega)) := by
          simpa [runItemT] using hrun1
        rw [hlev1] at this
        exact (Except.ok.inj this).symm
      refine ⟨_, List.mem_flatten.mpr ⟨outs[a + 1]'(by omega), List.getElem_mem _,
        by rw [hout1]; exact List.mem_singleton_self _⟩, by simp only [hcb1], ?_⟩
      show (children[a + 1]).target = Row.bump (children[a]).target 0
      rw [htg1, htg0]
      exact (Recon.RowLaw.bump_slot 0 it.target a).symm

/-- **Every clean non-cut emit of an item of level `≥ 2` has its gap copy one row up.** -/
theorem runItemT_firstGap (ctx : Context) (τ : Row) (hV : MountainValid ctx.source)
    (hi : 1 ≤ ctx.block) (hMD : FactMD ctx τ) (hFG : FactFG ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 2) it = .ok ps →
      Reach ctx τ (d + 2) it → FirstGap ps
  | 0, it, ps, h, hRe => runItemT_two_firstGap hV hi hMD hFG hRe h
  | d + 1, it, ps, h, hRe => by
      have h0 := h
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp r hpr
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hca : children[a]'(by omega) ∈ children := List.getElem_mem _
          have hIH := runItemT_firstGap ctx τ hV hi hMD hFG d _ _ (hall a (by omega) ha)
            (Reach.child hRe hch hca)
          obtain ⟨q, hq, hq1, hq2⟩ := hIH p hpl r hpr
          exact ⟨q, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩, hq1, hq2⟩

/-- **In a copied column of a block `i ≥ 1` every clean non-cut emit has its gap copy one
row up**, given `FactFG` (MD is proved). -/
theorem emitsT_firstGap (ctx : Context) (τ : Row) (hV : MountainValid ctx.source)
    (hi : 1 ≤ ctx.block) (hMD : FactMD ctx τ) (hFG : FactFG ctx τ)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) : FirstGap es := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp r hpr
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hal : a < (lowerItems τ).length := by omega
          have hmem := List.getElem_mem (l := lowerItems τ) hal
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          have hrun := hall a hal ha
          rw [hk] at hrun
          have hmem' := hmem
          rw [hk] at hmem'
          cases k with
          | zero =>
              -- a first item of level 1 copies no root row
              exfalso
              have hlev : levelOneT ctx ⟨slot 2 τ j, slot 2 τ j, none, 0, false⟩ = .ok outs[a] := by
                simpa [runItemT] using hrun
              obtain ⟨C, _, _, hC, _⟩ := levelOneT_clean hlev hpl hpr
              cases hC
          | succ k =>
              obtain ⟨q, hq, hq1, hq2⟩ := runItemT_firstGap ctx τ hV hi hMD hFG k _ _ hrun
                (Reach.top hmem') p hpl r hpr
              exact ⟨q, List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩),
                hq1, hq2⟩
      · unfold upperT at hus
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hus hp
        obtain ⟨h1, _⟩ := upper_emit hqp
        rw [h1] at hpr
        cases hpr

end OmegaY.Official.Classification.Proofs.CutGap
