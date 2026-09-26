/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBCutLegR1.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBCutLegStep

set_option backward.do.legacy false

/-!
# `CutLeg`: the step of two equal items (stage B)

`r1_step`: when the copies of `ℓ` and of `x` reach the same item, a child of it in the copy of
`ℓ` that produces a target origin row is a child in the copy of `x` as well (or the two
children are related by `R2`, when the ascension tests differ). The children lists differ only
in the top of the column (handled by the shadow nodes of `x`), and, for a copied root row, in
the generations (`GenLeg`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof
open Recon.LowerPB

namespace Setup

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
  {ctx ctx' : Context} {k : Nat} {cp : Cell} {r : Ref}

theorem e_bounds {d : Nat} {e : Int} (he : e = if d + 2 = 2 then 1 else 0) : 0 ≤ e ∧ e ≤ 1 := by
  rw [he]; split <;> omega

/-- `GenLeg` at a target row. -/
theorem gen_le (h : Setup s n R M t root i ctx ctx' k cp r) (hG : GenLeg) {C : Row}
    (hT : TG M ctx ctx' cp C) {ax ay : Ref} {cx cy : Cell} {gx gy : Nat}
    (hx : nodeAt ctx.source ctx.x C = some (ax, cx)) (hy : nodeAt ctx'.source ctx'.x C = some (ay, cy))
    (hgx : generations ctx.source ctx.rootColumn C (ctx.x + 1) ax cx 0 = .ok gx)
    (hgy : generations ctx'.source ctx'.rootColumn C (ctx'.x + 1) ay cy 0 = .ok gy) :
    gy ≤ gx := by
  rw [h.B.source] at hx hgx
  rw [h.B.root] at hgx
  rw [h.B'.source] at hy hgy
  rw [h.B'.root] at hgy
  rw [← h.hr] at hy hgy
  obtain ⟨q, cq, hqc, hq1, hcq, hrow, hor⟩ := hT
  obtain ⟨hyc, hy1, hycell, hyrow⟩ := Classification.nodeAt_spec hy
  have hqy : ay = q := ref_eq_of_official h.V (by rw [hyc, hqc, h.hr]) hy1 hq1 hycell hcq
    (by rw [hyrow, hrow])
  subst hqy
  have hcc : cy = cq := Option.some.inj (hycell.symm.trans hcq)
  subst hcc
  have hle : cy.row ≤ cp.row := by
    rcases hor with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact le_of_eq heq
  exact hG s M t root h.top ctx.x k cp r h.hx h.xle h.hk h.hcp h.hl h.lge C ax ay cx cy gx gy hx hy
    hle hgx hgy

/-- **The step of two equal items.** -/
theorem r1_step (h : Setup s n R M t root i ctx ctx' k cp r) (hG : GenLeg) {d : Nat} {it : Item}
    {csL csX : List Item} (hcL : ChildCase ctx' d it csL) (hcX : ChildCase ctx d it csX)
    (hRe : Reach ctx (official t.row) (d + 2) it) {c : Item} (hc : c ∈ csL) {r0 : Row}
    (hrg : Rg ctx' (d + 1) c r0) (hT : TG M ctx ctx' cp r0)
    (hin : inRegion (d + 2) it.source r0 = true) :
    ∃ c' ∈ csX, RelC M root.column ctx cp (d + 1) c c' := by
  obtain ⟨a, ha, haσ⟩ := h.topX hT hin
  have hax : topIn ctx.source ctx.x (d + 2) it.source = some a := by rw [h.B.source]; exact ha
  have hblk : ctx.block ≠ 0 := by rw [h.blk]; exact Nat.pos_iff_ne_zero.mp h.i1
  have hcL0 := hcL
  have hcX0 := hcX
  have hrt : ∀ ρ, topIn ctx'.source ctx'.rootColumn (d + 2) it.source = some ρ →
      topIn ctx.source ctx.rootColumn (d + 2) it.source = some ρ := by
    intro ρ h'; rw [h.B'.source, h.B'.root] at h'; rw [h.B.source, h.B.root]; exact h'
  have hrtM : ∀ ρ, topIn ctx.source ctx.rootColumn (d + 2) it.source = some ρ →
      topIn M root.column (d + 2) it.source = some ρ := by
    intro ρ h'; rw [h.B.source, h.B.root] at h'; exact h'
  cases hcL with
  | none _ => simp at hc
  | case1 aL haL hascL hcl hoff hcb =>
      cases hcX with
      | none hn => rw [hax] at hn; cases hn
      | case1 aX haX _ _ _ _ =>
          rw [hax] at haX
          obtain rfl := Option.some.inj haX
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          obtain ⟨_, hj⟩ := slot_coeff (rg_plain hrg)
          refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, rfl⟩, Or.inl rfl⟩
          rw [height_eq]; omega
      | case2 aX haX ρr ρc hρ hascX _ _ L e hL he =>
          have hρ' : topIn ctx'.source ctx'.rootColumn (d + 2) it.source = some (ρr, ρc) := by
            rw [h.B'.source, h.B'.root]; rw [h.B.source, h.B.root] at hρ; exact hρ
          rw [hρ'] at hascL
          exact h.r1_plain_diff hcL0 hcX0 hRe hcl hcb (hrtM _ hρ) hascL hascX (by simp) hc hrg
            hT hin
      | case3 _ _ _ _ _ _ _ hcb' _ _ => rw [hcb] at hcb'; cases hcb'
      | case4 _ _ _ _ _ _ C hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
  | case2 aL haL ρr ρc hρ hascL hcl hcb L e hL he =>
      cases hcX with
      | none hn => rw [hax] at hn; cases hn
      | case1 aX haX hascX _ _ _ =>
          rw [hrt _ hρ] at hascX
          exact h.r1_plain_diff hcL0 hcX0 hRe hcl hcb (hrtM _ (hrt _ hρ)) hascL hascX (by simp) hc
            hrg hT hin
      | case2 aX haX ρr' ρc' hρ' hascX _ _ L' e' hL' he' =>
          rw [hax] at haX
          obtain rfl := Option.some.inj haX
          rw [hrt _ hρ] at hρ'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
          have hLL : L' = L := by
            rw [hL, hL', h.B.source, h.B'.source, h.B.last, h.B'.last, h.blk, h.blk']
          have hee : e' = e := by rw [he, he']
          subst hLL hee
          have hMD := CopyShape.Found.factMD_of_bctx h.top h.B d it hRe ρr ρc (hrt _ hρ) hascX
          have hL1 : 1 ≤ L' := by
            rw [hL']
            apply one_le_mul_int
            · have : heightOf (d + 2) (some (ρr, ρc)) = height (d + 2) (official ρc.row) := rfl
              omega
            · rw [h.blk]; exact_mod_cast h.i1
          obtain ⟨he0, he1⟩ := e_bounds he'
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, by rw [h.blk, h.blk']⟩, Or.inl rfl⟩
          have hrg' := hrg
          unfold c2 at hrg'
          by_cases h1 : j < height (d + 2) (official ρc.row)
          · rw [if_pos h1] at hrg'
            obtain ⟨_, hj⟩ := slot_coeff (rg_plain hrg')
            rw [height_eq] at *; omega
          · rw [if_neg h1] at hrg'
            by_cases h2 : (j : Int) < (height (d + 2) (official ρc.row) : Int) + L' + e'
            · rw [if_pos h2] at hrg'
              have hσ : r0.coeff d = height (d + 2) (official ρc.row) := by
                by_cases h3 : height (d + 2) (official ρc.row) < j
                · have hb : decide (height (d + 2) (official ρc.row) < j) = true := by simpa using h3
                  rw [hb] at hrg'
                  rw [rg_cib hrg']; rfl
                · have hb : decide (height (d + 2) (official ρc.row) < j) = false := by
                    simpa using h3
                  rw [hb] at hrg'
                  exact (slot_coeff (rg_clean hrg').1).2
              rw [height_eq] at *; omega
            · rw [if_neg h2] at hrg'
              obtain ⟨_, hj⟩ := slot_coeff hrg'.1
              rw [height_eq] at *; omega
      | case3 _ _ _ _ _ _ _ hcb' _ _ => rw [hcb] at hcb'; cases hcb'
      | case4 _ _ _ _ _ _ C hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
  | case3 aL haL ρr ρc hρ hascL hcl hcb e he =>
      cases hcX with
      | none hn => rw [hax] at hn; cases hn
      | case1 _ _ _ _ _ hcb' => rw [hcb] at hcb'; cases hcb'
      | case2 _ _ _ _ _ _ _ hcb' _ _ _ _ => rw [hcb] at hcb'; cases hcb'
      | case3 aX haX ρr' ρc' hρ' hascX _ _ e' he' =>
          rw [hax] at haX
          obtain rfl := Option.some.inj haX
          rw [hrt _ hρ] at hρ'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
          have hee : e' = e := by rw [he, he']
          subst hee
          obtain ⟨he0, he1⟩ := e_bounds he'
          have hbb := h.bnd_eq (d + 2) it.target
          have hblk' : ctx'.block ≠ 0 := by rw [h.blk']; exact Nat.pos_iff_ne_zero.mp h.i1
          obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc
          obtain ⟨hjr, hjR⟩ := List.mem_filter.mp hjm
          have hjR' : height (d + 2) (official ρc.row) ≤ j := by simpa using hjR
          rw [if_neg hblk'] at hjr
          rw [hbb] at hrg ⊢
          refine ⟨_, List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr ?_, hjR⟩, rfl⟩,
            Or.inl rfl⟩
          rw [if_neg hblk]
          have hrg' := hrg
          unfold c3 at hrg'
          by_cases h2 : (j : Int) < (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2)
              it.target) : Int) + (height (d + 2) (official ρc.row) : Int) + e'
          · rw [if_pos h2] at hrg'
            have hσ : r0.coeff d = height (d + 2) (official ρc.row) := by rw [rg_cib hrg']; rfl
            rw [height_eq] at *; omega
          · rw [if_neg h2] at hrg'
            obtain ⟨_, hj⟩ := slot_coeff hrg'.1
            rw [height_eq] at *; omega
      | case4 _ _ _ _ _ _ C hcl' _ _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
  | case4 aL haL ρr ρc hρ hascL C hcl csRefL csL0 hcsL gL hgL hbndL =>
      cases hcX with
      | none hn => rw [hax] at hn; cases hn
      | case1 _ _ _ hcl' _ _ => rw [hcl] at hcl'; cases hcl'
      | case2 _ _ _ _ _ _ hcl' _ _ _ _ _ => rw [hcl] at hcl'; cases hcl'
      | case3 _ _ _ _ _ _ hcl' _ _ _ => rw [hcl] at hcl'; cases hcl'
      | case4 aX haX ρr' ρc' hρ' hascX C' hcl' csRefX csX0 hcsX gX hgX hbndX =>
          rw [hax] at haX
          obtain rfl := Option.some.inj haX
          rw [hrt _ hρ] at hρ'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
          rw [hcl] at hcl'
          obtain rfl := Option.some.inj hcl'
          have hbb := h.bnd_eq (d + 2) it.target
          have hblk' : ctx'.block ≠ 0 := by rw [h.blk']; exact Nat.pos_iff_ne_zero.mp h.i1
          obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc
          have hjr := List.mem_range.mp hjm
          rw [if_neg hblk'] at hjr
          rw [hbb] at hrg hjr ⊢
          refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, rfl⟩, Or.inl rfl⟩
          rw [if_neg hblk]
          -- the generations bound at the copied row, when the child copies it
          have hgen : r0 = C → gL ≤ gX := by
            intro hrC
            subst hrC
            exact h.gen_le hG hT hcsX hcsL hgX hgL
          have hrg' := hrg
          unfold c4 at hrg'
          cases hcut : it.cutBottom with
          | true =>
              rw [hcut] at hrg'
              simp only [if_true] at hrg'
              have := hgen (rg_cib hrg')
              omega
          | false =>
              have hoff : it.offset = 0 := by
                by_contra hne
                exact hbndX ⟨by rw [hcut]; simp, Or.inr hne⟩
              have hMH := CopyShape.Found.factMH_of_bctx h.run h.top h.i1 h.iln h.B d it _ hRe hcl
                hcut csRefX csX0 gX hcsX hgX
              rw [hrt _ hρ] at hMH
              have hMH' : height (d + 2) (official ρc.row) ≤
                  heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + gX := hMH
              rw [hcut] at hrg'
              simp only [Bool.false_eq_true, if_false] at hrg'
              rw [hoff] at hjr ⊢
              by_cases h1 : j < height (d + 2) (official ρc.row)
              · omega
              · rw [if_neg h1] at hrg'
                by_cases h3 : height (d + 2) (official ρc.row) < j
                · have hb : decide (height (d + 2) (official ρc.row) < j) = true := by simpa using h3
                  rw [hb] at hrg'
                  have := hgen (rg_cib hrg')
                  omega
                · omega

end Setup

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.Setup.r1_step
