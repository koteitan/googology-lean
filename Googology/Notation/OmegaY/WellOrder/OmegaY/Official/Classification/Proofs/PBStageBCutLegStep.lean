/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBCutLegStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBCutLeg

set_option backward.do.legacy false

/-!
# `CutLeg`: the children of related items (stage B)

The step of the parallel run of `PBStageBCutLeg.lean`: if `λ` (copy of `ℓ`) and `ξ` (copy of `x`)
are related (`RelC`) and a child `c` of `λ` produces an emit whose origin row is a target, then
`ξ` has a child `c'` related to `c` (`relC_step`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof
open Recon.LowerPB

/-! ## Ranges of origin rows -/

theorem rg_src {ctx : Context} {d : Nat} {c : Item} {r : Row} (hI : Inv ctx d c)
    (h : Rg ctx d c r) : inRegion d c.source r = true := by
  unfold Rg at h
  cases hc : c.clean with
  | none => simp only [hc] at h; exact h.1
  | some C =>
      simp only [hc] at h
      by_cases hb : c.cutBottom = true
      · rw [if_pos hb] at h
        subst h
        exact rootTop_mem (hI _ hc)
      · rw [if_neg hb] at h
        exact h.1

theorem rg_plain {ctx : Context} {d : Nat} {S T r : Row} {o : Nat}
    (h : Rg ctx d ⟨S, T, none, o, false⟩ r) : inRegion d S r = true := h.1

theorem rg_cib {ctx : Context} {d : Nat} {S T C r : Row} {o : Nat}
    (h : Rg ctx d ⟨S, T, some C, o, true⟩ r) : r = C := h

theorem rg_clean {ctx : Context} {d : Nat} {S T C r : Row} {o : Nat}
    (h : Rg ctx d ⟨S, T, some C, o, false⟩ r) : inRegion d S r = true ∧ r ≤ C := h

theorem rg_ib {ctx : Context} {d : Nat} {S T r : Row} {o : Nat}
    (h : Rg ctx d ⟨S, T, none, o, true⟩ r) :
    inRegion d S r = true ∧ ∀ ρ, rootTop ctx d S = some ρ → ρ ≤ r := ⟨h.1, h.2 rfl⟩

theorem slot_coeff {d : Nat} {S r : Row} {j : Nat}
    (h : inRegion (d + 1) (slot (d + 2) S j) r = true) :
    inRegion (d + 2) S r = true ∧ r.coeff d = j := Recon.RowLaw.inRegion_slot_iff.mp h

theorem height_eq (d : Nat) (r : Row) : height (d + 2) r = r.coeff d := rfl

theorem rootTop_eq {ctx : Context} {M : Mountain} {cr d : Nat} {S : Row} {ρ : Ref × Cell}
    (hs : ctx.source = M) (hr : ctx.rootColumn = cr) (h : topIn M cr d S = some ρ) :
    rootTop ctx d S = some (official ρ.2.row) := by
  unfold rootTop
  rw [hs, hr, h]
  rfl

namespace Setup

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
  {ctx ctx' : Context} {k : Nat} {cp : Cell} {r : Ref}

theorem blk (h : Setup s n R M t root i ctx ctx' k cp r) : ctx.block = i := h.B.block
theorem blk' (h : Setup s n R M t root i ctx ctx' k cp r) : ctx'.block = i := h.B'.block

/-! ## The `R2` step on the side of `ℓ` -/

/-- **The children of a plain or clean item of `ℓ` that can produce a target row below the root
top `ρ`**: a plain child in a slot below `ρ`, or a child in the slot of `ρ`. -/
theorem r2_child_L (h : Setup s n R M t root i ctx ctx' k cp r) {d : Nat} {it : Item}
    {cs : List Item} (hcase : ChildCase ctx' d it cs) (hcb : it.cutBottom = false)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M root.column (d + 2) it.source = some (ρr, ρc))
    (hcl : it.clean = none ∨ it.clean = some (official ρc.row)) {c : Item} (hc : c ∈ cs)
    {r0 : Row} (hrg : Rg ctx' (d + 1) c r0) (hlt : r0 < official ρc.row)
    (hin : inRegion (d + 2) it.source r0 = true) :
    (r0.coeff d < height (d + 2) (official ρc.row) ∧
      c = ⟨slot (d + 2) it.source (r0.coeff d), slot (d + 2) it.target (r0.coeff d), none, 0,
        false⟩) ∨
    (r0.coeff d = height (d + 2) (official ρc.row) ∧
      c.source = slot (d + 2) it.source (height (d + 2) (official ρc.row)) ∧
      c.target = slot (d + 2) it.target (height (d + 2) (official ρc.row)) ∧
      c.cutBottom = false ∧ (c.clean = none ∨ c.clean = some (official ρc.row))) := by
  have hρin := topIn_inRegion hρ
  have hσle : r0.coeff d ≤ height (d + 2) (official ρc.row) :=
    Recon.RowLaw.coeff_le_of_inRegion hin hρin hlt.le
  have hrt : rootTop ctx' (d + 2) it.source = some (official ρc.row) :=
    rootTop_eq h.B'.source h.B'.root hρ
  have hrts := rootTop_slot hrt
  cases hcase with
  | none _ => simp at hc
  | case1 a ha hasc hcl' hoff hcb' =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      obtain ⟨_, hj⟩ := slot_coeff (rg_plain hrg)
      subst hj
      rcases Nat.lt_or_eq_of_le hσle with hl | he
      · exact Or.inl ⟨hl, rfl⟩
      · exact Or.inr ⟨he, by rw [he], by rw [he], rfl, Or.inl rfl⟩
  | case2 a ha ρr' ρc' hρ' hasc hcl' hcb' L e hL he =>
      rw [h.B'.source, h.B'.root, hρ] at hρ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      unfold c2 at hrg ⊢
      by_cases h1 : j < height (d + 2) (official ρc.row)
      · rw [if_pos h1] at hrg ⊢
        obtain ⟨_, hj⟩ := slot_coeff (rg_plain hrg)
        subst hj
        exact Or.inl ⟨h1, rfl⟩
      · rw [if_neg h1] at hrg ⊢
        by_cases h2 : (j : Int) < (height (d + 2) (official ρc.row) : Int) + L + e
        · rw [if_pos h2] at hrg ⊢
          by_cases h3 : height (d + 2) (official ρc.row) < j
          · have hb : decide (height (d + 2) (official ρc.row) < j) = true := by simpa using h3
            rw [hb] at hrg
            exact absurd (rg_cib hrg) (ne_of_lt hlt)
          · have hb : decide (height (d + 2) (official ρc.row) < j) = false := by simpa using h3
            have hjR : j = height (d + 2) (official ρc.row) := by omega
            rw [hb] at hrg
            obtain ⟨_, hσ⟩ := slot_coeff (rg_clean hrg).1
            refine Or.inr ⟨hσ, rfl, by rw [hjR], ?_, Or.inr rfl⟩
            simp only [hb]
        · rw [if_neg h2] at hrg ⊢
          exfalso
          obtain ⟨hin', hσ⟩ := slot_coeff hrg.1
          have hσ' : (((j : Int) - L).toNat) = height (d + 2) (official ρc.row) := by omega
          have he0 : j = height (d + 2) (official ρc.row) + L := by omega
          have hbT : decide (ctx'.block ≠ 0 ∧ (j : Int) =
              (height (d + 2) (official ρc.row) : Int) + L) = true := by
            simp only [decide_eq_true_eq]
            exact ⟨by rw [h.blk']; exact Nat.pos_iff_ne_zero.mp h.i1, he0⟩
          have hle := hrg.2 hbT (official ρc.row) (by rw [hσ']; exact hrts)
          exact absurd hle (not_le.mpr hlt)
  | case3 a ha ρr' ρc' hρ' hasc hcl' hcb' e he =>
      rw [hcb] at hcb'; cases hcb'
  | case4 a ha ρr' ρc' hρ' hasc C hcl' csRef cs0 hcs g hg hbnd =>
      rw [h.B'.source, h.B'.root, hρ] at hρ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
      have hC : C = official ρc.row := by
        rcases hcl with h0 | h0 <;> rw [hcl'] at h0
        · cases h0
        · exact Option.some.inj h0
      subst hC
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      unfold c4 at hrg ⊢
      rw [hcb] at hrg ⊢
      simp only [Bool.false_eq_true, if_false] at hrg ⊢
      by_cases h1 : j < height (d + 2) (official ρc.row)
      · rw [if_pos h1] at hrg ⊢
        obtain ⟨_, hj⟩ := slot_coeff (rg_plain hrg)
        subst hj
        exact Or.inl ⟨h1, rfl⟩
      · rw [if_neg h1] at hrg ⊢
        by_cases h3 : height (d + 2) (official ρc.row) < j
        · have hb : decide (height (d + 2) (official ρc.row) < j) = true := by simpa using h3
          rw [hb] at hrg
          exact absurd (rg_cib hrg) (ne_of_lt hlt)
        · have hb : decide (height (d + 2) (official ρc.row) < j) = false := by simpa using h3
          have hjR : j = height (d + 2) (official ρc.row) := by omega
          rw [hb] at hrg
          obtain ⟨_, hσ⟩ := slot_coeff (rg_clean hrg).1
          refine Or.inr ⟨hσ, rfl, by rw [hjR], ?_, Or.inr rfl⟩
          simp only [hb]

theorem one_le_mul_int {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have := Int.mul_le_mul ha hb (by decide) (by omega)
  simpa using this

/-! ## The `R2` step on the side of `x` -/

/-- **The children of a plain or clean item of `x` below and at the root top `ρ`.** -/
theorem r2_child_X (h : Setup s n R M t root i ctx ctx' k cp r) {d : Nat} {it : Item}
    {cs : List Item} (hcase : ChildCase ctx d it cs) (hRe : Reach ctx (official t.row) (d + 2) it)
    (hcb : it.cutBottom = false)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M root.column (d + 2) it.source = some (ρr, ρc))
    (hcl : it.clean = none ∨ it.clean = some (official ρc.row)) {r0 : Row}
    (hT : TG M ctx ctx' cp r0) (hin : inRegion (d + 2) it.source r0 = true)
    (hle : r0.coeff d ≤ height (d + 2) (official ρc.row)) :
    (r0.coeff d < height (d + 2) (official ρc.row) →
      (⟨slot (d + 2) it.source (r0.coeff d), slot (d + 2) it.target (r0.coeff d), none, 0,
        false⟩ : Item) ∈ cs) ∧
    (r0.coeff d = height (d + 2) (official ρc.row) →
      ∃ c' ∈ cs, c'.source = slot (d + 2) it.source (height (d + 2) (official ρc.row)) ∧
        c'.target = slot (d + 2) it.target (height (d + 2) (official ρc.row)) ∧
        c'.cutBottom = false ∧ (c'.clean = none ∨ c'.clean = some (official ρc.row))) := by
  obtain ⟨a, ha, haσ⟩ := h.topX hT hin
  have hρx : topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) := by
    rw [h.B.source, h.B.root]; exact hρ
  have hblk : ctx.block ≠ 0 := by rw [h.blk]; exact Nat.pos_iff_ne_zero.mp h.i1
  cases hcase with
  | none hn =>
      rw [h.B.source, ha] at hn; cases hn
  | case1 a' ha' hasc hcl' hoff hcb' =>
      rw [h.B.source, ha] at ha'
      obtain rfl := Option.some.inj ha'
      refine ⟨fun hl => ?_, fun he => ?_⟩
      · exact List.mem_map.mpr ⟨r0.coeff d, List.mem_range.mpr (by rw [height_eq]; omega), rfl⟩
      · refine ⟨_, List.mem_map.mpr ⟨height (d + 2) (official ρc.row),
          List.mem_range.mpr (by rw [height_eq, height_eq] at *; omega), rfl⟩, rfl, rfl, rfl,
          Or.inl rfl⟩
  | case2 a' ha' ρr' ρc' hρ' hasc hcl' hcb' L e hL he =>
      rw [h.B.source, ha] at ha'
      obtain rfl := Option.some.inj ha'
      rw [hρx] at hρ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
      have hMD := CopyShape.Found.factMD_of_bctx h.top h.B d it hRe ρr ρc hρx hasc
      have hL1 : 1 ≤ L := by
        rw [hL]
        apply one_le_mul_int
        · have : heightOf (d + 2) (some (ρr, ρc)) = height (d + 2) (official ρc.row) := rfl
          omega
        · rw [h.blk]; exact_mod_cast h.i1
      have he0 : 0 ≤ e := by rw [he]; split <;> omega
      refine ⟨fun hl => ?_, fun heq => ?_⟩
      · refine List.mem_map.mpr ⟨r0.coeff d, List.mem_range.mpr ?_, ?_⟩
        · rw [height_eq] at *; omega
        · unfold c2; rw [if_pos hl]
      · refine ⟨_, List.mem_map.mpr ⟨height (d + 2) (official ρc.row), List.mem_range.mpr ?_, rfl⟩,
          ?_, ?_, ?_, ?_⟩
        · rw [height_eq, height_eq] at *; omega
        · unfold c2
          rw [if_neg (lt_irrefl _), if_pos (by omega)]
        · unfold c2
          rw [if_neg (lt_irrefl _), if_pos (by omega)]
        · unfold c2
          rw [if_neg (lt_irrefl _), if_pos (by omega)]
          simp
        · unfold c2
          rw [if_neg (lt_irrefl _), if_pos (by omega)]
          exact Or.inr rfl
  | case3 a' ha' ρr' ρc' hρ' hasc hcl' hcb' e he =>
      rw [hcb] at hcb'; cases hcb'
  | case4 a' ha' ρr' ρc' hρ' hasc C hcl' csRef cs0 hcs g hg hbnd =>
      rw [h.B.source, ha] at ha'
      obtain rfl := Option.some.inj ha'
      rw [hρx] at hρ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
      have hC : C = official ρc.row := by
        rcases hcl with h0 | h0 <;> rw [hcl'] at h0
        · cases h0
        · exact Option.some.inj h0
      subst hC
      have hoff : it.offset = 0 := by
        by_contra hne
        exact hbnd ⟨by rw [hcb]; simp, Or.inr hne⟩
      have hMH := CopyShape.Found.factMH_of_bctx h.run h.top h.i1 h.iln h.B d it _ hRe hcl' hcb
        csRef cs0 g hcs hg
      rw [hρx] at hMH
      have hMH' : height (d + 2) (official ρc.row) ≤
          heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g := hMH
      rw [if_neg hblk, hoff]
      refine ⟨fun hl => ?_, fun heq => ?_⟩
      · refine List.mem_map.mpr ⟨r0.coeff d, List.mem_range.mpr ?_, ?_⟩
        · rw [height_eq] at *; omega
        · unfold c4; rw [hcb]; simp only [Bool.false_eq_true, if_false]; rw [if_pos hl]
      · refine ⟨_, List.mem_map.mpr ⟨height (d + 2) (official ρc.row), List.mem_range.mpr ?_, rfl⟩,
          ?_, ?_, ?_, ?_⟩
        · omega
        · unfold c4; rw [hcb]; simp
        · unfold c4; rw [hcb]; simp
        · unfold c4; rw [hcb]; simp
        · unfold c4; rw [hcb]; simp

/-! ## The step of `R2` -/

theorem r2_step (h : Setup s n R M t root i ctx ctx' k cp r) {d : Nat} {a b : Item}
    {csL csX : List Item} (hR2 : R2 M root.column ctx cp (d + 2) a b)
    (hcL : ChildCase ctx' d a csL) (hcX : ChildCase ctx d b csX)
    (hRe : Reach ctx (official t.row) (d + 2) b) {c : Item} (hc : c ∈ csL) {r0 : Row}
    (hrg : Rg ctx' (d + 1) c r0) (hT : TG M ctx ctx' cp r0)
    (hin : inRegion (d + 2) a.source r0 = true) :
    ∃ c' ∈ csX, RelC M root.column ctx cp (d + 1) c c' := by
  obtain ⟨hs, ht, hcbL, hcbX, ⟨ρr, ρc⟩, hρ, hcond, hclL, hclX⟩ := hR2
  have hlt := h.tg_lt hT hcond
  have hle : r0.coeff d ≤ height (d + 2) (official ρc.row) :=
    Recon.RowLaw.coeff_le_of_inRegion hin (topIn_inRegion hρ) hlt.le
  have hρ' : topIn M root.column (d + 2) b.source = some (ρr, ρc) := by rw [← hs]; exact hρ
  have hin' : inRegion (d + 2) b.source r0 = true := by rw [← hs]; exact hin
  obtain ⟨hX1, hX2⟩ := h.r2_child_X hcX hRe hcbX hρ' hclX hT hin' hle
  rcases h.r2_child_L hcL hcbL hρ hclL hc hrg hlt hin with ⟨hl, rfl⟩ | ⟨heq, hsrc, htgt, hcb', hcl'⟩
  · refine ⟨_, hX1 hl, Or.inl ?_⟩
    rw [hs, ht]
  · obtain ⟨c', hc', hsrc', htgt', hcb'', hcl''⟩ := hX2 heq
    refine ⟨c', hc', Or.inr ⟨by rw [hsrc, hsrc', hs], by rw [htgt, htgt', ht], hcb', hcb'',
      (ρr, ρc), ?_, hcond, hcl', hcl''⟩⟩
    rw [hsrc]
    exact ChainCorr.Inner.topIn_slot hρ

/-! ## The step of `R1` (the same item) -/

theorem bnd_eq (h : Setup s n R M t root i ctx ctx' k cp r) (d : Nat) (T : Row) :
    topIn ctx'.result ctx'.boundary d T = topIn ctx.result ctx.boundary d T := by
  have e1 : ctx.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary; rw [h.B.root, h.B.width, h.B.block]
  have e2 : ctx'.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary; rw [h.B'.root, h.B'.width, h.B'.block]
  rw [e1, e2, CopyShape.Found.topIn_congr h.B.bnd, CopyShape.Found.topIn_congr h.B'.bnd]

/-- The two ascension tests at a root top, as a case split: equal, or `R2Cond`. -/
theorem r1_plain_diff (h : Setup s n R M t root i ctx ctx' k cp r) {d : Nat} {it : Item}
    {csL csX : List Item} (hcL : ChildCase ctx' d it csL) (hcX : ChildCase ctx d it csX)
    (hRe : Reach ctx (official t.row) (d + 2) it) (hcl : it.clean = none)
    (hcb : it.cutBottom = false) {ρr : Ref} {ρc : Cell}
    (hρ : topIn M root.column (d + 2) it.source = some (ρr, ρc)) {b1 b2 : Bool}
    (h1 : ascends ctx' (some (ρr, ρc)) = .ok b1) (h2 : ascends ctx (some (ρr, ρc)) = .ok b2)
    (hne : b1 ≠ b2) {c : Item} (hc : c ∈ csL) {r0 : Row}
    (hrg : Rg ctx' (d + 1) c r0) (hT : TG M ctx ctx' cp r0)
    (hin : inRegion (d + 2) it.source r0 = true) :
    ∃ c' ∈ csX, RelC M root.column ctx cp (d + 1) c c' :=
  h.r2_step ⟨rfl, rfl, hcb, hcb, (ρr, ρc), hρ, h.asc_diff hρ h1 h2 hne, Or.inl hcl, Or.inl hcl⟩
    hcL hcX hRe hc hrg hT hin

end Setup

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB
