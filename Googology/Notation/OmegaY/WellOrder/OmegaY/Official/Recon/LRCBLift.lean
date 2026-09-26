/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBLift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBSim

set_option backward.do.legacy false

/-!
# The top of the boundary column in a lifting region of `X`

`bnd_lift`: for a lifting item `K` of the tree of `X = x + w·(i+1)` (plain, no cut bottom, `x`
ascending at the root top `ρ` of its region), the boundary column `B = c_r + w·(i+1)` (the copy
of `x₀` in block `i`) has its top in the target region of `K` at height
`h_κ + (h_κ - h_ρ)·i`, where `κ` is the top of `x₀` in the region.

The proof: the path of `K` is aligned (`aligned_anc`); `simB_chain` follows it in the tree of
`B` (`stepB`), which therefore contains `K` itself, of case 2 (`x₀` ascends everywhere); its
last child is `h_κ + (h_κ - h_ρ)·i`, and it emits.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- The source regions of the items of the tree have a normal base. -/
theorem desc_src_zero {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) (hA : ZeroBelow (d - 1) A.source) : ZeroBelow (d' - 1) B.source := by
  induction hD with
  | refl => exact hA
  | @step d A cs c d' B hcs hc _ ih =>
    apply ih
    obtain ⟨j, hj⟩ := LegJump.childItems_source hcs c hc
    rw [hj]
    have := slot_zeroBelow d A.source j
    simpa using this

theorem tree_src_zero {ctx : Context} {τ : Row} {d : Nat} {B : Item}
    (h : InTree ctx τ d B) : ZeroBelow (d - 1) B.source := by
  obtain ⟨F, hF, hD⟩ := h
  apply desc_src_zero hD
  obtain ⟨k, j, _, _, hkj⟩ := mem_lowerItems hF
  rw [hkj]
  have := slot_zeroBelow k τ j
  simpa using this

/-- Two regions of one level with normal bases that share a row are equal. -/
theorem region_eq {d : Nat} {S T r : Row} (hS : ZeroBelow (d - 1) S) (hT : ZeroBelow (d - 1) T)
    (hrS : inRegion d S r = true) (hrT : inRegion d T r = true) : S = T := by
  apply row_ext
  intro q
  by_cases hq : q < d - 1
  · rw [hS q hq, hT q hq]
  · rw [← inRegion_iff'.mp hrS q (by omega), inRegion_iff'.mp hrT q (by omega)]

/-- **The ancestors of an aligned item are aligned.** -/
theorem aligned_anc {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item} {d' : Nat} {K : Item}
    (hD : Desc ctx d A d' K) (hA : InTree ctx (official t.row) d A)
    (hK : K.source = K.target) : A.source = A.target := by
  obtain ⟨hd1, hAOK⟩ := LowerLeftProof.inTree_itemOK hctx hA
  obtain ⟨hd'1, _, _, htgt, _⟩ := desc_facts hctx hD hd1 hAOK
  have hsrc := LowerLeftProof.desc_source hD
  have h1 := hsrc K.source (self_inRegion _ _)
  have h2 := htgt K.source (by rw [hK]; exact self_inRegion _ _)
  exact region_eq (tree_src_zero hA) hAOK.target h1 h2

/-- **The simulation of the aligned path of a lifting item by the tree of `B`.** -/
theorem simB_chain {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (hNCx : NewColumn s n R M t root (i + 1) x)
    (hNCb : NewColumn s n R M t root i (M.size - 1))
    {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB)
    {F : Nat × Item} (hF : F ∈ lowerItems (official t.row)) {dK : Nat} {K : Item}
    (hDK : Desc (colCtx M R root (i + 1) x) F.1 F.2 dK K) (hK2 : 2 ≤ dK)
    (hKal : K.source = K.target) {rK : Ref} {cK : Cell}
    (hρK : topIn M root.column dK K.source = some (rK, cK)) :
    ∀ m d A, d + m = F.1 → Desc (colCtx M R root (i + 1) x) F.1 F.2 d A →
      Desc (colCtx M R root (i + 1) x) d A dK K →
      ∃ A', Desc (colCtx M R root i (M.size - 1)) F.1 F.2 d A' ∧
        SimB (colCtx M R root (i + 1) x) (colCtx M R root i (M.size - 1)) d A A' ∧
        A.cutBottom = false := by
  have rX := hNCx.runCtx
  have rB := hNCb.runCtx
  have hb : Canonical.build s = .ok M := hNCx.top.build
  have hT := hNCx.top
  have hin : i + 1 ≤ n := by have := hNCx.block; omega
  have hFMDX := Proofs.CopyShape.Found.factMD_of_bctx hT (colCtx_bctx hNCx)
  have hFMDB := Proofs.CopyShape.Found.factMD_of_bctx hT (colCtx_bctx hNCb)
  obtain ⟨hρKm, hρKreg, _⟩ := RowLaw.topIn_spec hρK
  intro m
  induction m with
  | zero =>
    intro d A hd hD _
    subst hd
    have := desc_eq hD
    subst this
    refine ⟨F.2, .refl _ _, Or.inl rfl, ?_⟩
    obtain ⟨k, j, _, _, hkj⟩ := mem_lowerItems hF
    rw [hkj]
  | succ m ih =>
    intro d A hd hD hDAK
    obtain ⟨K0, csK0, hDK0, hcsK0, hAm⟩ := desc_parent hD (by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hAm
    have hlevA := desc_level_le hDAK
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    have hDK0' : Desc (colCtx M R root (i + 1) x) F.1 F.2 (d'' + 2) K0 := hDK0
    have hcsK0' : childItems (colCtx M R root (i + 1) x) (d'' + 2) K0 = .ok csK0 := hcsK0
    have hDK0K : Desc (colCtx M R root (i + 1) x) (d'' + 2) K0 dK K :=
      .step hcsK0' (List.getElem_mem hj) hDAK
    obtain ⟨K0', hDB, hsim, hK0cb⟩ := ih (d'' + 2) K0 (by omega) hDK0' hDK0K
    have hK0t : InTree (colCtx M R root (i + 1) x) (official t.row) (d'' + 2) K0 := ⟨F, hF, hDK0'⟩
    have hAt : InTree (colCtx M R root (i + 1) x) (official t.row) (d'' + 1) csK0[j] := ⟨F, hF, hD⟩
    obtain ⟨_, hK0OK⟩ := LowerLeftProof.inTree_itemOK rX hK0t
    have hK0B : InTree (colCtx M R root i (M.size - 1)) (official t.row) (d'' + 2) K0' := ⟨F, hF, hDB⟩
    obtain ⟨_, _, LB, hLB, _, _⟩ := inTree_facts rB hvsB hK0B
    obtain ⟨csB, _, hcsB, _, _⟩ := runItem_children hLB
    obtain ⟨ax, hax⟩ : ∃ ax, topIn M x (d'' + 2) K0.source = some ax := by
      cases h : topIn M x (d'' + 2) K0.source with
      | none =>
        have := childItems_none hcsK0' h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    -- `ρK` in the regions of the path
    have hρKA : inRegion (d'' + 1) csK0[j].source (official cK.row) = true :=
      LowerLeftProof.desc_source hDAK _ hρKreg
    have hρK0 : inRegion (d'' + 2) K0.source (official cK.row) = true :=
      LowerLeftProof.desc_source hDK0K _ hρKreg
    obtain ⟨ρr, ρc, hρ0, _⟩ := LowerLeftProof.top_ge hb hρKm hρK0
    obtain ⟨hρ0m, hρ0reg, _⟩ := RowLaw.topIn_spec hρ0
    have hρ0τ : official ρc.row < official t.row := hK0OK.below _ hρ0reg
    have hx0 : ∀ ρr' ρc', topIn M root.column (d'' + 2) K0.source = some (ρr', ρc') →
        ascends (colCtx M R root i (M.size - 1)) (some (ρr', ρc')) = .ok true := by
      intro ρr' ρc' h'
      obtain ⟨hm', hreg', _⟩ := RowLaw.topIn_spec h'
      exact x0_asc hT rfl rfl rfl hm' (hK0OK.below _ hreg')
    obtain ⟨ρ', hρ'e, q0, hq0, hq0r⟩ := node_of_ascends rB (hx0 ρr ρc hρ0)
    obtain rfl := Option.some.inj hρ'e
    have hq0reg : inRegion (d'' + 2) K0.source (official q0.2.row) = true := by
      rw [hq0r]; exact hρ0reg
    obtain ⟨bxr, bxc, hbx, hbxge⟩ := LowerLeftProof.top_ge hb hq0 hq0reg
    have hx0ρ : ∀ ρr' ρc', topIn M root.column (d'' + 2) K0.source = some (ρr', ρc') →
        height (d'' + 2) (official ρc'.row) ≤ height (d'' + 2) (official bxc.row) := by
      intro ρr' ρc' h'
      rw [hρ0] at h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      show (official ρc.row).coeff d'' ≤ (official bxc.row).coeff d''
      rw [← hq0r]; exact hbxge
    have hal := aligned_anc rX hDAK hAt hKal
    have hK0al := aligned_anc rX hDK0K hK0t hKal
    have hS' := hsim.source
    obtain ⟨hjB, hsimj, hcbj⟩ := stepB (cX := colCtx M R root (i + 1) x)
      (cB := colCtx M R root i (M.size - 1)) rfl rfl rfl (by show i + 1 ≠ 0; omega) hb hsim hK0cb
      hcsK0' hcsB hax hbx hj hal hK0al hρKm hρKA hx0 hx0ρ
      (fun r cl hρ hasc => hFMDX d'' K0 (reach_of_inTree hK0t) r cl hρ hasc)
      (fun r cl hρ hasc => by
        have := hFMDB d'' K0' (reach_of_inTree hK0B) r cl (by rw [hS']; exact hρ) hasc
        rw [hS'] at this; exact this)
      (fun C r cl csRef csc g hcl hcb hρ hn hg hbk => by
        have hi1 : 1 ≤ i := by
          have : (colCtx M R root i (M.size - 1)).block = i := rfl
          omega
        have hFMHB := Proofs.CopyShape.Found.factMH_of_bctx hNCx.run hT hi1 (by omega)
          (colCtx_bctx hNCb)
        have := hFMHB d'' K0' C (reach_of_inTree hK0B) hcl hcb csRef csc g hn hg
        have hρ' : topIn (colCtx M R root i (M.size - 1)).source
          (colCtx M R root i (M.size - 1)).rootColumn (d'' + 2) K0'.source = some (r, cl) := hρ
        rw [hρ'] at this
        exact this)
    exact ⟨csB[j], LowerLeftProof.desc_snoc hDB hcsB (List.getElem_mem hjB), hsimj, hcbj⟩

/-- The top of a region in a valid mountain is at or above every node of the region. -/
theorem topIn_row_max' {Rm : Mountain} (hV : MountainValid Rm) {c d : Nat} {T : Row}
    {q : Ref × Cell} (h : topIn Rm c d T = some q) {p : Ref × Cell} (hp : p ∈ realNodes Rm c)
    (hin : inRegion d T (official p.2.row) = true) : official p.2.row ≤ official q.2.row := by
  obtain ⟨hq, _, hmax⟩ := RowLaw.topIn_spec h
  have hle := Proofs.CopyShape.MHProof.row_le_of_index hV hp hq (hmax p hp hin)
  exact official_mono (realNodes_row_one_le hV hp) hle

/-- **The top of the boundary column in the target of a lifting item of `X`.** -/
theorem bnd_lift {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (hNCx : NewColumn s n R M t root (i + 1) x)
    (hNCb : NewColumn s n R M t root i (M.size - 1)) {d : Nat} {K : Item}
    (hK : InTree (colCtx M R root (i + 1) x) (official t.row) (d + 2) K)
    (hcl : K.clean = none) (hcb : K.cutBottom = false) {ax : Ref × Cell}
    (hax : topIn M x (d + 2) K.source = some ax) {rK : Ref} {cK : Cell}
    (hρK : topIn M root.column (d + 2) K.source = some (rK, cK))
    (hasc : ascends (colCtx M R root (i + 1) x) (some (rK, cK)) = .ok true) :
    K.source = K.target ∧
    height (d + 2) (official cK.row) <
      heightOf (d + 2) (topIn M (M.size - 1) (d + 2) K.source) ∧
    ∃ q, topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) (d + 2) K.target = some q ∧
      (official q.2.row).coeff d = heightOf (d + 2) (topIn M (M.size - 1) (d + 2) K.source) +
        (heightOf (d + 2) (topIn M (M.size - 1) (d + 2) K.source) -
          height (d + 2) (official cK.row)) * i := by
  have rX := hNCx.runCtx
  have rB := hNCb.runCtx
  have hb : Canonical.build s = .ok M := hNCx.top.build
  have hT := hNCx.top
  have hV : MountainValid M := build_valid_of_success hb
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hNCx.run
  have hVR : MountainValid R := hBasic.valid
  obtain ⟨_, hKOK⟩ := LowerLeftProof.inTree_itemOK rX hK
  -- `K` is aligned
  have hKal : K.source = K.target := by
    have hg := Proofs.CopyShape.MHProof.reach_good (ctx := colCtx M R root (i + 1) x) hV
      (by show 1 ≤ i + 1; omega) (reach_of_inTree hK)
    rcases hg with h | h | ⟨_, h⟩
    · exact h
    · rw [hcb] at h; cases h
    · have h' : topIn M root.column (d + 2) K.source = none := h
      rw [hρK] at h'; cases h'
  refine ⟨hKal, ?_⟩
  -- `K` is an item of the tree of `B`
  obtain ⟨vsB, usB, colB, hvsB, husB, _, hrowsB⟩ := hNCb.emits
  obtain ⟨F, hF, hDK⟩ := hK
  obtain ⟨K', hDK', hsim, _⟩ := simB_chain hNCx hNCb hvsB hF hDK (by omega) hKal hρK
    (F.1 - (d + 2)) (d + 2) K (by have := desc_level_le hDK; omega) hDK (.refl _ _)
  have hK'K : K' = K := by
    rcases hsim with h | ⟨_, _, _, _, C, h, _⟩ | ⟨_, _, _, _, _, r1, c1, h1, _, h2⟩ |
        ⟨_, _, _, _, _, _, r1, c1, _, h⟩
    · exact h
    · rw [hcl] at h; cases h
    · have e1 : (r1, c1) = (rK, cK) := Option.some.inj (h1.symm.trans hρK)
      rw [e1] at h2; rw [hasc] at h2; cases h2
    · rw [hcl] at h; cases h
  subst hK'K
  have hKB : InTree (colCtx M R root i (M.size - 1)) (official t.row) (d + 2) K' := ⟨F, hF, hDK'⟩
  obtain ⟨_, hKBOK, LB, hLB, hLBsub, hLBback⟩ := inTree_facts rB hvsB hKB
  obtain ⟨csB, _, hcsB, _, _⟩ := runItem_children hLB
  -- `x₀` ascends at `ρ` and has its top `κ` in the region
  obtain ⟨hρKm, hρKreg, _⟩ := RowLaw.topIn_spec hρK
  have hascB := x0_asc hT (ctx := colCtx M R root i (M.size - 1)) rfl rfl rfl hρKm
    (hKOK.below _ hρKreg)
  obtain ⟨ρ', hρ'e, q0, hq0, hq0r⟩ := node_of_ascends rB hascB
  obtain rfl := Option.some.inj hρ'e
  have hq0reg : inRegion (d + 2) K'.source (official q0.2.row) = true := by
    rw [hq0r]; exact hρKreg
  obtain ⟨κr, κc, hκ, _⟩ := LowerLeftProof.top_ge hb hq0 hq0reg
  have hFMDB := Proofs.CopyShape.Found.factMD_of_bctx hT (colCtx_bctx hNCb)
  have hMD := hFMDB d K' (reach_of_inTree hKB) rK cK hρK hascB
  refine ⟨hMD, ?_⟩
  have hκ' : topIn (colCtx M R root i (M.size - 1)).source (colCtx M R root i (M.size - 1)).x
      (d + 2) K'.source = some (κr, κc) := hκ
  obtain ⟨hlB, _⟩ := kids2 hcsB hcl hcb hκ' hρK hascB
  have hκtop : heightOf (d + 2) (topIn M (M.size - 1) (d + 2) K'.source) =
      height (d + 2) (official κc.row) := by
    have hκ2 : topIn M (M.size - 1) (d + 2) K'.source = some (κr, κc) := hκ
    rw [hκ2]; rfl
  have hMD' : height (d + 2) (official cK.row) < height (d + 2) (official κc.row) := by
    have := hMD; change _ < heightOf (d + 2) (topIn M (M.size - 1) (d + 2) K'.source) at this
    rw [hκtop] at this; exact this
  have hlen : csB.length = height (d + 2) (official κc.row) +
      (height (d + 2) (official κc.row) - height (d + 2) (official cK.row)) * i + 1 := by
    rw [hlB]
    have e : heightOf (d + 2) (topIn (colCtx M R root i (M.size - 1)).source
        (colCtx M R root i (M.size - 1)).lastColumn (d + 2) K'.source) =
        height (d + 2) (official κc.row) := hκtop
    rw [e]
    have : (((height (d + 2) (official κc.row) : Nat) : Int) -
        ((height (d + 2) (official cK.row) : Nat) : Int)) =
        (((height (d + 2) (official κc.row) - height (d + 2) (official cK.row) : Nat)) : Int) := by
      omega
    rw [this]
    have hi : ((colCtx M R root i (M.size - 1)).block : Int) = (i : Int) := rfl
    rw [hi]
    push_cast
    omega
  rw [hκtop]
  -- the emit of the last child
  have hHas : Has (colCtx M R root i (M.size - 1)) (d + 2) K'.source := ⟨q0, hq0, hq0reg⟩
  obtain ⟨_, em, hem, hemc⟩ := JumpLawLower.run_top rB hKBOK hHas hLB hcsB
  have hgood := runItem_good rB (d + 2) (by omega) K' hKBOK LB hLB
  have hemT := hgood.1.2.1 em hem
  -- the row of `em` is a row of `B`
  have hemR : em.row ∈ rowsOf R (root.column + (M.size - 1 - root.column) * (i + 1)) := by
    have e : root.column + (M.size - 1 - root.column) * (i + 1) =
        M.size - 1 + (M.size - 1 - root.column) * i := by
      have := hT.lt
      rw [Nat.mul_succ]; omega
    rw [e, hrowsB]
    exact List.mem_map.mpr ⟨em, List.mem_append_left _ (hLBsub em hem), rfl⟩
  obtain ⟨pe, hpe, hper⟩ := List.mem_map.mp hemR
  cases hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) (d + 2) K'.target with
  | none =>
    exfalso
    have := RowLaw.topIn_none hq pe hpe
    rw [hper, hemT] at this; cases this
  | some q =>
    refine ⟨q, rfl, ?_⟩
    obtain ⟨hqm, hqreg, _⟩ := RowLaw.topIn_spec hq
    have hle := topIn_row_max' hVR hq hpe (by rw [hper]; exact hemT)
    rw [hper] at hle
    have h1 := coeff_le_of_inRegion hemT hqreg hle
    -- the top is a lower row, emitted by `K'`
    have hqR : official q.2.row ∈ rowsOf R (M.size - 1 + (M.size - 1 - root.column) * i) := by
      have e : root.column + (M.size - 1 - root.column) * (i + 1) =
          M.size - 1 + (M.size - 1 - root.column) * i := by
        have := hT.lt
        rw [Nat.mul_succ]; omega
      rw [← e]
      exact List.mem_map.mpr ⟨q, hqm, rfl⟩
    rw [hrowsB] at hqR
    obtain ⟨emq, hemq, hemqr⟩ := List.mem_map.mp hqR
    have hqτ : official q.2.row < official t.row := by
      rw [← hKal] at hqreg; exact hKOK.below _ hqreg
    rcases List.mem_append.mp hemq with hl | hu
    · have hback := hLBback emq hl (by rw [hemqr]; exact hqreg)
      have h2 := run_coeff_lt rB hKBOK hLB hcsB emq hback
      rw [hemqr] at h2
      rw [hlen] at hemc h2
      show (official q.2.row).coeff d = _
      omega
    · obtain ⟨hU1, _⟩ := upper_facts husB
      obtain ⟨_, _, hr, hτ, _⟩ := hU1 emq hu
      rw [hemqr] at hτ
      exact absurd (lt_of_le_of_lt hτ hqτ) (lt_irrefl _)

end OmegaY.Official.Recon.LRC
