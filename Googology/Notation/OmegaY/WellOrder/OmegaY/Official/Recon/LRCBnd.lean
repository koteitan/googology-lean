/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBnd.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBInv

set_option backward.do.legacy false

/-!
# `LowerRowsBoundary` holds

`lowerRowsBoundary_holds : LowerRowsBoundary` (the boundary case of the rows form of the jump
law for the lower pairs, `JumpLawLowerSplit.lean`).

For a lower pair `λ < θ = bump λ e` of the column `X = x + w·(i+1)` whose upper node `θ` has its
leg in the root column `c_r`, the parent column is the boundary column `B = c_r + w·(i+1)`, the
copy of `x₀` in block `i`. In the tree of `X`, the counts of children read `B` through the
heights `h_B` of its tops in the target regions. With `T` the target of the item `J` of `λ`:

* (a) `B` has a lower node in `T`: `J` is aligned and holds the parent `p` of the origin of `θ`
  (a node of `c_r`, and `B` has every node of `c_r` below `τ`), or `J` has a cut bottom or
  copies a root row with offset `0` (`qb_tree`);
* (b) for `e = d + 1`, the top of `B` in `T` has height `h_B(T) < λ_d`: when `J` copies the root
  row `a` of `θ`, `a` has one generation (its leg is `c_r`) and `J` has offset `0`, so `J` has
  `h_B(T) + 2` children; otherwise `J` lifts (`bnd_lift`: `h_B(T) = h_ρ + Δ`) or has a cut
  bottom, and the top of `x` in `T` is above the root top `p`.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- A node whose leg is the root column has one generation. -/
theorem gen_one {M : Mountain} {cr : Nat} {C : Row} {fuel : Nat} {ref : Ref} {cell : Cell}
    {g : Nat} (h : generations M cr C fuel ref cell 0 = .ok g) (hc : cr < ref.column)
    (hl : leftColumn cell = .ok cr) : g = 1 := by
  cases fuel with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel =>
    unfold generations at h
    rw [if_neg (by omega)] at h
    simp only [bind, Except.bind, hl] at h
    rw [if_neg (by omega)] at h
    cases hn : nodeAt M cr C with
    | none => rw [hn] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | some q =>
      obtain ⟨r2, c2⟩ := q
      rw [hn] at h
      simp only at h
      obtain ⟨hm, _⟩ := RowLaw.nodeAt_spec hn
      have hr2 : r2.column = cr := (realNodes_column hm).1
      cases fuel with
      | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h
      | succ f =>
        unfold generations at h
        rw [if_pos (by omega)] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        omega

/-- **A copy of a root row with one generation, followed by a sibling, has offset `0`.** -/
theorem child_off0 {ctx : Context} (hblk : ctx.block ≠ 0) {d : Nat} {P : Item}
    {cs : List Item} (hcs : childItems ctx (d + 2) P = .ok cs) {ax : Ref × Cell}
    (hax : topIn ctx.source ctx.x (d + 2) P.source = some ax) {jJ : Nat}
    (hj : jJ + 1 < cs.length) {C : Row} (hC : (cs[jJ]'(by omega)).clean = some C)
    (hg1 : ∀ csRef csc g, nodeAt ctx.source ctx.x C = some (csRef, csc) →
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef csc 0 = .ok g → g = 1) :
    (cs[jJ]'(by omega)).offset = 0 := by
  have hj0 : jJ < cs.length := by omega
  obtain ⟨b, hb⟩ := childItems_asc hcs hax
  cases b with
  | false =>
    obtain ⟨_, _, _, hg⟩ := kids1 hcs hax hb
    rw [hg jJ hj0] at hC; cases hC
  | true =>
    cases hρ : topIn ctx.source ctx.rootColumn (d + 2) P.source with
    | none => rw [hρ] at hb; cases hb
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hb
      cases hPcl : P.clean with
      | none =>
        cases hPcb : P.cutBottom with
        | false =>
          obtain ⟨_, hg⟩ := kids2 hcs hPcl hPcb hax hρ hb
          rw [hg jJ hj0] at hC ⊢
          unfold c2 at hC ⊢
          split_ifs at hC ⊢ <;> first | rfl | simp at hC
        | true =>
          obtain ⟨_, hg⟩ := kids3 hcs hPcl hPcb hblk hax hρ hb
          rw [hg jJ hj0] at hC ⊢
          unfold c3 at hC ⊢
          split_ifs at hC ⊢ <;> first | rfl | simp at hC
      | some CP =>
        obtain ⟨xr, xc, g, hxn, hxg, _, hl, hg⟩ := kids4 hcs hPcl hblk hax hρ hb
        have hcj := hg jJ hj0
        have hCP : C = CP := by
          rw [hcj] at hC
          unfold c4 at hC
          split_ifs at hC <;> simp at hC <;> exact hC.symm
        subst hCP
        have hg' := hg1 xr xc g hxn hxg
        subst hg'
        have hoff := c4_offset (by rw [← hcj, hC]; simp)
        rw [← hcj] at hoff
        rw [hoff]
        rw [hl] at hj
        omega

/-- A node of `B` below `τ` is a node of its lower part. -/
theorem lower_of_node {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    (hNCb : NewColumn s n R M t root i (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB) {q : Ref × Cell}
    (hq : q ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i + 1)))
    (hτ : official q.2.row < official t.row) :
    ∃ em ∈ vsB.flatten, em.row = official q.2.row := by
  obtain ⟨vsB', usB, _, hvsB', husB, _, hrowsB⟩ := hNCb.emits
  have hvv : vsB' = vsB := Except.ok.inj (hvsB'.symm.trans hvsB)
  subst hvv
  have e : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    have := hNCb.top.lt
    rw [Nat.mul_succ]; omega
  have hqR : official q.2.row ∈ rowsOf R (M.size - 1 + (M.size - 1 - root.column) * i) := by
    rw [← e]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hrowsB] at hqR
  obtain ⟨emq, hemq, hemqr⟩ := List.mem_map.mp hqR
  rcases List.mem_append.mp hemq with hl | hu
  · exact ⟨emq, hl, hemqr⟩
  · exfalso
    obtain ⟨hU1, _⟩ := upper_facts husB
    obtain ⟨_, _, _, hτ', _⟩ := hU1 emq hu
    rw [hemqr] at hτ'
    exact absurd (lt_of_le_of_lt hτ' hτ) (lt_irrefl _)

/-- A lower node of `B` is not above the top of `B` in a region. -/
theorem lower_le_top {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    (hNCb : NewColumn s n R M t root i (M.size - 1)) (hVR : MountainValid R)
    {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i (M.size - 1)) (official t.row) vsB) {dd : Nat} {T : Row}
    {em : Emit} (hem : em ∈ vsB.flatten) (hin : inRegion dd T em.row = true) {q : Ref × Cell}
    (hq : topIn R (root.column + (M.size - 1 - root.column) * (i + 1)) dd T = some q) :
    em.row ≤ official q.2.row := by
  obtain ⟨vsB', usB, _, hvsB', _, _, hrowsB⟩ := hNCb.emits
  have hvv : vsB' = vsB := Except.ok.inj (hvsB'.symm.trans hvsB)
  subst hvv
  have e : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    have := hNCb.top.lt
    rw [Nat.mul_succ]; omega
  have hR : em.row ∈ rowsOf R (root.column + (M.size - 1 - root.column) * (i + 1)) := by
    rw [e, hrowsB]; exact List.mem_map.mpr ⟨em, List.mem_append_left _ hem, rfl⟩
  obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hR
  rw [← hpr]
  exact topIn_row_max' hVR hq hp (by rw [hpr]; exact hin)

set_option maxHeartbeats 1600000 in
/-- **`LowerRowsBoundary` holds.** -/
theorem lowerRowsBoundary_holds : LowerRowsBoundary := by
  intro s n R M t root i x lam θ e J hP hNCb vsY hvsY
  have rX := hP.nc.runCtx
  have rB := hNCb.runCtx
  have hb : Canonical.build s = .ok M := hP.nc.top.build
  have hT := hP.nc.top
  have hblk : (colCtx M R root (i + 1) x).block ≠ 0 := by show i + 1 ≠ 0; omega
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hP.nc.run
  have hVR : MountainValid R := hBasic.valid
  have hbnd := colCtx_bnd hP.nc
  obtain ⟨outsT, houts, θp, hθp, hθrow, cθ, hcθm, hcθ, hleg, haτ, hcls⟩ := xside hP
  set a := official cθ.row with ha
  obtain ⟨vs, us, col, hvs, _, hasm, k, hk, hkL, hlam, hθ, hleft, ⟨LJ, hLJ, hlamJ⟩, hmax⟩ := hP.run
  obtain ⟨F, hF, hDJ⟩ := hP.tree
  have hJt : InTree (colCtx M R root (i + 1) x) (official t.row) (e + 1) J := ⟨F, hF, hDJ⟩
  obtain ⟨_, hJOK⟩ := LowerLeftProof.inTree_itemOK rX hJt
  obtain ⟨hFOK, hFst, hF1, _⟩ := lower_itemOK (ctx := colCtx M R root (i + 1) x) hF
  obtain ⟨_, hlev, _, hJF, _⟩ := desc_facts rX hDJ hF1 hFOK
  have hJbelow : ∀ r, inRegion (e + 1) J.target r = true → r < official t.row := by
    intro r hr
    have := hJF r hr
    rw [← hFst] at this
    exact hFOK.below r this
  have hQB := qb_tree hP.nc hNCb hvsY hF (F.1 - (e + 1)) (e + 1) J (by omega) hDJ
  -- the node `(x, a)`
  obtain ⟨hua, hu1, hucell⟩ := Classification.mem_realNodes hcθm
  -- (a) `B` has a lower node in the target of `J`
  have hθmem : (vs.flatten ++ us)[k + 1] ∈ vs.flatten := getElem_mem_left hk hkL
  have hA : ∃ em ∈ vsY.flatten, inRegion (e + 1) J.target em.row = true := by
    cases hJcl : J.clean with
    | none =>
      cases hJcb : J.cutBottom with
      | true => exact hQB (Or.inl ⟨hJcl, hJcb⟩)
      | false =>
        rcases hcls with hJC | hadj
        · rw [hJC] at hJcl; cases hJcl
        · obtain ⟨p, hpm, hpJ, _, _, _⟩ := adj_M hb hcθm hleg hadj haτ
          obtain ⟨qp, hqp, hqpr⟩ := List.mem_map.mp hpm
          -- `J` is aligned: its source region holds the node `p` of the root column
          have hV : MountainValid M := build_valid_of_success hb
          have hg := Proofs.CopyShape.MHProof.reach_good (ctx := colCtx M R root (i + 1) x) hV
            (by show 1 ≤ i + 1; omega) (reach_of_inTree hJt)
          have hJal : J.source = J.target := by
            rcases hg with h | h | ⟨_, h⟩
            · exact h
            · rw [hJcb] at h; cases h
            · have h' : topIn M root.column (e + 1) J.source = none := h
              have := RowLaw.topIn_none h' qp hqp
              rw [hqpr, hpJ] at this; cases this
          rw [hJal] at hpJ
          have hpτ := hJbelow p hpJ
          obtain ⟨colM, hcolM, htM⟩ : ∃ colM, M[M.size - 1]? = some colM ∧ colM.back? = some t := by
            have h := hT.top
            cases hc : M[M.size - 1]? with
            | none => rw [hc] at h; cases h
            | some colM => rw [hc] at h; exact ⟨colM, rfl, h⟩
          have hin' : i + 1 ≤ n := by have := hP.nc.block; omega
          have hBR := CutPredMD.boundaryRootRowsHolds s n R hP.nc.run M colM t root hb hcolM htM hT.left
            hT.lt (i + 1) (by omega)
            (Proofs.CopyShape.Found.boundary_lt hP.nc.run hT (by omega) hin') qp hqp
            (by rw [hqpr]; exact hpτ)
          obtain ⟨qB, hqB, hqBr⟩ := hBR
          obtain ⟨em, hem, hemr⟩ := lower_of_node hNCb hvsY hqB (by rw [hqBr, hqpr]; exact hpτ)
          exact ⟨em, hem, by rw [hemr, hqBr, hqpr]; exact hpJ⟩
    | some C =>
      have hoff : J.offset = 0 := by
        rcases hcls with hJC | hadj
        · -- `J` copies `a`, with one generation; it is followed by the item of `θ`
          have hlev := desc_level_le hDJ
          have hltF : e + 1 < F.1 := by
            rcases Nat.eq_or_lt_of_le hlev with heq | h
            · exfalso
              obtain ⟨F1, F2⟩ := F
              simp only at heq hDJ
              subst heq
              have := desc_eq hDJ
              subst this
              rw [Inner.lowerItems_clean _ _ hF] at hJC; cases hJC
            · exact h
          obtain ⟨P, csP, hDP, hcsP, hJm⟩ := desc_parent hDJ hltF
          have hDP' : Desc (colCtx M R root (i + 1) x) F.1 F.2 (e + 2) P := hDP
          have hcsP' : childItems (colCtx M R root (i + 1) x) (e + 2) P = .ok csP := hcsP
          obtain ⟨jJ, hjJ, hjJe⟩ := List.getElem_of_mem hJm
          have hPt : InTree (colCtx M R root (i + 1) x) (official t.row) (e + 2) P := ⟨F, hF, hDP'⟩
          obtain ⟨_, hPOK⟩ := LowerLeftProof.inTree_itemOK rX hPt
          obtain ⟨axP, haxP⟩ : ∃ ax, topIn (colCtx M R root (i + 1) x).source
              (colCtx M R root (i + 1) x).x (e + 2) P.source = some ax := by
            cases h : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).x
                (e + 2) P.source with
            | none =>
              have := childItems_none hcsP' h
              rw [this] at hjJ; simp at hjJ
            | some ax => exact ⟨ax, rfl⟩
          obtain ⟨_, hJtg⟩ := child_itemOK rX hPOK hcsP' jJ hjJ
          have hLc : lam.coeff e = jJ := by
            have := hP.region
            rw [← hjJe, hJtg] at this
            exact coeff_of_slot this
          have hLP1 : inRegion (e + 2) P.target lam = true := by
            have := hP.region
            rw [← hjJe, hJtg] at this
            exact region_of_slot this
          have hθP : inRegion (e + 2) P.target θ = true := by
            rw [inRegion_iff'] at hLP1 ⊢
            intro q hq
            rw [hP.bump, bump_coeff_hi (by omega), hLP1 q hq]
          obtain ⟨_, _, LP, hLP, _, hbackP⟩ := inTree_facts rX hvs hPt
          have hθLP := hbackP _ hθmem (by rw [hθ]; exact hθP)
          have hθc := run_coeff_lt rX hPOK hLP hcsP' _ hθLP
          rw [hθ, hP.bump, bump_coeff_e, hLc] at hθc
          have hCj : (csP[jJ]'hjJ).clean = some a := by rw [hjJe]; exact hJC
          have hg1 : ∀ csRef csc g, nodeAt (colCtx M R root (i + 1) x).source
              (colCtx M R root (i + 1) x).x a = some (csRef, csc) →
              generations (colCtx M R root (i + 1) x).source
                (colCtx M R root (i + 1) x).rootColumn a
                ((colCtx M R root (i + 1) x).x + 1) csRef csc 0 = .ok g → g = 1 := by
            intro csRef csc g hn hg
            have hxe := nodeAt_eq_of_mem hb hcθm hn
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxe
            exact gen_one hg (by rw [hua]; exact (mem_blockColumns hT.lt hP.nc.mem).1) hleg
          have := child_off0 hblk hcsP' haxP hθc hCj hg1
          rw [hjJe] at this
          exact this
        · obtain ⟨_, _, _, _, _, _, hoff, _⟩ := hadj
          exact hoff (by rw [hJcl]; simp)
      exact hQB (Or.inr ⟨by rw [hJcl]; simp, hoff⟩)
  refine ⟨hA, ?_⟩
  -- (b) the nodes of `B` in the target of `J` are below the slot of `λ`
  intro em hem hin d hd
  subst hd
  obtain ⟨q, hq⟩ := top_of_lower hNCb hvsY hem hin
  have hle := lower_le_top hNCb hVR hvsY hem hin hq
  obtain ⟨_, hqreg, _⟩ := RowLaw.topIn_spec hq
  have hcoef := coeff_le_of_inRegion hin hqreg hle
  have hB : heightOf (d + 1 + 1) (topIn (colCtx M R root (i + 1) x).result
      (colCtx M R root (i + 1) x).boundary (d + 1 + 1) J.target) = (official q.2.row).coeff d := by
    rw [hbnd, hq]; rfl
  obtain ⟨csJ, _, hcsJ, _, _⟩ := runItem_children hLJ
  have hlh := lam_height hP hcsJ
  obtain ⟨ax, hax⟩ : ∃ ax, topIn M x (d + 2) J.source = some ax := by
    cases h : topIn M x (d + 2) J.source with
    | none =>
      have := childItems_none hcsJ h
      rw [this] at hlh; simp at hlh
    | some ax => exact ⟨ax, rfl⟩
  have hax' : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).x (d + 2)
      J.source = some ax := hax
  rcases hcls with hJC | hadj
  · -- `J` copies `a`: one generation and offset `0`
    have hbJ := asc_true_of_kind hcsJ hax' (Or.inl (by rw [hJC]; simp))
    cases hρ : topIn M root.column (d + 2) J.source with
    | none =>
      have : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).rootColumn
        (d + 2) J.source = none := hρ
      rw [this] at hbJ; cases hbJ
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      have hρ' : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).rootColumn
        (d + 2) J.source = some (r, cl) := hρ
      rw [hρ'] at hbJ
      obtain ⟨xr, xc, g, hxn, hxg, _, hl, _⟩ := kids4 hcsJ hJC hblk hax' hρ' hbJ
      have hxe := nodeAt_eq_of_mem hb hcθm hxn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxe
      have hxgt : root.column < x := (mem_blockColumns hT.lt hP.nc.mem).1
      have hg1 : g = 1 := gen_one hxg (by rw [hua]; exact hxgt) hleg
      subst hg1
      have hinv := off_tree (ctx := colCtx M R root (i + 1) x) hblk hVR hbnd (le_refl 1) hxn hxg hJt
      have hoff : J.offset = 0 := by
        rcases hinv hJC with h | ⟨_, hfree⟩
        · omega
        · exfalso
          rw [hbnd, hq] at hfree; cases hfree
      rw [hB, hoff] at hl
      have : lam.coeff d + 1 = (official q.2.row).coeff d + 2 := by rw [hlh, hl]; omega
      show em.row.coeff d < lam.coeff d
      omega
  · -- adjacent: `J` is plain
    obtain ⟨p, hpm, hpJ, _, hpmax, aL, haLm, haLJ, haLmax, hJlt, hlte, _⟩ :=
      adj_M hb hcθm hleg hadj haτ
    obtain ⟨_, _, _, _, _, hJcl, _, _⟩ := hadj
    have hJn := hJcl (by omega)
    -- the top of `x` in the region of `J` is `a_λ`
    have htxr : official ax.2.row = aL := by
      obtain ⟨htxm, htxin, _⟩ := RowLaw.topIn_spec hax
      apply le_antisymm
      · exact haLmax _ (List.mem_map.mpr ⟨ax, htxm, rfl⟩) htxin
      · obtain ⟨qL, hqL, hqLr⟩ := List.mem_map.mp haLm
        rw [← hqLr]
        exact topIn_row_max hb hax hqL (by rw [hqLr]; exact haLJ)
    -- the root top in the region of `J` is `p`
    obtain ⟨qp, hqp, hqpr⟩ := List.mem_map.mp hpm
    obtain ⟨ρr, ρc, hρ, _⟩ := LowerLeftProof.top_ge hb hqp (by rw [hqpr]; exact hpJ)
    have hρr : official ρc.row = p := by
      obtain ⟨hρm, hρin, _⟩ := RowLaw.topIn_spec hρ
      apply le_antisymm
      · exact hpmax _ (List.mem_map.mpr ⟨(ρr, ρc), hρm, rfl⟩) (hJlt _ hρin)
      · rw [← hqpr]
        exact topIn_row_max hb hρ hqp (by rw [hqpr]; exact hpJ)
    have hρ' : topIn (colCtx M R root (i + 1) x).source (colCtx M R root (i + 1) x).rootColumn
      (d + 2) J.source = some (ρr, ρc) := hρ
    -- `x` ascends there (its node `(x, a)` has its leg in the root column)
    have ha0 : official cθ.row ≠ 0 := by
      intro h0
      have := hJlt aL haLJ
      rw [h0] at this
      exact absurd this (not_lt.mpr (Row.zero_le _))
    have hasc : ascends (colCtx M R root (i + 1) x) (some (ρr, ρc)) = .ok true := by
      obtain ⟨hρm, _, _⟩ := RowLaw.topIn_spec hρ
      refine ascends_of_root_leg hb rfl (q := (θp.2.src, cθ)) hcθm ha0 hleg
        ⟨hpm, hJlt p hpJ, hpmax⟩ hρm (by rw [hρr])
    have hHR : height (d + 2) (official ρc.row) = p.coeff d := by rw [hρr]; rfl
    have hTX : height (d + 2) (official ax.2.row) = aL.coeff d := by rw [htxr]; rfl
    have hlt' := hlte d rfl
    cases hcb : J.cutBottom with
    | false =>
      obtain ⟨hl, _⟩ := kids2 hcsJ hJn hcb hax' hρ' hasc
      obtain ⟨_, hMD, q', hq', hq'c⟩ := bnd_lift hP.nc hNCb hJt hJn hcb hax hρ hasc
      rw [hq] at hq'
      obtain rfl := Option.some.inj hq'
      have e1 : heightOf (d + 2) (topIn (colCtx M R root (i + 1) x).source
          (colCtx M R root (i + 1) x).lastColumn (d + 2) J.source) =
          heightOf (d + 2) (topIn M (M.size - 1) (d + 2) J.source) := rfl
      have e2 : ((colCtx M R root (i + 1) x).block : Int) = ((i + 1 : Nat) : Int) := rfl
      rw [e1, e2, hTX] at hl
      rw [hHR] at hl hq'c hMD
      generalize hK : heightOf (d + 2) (topIn M (M.size - 1) (d + 2) J.source) = K at hl hq'c hMD
      have hl' : csJ.length = aL.coeff d + (K - p.coeff d) * (i + 1) + 1 := by
        rw [hl]
        have : ((K : Int) - (p.coeff d : Int)) = ((K - p.coeff d : Nat) : Int) := by omega
        rw [this]
        have e3 : (((aL.coeff d : Nat) : Int) + ((K - p.coeff d : Nat) : Int) * ((i + 1 : Nat) : Int)
            + 1) = ((aL.coeff d + (K - p.coeff d) * (i + 1) + 1 : Nat) : Int) := by push_cast; rfl
        rw [e3, Int.toNat_natCast]
      rw [Nat.mul_succ] at hl'
      generalize hP' : (K - p.coeff d) * i = PP at hl' hq'c
      show em.row.coeff d < lam.coeff d
      omega
    | true =>
      obtain ⟨hl, _⟩ := kids3 hcsJ hJn hcb hblk hax' hρ' hasc
      rw [hB, hTX, hHR] at hl
      show em.row.coeff d < lam.coeff d
      omega

end OmegaY.Official.Recon.LRC

#print axioms OmegaY.Official.Recon.LRC.lowerRowsBoundary_holds
