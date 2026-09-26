/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCCopy.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCChain

set_option backward.do.legacy false

/-!
# `LowerRowsCopy` holds

`lowerRowsCopy_holds : LowerRowsCopy` (the copy case of the rows form of the jump law for the
lower pairs, `JumpLawLowerSplit.lean`).

For a lower pair `λ < θ = bump λ e` of the column `X = x + w·i` whose upper node `θ` has its
leg in the column `l`, `c_r < l < x`, the column read for the parent is `Y = l + w·i`.

1. (`xside`, `LRCX.lean`) `θ` comes from a node `(x, a)` with leg `l`. Either the item `J` of
   `λ` copies the root row `a` (**F1**), or `a` is the node of `x` just above the origin `a_λ`
   of `λ`, in the next slot of level `e + 1` (**Adj**).
2. A row `w` of `l`: `a` itself (F1: `l` ascends at `a` by `ascLegLe`, so it has the node
   `node_of_ascends`), or the parent `p` of `(x, a)` (Adj, `adj_M`). It agrees with `a` above
   `e` and lies in the source region of `J`.
3. (`sim_chain`, `step`) The tree of `Y` has, along the path of `λ`, items similar to those of
   `X`, and at the level of `J` the item `J` itself.
4. `J` has fewer children in `Y` than in `X`: one generation less (F1, `gen_step`), or the top
   of `l` in the source region of `J` is `p`, below the top `a_λ` of `x` (Adj).
5. `rows_of_item` turns this into the rows conclusion.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

theorem gen_pos {M : Mountain} {cr : Nat} {C : Row} {fuel : Nat} {ref : Ref} {cell : Cell}
    {g0 g : Nat} (h : generations M cr C fuel ref cell g0 = .ok g) (hc : cr < ref.column) :
    g0 + 1 ≤ g := by
  cases fuel with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel =>
    unfold generations at h
    rw [if_neg (by omega)] at h
    simp only [bind, Except.bind] at h
    cases hl : leftColumn cell with
    | error e => rw [hl] at h; cases h
    | ok p =>
      rw [hl] at h
      simp only at h
      by_cases hp : p < ref.column
      · rw [if_neg (by omega)] at h
        cases hn : nodeAt M p C with
        | none => rw [hn] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
        | some q =>
          obtain ⟨r2, c2⟩ := q
          rw [hn] at h
          simp only at h
          have := gen_shift M cr C fuel r2 c2 (g0 + 1) g h fuel (g0 + 1) g h
          have hge := gen_ge M cr C fuel r2 c2 (g0 + 1) g h
          omega
      · rw [if_pos (by omega)] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
where
  gen_ge (M : Mountain) (cr : Nat) (C : Row) : ∀ fuel ref cell g0 g,
      generations M cr C fuel ref cell g0 = .ok g → g0 ≤ g
    | 0, _, _, _, _, h => by simp [generations, throw, throwThe, MonadExceptOf.throw] at h
    | fuel + 1, ref, cell, g0, g, h => by
      unfold generations at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; omega
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · have := gen_ge M cr C fuel _ _ (g0 + 1) g h
              omega

/-- A child that copies a root row comes from an item whose column ascends at the root top of
its region, the copied row. -/
theorem clean_child_root {ctx : Context} (hblk : ctx.block ≠ 0) {d : Nat} {P : Item}
    {cs : List Item} (hcs : childItems ctx (d + 2) P = .ok cs) {ax : Ref × Cell}
    (hax : topIn ctx.source ctx.x (d + 2) P.source = some ax)
    (hct : LegJump.CleanTop ctx (d + 2) P) {j : Nat} (hj : j < cs.length) {C : Row}
    (hC : cs[j].clean = some C) :
    ∃ r cl, topIn ctx.source ctx.rootColumn (d + 2) P.source = some (r, cl) ∧
      official cl.row = C ∧ ascends ctx (some (r, cl)) = .ok true := by
  obtain ⟨b, hb⟩ := childItems_asc hcs hax
  cases b with
  | false =>
    obtain ⟨_, _, _, hg⟩ := kids1 hcs hax hb
    rw [hg j hj] at hC; cases hC
  | true =>
    cases hρ : topIn ctx.source ctx.rootColumn (d + 2) P.source with
    | none => rw [hρ] at hb; cases hb
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hb
      refine ⟨r, cl, rfl, ?_, hb⟩
      cases hPcl : P.clean with
      | none =>
        cases hPcb : P.cutBottom with
        | false =>
          obtain ⟨_, hg⟩ := kids2 hcs hPcl hPcb hax hρ hb
          rw [hg j hj] at hC
          rcases c2_cases (d := d + 2) (S := P.source) (T := P.target) (i := ctx.block)
            (hR := height (d + 2) (official cl.row))
            (lift := (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) P.source) :
              Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) * (ctx.block : Int))
            (C := official cl.row) j with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
          · rw [h2] at hC; cases hC
          · rw [h3] at hC; exact Option.some.inj hC
          · rw [h3.2.1] at hC; cases hC
        | true =>
          obtain ⟨_, hg⟩ := kids3 hcs hPcl hPcb hblk hax hρ hb
          rw [hg j hj] at hC
          rcases c3_cases (d := d + 2) (S := P.source) (T := P.target)
            (hR := height (d + 2) (official cl.row))
            (hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) P.target))
            (C := official cl.row) (j + height (d + 2) (official cl.row)) with ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [h2] at hC; exact Option.some.inj hC
          · rw [h2] at hC; cases hC
      | some CP =>
        obtain ⟨_, _, _, _, _, _, _, hg⟩ := kids4 hcs hPcl hblk hax hρ hb
        rw [hg j hj] at hC
        have hCP : C = CP := by
          unfold c4 at hC
          split_ifs at hC <;> simp at hC <;> exact hC.symm
        subst hCP
        obtain ⟨ρ', hρ', hρ'r⟩ := hct C hPcl
        rw [hρ] at hρ'
        rw [← Option.some.inj hρ'] at hρ'r
        exact hρ'r

set_option maxHeartbeats 1000000 in
/-- **`LowerRowsCopy` holds.** -/
theorem lowerRowsCopy_holds : LowerRowsCopy := by
  intro s n R M t root i x lam θ l e J hP hlt hlx hNCy vsY hvsY
  have hCS : CS s n R M t root i x l := ⟨hP.nc, hNCy, hP.pos, hlt, hlx⟩
  have rX := hP.nc.runCtx
  have rY := hNCy.runCtx
  have hb : Canonical.build s = .ok M := hP.nc.top.build
  have hblk : (colCtx M R root i x).block ≠ 0 := by show i ≠ 0; have := hP.pos; omega
  have pr : Pair (colCtx M R root i x) (colCtx M R root i l) :=
    ⟨rfl, rfl, rfl, rfl, fun d T => (hCS.bnd d T).symm, hblk⟩
  have hin : i ≤ n := by have := hP.nc.block; omega
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hP.nc.run
  have hVR : MountainValid R := hBasic.valid
  obtain ⟨outsT, houts, θp, hθp, hθrow, cθ, hcθm, hcθ, hleg, haτ, hcls⟩ := xside hP
  have H := anch_of hCS hcθm hleg
  set a := official cθ.row with ha
  -- the emits `λ`, `θ` of `X`
  obtain ⟨vs, us, col, hvs, _, hasm, k, hk, hkL, hlam, hθ, hleft, ⟨LJ, hLJ, hlamJ⟩, hmax⟩ := hP.run
  obtain ⟨F, hF, hDJ⟩ := hP.tree
  have hθreg : ∀ d (T : Row), e + 2 ≤ d → inRegion d T lam = true → inRegion d T θ = true := by
    intro d T hd hT
    rw [inRegion_iff'] at hT ⊢
    intro q hq
    rw [hP.bump, bump_coeff_hi (by omega), hT q hq]
  have hEOK : ∀ d A, Desc (colCtx M R root i x) F.1 F.2 d A → e + 2 ≤ d →
      inRegion d A.target lam = true →
      Inner.EmitOK (colCtx M R root i x).source (colCtx M R root i x).rootColumn d A θp := by
    intro d A hD hd hA
    exact eok_of_tree rX houts hθp ⟨F, hF, hD⟩ (by rw [hθrow]; exact hθreg d A.target hd hA)
  have hY : ∀ d B, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B →
      ∃ csY, childItems (colCtx M R root i l) (d + 2) B = .ok csY := by
    intro d B hD
    obtain ⟨_, _, LB, hLB, _, _⟩ := inTree_facts rY hvsY ⟨F, hF, hD⟩
    obtain ⟨cs, _, hcs, _, _⟩ := runItem_children hLB
    exact ⟨cs, hcs⟩
  have hFMDX := Proofs.CopyShape.Found.factMD_of_bctx hP.nc.top (colCtx_bctx hP.nc)
  have hFMDY := Proofs.CopyShape.Found.factMD_of_bctx hP.nc.top (colCtx_bctx hNCy)
  have hFMHX := Proofs.CopyShape.Found.factMH_of_bctx hP.nc.run hP.nc.top hP.pos hin
    (colCtx_bctx hP.nc)
  have hFMHY := Proofs.CopyShape.Found.factMH_of_bctx hP.nc.run hP.nc.top hP.pos hin
    (colCtx_bctx hNCy)
  have hMDX : ∀ d A r cl, Desc (colCtx M R root i x) F.1 F.2 (d + 2) A →
      topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2) A.source =
        some (r, cl) →
      ascends (colCtx M R root i x) (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
          (d + 2) A.source) :=
    fun d A r cl hD hρ hasc => hFMDX d A (reach_of_inTree ⟨F, hF, hD⟩) r cl hρ hasc
  have hMDY : ∀ d B r cl, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B →
      topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2) B.source =
        some (r, cl) →
      ascends (colCtx M R root i l) (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
          (d + 2) B.source) :=
    fun d B r cl hD hρ hasc => hFMDY d B (reach_of_inTree ⟨F, hF, hD⟩) r cl hρ hasc
  have hMHY : ∀ d B, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B → ∀ C r cl csRef csc g,
      B.clean = some C → B.cutBottom = false →
      topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2) B.source =
        some (r, cl) →
      nodeAt (colCtx M R root i x).source (colCtx M R root i l).x C = some (csRef, csc) →
      generations (colCtx M R root i x).source (colCtx M R root i x).rootColumn C
        ((colCtx M R root i l).x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn (colCtx M R root i x).result (colCtx M R root i x).boundary
          (d + 2) B.target) + g := by
    intro d B hD C r cl csRef csc g hC hcb hρ hn hg
    have := hFMHY d B C (reach_of_inTree ⟨F, hF, hD⟩) hC hcb csRef csc g hn hg
    have hρ' : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
        B.source = some (r, cl) := hρ
    rw [hρ', pr.bnd] at this
    exact this
  -- the node `λ`, `θ` of `X` in `vs`
  have hkL0 : k < vs.flatten.length := by omega
  have hLmem : (vs.flatten ++ us)[k] ∈ vs.flatten := getElem_mem_left (by omega) hkL0
  have hθmem : (vs.flatten ++ us)[k + 1] ∈ vs.flatten := getElem_mem_left hk hkL
  have hne : (vs.flatten ++ us)[k] ≠ (vs.flatten ++ us)[k + 1] := by
    intro h
    have : lam = θ := by rw [← hlam, ← hθ, h]
    rw [hP.bump] at this
    exact absurd this (ne_of_lt (Row.lt_bump lam e))
  have hnt : ∀ d A cs j, Desc (colCtx M R root i x) F.1 F.2 (d + 2) A →
      childItems (colCtx M R root i x) (d + 2) A = .ok cs →
      ∀ hj : j < cs.length, e + 2 ≤ d + 1 → inRegion (d + 1) cs[j].target lam = true →
        A.clean = some a → j + 1 < cs.length := by
    intro d A cs j hD hcs hj hed hLj hcl
    by_contra hn
    have hjl : j + 1 = cs.length := by omega
    have hAt : InTree (colCtx M R root i x) (official t.row) (d + 2) A := ⟨F, hF, hD⟩
    obtain ⟨ax, hax⟩ : ∃ ax, topIn (colCtx M R root i x).source (colCtx M R root i x).x
        (d + 2) A.source = some ax := by
      cases h : topIn (colCtx M R root i x).source (colCtx M R root i x).x (d + 2) A.source with
      | none =>
        have := childItems_none hcs h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    have hbA := asc_true_of_kind hcs hax (Or.inl (by rw [hcl]; simp))
    cases hρ : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
        A.source with
    | none => rw [hρ] at hbA; cases hbA
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hbA
      obtain ⟨xr, xc, g, hxn, hxg, _, _, _⟩ := kids4 hcs hcl hblk hax hρ hbA
      have hxr : xr.column = x := by
        obtain ⟨hm, _⟩ := RowLaw.nodeAt_spec hxn
        exact (realNodes_column hm).1
      have hg1 : 1 ≤ g := by
        have := gen_pos hxg (by rw [hxr]; exact hCS.xgt)
        omega
      have hMH : A.cutBottom = false →
          heightOf (d + 2) (topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn
            (d + 2) A.source) ≤ heightOf (d + 2) (topIn (colCtx M R root i x).result
              (colCtx M R root i x).boundary (d + 2) A.target) + g :=
        fun hcb => hFMHX d A a (reach_of_inTree hAt) hcl hcb xr xc g hxn hxg
      have hcT : InTree (colCtx M R root i x) (official t.row) (d + 1) cs[j] :=
        LowerLeftProof.inTree_snoc hAt hcs (List.getElem_mem hj)
      obtain ⟨_, _, LB, hLB, _, hback⟩ := inTree_facts rX hvs hcT
      have hlen := top_single hblk hVR (colCtx_bnd hP.nc) hg1 hxn hxg hAt hcl hcs hax hMH hjl hLB
      have h1 := hback _ hLmem (by rw [hlam]; exact hLj)
      have h2 := hback _ hθmem (by rw [hθ]; exact hθreg (d + 1) _ hed hLj)
      match LB, hlen, h1, h2 with
      | [z], _, h1, h2 =>
        simp only [List.mem_singleton] at h1 h2
        exact hne (h1.trans h2.symm)
      | [], _, h1, _ => simp at h1
  -- the item `J` is not a first item when it copies a root row
  have hJnotF : J.clean ≠ none → e + 1 < F.1 := by
    intro hJc
    have hlev := desc_level_le hDJ
    rcases Nat.eq_or_lt_of_le hlev with heq | h
    · exfalso
      obtain ⟨F1, F2⟩ := F
      simp only at heq hDJ
      subst heq
      have := desc_eq hDJ
      subst this
      exact hJc (Inner.lowerItems_clean _ _ hF)
    · exact h
  -- a row of `l` that agrees with `a` above `e` and lies in the source region of `J`
  have hwit : ∃ wq ∈ realNodes M l, (∀ q, e < q → (official wq.2.row).coeff q = a.coeff q) ∧
      inRegion (e + 1) J.source (official wq.2.row) = true := by
    rcases hcls with hJC | hadj
    · have hlt' := hJnotF (by rw [hJC]; simp)
      obtain ⟨P, csP, hDP, hcsP, hJm⟩ := desc_parent hDJ hlt'
      have hDP' : Desc (colCtx M R root i x) F.1 F.2 (e + 2) P := hDP
      have hcsP' : childItems (colCtx M R root i x) (e + 2) P = .ok csP := hcsP
      obtain ⟨jJ, hjJ, rfl⟩ := List.getElem_of_mem hJm
      obtain ⟨ax, hax⟩ : ∃ ax, topIn M x (e + 2) P.source = some ax := by
        cases h : topIn M x (e + 2) P.source with
        | none =>
          have := childItems_none hcsP' h
          rw [this] at hjJ; simp at hjJ
        | some ax => exact ⟨ax, rfl⟩
      have hct := LowerLeftProof.inTree_cleanTop (⟨F, hF, hDP'⟩ :
        InTree (colCtx M R root i x) (official t.row) (e + 2) P)
      obtain ⟨r, cl, hρ, hrow, hasc⟩ := clean_child_root hblk hcsP' hax hct hjJ hJC
      have hascY := H.le e P.source r cl hρ (by rw [hrow]) hasc
      obtain ⟨ρ', hρ', q, hq, hqrow⟩ := node_of_ascends rY hascY
      obtain rfl := Option.some.inj hρ'
      refine ⟨q, hq, fun q' _ => by rw [hqrow, hrow], ?_⟩
      have hctJ := LowerLeftProof.inTree_cleanTop (⟨F, hF, hDJ⟩ :
        InTree (colCtx M R root i x) (official t.row) (e + 1) csP[jJ])
      obtain ⟨ρ1, hρ1, hρ1r⟩ := hctJ a hJC
      rw [hqrow, hrow, ← hρ1r]
      exact topIn_inRegion hρ1
    · obtain ⟨p, hpm, hpJ, hpag, _, _⟩ := adj_M hb hcθm hleg hadj haτ
      obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hpm
      exact ⟨q, hq, fun q' hq' => by rw [hqr]; exact hpag q' hq', by rw [hqr]; exact hpJ⟩
  obtain ⟨wq, hwq, hwa, hwJ⟩ := hwit
  -- `J` is in the tree of `Y`
  have hJY : InTree (colCtx M R root i l) (official t.row) (e + 1) J := by
    have hlev := desc_level_le hDJ
    rcases Nat.eq_or_lt_of_le hlev with heq | hltF
    · obtain ⟨F1, F2⟩ := F
      simp only at heq hDJ
      subst heq
      have := desc_eq hDJ
      subst this
      exact ⟨_, hF, .refl _ _⟩
    · obtain ⟨P, csP, hDP, hcsP, hJm⟩ := desc_parent hDJ hltF
      have hDP' : Desc (colCtx M R root i x) F.1 F.2 (e + 2) P := hDP
      have hcsP' : childItems (colCtx M R root i x) (e + 2) P = .ok csP := hcsP
      obtain ⟨jJ, hjJ, rfl⟩ := List.getElem_of_mem hJm
      have hPt : InTree (colCtx M R root i x) (official t.row) (e + 2) P := ⟨F, hF, hDP'⟩
      obtain ⟨_, hPOK⟩ := LowerLeftProof.inTree_itemOK rX hPt
      have hLP0 := region_sub_of_child rX hPOK hcsP' hjJ hP.region
      obtain ⟨BP, hDBP, hsimP⟩ := sim_chain pr rX hF hb H hcθ rfl hEOK hY hwq hwa hnt hMDX hMDY
        hMHY (F.1 - (e + 2)) (e + 2) P (by omega) hDP' le_rfl hLP0
      obtain ⟨csY, hcsY⟩ := hY e BP hDBP
      obtain ⟨ax, hax⟩ : ∃ ax, topIn M x (e + 2) P.source = some ax := by
        cases h : topIn M x (e + 2) P.source with
        | none =>
          have := childItems_none hcsP' h
          rw [this] at hjJ; simp at hjJ
        | some ax => exact ⟨ax, rfl⟩
      -- the child of `θ`
      obtain ⟨_, _, LP, hLP, _, hbackP⟩ := inTree_facts rX hvs hPt
      have hθP := hbackP _ hθmem (by rw [hθ]; exact hθreg (e + 2) _ le_rfl hLP0)
      have hθc := run_coeff_lt rX hPOK hLP hcsP' _ hθP
      obtain ⟨_, hJtg⟩ := child_itemOK rX hPOK hcsP' jJ hjJ
      have hLc : lam.coeff e = jJ := by
        have := hP.region
        rw [hJtg] at this
        exact coeff_of_slot this
      have hθce : θ.coeff e = jJ + 1 := by rw [hP.bump, bump_coeff_e, hLc]
      rw [hθ, hθce] at hθc
      have hθt : inRegion (e + 1) csP[jJ + 1].target θ = true := by
        obtain ⟨_, htg⟩ := child_itemOK rX hPOK hcsP' (jJ + 1) hθc
        rw [htg]
        exact inRegion_slot_iff.mpr ⟨hθreg (e + 2) _ le_rfl hLP0, hθce⟩
      have hEc := eok_of_tree rX houts hθp (LowerLeftProof.inTree_snoc hPt hcsP'
        (List.getElem_mem hθc)) (by rw [hθrow]; exact hθt)
      have hEA := hEOK (e + 2) P hDP' le_rfl hLP0
      have hBs := hsimP.source
      obtain ⟨hjY, _, heq⟩ := step pr hb H hcθ rfl hsimP hcsP' hcsY hax (Nat.le_succ jJ) le_rfl
        hθc hEA hEc hwq hwJ (fun _ _ _ => hθc) (hMDX e P · · hDP') (fun r cl hρ hasc => by
          have := hMDY e BP r cl hDBP (by rw [hBs]; exact hρ) hasc
          rw [hBs] at this; exact this) (hMHY e BP hDBP)
      rw [heq (Nat.lt_succ_self _)]
      exact ⟨F, hF, LowerLeftProof.desc_snoc hDBP hcsY (List.getElem_mem hjY)⟩
  have hHas : Has (colCtx M R root i l) (e + 1) J.source := ⟨wq, hwq, hwJ⟩
  -- `J` has fewer children in `Y`
  have hfew : ∀ d, e = d + 1 → ∀ cs cs', childItems (colCtx M R root i x) (d + 2) J = .ok cs →
      childItems (colCtx M R root i l) (d + 2) J = .ok cs' → cs'.length < cs.length := by
    intro d hd cs cs' hcs hcs'
    subst hd
    have hlh := lam_height hP hcs
    obtain ⟨tx, htx⟩ : ∃ tx, topIn M x (d + 2) J.source = some tx := by
      cases h : topIn M x (d + 2) J.source with
      | none =>
        have := childItems_none hcs h
        rw [this] at hlh; simp at hlh
      | some tx => exact ⟨tx, rfl⟩
    obtain ⟨ty, hty, _⟩ := topY hb hwq hwJ
    have htyY : topIn (colCtx M R root i l).source (colCtx M R root i l).x (d + 2) J.source =
        some ty := hty
    rcases hcls with hJC | hadj
    · -- `J` copies `a`: one generation less
      have hbX := asc_true_of_kind hcs htx (Or.inl (by rw [hJC]; simp))
      have hbY := asc_true_of_kind hcs' htyY (Or.inl (by rw [hJC]; simp))
      cases hρ : topIn M root.column (d + 2) J.source with
      | none =>
        have : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
          J.source = none := hρ
        rw [this] at hbX; cases hbX
      | some ρ =>
        obtain ⟨r, cl⟩ := ρ
        have hρX : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
          J.source = some (r, cl) := hρ
        have hρY : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
          J.source = some (r, cl) := hρ
        rw [hρX] at hbX
        rw [hρY] at hbY
        have hblkY : (colCtx M R root i l).block ≠ 0 := hblk
        obtain ⟨xr, xc, gx, hxn, hxg, _, hlX, _⟩ := kids4 hcs hJC hblk htx hρX hbX
        obtain ⟨yr, yc, gy, hyn, hyg, _, hlY, _⟩ := kids4 hcs' hJC hblkY htyY hρY hbY
        have hg := H.gen xr xc gx yr yc gy hxn hxg hyn hyg
        rw [pr.bnd] at hlY
        omega
    · -- adjacent: the top of `l` in the region of `J` is below that of `x`
      obtain ⟨p, hpm, hpJ, _, hpmax, aL, haLm, haLJ, haLmax, hJlt, hlte, _⟩ :=
        adj_M hb hcθm hleg hadj haτ
      obtain ⟨_, _, _, _, _, hJcl, _, _⟩ := hadj
      have hJn := hJcl (by omega)
      have htxr : official tx.2.row = aL := by
        obtain ⟨htxm, htxin, _⟩ := RowLaw.topIn_spec htx
        apply le_antisymm
        · exact haLmax _ (List.mem_map.mpr ⟨tx, htxm, rfl⟩) htxin
        · obtain ⟨qL, hqL, hqLr⟩ := List.mem_map.mp haLm
          rw [← hqLr]
          exact topIn_row_max hb htx hqL (by rw [hqLr]; exact haLJ)
      have htyr : official ty.2.row = p := by
        obtain ⟨htym, htyin, _⟩ := RowLaw.topIn_spec hty
        apply le_antisymm
        · exact hpmax _ (List.mem_map.mpr ⟨ty, htym, rfl⟩) (hJlt _ htyin)
        · obtain ⟨qp, hqp, hqpr⟩ := List.mem_map.mp hpm
          rw [← hqpr]
          exact topIn_row_max hb hty hqp (by rw [hqpr]; exact hpJ)
      have hheights : height (d + 2) (official ty.2.row) < height (d + 2) (official tx.2.row) := by
        show (official ty.2.row).coeff d < (official tx.2.row).coeff d
        rw [htxr, htyr]; exact hlte d rfl
      obtain ⟨bX, hbX⟩ := childItems_asc hcs htx
      obtain ⟨bY, hbY⟩ := childItems_asc hcs' htyY
      have hasc_eq : bX = bY := by
        cases hρ : topIn M root.column (d + 2) J.source with
        | none =>
          have h1 : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
            J.source = none := hρ
          have h2 : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
            J.source = none := hρ
          rw [h1] at hbX; rw [h2] at hbY
          rw [ascends_none'] at hbX hbY
          rw [← Except.ok.inj hbX, ← Except.ok.inj hbY]
        | some ρ =>
          obtain ⟨r, cl⟩ := ρ
          have h1 : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
            J.source = some (r, cl) := hρ
          have h2 : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
            J.source = some (r, cl) := hρ
          rw [h1] at hbX; rw [h2] at hbY
          have hlt' := hJlt _ (topIn_inRegion hρ)
          have hiff := H.eq d J.source r cl h1 hlt'
          rw [hbX, hbY] at hiff
          cases bX <;> cases bY <;> simp_all
      subst hasc_eq
      cases bX with
      | false =>
        obtain ⟨_, _, hlX, _⟩ := kids1 hcs htx hbX
        obtain ⟨_, _, hlY, _⟩ := kids1 hcs' htyY hbY
        rw [hlX, hlY]; omega
      | true =>
        cases hρ : topIn M root.column (d + 2) J.source with
        | none =>
          have h1 : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
            J.source = none := hρ
          rw [h1] at hbX; cases hbX
        | some ρ =>
          obtain ⟨r, cl⟩ := ρ
          have hρX : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2)
            J.source = some (r, cl) := hρ
          have hρY : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
            J.source = some (r, cl) := hρ
          rw [hρX] at hbX
          rw [hρY] at hbY
          cases hcb : J.cutBottom with
          | false =>
            obtain ⟨hlX, _⟩ := kids2 hcs hJn hcb htx hρX hbX
            obtain ⟨hlY, _⟩ := kids2 hcs' hJn hcb htyY hρY hbY
            have hl' : cs.length ≥ 1 := by omega
            rw [hlX] at hl' ⊢
            rw [hlY]
            have e1 : (colCtx M R root i l).block = (colCtx M R root i x).block := rfl
            have e2 : topIn (colCtx M R root i l).source (colCtx M R root i l).lastColumn (d + 2)
              J.source = topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
                (d + 2) J.source := rfl
            rw [e1, e2]
            omega
          | true =>
            have hblkY : (colCtx M R root i l).block ≠ 0 := hblk
            obtain ⟨hlX, _⟩ := kids3 hcs hJn hcb hblk htx hρX hbX
            obtain ⟨hlY, _⟩ := kids3 hcs' hJn hcb hblkY htyY hρY hbY
            rw [pr.bnd] at hlY
            have hl' : cs.length ≥ 1 := by omega
            rw [hlX] at hl' ⊢
            rw [hlY]
            omega
  exact rows_of_item hP hNCy hJY rfl hHas hfew vsY hvsY

end OmegaY.Official.Recon.LRC

#print axioms OmegaY.Official.Recon.LRC.lowerRowsCopy_holds
