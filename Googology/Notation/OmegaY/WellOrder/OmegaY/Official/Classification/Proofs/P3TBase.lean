/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/P3TBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Main
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCJump

set_option backward.do.legacy false

/-!
# Package 3, the two row facts: the setting and the tools (`P3T`)

Tools for `CutRunTop` (`P3TRunTop.lean`) and `CutJumpRootRow` (`P3TRootRow.lean`), the two
open statements of package 3 (`Pkg3Jump.lean`, `Pkg3Run.lean`).

* `site_nc`: a `Site` of `KeyLeRest` is a new column (`Recon.JumpLawLower.NewColumn`) of the
  lower row laws, whose copy context `colCtx` is the context of the site.
* `cb_emit`: in the tree of a copied column `l` of a block `i ≥ 1`, an item copying the root row
  `a` with a cut bottom, or a plain item with a cut bottom whose root top has the row `a`, emits a
  gap copy of the node `(l, a)` (the first child is again such an item; offsets stay at most the
  number of generations, `ItemOK.offset`).
* `no_clean_above`: on the path of a gap copy `p` of origin row `a`, no ancestor of a plain item
  copies `a` (a plain child of an item copying `a` lies in a slot below the root top `a`).
* `sim_down`: the path of the tree of `x` down to a plain item holding `p` is simulated in the
  tree of the leg column `l` (the argument of `Recon.LRC.sim_chain`, with `Recon.LRC.step`;
  the non-top condition of the step holds by `no_clean_above`).

The proofs use the proved lower row laws (`Recon/LRC*.lean`: `LRC.step`, `LRC.qb_tree`,
`LRC.bnd_lift`, `LRC.anch_of`).
-/

namespace OmegaY.Official.Classification.Proofs.P3T

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CutParts

theorem left_of_root {M : Mountain} {D : Nat} {ρ : Root} {col : Column} {t : Cell}
    (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t) (h : root? M D = some ρ) :
    ∃ r, t.left = some r ∧ ρ.cr = r.column := by
  unfold root? at h
  rw [hcol] at h
  simp only at h
  split at h
  · cases h
  · have hb : col[col.size - 1]? = some t := by
      rw [← ht]; simp [Array.back?]
    rw [hb] at h
    simp only at h
    cases hl : t.left with
    | none => rw [hl] at h; cases h
    | some r =>
      rw [hl] at h
      simp only at h
      split at h
      · cases h
      · split at h
        · obtain rfl := Option.some.inj h
          exact ⟨r, rfl, rfl⟩
        · cases h


open Recon Recon.JumpLaw Recon.JumpLawLower in
/-- **The setting of the lower row laws from a site.** -/
theorem site_nc {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) :
    ∃ root : Ref, Recon.Top s M t root ∧ ρ.cr = root.column ∧ ρ.x0 = M.size - 1 ∧
      NewColumn s n R M t root i x ∧ X = x + (M.size - 1 - root.column) * i ∧
      colCtx M R root i x = ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X := by
  obtain ⟨col, t', hcol, ht', hx0, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col2, hcol2, ht2⟩ := hS.last
    have : col = col2 := Option.some.inj (hcol.symm.trans hcol2)
    subst this
    exact Option.some.inj (ht'.symm.trans ht2)
  subst htt
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  obtain ⟨root, hleft, hcr⟩ := left_of_root hcol ht' hS.splice.root
  have hreal : official t'.row ≠ 0 := by
    intro h0
    have := root?_none_of_official_zero hV D hcol ht' h0
    rw [hS.splice.root] at this
    cases this
  have hTop : Recon.Top s M t' root :=
    ⟨hb, by rw [hcol]; exact ht', hreal, hleft, by omega⟩
  have hXeq : X = x + (M.size - 1 - root.column) * i := by
    rw [hS.Xeq, hx0, hcr]
  have hctx : colCtx M R root i x = ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X := by
    simp only [colCtx, hx0, hcr, hXeq]
  refine ⟨root, hTop, hcr, hx0, ?_, hXeq, hctx⟩
  obtain ⟨c, hc, hcopy⟩ := hS.copy
  refine ⟨hS.run, hTop, hS.splice.copies, ?_, hS.iLt, ?_, ?_, ?_⟩
  · rw [hx0, hcr] at hinv; exact hinv
  · have := hS.xMem; rw [hx0, hcr] at this; exact this
  · rw [← hXeq]; exact hS.XR
  · refine ⟨c, by rw [← hXeq]; exact hc, ?_⟩
    rw [hctx]; exact hcopy


section CB
open Recon Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC

theorem nodeAt_pa {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {l : Nat}
    {pa : Ref × Cell} (hpa : pa ∈ realNodes M l) : nodeAt M l (official pa.2.row) = some pa := by
  obtain ⟨p', hp'⟩ := nodeAt_of_mem hpa
  rw [hp', nodeAt_eq_of_mem hb hpa hp']

/-- **A cut-bottom item of the copied root row emits a gap copy.** In the tree of the column
`l`, an item that copies the root row `a` with a cut bottom, or a plain item with a cut bottom
whose root top has the row `a`, emits a gap copy of the node `pa = (l, a)`. -/
theorem cb_emit {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i l : Nat}
    (hNC : NewColumn s n R M t root i l) (hblk : i ≠ 0)
    {a : Row} {pa : Ref × Cell} (hpa : pa ∈ realNodes M l) (hpaa : official pa.2.row = a)
    (hasc : ∀ D S r cl, topIn M root.column D S = some (r, cl) → official cl.row = a →
      ascends (colCtx M R root i l) (some (r, cl)) = .ok true) :
    ∀ d K, InTree (colCtx M R root i l) (official t.row) (d + 1) K →
      ∀ TK, runItemT (colCtx M R root i l) (d + 1) K = .ok TK →
      ((K.clean = some a ∧ K.cutBottom = true) ∨
        (K.clean = none ∧ K.cutBottom = true ∧ 1 ≤ d ∧ ∃ r cl,
          topIn M root.column (d + 1) K.source = some (r, cl) ∧ official cl.row = a)) →
      ∃ q ∈ TK, q.2 = .clean pa.1 true
  | 0, K, hK, TK, hTK, hkind => by
      have hb := hNC.top.build
      have hct := LowerLeftProof.inTree_cleanTop hK
      rcases hkind with ⟨hcl, hcb⟩ | ⟨_, _, h1, _⟩
      · obtain ⟨ρ, hρ, hρa⟩ := hct a hcl
        have hsrc : a = K.source := by
          have := Classification.topIn_inRegion hρ
          rw [hρa] at this
          exact Classification.inRegion_one this
        have hn := nodeAt_pa hb hpa
        rw [hpaa] at hn
        have hTK' : levelOneT (colCtx M R root i l) K = .ok TK := by simpa [runItemT] using hTK
        unfold levelOneT at hTK'
        have hn1 : nodeAt (colCtx M R root i l).source (colCtx M R root i l).x K.source =
            some pa := by rw [← hsrc]; exact hn
        have hn2 : nodeAt (colCtx M R root i l).source (colCtx M R root i l).x a = some pa := hn
        rw [hn1, hcl] at hTK'
        simp only [hn2, hcb, bind, Except.bind, pure, Except.pure] at hTK'
        split at hTK'
        · cases hTK'
        · cases hTK'
          exact ⟨_, List.mem_singleton_self _, rfl⟩
      · omega
  | d + 1, K, hK, TK, hTK, hkind => by
      have hb := hNC.top.build
      have rY := hNC.runCtx
      have hct := LowerLeftProof.inTree_cleanTop hK
      obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTK
      obtain ⟨hlenF, hgetF⟩ := forall₂_getElem hF
      -- the root top of the region, at the row `a`
      obtain ⟨r, cl, hρ, hρa⟩ : ∃ r cl, topIn M root.column (d + 2) K.source = some (r, cl) ∧
          official cl.row = a := by
        rcases hkind with ⟨hcl, _⟩ | ⟨_, _, _, r, cl, hρ, hρa⟩
        · obtain ⟨ρ, hρ, hρa⟩ := hct a hcl
          exact ⟨ρ.1, ρ.2, hρ, hρa⟩
        · exact ⟨r, cl, hρ, hρa⟩
      have hreg : inRegion (d + 2) K.source (official pa.2.row) = true := by
        rw [hpaa, ← hρa]; exact Classification.topIn_inRegion hρ
      obtain ⟨ay, hay, hayh⟩ := topY hb hpa hreg
      have hayY : topIn (colCtx M R root i l).source (colCtx M R root i l).x (d + 2) K.source =
          some ay := hay
      have hρY : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
          K.source = some (r, cl) := hρ
      have hascY := hasc _ _ r cl hρ hρa
      have hblkY : (colCtx M R root i l).block ≠ 0 := hblk
      -- the first child emits a gap copy
      have hfirst : ∀ (h0 : 0 < cs.length), ((cs[0].clean = some a ∧ cs[0].cutBottom = true) ∨
          (cs[0].clean = none ∧ cs[0].cutBottom = true ∧ 1 ≤ d ∧ ∃ r cl,
            topIn M root.column (d + 1) cs[0].source = some (r, cl) ∧ official cl.row = a)) →
          ∃ q ∈ outs.flatten, q.2 = .clean pa.1 true := by
        intro h0 hk0
        have hc0 : InTree (colCtx M R root i l) (official t.row) (d + 1) cs[0] :=
          LowerLeftProof.inTree_snoc hK hcs (List.getElem_mem h0)
        obtain ⟨q, hq, hq2⟩ := cb_emit hNC hblk hpa hpaa hasc d cs[0] hc0 outs[0]
          (hgetF 0 h0 (by omega)) hk0
        exact ⟨q, List.mem_flatten.mpr ⟨outs[0], List.getElem_mem (by omega), hq⟩, hq2⟩
      rcases hkind with ⟨hcl, hcb⟩ | ⟨hcl, hcb, _, _⟩
      · obtain ⟨csRef, csc, g, hn, hg, _, hlen, hget⟩ := kids4 hcs hcl hblkY hayY hρY hascY
        have hoff := (LowerLeftProof.inTree_itemOK rY hK).2.offset a hcl hblkY csRef csc g hn hg
        have h0 : 0 < cs.length := by rw [hlen]; omega
        apply hfirst h0
        left
        rw [hget 0 h0, hcb]
        exact ⟨rfl, rfl⟩
      · obtain ⟨hlen, hget⟩ := kids3 hcs hcl hcb hblkY hayY hρY hascY
        have hle : height (d + 2) (official cl.row) ≤ height (d + 2) (official ay.2.row) := by
          show (official cl.row).coeff d ≤ (official ay.2.row).coeff d
          rw [hρa, ← hpaa]; exact hayh
        have h0 : 0 < cs.length := by rw [hlen]; omega
        apply hfirst h0
        rw [hget 0 h0]
        rcases c3_cases (d := d + 2) (S := K.source) (T := K.target)
          (hR := height (d + 2) (official cl.row))
          (hB := heightOf (d + 2) (topIn (colCtx M R root i l).result
            (colCtx M R root i l).boundary (d + 2) K.target))
          (C := official cl.row) (0 + height (d + 2) (official cl.row)) with ⟨_, h2⟩ | ⟨h1, h2⟩
        · rw [h2, hρa]; left; exact ⟨rfl, rfl⟩
        · rw [h2]
          have hd1 : 1 ≤ d := by
            by_contra hd
            have : d = 0 := by omega
            subst this
            simp at h1
            omega
          have hB0 : heightOf (d + 2) (topIn (colCtx M R root i l).result
              (colCtx M R root i l).boundary (d + 2) K.target) = 0 := by
            have : d + 2 ≠ 2 := by omega
            simp only [this, if_false] at h1
            omega
          right
          refine ⟨rfl, by simp [hB0], hd1, r, cl, ?_, hρa⟩
          have := ChainCorr.Inner.topIn_slot hρ
          simp only [hB0, Nat.zero_add, Nat.sub_zero]
          exact this

end CB


section Path
open Recon Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC

/-- The target of a descendant lies in the target of an item of the tree. -/
theorem desc_region {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {K : Item} {d' : Nat} {A : Item}
    (hK : InTree ctx (official t.row) d K) (hD : Desc ctx d K d' A) {r : Row}
    (hr : inRegion d' A.target r = true) : inRegion d K.target r = true := by
  obtain ⟨hd1, hKOK⟩ := LowerLeftProof.inTree_itemOK hctx hK
  exact (desc_facts hctx hD hd1 hKOK).2.2.2.1 r hr

/-- A descendant of an item of the tree is in the tree. -/
theorem inTree_desc {ctx : Context} {τ : Row} {d : Nat} {K : Item} {d' : Nat} {A : Item}
    (hK : InTree ctx τ d K) (hD : Desc ctx d K d' A) : InTree ctx τ d' A := by
  induction hD with
  | refl => exact hK
  | step hcs hc _ ih => exact ih (LowerLeftProof.inTree_snoc hK hcs hc)

/-- **No copy of the root row `a` above a plain item on the path of a copy of `a`.** If `p`
(origin row `a`) lies in the target of a plain item `A`, no ancestor of `A` copies `a`: the
children of an item copying `a` that hold `p` copy `a` again (a plain child lies in a slot below
the root top, which has the row `a`). -/
theorem no_clean_above {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (hblk : ctx.block ≠ 0) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT)
    {p : Emit × Origin} (hp : p ∈ outsT.flatten) {cθ : Cell}
    (hcθ : cell? ctx.source p.2.src = some cθ) {a : Row} (hθa : official cθ.row = a) :
    ∀ {dK : Nat} {K : Item} {dA : Nat} {A : Item}, Desc ctx dK K dA A →
      InTree ctx (official t.row) dK K → inRegion dA A.target p.1.row = true →
      K.clean = some a → A.clean = none → False := by
  intro dK K dA A hD
  induction hD with
  | refl => intro _ _ h1 h2; rw [h1] at h2; cases h2
  | @step d K cs c d' A hcs hc hD ih =>
    intro hK hreg hcl hAcl
    have hcT : InTree ctx (official t.row) (d + 1) c := LowerLeftProof.inTree_snoc hK hcs hc
    apply ih hcT hreg _ hAcl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨ax, hax⟩ : ∃ ax, topIn ctx.source ctx.x (d + 2) K.source = some ax := by
      cases h : topIn ctx.source ctx.x (d + 2) K.source with
      | none =>
        have := childItems_none hcs h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    have hbK := asc_true_of_kind hcs hax (Or.inl (by rw [hcl]; simp))
    obtain ⟨ρ, hρ, hρa⟩ := LowerLeftProof.inTree_cleanTop hK a hcl
    obtain ⟨r, cl⟩ := ρ
    rw [hρ] at hbK
    obtain ⟨_, _, _, _, _, _, _, hget⟩ := kids4 hcs hcl hblk hax hρ hbK
    rw [hget j hj]
    unfold c4
    split
    · rfl
    · split
      · exfalso
        rename_i hlt
        -- the plain child holds `p`, whose origin row `a` is in its source slot `j`
        have hin := desc_region hctx hcT hD hreg
        have hE := eok_of_tree hctx houts hp hcT hin
        obtain ⟨hsrc, _⟩ := eok_parts hE hcθ
        rw [hget j hj] at hsrc
        unfold c4 at hsrc
        rw [if_neg (by assumption), if_pos hlt] at hsrc
        have hco := (inRegion_slot_iff.mp hsrc).2
        rw [hθa] at hco
        simp only at hρa
        have : height (d + 2) (official cl.row) = a.coeff d := by
          show (official cl.row).coeff (d + 2 - 2) = a.coeff d
          rw [hρa]; rfl
        omega
      · rfl


/-- **The simulation of the path down to a plain item `A` holding `p`.** Every ancestor `K` of
`A` in the tree of `X` has a similar item in the tree of `Y` (the argument of `LRC.sim_chain`;
the non-top condition of `LRC.step` holds since no ancestor copies `a`, `no_clean_above`). -/
theorem sim_down {cX cY : Context} (P : Pair cX cY) {s : List Nat} {t : Cell} {root : Ref}
    (hctx : RunCtx s cX t root) (hb : Canonical.build s = .ok cX.source) {a : Row}
    (H : Anch cX cY a) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT cX p.1 p.2) = .ok outsT)
    {p : Emit × Origin} (hp : p ∈ outsT.flatten) {cθ : Cell}
    (hcθ : cell? cX.source p.2.src = some cθ) (hθa : official cθ.row = a)
    {F : Nat × Item} (hF : F ∈ lowerItems (official t.row)) {dA : Nat} {A : Item}
    (hreg : inRegion dA A.target p.1.row = true) (hAcl : A.clean = none)
    (hY : ∀ d B, Desc cY F.1 F.2 (d + 2) B → ∃ csY, childItems cY (d + 2) B = .ok csY)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x) (hwa : official wq.2.row = a)
    (hMDX : ∀ d A r cl, Desc cX F.1 F.2 (d + 2) A →
      topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDY : ∀ d B r cl, Desc cY F.1 F.2 (d + 2) B →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) B.source))
    (hMHY : ∀ d B, Desc cY F.1 F.2 (d + 2) B → ∀ C r cl csRef csc g, B.clean = some C →
      B.cutBottom = false → topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∀ m d K, d + m = F.1 → Desc cX F.1 F.2 d K → Desc cX d K dA A →
      ∃ B, Desc cY F.1 F.2 d B ∧ Sim cX cY d K B := by
  intro m
  induction m with
  | zero =>
    intro d K hd hD _
    subst hd
    have := desc_eq hD
    subst this
    exact ⟨F.2, .refl _ _, Or.inl rfl⟩
  | succ m ih =>
    intro d K hd hD hKA
    obtain ⟨Kp, csK, hDKp, hcsK, hKm⟩ := desc_parent hD (by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hKm
    have hKT : InTree cX (official t.row) d csK[j] := ⟨F, hF, hD⟩
    have hd1 : 1 ≤ d := (LowerLeftProof.inTree_itemOK hctx hKT).1
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    have hDKp' : Desc cX F.1 F.2 (d'' + 2) Kp := hDKp
    have hcsK' : childItems cX (d'' + 2) Kp = .ok csK := hcsK
    have hKpT : InTree cX (official t.row) (d'' + 2) Kp := ⟨F, hF, hDKp'⟩
    have hKpA : Desc cX (d'' + 2) Kp dA A := .step hcsK' hKm hKA
    obtain ⟨BK, hDBK, hsimK⟩ := ih (d'' + 2) Kp (by omega) hDKp' hKpA
    obtain ⟨csY, hcsY⟩ := hY d'' BK hDBK
    obtain ⟨ax, hax⟩ : ∃ ax, topIn cX.source cX.x (d'' + 2) Kp.source = some ax := by
      cases h : topIn cX.source cX.x (d'' + 2) Kp.source with
      | none =>
        have := childItems_none hcsK' h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    have hinK := desc_region hctx hKT hKA hreg
    have hinKp := desc_region hctx hKpT hKpA hreg
    have hEA := eok_of_tree hctx houts hp hKpT hinKp
    have hEc := eok_of_tree hctx houts hp hKT hinK
    have hw : inRegion (d'' + 1) csK[j].source (official wq.2.row) = true := by
      obtain ⟨haReg, _⟩ := eok_parts hEc hcθ
      rw [hwa, ← hθa]; exact haReg
    have hnt : ∀ C, Kp.clean = some C → C = a → j + 1 < csK.length := by
      intro C hC hCa
      rw [hCa] at hC
      exact absurd (no_clean_above hctx P.blk houts hp hcθ hθa hKpA hKpT hreg hC hAcl) id
    have hBs := hsimK.source
    obtain ⟨hjY, hsim, _⟩ := step P hb H hcθ hθa hsimK hcsK' hcsY hax le_rfl (by omega) hj
      hEA hEc hwq hw hnt (hMDX d'' Kp · · hDKp') (fun r cl hρ hasc => by
        have := hMDY d'' BK r cl hDBK (by rw [hBs]; exact hρ) hasc
        rw [hBs] at this; exact this) (hMHY d'' BK hDBK)
    exact ⟨csY[j], LowerLeftProof.desc_snoc hDBK hcsY (List.getElem_mem hjY), hsim⟩

end Path

end OmegaY.Official.Classification.Proofs.P3T
