/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchBoundary.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchLower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchTop
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# `BoundaryRootRows`: the boundary columns keep the rows of the root column

The copy of the last column `x₀` made by block `i'` (the boundary column `cr + w·(i' + 1)`)
emits every official row `σ < τ` of the root column `c_r`. With
`legRowMatchRootLower_of_boundary` this proves `LegRowMatchRootLower`.

The row `σ` lies in a first item (`lowerItems_cover`); from there the item recursion is
followed to the slot of `σ`, always through an aligned item without cut bottom (source region
= target region):

* `j_σ ≤ h_ρ` (the top `ρ` of `c_r` in the region is at least as high as `σ`), and
  `h_ρ < h_κ` (`TopRoot.topAboveRoot`; `κ` is the top of `x₀`, which is here the source column
  `x`), so the slot `j_σ` is among the children in cases 1 and 2, and the lift of case 2 is
  positive in blocks `i' ≥ 1`: the root slot `h_ρ` gets a copied root row without cut bottom
  (in block `0` the lift is `0` and the root slot is plain without cut bottom);
* in case 4 the children go up to `h_B + g ≥ h_B`, and `h_B ≥ j_σ` because the previous
  boundary column (block `i' - 1`) has a node at `σ` (induction over the blocks); in block `0`
  they go up to `h_κ`;
* at level `1` the aligned item emits its target row `σ` (the node `(x₀, σ)` exists, `root_rows`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

open Canonical Reserve Official Descent Classification Proofs

namespace BoundaryRows

/-- The data of the copy of the last column used by the forward induction. -/
structure FwdCtx (s : List Nat) (ctx : Context) (t : Cell) (root : Ref) : Prop where
  top : Recon.Top s ctx.source t root
  last : ctx.lastColumn = ctx.source.size - 1
  rootc : ctx.rootColumn = root.column
  xlast : ctx.x = ctx.lastColumn
  bnd : ctx.block ≠ 0 → ∀ σ, RowFix.CrRow ctx σ → σ < official t.row →
    ∀ d T, inRegion (d + 2) T σ = true →
      σ.coeff d ≤ heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) T)

/-- The last column has a node at every row of the root column below `τ`. -/
theorem node_x_of_crRow {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hc : FwdCtx s ctx t root) {σ : Row} (hσ : RowFix.CrRow ctx σ) (hlt : σ < official t.row) :
    ∃ p, nodeAt ctx.source ctx.x σ = some p := by
  obtain ⟨q, hq, hqrow⟩ := hσ
  rw [hc.rootc] at hq
  have hqlt : q.2.row < t.row := Recon.row_lt_of_official hc.top.row_one_le (by rw [hqrow]; exact hlt)
  obtain ⟨v, hv, hvrow⟩ := hc.top.root_rows hq hqlt
  obtain ⟨p, hp⟩ := Recon.RowLaw.nodeAt_of_mem hv
  rw [hvrow, hqrow, ← hc.last, ← hc.xlast] at hp
  exact ⟨p, hp⟩

/-- **Level one.** -/
theorem levelOneT_emits {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hc : FwdCtx s ctx t root) {it : Item} (hst : it.source = it.target) {σ : Row}
    (hσ : RowFix.CrRow ctx σ) (hlt : σ < official t.row) (hin : inRegion 1 it.source σ = true)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) : ∃ p ∈ ps, p.1.row = σ := by
  have hσs : σ = it.source := RowFix.eq_of_inRegion_one hin
  obtain ⟨q, hq⟩ := node_x_of_crRow hc hσ hlt
  rw [hσs] at hq
  unfold levelOneT at h
  rw [hq] at h
  obtain ⟨srcRef, src⟩ := q
  simp only at h
  cases hC : it.clean with
  | some C =>
      simp only [hC] at h
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
      | some q' =>
          obtain ⟨csRef, cs⟩ := q'
          simp only [hcs, bind, Except.bind, pure, Except.pure] at h
          split at h
          · cases h
          · cases h
            exact ⟨_, List.mem_singleton_self _, by rw [hσs, hst]⟩
  | none =>
      simp only [hC] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨_, List.mem_singleton_self _, by rw [hσs, hst]⟩
      · simp only [bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · cases h
          exact ⟨_, List.mem_singleton_self _, by rw [hσs, hst]⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 800000 in
/-- **The aligned child at the slot of `σ`.** -/
theorem childItems_emit_child {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hc : FwdCtx s ctx t root) {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hbel : Below (official t.row) (d + 2) it)
    (hcb : it.cutBottom = false) (hst : it.source = it.target)
    {σ : Row} (hσ : RowFix.CrRow ctx σ) (hin : inRegion (d + 2) it.source σ = true) :
    ∃ c ∈ cs, c.cutBottom = false ∧ c.source = c.target ∧ inRegion (d + 1) c.source σ = true := by
  have hlt := hbel σ hin
  have hb := hc.top.build
  obtain ⟨q, hqmem, hqrow⟩ := hσ
  -- the top `ρ` of the root column in the region
  obtain ⟨ρ, hρ⟩ : ∃ ρ, topIn ctx.source ctx.rootColumn (d + 2) it.source = some ρ := by
    cases hr : topIn ctx.source ctx.rootColumn (d + 2) it.source with
    | none =>
        exfalso
        have := Recon.RowLaw.topIn_none hr q hqmem
        rw [hqrow, hin] at this
        cases this
    | some ρ => exact ⟨ρ, rfl⟩
  have hρ' : topIn ctx.source root.column (d + 2) it.source = some ρ := by rw [← hc.rootc]; exact hρ
  obtain ⟨κ, hκ, hκρ⟩ := TopRoot.topAboveRoot hc.top hbel hρ'
  have hxκ : topIn ctx.source ctx.x (d + 2) it.source = some κ := by
    rw [hc.xlast, hc.last]; exact hκ
  have hLκ : topIn ctx.source ctx.lastColumn (d + 2) it.source = some κ := by
    rw [hc.last]; exact hκ
  -- the slot of `σ` is at most the height of `ρ`
  have hjR : σ.coeff d ≤ (official ρ.2.row).coeff d := by
    have hle := Recon.RowLaw.topIn_row_max hb hρ hqmem (by rw [hqrow]; exact hin)
    rw [hqrow] at hle
    exact Recon.RowLaw.coeff_le_of_inRegion hin (Recon.RowLaw.topIn_spec hρ).2.1 hle
  have hinT : inRegion (d + 2) it.target σ = true := by rw [← hst]; exact hin
  have hjB : ctx.block ≠ 0 →
      σ.coeff d ≤ heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) :=
    fun hb0 => hc.bnd hb0 σ ⟨q, hqmem, hqrow⟩ hlt d it.target hinT
  have hslot : ∀ j, j = σ.coeff d → inRegion (d + 1) (slot (d + 2) it.source j) σ = true := by
    intro j hj
    exact Recon.RowLaw.inRegion_slot_iff.mpr ⟨hin, hj.symm⟩
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  rw [hxκ, hρ, hLκ] at h
  generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h hjB
  simp only [heightOf, Recon.RowLaw.height_eq] at h
  generalize (official ρ.2.row).coeff d = hR at h hjR hκρ
  generalize (official κ.2.row).coeff d = hT at h hκρ
  generalize hj : σ.coeff d = j at hjR hjB hslot
  split at h
  · cases h
  · rename_i asc hasc
    split at h
    · -- case 1
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain rfl := Except.ok.inj h
        refine ⟨⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0, false⟩,
          List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, rfl, by simp [hst],
          hslot j rfl⟩
    · split at h
      · split at h
        · -- case 2
          obtain rfl := Except.ok.inj h
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          have he : 0 ≤ e := by rw [← hedef]; split <;> omega
          have hlift : (0 : Int) ≤ ((hT : Int) - hR) * ctx.block :=
            Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
          refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
          by_cases h1 : j < hR
          · simp only [h1, if_true]
            exact ⟨by simp, by simp [hst], hslot j rfl⟩
          · have hjR' : j = hR := by omega
            subst hjR'
            simp only [h1, if_false]
            by_cases h2 : (j : Int) < j + ((hT : Int) - j) * ctx.block + e
            · simp only [h2, if_true]
              exact ⟨by simp, by simp [hst], hslot j rfl⟩
            · simp only [h2, if_false]
              have hl0 : ((hT : Int) - j) * ctx.block = 0 := by omega
              have hb0 : ctx.block = 0 := by
                rcases Int.mul_eq_zero.mp hl0 with h' | h'
                · omega
                · exact_mod_cast h'
              refine ⟨by simp [hb0], by simp [hl0, hst], ?_⟩
              simp only [hl0, sub_zero, Int.toNat_natCast]
              exact hslot j rfl
        · -- case 3: impossible
          rename_i hcut
          simp [hcb] at hcut
      · -- case 4
        rename_i C hC
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · cases h
          · rename_i g hg
            split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · rename_i hflag
              obtain rfl := Except.ok.inj h
              have hoff : it.offset = 0 := by
                by_contra hne
                exact hflag ⟨by simp [hcb], Or.inr hne⟩
              have hjt : j < ((if ctx.block = 0 then (hT : Int) else (hB : Int) + g - it.offset)
                  + 1).toNat := by
                split
                · omega
                · rename_i hb0
                  have := hjB hb0
                  omega
              refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hjt, rfl⟩, ?_⟩
              simp only [hcb, Bool.false_eq_true, if_false]
              by_cases h1 : j < hR
              · simp only [h1, if_true]
                exact ⟨by simp, by simp [hst], hslot j rfl⟩
              · have hjR' : j = hR := by omega
                subst hjR'
                simp only [h1, if_false]
                exact ⟨by simp, by simp [hst], hslot j rfl⟩

/-- **The aligned items emit the rows of the root column.** -/
theorem runItemT_emits {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hc : FwdCtx s ctx t root) :
    ∀ (d : Nat) (it : Item), 1 ≤ d → Below (official t.row) d it → it.cutBottom = false →
      it.source = it.target → CleanTop ctx d it → ∀ σ, RowFix.CrRow ctx σ →
      inRegion d it.source σ = true → ∀ ps, runItemT ctx d it = .ok ps → ∃ p ∈ ps, p.1.row = σ
  | 0, _, h0, _, _, _, _, _, _, _, _, _ => absurd h0 (by omega)
  | 1, _, _, hbel, _, hst, _, σ, hσ, hin, ps, h =>
      levelOneT_emits hc hst hσ (hbel σ hin) hin (by simpa [runItemT] using h)
  | d + 2, it, _, hbel, hcb, hst, hct, σ, hσ, hin, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨c, hcmem, hccb, hcst, hcin⟩ :=
            childItems_emit_child hc hch hbel hcb hst hσ hin
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcmem
          have hrun := hall k hk (by omega)
          have hcbel : Below (official t.row) (d + 1) children[k] := by
            obtain ⟨j, hj⟩ := childItems_source hch _ hcmem
            intro r hr
            rw [hj] at hr
            exact hbel r (Recon.RowLaw.inRegion_of_slot hr)
          obtain ⟨p, hp, hprow⟩ := runItemT_emits hc (d + 1) children[k] (by omega) hcbel hccb
            hcst (childItems_cleanTop hch hct _ hcmem) σ hσ hcin _ hrun
          exact ⟨p, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hp⟩, hprow⟩

/-- **The copy of the last column emits every row of the root column below `τ`.** -/
theorem emitsT_emits {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hc : FwdCtx s ctx t root) {es : List (Emit × Origin)}
    (h : emitsT ctx (official t.row) = .ok es) {σ : Row} (hσ : RowFix.CrRow ctx σ)
    (hlt : σ < official t.row) : ∃ p ∈ es, p.1.row = σ := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      unfold lowerT at hlower
      simp only [bind, Except.bind, pure, Except.pure] at hlower
      split at hlower
      · cases hlower
      · rename_i outs houts
        cases hlower
        obtain ⟨q, hq, hqin⟩ := Recon.JumpLaw.lowerItems_cover (official t.row) hlt
        obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
        obtain ⟨m, hm, hmq⟩ := List.getElem_of_mem hq
        have hrun := hall m hm (by omega)
        rw [hmq] at hrun
        have hbel := (lowerItems_below (official t.row) _ hq).1
        obtain ⟨p, hp, hprow⟩ := runItemT_emits hc (k + 1) _ (by omega) hbel rfl rfl
          (fun C hC => by cases hC) σ hσ hqin _ hrun
        exact ⟨p, List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.getElem_mem _, hp⟩),
          hprow⟩

/-! ## The blocks -/

/-- The top `t` of a splice expansion is a real top whose left endpoint is in the root column
(as `site_top`). -/
theorem data_top {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : SpliceData s n D M out ρ R t) :
    ∃ root, Recon.Top s M t root ∧ root.column = ρ.cr ∧ ρ.x0 = M.size - 1 := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col, hcol, ht⟩ := hS.last
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hS.run
  rw [hS.splice.build] at hM'
  cases hM'
  have hsz := build_size hS.splice.build
  rcases hcases with ⟨he, _⟩ | ⟨col', t', hcol', ht', hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    have h0 : M.size = 0 := by simpa using hsz
    rw [Array.getElem?_eq_none (by omega)] at hcol
    cases hcol
  · have hcc : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst hcc
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst htt
    rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, hlt, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hS.splice.root
        rw [root?_none_of_official_zero hV D hcol' ht' h0] at hr
        cases hr
      · exact absurd h0 hS.splice.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol' ht' (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hS.splice.root)
      subst hρ
      refine ⟨root, ⟨hS.splice.build, by rw [hcol']; exact ht', fun h0 => hsp (Or.inl h0), htl,
        hlt⟩, hcr'.symm, hx0⟩

set_option maxHeartbeats 800000 in
/-- **Every block's copy of the last column emits the rows of the root column below `τ`.** -/
theorem block_emits {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : SpliceData s n D M out ρ R t) :
    ∀ i', i' < n → ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) i' ρ.x0 = .ok esB →
      ∀ σ, (∃ q ∈ realNodes M ρ.cr, official q.2.row = σ) → σ < official t.row →
        ∃ p ∈ esB, p.1.row = σ := by
  obtain ⟨root, hTop, hroot, hx0⟩ := data_top hS
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hVR := build_valid_of_success hS.canon
  intro i'
  induction i' using Nat.strong_induction_on with
  | _ i' ih =>
    intro hi' esB hesB σ hσ hlt
    have hw : 0 < ρ.x0 - ρ.cr := by omega
    refine emitsT_emits (s := s) (root := root) ?_ hesB ?_ hlt
    · refine ⟨hTop, by simp [ctxAt, hx0], by simp [ctxAt, hroot], rfl, ?_⟩
      intro hb0 σ' hσ' hlt' d T hT
      simp only [ctxAt, Context.boundary] at hb0 ⊢
      -- the boundary column `cr + w·i'` is the copy of `x₀` by block `i' - 1`
      have hwi : (ρ.x0 - ρ.cr) * i' ≤ n * (ρ.x0 - ρ.cr) := by
        rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
      have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i' := Nat.le_mul_of_pos_right _ (by omega)
      have hXlt : ρ.cr + (ρ.x0 - ρ.cr) * i' < R.size := by omega
      have hX0 : ρ.x0 ≤ ρ.cr + (ρ.x0 - ρ.cr) * i' := by omega
      obtain ⟨i'', x'', _, hx'', hXeq, hcopy⟩ := hinv.2.2 _ hXlt hX0
      have hxx := boundary_x hcrx (by omega : 0 < i') hx'' hXeq
      subst hxx
      have hii : i'' = i' - 1 := by
        have h1 : (ρ.x0 - ρ.cr) * i' = (ρ.x0 - ρ.cr) * (i'' + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
        have := Nat.eq_of_mul_eq_mul_left hw h1
        omega
      subst hii
      obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopy
      have hesl' : blockEmits M R ρ.cr ρ.x0 (official t.row) (i' - 1) ρ.x0 = .ok esl := by
        unfold blockEmits
        rw [← hXeq]
        exact hesl
      obtain ⟨p, hp, hprow⟩ := ih (i' - 1) (by omega) (by omega) esl hesl' σ' hσ' hlt'
      have hcolX : R[ρ.cr + (ρ.x0 - ρ.cr) * i']? = some R[ρ.cr + (ρ.x0 - ρ.cr) * i'] :=
        Array.getElem?_eq_getElem hXlt
      obtain ⟨_, hcells⟩ := cells_of_copy hcolX hcopy hesl
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨cell, hcell, hcrow⟩ := hcells k hk
      have hmem := mem_realNodes_of_cell hcell (by omega)
      have hoff : official cell.row = σ' := by
        rw [hcrow, Recon.JumpLaw.official_stored, hprow]
      have hcong : realNodes (R.extract 0 (ρ.x0 + (ρ.x0 - ρ.cr) * i')) (ρ.cr + (ρ.x0 - ρ.cr) * i') =
          realNodes R (ρ.cr + (ρ.x0 - ρ.cr) * i') :=
        Recon.JumpLaw.realNodes_congr (Recon.JumpLaw.getElem?_extract_lt (by omega))
      rw [← hcong] at hmem
      have hin : inRegion (d + 2) T (official cell.row) = true := by rw [hoff]; exact hT
      obtain ⟨b, hbtop⟩ := Recon.filter_last_exists
        (P := fun q => inRegion (d + 2) T (official q.2.row)) hmem hin
      have hbtop' : topIn (R.extract 0 (ρ.x0 + (ρ.x0 - ρ.cr) * i')) (ρ.cr + (ρ.x0 - ρ.cr) * i')
          (d + 2) T = some b := hbtop
      rw [hbtop']
      obtain ⟨hbmem, hbin, hbmax⟩ := Recon.filter_last_max hbtop
      have hbin' : inRegion (d + 2) T (official b.2.row) = true := hbin
      have hidx := hbmax _ hmem hin
      rw [hcong] at hbmem hmem
      have hrow := Recon.realNodes_row_le hVR hmem hbmem hidx
      have hoffle : σ' ≤ official b.2.row := by
        rw [← hoff]
        exact Recon.official_mono (Recon.realNodes_row_one_le hVR hmem) hrow
      simp only [heightOf, Recon.RowLaw.height_eq]
      exact Recon.RowLaw.coeff_le_of_inRegion hT hbin' hoffle
    · obtain ⟨q, hq, hqrow⟩ := hσ
      exact ⟨q, by simpa [ctxAt] using hq, hqrow⟩

end BoundaryRows

/-- **`BoundaryRootRows` holds.** -/
theorem boundaryRootRows : BoundaryRootRows := by
  intro s n D M out ρ R t hS i hi hin esB hesB q hq hqlt
  obtain ⟨p, hp, hprow⟩ :=
    BoundaryRows.block_emits hS (i - 1) (by omega) esB hesB _ ⟨q, hq, rfl⟩ hqlt
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact ⟨k, hk, hprow⟩

/-- **`LegRowMatchRootLower` holds.** -/
theorem legRowMatchRootLower : LegRowMatchRootLower :=
  legRowMatchRootLower_of_boundary boundaryRootRows

/-- **`LegRowMatchRoot` holds** (upper and lower origins). -/
theorem legRowMatchRoot : LegRowMatchRoot :=
  legRowMatchRoot_of_boundary boundaryRootRows

end OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.BoundaryRows.emitsT_emits
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.boundaryRootRows
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatchRootLower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatchRoot
