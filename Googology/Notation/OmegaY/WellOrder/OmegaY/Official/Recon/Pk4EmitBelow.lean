/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4EmitBelow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFound

set_option backward.do.legacy false

/-!
# `EmitBelow` for every block `i ≥ 1` (also `i > n`)

`CrossPlainPos.EmitBelow K` (`CrossPlainPosColumn.lean`) is stated with `CrossPlainPos.ColumnFact`,
which ranges over every block `i ≥ 1` and every `x ∈ blockColumns c_r x₀ n i`, with no bound
`i ≤ n`. For `i ≤ n` the lower part of the column covers every node below `τ`
(`CopyShape.Found.lowerT_covers`, from (MD) and (MH)). For `i > n` the output has no boundary
column `c_r + w·i` (`R.size ≤ x₀ + n·w`), so (MH) can fail; but then a clean item without the cut
flag and with a node in its region throws (`missingBoundaryNode`), so (MH) is never needed.

* `FactMHb`: (MH) only for items whose boundary top exists. It holds for `i ≤ n` (from
  `factMH_of_bctx`) and vacuously for `i > n`.
* `runItemT_coversB`: the covering part of `NoMA.runItemT_shapeW` with `FactMHb` in place of
  (MH).
* `lowerT_coversB`: every node of the column below `τ` is the origin of a non-cut emit of the
  lower part, for every block `i ≥ 1`.
* `emitBelow_all : ∀ K, (∀ o, K o → o.isUpper = false) → EmitBelow K`, and
  `emitBelow_plain`, `emitBelow_clean`.

## Numerical check

`p4-col.cjs` (scratch harness of this task, on `omegay-trace.cjs`): `EmitBelow` and `CleanFirst`
on every context of `ColumnFact`, including the blocks `i = n + 1, n + 2`: all legal inputs of
length `≤ 6` with entries `≤ 12`, `n = 1, 2` (2526699 contexts, 1107276 of them with `i > n`,
2972168 checks), 0 failures.
-/

namespace OmegaY.Official.Recon.Pk4

open Canonical Reserve Official Descent Classification Proofs
open Classification.Proofs.CopyShape

/-- (MH) for the items whose boundary top exists. -/
def FactMHb (ctx : Context) (τ : Row) : Prop :=
  ∀ d it C, Reach ctx τ (d + 2) it → it.clean = some C → it.cutBottom = false →
    topIn ctx.result ctx.boundary (d + 2) it.target ≠ none →
    ∀ csRef cs g, nodeAt ctx.source ctx.x C = some (csRef, cs) →
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g →
      heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
        heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g

theorem factMHb_of_factMH {ctx : Context} {τ : Row} (h : FactMH ctx τ) : FactMHb ctx τ :=
  fun d it C hRe hC hb _ => h d it C hRe hC hb

/-- A clean item without the cut flag whose column has a node in the region needs the boundary
top. -/
theorem childItems_bnd {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a) {C : Row} (hC : it.clean = some C)
    (hb : it.cutBottom = false) : topIn ctx.result ctx.boundary d it.target ≠ none := by
  intro hnone
  unfold childItems at h
  simp only [hx, bind, Except.bind, pure, Except.pure] at h
  cases hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) with
  | error e => rw [hasc] at h; cases h
  | ok v =>
    rw [hasc] at h
    cases v with
    | false =>
      simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hc
        simp [hC] at hc
    | true =>
      simp only [not_true_eq_false, if_false, hC] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · cases h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · rename_i hcond
            exact hcond ⟨by simp [hb], Or.inl (by simp [hnone])⟩

/-- **The covering part of `runItemT_shapeW`, with `FactMHb`.** -/
theorem runItemT_coversB (ctx : Context) (τ : Row)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hMD : FactMD ctx τ) (hMH : FactMHb ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      Reach ctx τ (d + 1) it → ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
        Covers (Env.ofCtx ctx ctx.result ctx.boundary) ctx.x (d + 1) it ps
  | 0, it, ps, h, _, hinv =>
      (NoMA.levelOneT_shapeW (R := ctx.result) (B := ctx.boundary) hV
        (by simpa [runItemT] using h) hinv).2.2
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
          have hcov : ∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index →
              cell? ctx.source p = some c →
              CovRow (Env.ofCtx ctx ctx.result ctx.boundary) (d + 2) it (official c.row) →
              ∃ ch ∈ children,
                CovRow (Env.ofCtx ctx ctx.result ctx.boundary) (d + 1) ch (official c.row) := by
            cases hx : topIn ctx.source ctx.x (d + 2) it.source with
            | none =>
              intro p c hpc hp1 hc hcov
              exact absurd hx (topIn_ne_none_of_node hpc hp1 hc hcov.1)
            | some a =>
              exact (NoMA.childItems_shapeW (R := ctx.result) (B := ctx.boundary) hV hi
                (fun _ _ => rfl) hch hinv (hMD d it hRe)
                (fun C hC hb => hMH d it C hRe hC hb (childItems_bnd hch hx hC hb))).2
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hIH : ∀ a (ha : a < outs.length),
              Covers (Env.ofCtx ctx ctx.result ctx.boundary) ctx.x (d + 1)
                (children[a]'(by omega)) outs[a] :=
            fun a ha => runItemT_coversB ctx τ hV hi hMD hMH d _ _
              (hall a (by omega) ha) (Reach.child hRe hch (List.getElem_mem _))
              (hinvc _ (List.getElem_mem _))
          intro p c hpc hp1 hc hcr
          obtain ⟨ch, hch', hcr'⟩ := hcov p c hpc hp1 hc hcr
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hch'
          obtain ⟨q, hq, hqs⟩ := hIH a (by omega) p c hpc hp1 hc hcr'
          exact ⟨q, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩, hqs⟩

/-- **The lower part covers the column**, with `FactMHb`. -/
theorem lowerT_coversB {ctx : Context} {τ : Row} (hV : MountainValid ctx.source)
    (hblk : 1 ≤ ctx.block) (hMD : FactMD ctx τ) (hMH : FactMHb ctx τ)
    {es : List (Emit × Origin)} (hes : lowerT ctx τ = .ok es) {k : Nat} {c : Cell} (hk : 1 ≤ k)
    (hc : cell? ctx.source ⟨ctx.x, k⟩ = some c) (hτ : official c.row < τ) :
    ∃ e ∈ es, ChainCorr.cutOrigin e.2 = false ∧ e.2.src = ⟨ctx.x, k⟩ := by
  obtain ⟨P, hP, hPin⟩ := Recon.JumpLaw.lowerItems_cover τ hτ
  unfold lowerT at hes
  simp only [bind, Except.bind, pure, Except.pure] at hes
  split at hes
  · cases hes
  · rename_i outs houts
    cases hes
    obtain ⟨out, hout, hPo⟩ := exists_of_mapM houts P hP
    obtain ⟨kk, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hP
    have hsh := runItemT_coversB ctx τ hV hblk hMD hMH kk _ out hPo (Reach.top hP)
      (fun C hC => by cases hC)
    have hcr : CovRow (Env.ofCtx ctx ctx.result ctx.boundary) (kk + 1)
        ⟨slot (kk + 2) τ j, slot (kk + 2) τ j, none, 0, false⟩ (official c.row) := by
      refine ⟨hPin, ?_, ?_⟩
      · intro C hC; cases hC
      · intro _ hb; cases hb
    obtain ⟨q, hq, hqs, hqc⟩ := hsh ⟨ctx.x, k⟩ c rfl hk hc hcr
    exact ⟨q, List.mem_flatten.mpr ⟨out, hout, hq⟩, hqc, hqs⟩

/-! ## The contexts of `ColumnFact` -/

/-- The output has at most `x₀ + n·w` columns. -/
theorem run_size_le {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    R.size ≤ (M.size - 1) + n * (M.size - 1 - root.column) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases hrun
    have hMM : M' = M := Except.ok.inj (hM'.symm.trans hTop.build)
    subst hMM
    have hlt := hTop.lt
    rcases hcases with ⟨hs, hR⟩ | ⟨_, col, t', _, _, hbr⟩
    · subst hs
      have h' : Canonical.build ([] : List Nat) = .ok #[] := rfl
      rw [h'] at hM'
      have hM0 : M' = #[] := (Except.ok.inj hM').symm
      subst hM0
      simp at hlt
    · rcases hbr with ⟨_, hR⟩ | ⟨_, h0, _⟩
      · subst hR; simp
      · exact absurd rfl h0
  · rw [Found.run_size hrun hTop (by omega)]

/-- **(MH) with the boundary premise holds in every context of `ColumnFact`.** -/
theorem factMHb_ctxAt {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i x : Nat} (hi : 0 < i)
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i) :
    FactMHb (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := Recon.mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi
  have hB : Recon.LowerPB.BCtx M R root.column (M.size - 1) i
      (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) :=
    Recon.LowerPB.bctx_ctxAt (le_of_lt hxg) hxl (by omega)
  rcases Nat.lt_or_ge n i with hni | hin
  · -- `i > n`: the boundary column is not a column of the output
    intro d it C _ _ _ hne
    exfalso
    apply hne
    have hsz := run_size_le hrun hTop
    have hwn : (M.size - 1 - root.column) * (n + 1) ≤ (M.size - 1 - root.column) * i :=
      Nat.mul_le_mul_left _ hni
    have hbig : (R.extract 0 (x + (M.size - 1 - root.column) * i)).size ≤
        root.column + (M.size - 1 - root.column) * i := by
      simp only [Array.size_extract]
      rw [Nat.mul_succ] at hwn
      have : n * (M.size - 1 - root.column) = (M.size - 1 - root.column) * n := Nat.mul_comm _ _
      omega
    unfold topIn realNodes
    simp only [ctxAt, Context.boundary]
    rw [Array.getElem?_eq_none hbig]
    rfl
  · exact factMHb_of_factMH (Found.factMH_of_bctx hrun hTop hi hin hB)

/-- **`EmitBelow K` for every kind `K` of lower copies.** -/
theorem emitBelow_all (K : Origin → Prop) (hK : ∀ o, K o → o.isUpper = false) :
    CrossPlainPos.EmitBelow K := by
  intro s n R hrun M t root hTop i x hi hxb es hes k hk hKk h2
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := Recon.mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi
  have hV : MountainValid M := build_valid_of_success hTop.build
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  have hB : Recon.LowerPB.BCtx M R root.column (M.size - 1) i ctx :=
    Recon.LowerPB.bctx_ctxAt (le_of_lt hxg) hxl (by omega)
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts hes
  -- the emit `k` is in the lower part
  have hkl : k < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[k] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := CrossPlain.upperT_isUpper hus _ hmem
    rw [hK _ hKk] at this
    cases this
  have hek : (lo ++ us)[k] = lo[k] := List.getElem_append_left hkl
  have hmemk : lo[k] ∈ lo := List.getElem_mem _
  -- the origin `N` is a node of `x` below `τ`
  obtain ⟨cN, hcN, hτN⟩ := Recon.LowerPB.lowerT_below hlo _ hmemk
  obtain ⟨hgood, _⟩ := Recon.LowerPB.lowerT_good hlo _ hmemk
  obtain ⟨hsc, hidx, _⟩ := hgood
  have hnu : lo[k].2.isUpper = false := by rw [← hek]; exact hK _ hKk
  simp only [hnu, Bool.false_eq_true, if_false] at hsc
  change lo[k].2.src.column = x at hsc
  rw [hek] at h2 ⊢
  -- the node below `N`
  obtain ⟨col, hcol, hNc⟩ := cell?_spec hcN
  have hidx' : lo[k].2.src.index - 1 < col.size := by
    have := (cell?_spec hcN)
    have hlt : lo[k].2.src.index < col.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hNc
      cases hNc
    omega
  set cm := col[lo[k].2.src.index - 1] with hcm
  have hcol' : M[lo[k].2.src.column]? = some col := hcol
  have hcm' : cell? M ⟨lo[k].2.src.column, lo[k].2.src.index - 1⟩ = some cm := by
    simp only [Reserve.cell?, hcol', Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem hidx', hcm]
  have hrow : cm.row < cN.row := by
    obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcol'
    have hCV := hV _ hc
    rw [hcolEq] at hCV
    obtain ⟨_, hNc'⟩ : ∃ h : lo[k].2.src.index < col.size, col[lo[k].2.src.index] = cN := by
      by_cases hlt : lo[k].2.src.index < col.size
      · exact ⟨hlt, Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hNc)⟩
      · rw [Array.getElem?_eq_none (by omega)] at hNc; cases hNc
    exact hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem hidx') (by rw [← hNc]) (by omega)
  have hcm1 : (1 : Row) ≤ cm.row := one_le_row hV hcm' (by simp only; omega)
  have hτm : official cm.row < official t.row :=
    lt_trans (official_strictMono hcm1 hrow) hτN
  have hMD := Found.factMD_of_bctx hTop hB
  have hMH := factMHb_ctxAt hrun hTop hi hxb
  have hcm'' : cell? ctx.source ⟨ctx.x, lo[k].2.src.index - 1⟩ = some cm := by
    change cell? M ⟨x, lo[k].2.src.index - 1⟩ = some cm
    rw [← hsc]
    exact hcm'
  obtain ⟨e, he, _, hesrc⟩ := lowerT_coversB (ctx := ctx) hV (by simp [hctx, ctxAt]; omega) hMD
    hMH hlo (k := lo[k].2.src.index - 1) (by omega) hcm'' hτm
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he
  refine ⟨m, by simp; omega, ?_⟩
  rw [List.getElem_append_left hm, hesrc]
  show (⟨x, _⟩ : Ref) = _
  rw [hsc]

theorem emitBelow_plain : CrossPlainPos.EmitBelow IsPlain :=
  emitBelow_all _ CrossPlain.isPlain_notUpper

theorem emitBelow_clean : CrossPlainPos.EmitBelow IsClean :=
  emitBelow_all _ CrossPlain.isClean_notUpper

end OmegaY.Official.Recon.Pk4

#print axioms OmegaY.Official.Recon.Pk4.emitBelow_plain
#print axioms OmegaY.Official.Recon.Pk4.emitBelow_clean
