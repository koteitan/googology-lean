/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/P3TRunTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TBase

set_option backward.do.legacy false

/-!
# `CutRunTop` holds (`P3T`)

`CutRunTop` (`Pkg3Run.lean`): for a gap copy `u` (block `i ≥ 1`, origin `o = (x, a)`) whose leg
`l` is right of `c_r`, the copy of the column `l` in block `i` has a gap copy of `pa = (l, a)` at
a row `≥ row u`.

## The argument (`run_top_core`)

By induction up the path of `u` in the tree of `x`: every item `A` holding `u` either copies `a`
itself, or the tree of `l` has a gap copy of `pa` at a row `≥ row u` (in the traced lower part).

* A level-1 item that emits `u` copies `a`.
* An item copying some row whose child copies `a` copies `a` (case 4).
* A plain item `P` whose child `c` copies `a` (case 2 or 3, `x` ascends at the root top `ρ`,
  of row `a`): `P` is in the tree of `l` (`sim_down`), and `l` ascends at `ρ` (`Anch.le`).
  - At level 2 the child `c` is a level-1 gap copy item; the tree of `l` has the same child, and
    it emits a gap copy of `pa` at the same row.
  - Above level 2, the tree of `l` has the cut-bottom child `K = (S[h_ρ], T[k], ⊥, 0, 1)` of `P`
    (case 2: `k = h_ρ + Δ`; case 3: `k = h_B`), in a slot above that of `c`; `K` emits a gap copy
    of `pa` (`cb_emit`).
  (This is where the numbers of generations differ: the copies of `a` below `c` may have one
  more child in `x` than in `l`, since `g_x = g_l + 1`.)
* The first items do not copy a root row.

`cutRunTop : CutRunTop` (**proved**, no hypothesis).
-/

namespace OmegaY.Official.Classification.Proofs.P3T

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CutParts



section RunTop
open Recon Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC

/-- A clean emit of a level-1 item. -/
theorem levelOne_clean {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : runItemT ctx 1 it = .ok ps) {q : Emit × Origin} (hq : q ∈ ps) {o : Ref} {b : Bool}
    (hqo : q.2 = .clean o b) :
    ∃ C cs, it.clean = some C ∧ nodeAt ctx.source ctx.x C = some (o, cs) ∧ it.cutBottom = b ∧
      q.1.row = it.target := by
  have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
  unfold levelOneT at h'
  split at h'
  · cases h'; simp at hq
  · split at h'
    · rename_i C hC
      split at h'
      · cases h'
      · rename_i csRef cs hcs
        simp only [bind, Except.bind, pure, Except.pure] at h'
        split at h'
        · cases h'
        · cases h'
          simp only [List.mem_singleton] at hq
          subst hq
          simp only [Origin.clean.injEq] at hqo
          obtain ⟨rfl, rfl⟩ := hqo
          exact ⟨C, cs, hC, hcs, rfl, rfl⟩
    · split at h'
      · cases h'; simp only [List.mem_singleton] at hq; subst hq; cases hqo
      · simp only [bind, Except.bind, pure, Except.pure] at h'
        split at h'
        · cases h'
        · cases h'; simp only [List.mem_singleton] at hq; subst hq; cases hqo

theorem ascends_row {ctx : Context} {r r' : Ref} {cl cl' : Cell}
    (h : official cl.row = official cl'.row) :
    ascends ctx (some (r, cl)) = ascends ctx (some (r', cl')) := by
  unfold ascends; simp only; rw [h]



/-- The children of case 2 in the two columns: the partner of a copy of the root row. -/
theorem kid2_pick {D : Nat} {S T : Row} {blk hR : Nat} {lift : Int} {C : Row}
    {csX csY : List Item} {hTopY : Nat}
    (hgetX : ∀ j (hj : j < csX.length), csX[j] = c2 D S T blk hR lift C j)
    (hlenY : csY.length = ((hTopY : Int) + lift + 1).toNat)
    (hgetY : ∀ j (hj : j < csY.length), csY[j] = c2 D S T blk hR lift C j)
    (hhR : hR ≤ hTopY) {j : Nat} (hj : j < csX.length) {C' : Row}
    (hcj : csX[j].clean = some C') :
    (D = 2 → ∃ hjY : j < csY.length, csY[j] = csX[j]) ∧
    (D ≠ 2 → blk ≠ 0 → ∃ k, ∃ hk : k < csY.length, j < k ∧ csY[k].clean = none ∧
      csY[k].cutBottom = true ∧ csY[k].source = slot D S hR) := by
  rw [hgetX j hj] at hcj
  rcases c2_cases (d := D) (S := S) (T := T) (i := blk) (hR := hR) (lift := lift) (C := C) j with
    ⟨_, h2⟩ | ⟨h1, h2, _⟩ | ⟨_, _, _, h3, _⟩
  · rw [h2] at hcj; simp [k1] at hcj
  · constructor
    · intro hD
      subst hD
      simp only [if_true] at h2
      have hjY : j < csY.length := by rw [hlenY]; omega
      exact ⟨hjY, (hgetY j hjY).trans (hgetX j hj).symm⟩
    · intro hD hblk
      simp only [hD, if_false] at h2
      have hlpos : 0 < lift := by omega
      have hk : ((hR : Int) + lift).toNat < csY.length := by rw [hlenY]; omega
      refine ⟨_, hk, ?_⟩
      · have hkI : ((((hR : Int) + lift).toNat : Nat) : Int) = hR + lift := by omega
        rcases c2_cases (d := D) (S := S) (T := T) (i := blk) (hR := hR) (lift := lift) (C := C)
          ((hR : Int) + lift).toNat with ⟨hk1, _⟩ | ⟨_, hk2, _⟩ | ⟨_, _, hks, hkc, hkb⟩
        · omega
        · simp only [hD, if_false] at hk2; omega
        · rw [hgetY _ hk]
          refine ⟨by omega, hkc, ?_, ?_⟩
          · rw [hkb]; simp only [decide_eq_true_eq]; exact ⟨hblk, hkI⟩
          · rw [hks, hkI]; simp
  · rw [h3] at hcj; cases hcj

/-- The children of case 3 in the two columns: the partner of a copy of the root row. -/
theorem kid3_pick {D : Nat} {S T : Row} {hR hB : Nat} {C : Row}
    {csX csY : List Item} {hTopY : Nat}
    (hgetX : ∀ t (ht : t < csX.length), csX[t] = c3 D S T hR hB C (t + hR))
    (hlenY : csY.length = hB + hTopY + 1 - hR)
    (hgetY : ∀ t (ht : t < csY.length), csY[t] = c3 D S T hR hB C (t + hR))
    (hhR : hR ≤ hTopY) {j : Nat} (hj : j < csX.length) {C' : Row}
    (hcj : csX[j].clean = some C') :
    (D = 2 → ∃ hjY : j < csY.length, csY[j] = csX[j]) ∧
    (D ≠ 2 → ∃ k, ∃ hk : k < csY.length, j < k ∧ csY[k].clean = none ∧
      csY[k].cutBottom = true ∧ csY[k].source = slot D S hR) := by
  rw [hgetX j hj] at hcj
  rcases c3_cases (d := D) (S := S) (T := T) (hR := hR) (hB := hB) (C := C) (j + hR) with
    ⟨h1, _⟩ | ⟨_, h2⟩
  · constructor
    · intro hD
      subst hD
      simp only [if_true] at h1
      have hjY : j < csY.length := by rw [hlenY]; omega
      exact ⟨hjY, (hgetY j hjY).trans (hgetX j hj).symm⟩
    · intro hD
      simp only [hD, if_false] at h1
      have hk : hB < csY.length := by rw [hlenY]; omega
      refine ⟨hB, hk, by omega, ?_⟩
      rw [hgetY hB hk]
      rcases c3_cases (d := D) (S := S) (T := T) (hR := hR) (hB := hB) (C := C) (hB + hR) with
        ⟨hk1, _⟩ | ⟨_, hk2⟩
      · simp only [hD, if_false] at hk1; omega
      · rw [hk2]; simp
  · rw [h2] at hcj; cases hcj

/-- **`CutRunTop`, on the item trees.** For a gap copy `p` of `o = (x, a)` (leg `l`, `c_r < l`)
in the copy of the column `x`, the copy of the column `l` of the same block has a gap copy of
`pa = (l, a)` at a row `≥ row p`. -/
theorem run_top_core {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x l : Nat} (hCS : CS s n R M t root i x l) {outsX outsY : List (List (Emit × Origin))}
    (hoX : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsX)
    (hoY : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i l) p.1 p.2) = .ok outsY)
    {p : Emit × Origin} (hp : p ∈ outsX.flatten) {o : Ref} {cθ : Cell}
    (hpo : p.2 = .clean o true) (hu : (o, cθ) ∈ realNodes M x) (hleg : leftColumn cθ = .ok l)
    {pa : Ref × Cell} (hpa : pa ∈ realNodes M l) (hpaa : official pa.2.row = official cθ.row) :
    ∃ q ∈ outsY.flatten, q.2 = .clean pa.1 true ∧ p.1.row ≤ q.1.row := by
  have rX := hCS.ncx.runCtx
  have rY := hCS.ncy.runCtx
  have hb : Canonical.build s = .ok M := hCS.ncx.top.build
  have hi1 := hCS.pos
  have hblk : (colCtx M R root i x).block ≠ 0 := by show i ≠ 0; omega
  have hblkY : (colCtx M R root i l).block ≠ 0 := hblk
  have pr : Pair (colCtx M R root i x) (colCtx M R root i l) :=
    ⟨rfl, rfl, rfl, rfl, fun d T => (hCS.bnd d T).symm, hblk⟩
  have hin : i ≤ n := by have := hCS.ncx.block; omega
  have H := anch_of hCS hu hleg
  set a := official cθ.row with ha
  have hcθ : cell? M o = some cθ := by
    obtain ⟨huc, _, hucell⟩ := Classification.mem_realNodes hu
    exact hucell
  have hcθ' : cell? (colCtx M R root i x).source p.2.src = some cθ := by
    rw [hpo]; exact hcθ
  -- (MD), (MH)
  have hFMDX := Proofs.CopyShape.Found.factMD_of_bctx hCS.ncx.top (colCtx_bctx hCS.ncx)
  have hFMDY := Proofs.CopyShape.Found.factMD_of_bctx hCS.ncx.top (colCtx_bctx hCS.ncy)
  have hFMHY := Proofs.CopyShape.Found.factMH_of_bctx hCS.ncx.run hCS.ncx.top hCS.pos hin
    (colCtx_bctx hCS.ncy)
  -- the result
  let Res : Prop := ∃ q ∈ outsY.flatten, q.2 = .clean pa.1 true ∧ p.1.row ≤ q.1.row
  have claim : ∀ d A, InTree (colCtx M R root i x) (official t.row) (d + 1) A →
      ∀ TA, runItemT (colCtx M R root i x) (d + 1) A = .ok TA → p ∈ TA → Res ∨ A.clean = some a := by
    intro d
    induction d with
    | zero =>
      intro A _ TA hTA hpA
      right
      obtain ⟨C, cs, hC, hn, _, _⟩ := levelOne_clean hTA hpA hpo
      obtain ⟨hnm, hnr⟩ := RowLaw.nodeAt_spec hn
      obtain ⟨_, _, hcell⟩ := Classification.mem_realNodes hnm
      have : cs = cθ := Option.some.inj (hcell.symm.trans hcθ)
      subst this
      rw [hC, ← hnr]
    | succ d ih =>
      intro A hA TA hTA hpA
      obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children (show runItemT
        (colCtx M R root i x) (d + 2) A = .ok TA from hTA)
      obtain ⟨hlenF, hgetF⟩ := forall₂_getElem hF
      obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hpA
      obtain ⟨j, hjo, rfl⟩ := List.getElem_of_mem hL'
      have hj : j < cs.length := by omega
      have hcT : InTree (colCtx M R root i x) (official t.row) (d + 1) cs[j] :=
        LowerLeftProof.inTree_snoc hA hcs (List.getElem_mem hj)
      rcases ih cs[j] hcT outs[j] (hgetF j hj hjo) hpL' with hres | hcj
      · exact Or.inl hres
      obtain ⟨ax, hax⟩ : ∃ ax, topIn (colCtx M R root i x).source (colCtx M R root i x).x
          (d + 2) A.source = some ax := by
        cases h : topIn (colCtx M R root i x).source (colCtx M R root i x).x (d + 2) A.source with
        | none =>
          have := childItems_none hcs h
          rw [this] at hj; simp at hj
        | some ax => exact ⟨ax, rfl⟩
      have hct := LowerLeftProof.inTree_cleanTop hA
      obtain ⟨r, cl, hρ, hρa, hascX⟩ := clean_child_root hblk hcs hax hct hj hcj
      cases hAcl : A.clean with
      | some C' =>
        right
        obtain ⟨ρ', hρ', hρ'r⟩ := hct C' hAcl
        rw [hρ] at hρ'
        rw [← Option.some.inj hρ'] at hρ'r
        simp only at hρ'r
        rw [← hρ'r, hρa]
      | none =>
      left
      have hTA' : runItemT (colCtx M R root i x) (d + 2) A = .ok outs.flatten := hTA
      have hAOK := (LowerLeftProof.inTree_itemOK rX hA).2
      have hpreg : inRegion (d + 2) A.target p.1.row = true :=
        runItemT_region rX (by omega) hAOK hTA' p hpA
      obtain ⟨F, hF, hDA⟩ := hA
      have hY : ∀ d B, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B →
          ∃ csY, childItems (colCtx M R root i l) (d + 2) B = .ok csY := by
        intro d B hD
        obtain ⟨TB, hTB, _⟩ := tinTree rY hoY ⟨F, hF, hD⟩
        obtain ⟨csY, _, hcsY, _⟩ := runItemT_children hTB
        exact ⟨csY, hcsY⟩
      have hMDX : ∀ d A r cl, Desc (colCtx M R root i x) F.1 F.2 (d + 2) A →
          topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2) A.source =
            some (r, cl) →
          ascends (colCtx M R root i x) (some (r, cl)) = .ok true →
          height (d + 2) (official cl.row) < heightOf (d + 2) (topIn (colCtx M R root i x).source
            (colCtx M R root i x).lastColumn (d + 2) A.source) :=
        fun d A r cl hD hρ hasc => hFMDX d A (reach_of_inTree ⟨F, hF, hD⟩) r cl hρ hasc
      have hMDY : ∀ d B r cl, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B →
          topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn (d + 2) B.source =
            some (r, cl) →
          ascends (colCtx M R root i l) (some (r, cl)) = .ok true →
          height (d + 2) (official cl.row) < heightOf (d + 2) (topIn (colCtx M R root i x).source
            (colCtx M R root i x).lastColumn (d + 2) B.source) :=
        fun d B r cl hD hρ hasc => hFMDY d B (reach_of_inTree ⟨F, hF, hD⟩) r cl hρ hasc
      have hMHY : ∀ d B, Desc (colCtx M R root i l) F.1 F.2 (d + 2) B →
          ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
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
      obtain ⟨B, hDB, hsim⟩ := sim_down pr rX hb H hoX hp hcθ' rfl hF hpreg hAcl hY hpa hpaa
        hMDX hMDY hMHY (F.1 - (d + 2)) (d + 2) A (by have := desc_level_le hDA; omega) hDA
        (.refl _ _)
      have hBA : B = A := by
        rcases hsim with h | h | h
        · exact h.symm
        · exfalso
          obtain ⟨_, _, _, _, _, ρr, ρc, hρ', _, hf, _⟩ := h
          rw [hρ] at hρ'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hρ')
          rw [hascX] at hf; cases hf
        · exfalso
          obtain ⟨_, _, _, _, _, ρr, ρc, _, hcl', _⟩ := h
          rw [hAcl] at hcl'; cases hcl'
      subst hBA
      have hAY : InTree (colCtx M R root i l) (official t.row) (d + 2) B := ⟨F, hF, hDB⟩
      obtain ⟨TAY, hTAY, hsubY, _, _⟩ := tinTree rY hoY hAY
      obtain ⟨csY, outsYA, hcsY, hFY, rfl⟩ := runItemT_children (show runItemT
        (colCtx M R root i l) (d + 2) B = .ok TAY from hTAY)
      obtain ⟨hlenFY, hgetFY⟩ := forall₂_getElem hFY
      have ascY := H.le d B.source r cl hρ (le_of_eq hρa) hascX
      have hascAll : ∀ D S r' cl', topIn M root.column D S = some (r', cl') →
          official cl'.row = a → ascends (colCtx M R root i l) (some (r', cl')) = .ok true := by
        intro D S r' cl' _ h
        rw [ascends_row (r' := r) (cl' := cl) (h.trans hρa.symm)]
        exact ascY
      have hpaReg : inRegion (d + 2) B.source (official pa.2.row) = true := by
        rw [hpaa, ← hρa]; exact Classification.topIn_inRegion hρ
      obtain ⟨ay, hay, hayh⟩ := topY hb hpa hpaReg
      have hayY : topIn (colCtx M R root i l).source (colCtx M R root i l).x (d + 2) B.source =
          some ay := hay
      have hρY : topIn (colCtx M R root i l).source (colCtx M R root i l).rootColumn (d + 2)
          B.source = some (r, cl) := hρ
      have hhR : height (d + 2) (official cl.row) ≤ height (d + 2) (official ay.2.row) := by
        show (official cl.row).coeff (d + 2 - 2) ≤ (official ay.2.row).coeff (d + 2 - 2)
        rw [hρa, ← hpaa]; exact hayh
      have hpj : inRegion (d + 1) cs[j].target p.1.row = true :=
        runItemT_region rX (by omega) (LowerLeftProof.inTree_itemOK rX hcT).2 (hgetF j hj hjo) p
          hpL'
      rw [(child_itemOK rX hAOK hcs j hj).2] at hpj
      have hAOKY := (LowerLeftProof.inTree_itemOK rY hAY).2
      have fin : ∀ k (hk : k < csY.length), ((csY[k].clean = some a ∧ csY[k].cutBottom = true) ∨
          (csY[k].clean = none ∧ csY[k].cutBottom = true ∧ 1 ≤ d ∧ ∃ r cl,
            topIn M root.column (d + 1) csY[k].source = some (r, cl) ∧ official cl.row = a)) →
          (∀ q : Emit × Origin, inRegion (d + 1) (slot (d + 2) B.target k) q.1.row = true →
            p.1.row ≤ q.1.row) → Res := by
        intro k hk hkind hrow
        have hKT : InTree (colCtx M R root i l) (official t.row) (d + 1) csY[k] :=
          LowerLeftProof.inTree_snoc hAY hcsY (List.getElem_mem hk)
        have hkoY : k < outsYA.length := by omega
        obtain ⟨q, hq, hq2⟩ := cb_emit hCS.ncy (by omega) hpa hpaa hascAll d csY[k] hKT outsYA[k]
          (hgetFY k hk hkoY) hkind
        have hqreg := runItemT_region rY (by omega) (LowerLeftProof.inTree_itemOK rY hKT).2
          (hgetFY k hk hkoY) q hq
        rw [(child_itemOK rY hAOKY hcsY k hk).2] at hqreg
        exact ⟨q, hsubY q (List.mem_flatten.mpr ⟨_, List.getElem_mem hkoY, hq⟩), hq2, hrow q hqreg⟩
      -- the gap copy `p` is a copy with a cut bottom
      have hlev1 : d = 0 → cs[j].cutBottom = true ∧ p.1.row = cs[j].target := by
        intro hd0
        subst hd0
        obtain ⟨_, _, _, _, hcb1, hrow1⟩ := levelOne_clean (hgetF j hj hjo) hpL' hpo
        exact ⟨hcb1, hrow1⟩
      have hreg1 : ∀ (K : Item) (q : Emit × Origin), inRegion 1 K.target q.1.row = true →
          q.1.row = K.target := fun K q h => Classification.inRegion_one h
      have hfinish : ∀ D, D = d + 2 → ∀ (P2 : D = 2 → ∃ hjY : j < csY.length, csY[j] = cs[j])
          (P3 : D ≠ 2 → ∃ k, ∃ hk : k < csY.length, j < k ∧ csY[k].clean = none ∧
            csY[k].cutBottom = true ∧ csY[k].source = slot D B.source
              (height (d + 2) (official cl.row))), Res := by
        intro D hD P2 P3
        subst hD
        by_cases hd0 : d = 0
        · obtain ⟨hcb1, hrow1⟩ := hlev1 hd0
          obtain ⟨hjY, heq⟩ := P2 (by rw [hd0])
          apply fin j hjY
          · left; rw [heq]; exact ⟨hcj, hcb1⟩
          · intro q hq
            have h1 : q.1.row = slot (0 + 2) B.target j :=
              Classification.inRegion_one (by rw [hd0] at hq; exact hq)
            rw [h1, hrow1, (child_itemOK rX hAOK hcs j hj).2, hd0]
        · obtain ⟨k, hk, hjk, hkc, hkb, hks⟩ := P3 (fun h => hd0 (Nat.add_right_cancel
            (h.trans (Nat.zero_add 2).symm)))
          apply fin k hk
          · right
            refine ⟨hkc, hkb, Nat.pos_of_ne_zero hd0, r, cl, ?_, hρa⟩
            rw [hks]
            exact ChainCorr.Inner.topIn_slot hρ
          · intro q hq
            exact le_of_lt (ChainCorr.Inner.slot_rows_lt hpj hq hjk)
      cases hcb : B.cutBottom with
      | false =>
        obtain ⟨hlenX, hgetX⟩ := kids2 hcs hAcl hcb hax hρ hascX
        obtain ⟨hlenY, hgetY⟩ := kids2 hcsY hAcl hcb hayY hρY ascY
        obtain ⟨P2, P3⟩ := kid2_pick hgetX hlenY hgetY hhR hj hcj
        exact hfinish (d + 2) rfl P2 (fun hD => P3 hD hblk)
      | true =>
        obtain ⟨hlenX, hgetX⟩ := kids3 hcs hAcl hcb hblk hax hρ hascX
        obtain ⟨hlenY, hgetY⟩ := kids3 hcsY hAcl hcb hblkY hayY hρY ascY
        rw [pr.bnd] at hlenY hgetY
        obtain ⟨P2, P3⟩ := kid3_pick hgetX hlenY hgetY hhR hj hcj
        exact hfinish (d + 2) rfl P2 P3
  -- the first item holding `p`
  obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
  obtain ⟨k, hkL, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨hlen, hall⟩ := Classification.mapM_except_spec _ _ _ hoX
  have hk : k < (lowerItems (official t.row)).length := by omega
  have hFm := List.getElem_mem hk
  obtain ⟨_, _, hF1, _⟩ := RowLaw.lower_itemOK (ctx := colCtx M R root i x) hFm
  obtain ⟨d, hd⟩ : ∃ d, (lowerItems (official t.row))[k].1 = d + 1 :=
    ⟨(lowerItems (official t.row))[k].1 - 1, by omega⟩
  have hT : InTree (colCtx M R root i x) (official t.row) (d + 1)
      (lowerItems (official t.row))[k].2 := ⟨_, hFm, by rw [← hd]; exact .refl _ _⟩
  have hrun := hall k hk hkL
  rw [hd] at hrun
  rcases claim d _ hT _ hrun hpL with h | h
  · exact h
  · rw [ChainCorr.Inner.lowerItems_clean _ _ hFm] at h
    cases h


theorem leftColumn_of_left {cell : Cell} {l : Ref} (h : cell.left = some l) :
    leftColumn cell = .ok l.column := by
  unfold leftColumn Expansion.leftOf
  simp only [h]
  rfl

/-- The traced lower part of a column from its emits. -/
theorem lower_of_emits {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∃ outs us, (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outs ∧
      es = outs.flatten ++ us ∧ ∀ q ∈ us, q.2.isUpper = true := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := Recon.LowerPB.emitsT_split h
  unfold lowerT at hlo
  simp only [bind, Except.bind, pure, Except.pure] at hlo
  split at hlo
  · cases hlo
  · rename_i outs houts
    cases hlo
    refine ⟨outs, us, houts, rfl, ?_⟩
    intro q hq
    unfold upperT at hus
    obtain ⟨r, _, hqr⟩ := Classification.mem_of_mapM hus hq
    obtain ⟨h1, _⟩ := CopyShape.upper_emit hqr
    rw [h1]; rfl


end RunTop

open ChainCorr.Pkg3 in
/-- **`CutRunTop` holds.** -/
theorem cutRunTop : CutRunTop := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl hbl
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨root, hTop, hcr, hx0, hNCx, hXeq, hctx⟩ := site_nc hS
  have hi0 := hS.iPos
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨_, _, _, hcrx, _⟩ := spliceCase_data hS.splice hS.run
  -- the gap copy and its origin
  have ho := origin_clean_of_cut rfl hcut
  obtain ⟨hsrcc, hidx, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hup : es[j].2.isUpper = false := by rw [ho]; rfl
  rw [hup] at hsrcc
  simp only [Bool.false_eq_true, if_false] at hsrcc
  change es[j].2.src.column = x at hsrcc
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hlx : l.column < x := by omega
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    have := hS.xMem
    unfold blockColumns at this
    rw [if_neg (by omega)] at this
    simp only [List.mem_range'_1] at this
    split <;> split at this <;> omega
  -- the column `l` of the block
  obtain ⟨col, hcol, ht⟩ := hS.last
  have hSet : Inner.Setting s n D M out ρ R col t := ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩
  have hSL := site_of_emits hSet hi0 hS.iLt hlt hyx hymem rfl hbl
  obtain ⟨root', hTop', hcr', _, hNCl, _, hctxl⟩ := site_nc hSL
  have hrr : root' = root := Option.some.inj (hTop'.left.symm.trans hTop.left)
  subst hrr
  have hCS : Recon.LRC.CS s n R M t root' i x l.column :=
    ⟨hNCx, hNCl, hi0, by rw [← hcr]; exact hlt, hlx⟩
  -- the traced lower parts
  have hesX := hS.emits
  rw [← hctx] at hesX
  obtain ⟨outsX, usX, hoX, hesXe, hupX⟩ := lower_of_emits hesX
  have hesL := hSL.emits
  rw [← hctxl] at hesL
  obtain ⟨outsY, usY, hoY, hesLe, _⟩ := lower_of_emits hesL
  have hpX : es[j] ∈ outsX.flatten := by
    have hm : es[j] ∈ outsX.flatten ++ usX := by rw [← hesXe]; exact List.getElem_mem hj
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exact absurd (hupX _ h) (by rw [hup]; simp)
  -- the origin node and `pa`
  have hsrcx : (es[j].2.src, cv) ∈ realNodes M x := by
    have := CopyShape.mem_realNodes_of_cell' hL.hcv hidx
    rw [hsrcc] at this
    exact this
  have hleg : leftColumn cv = .ok l.column := leftColumn_of_left hL.hl
  obtain ⟨hpacol, hpa0, _⟩ := highestAtMost_spec hL.hpa
  have hpam : (pa, cpa) ∈ realNodes M l.column := by
    have := CopyShape.mem_realNodes_of_cell' hL.hcpa hpa0
    rw [hpacol] at this
    exact this
  have hparow := cutPaRow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  obtain ⟨q, hq, hq2, hqrow⟩ := run_top_core hCS hoX hoY hpX ho hsrcx hleg hpam
    (by show official cpa.row = official cv.row; rw [hparow])
  have hqm : q ∈ esl := by rw [hesLe]; exact List.mem_append_left _ hq
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hqm
  exact ⟨k, hk, hq2, hqrow⟩

end OmegaY.Official.Classification.Proofs.P3T

#print axioms OmegaY.Official.Classification.Proofs.P3T.cutRunTop
