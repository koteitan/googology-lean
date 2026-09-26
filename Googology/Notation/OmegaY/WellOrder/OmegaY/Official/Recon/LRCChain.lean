/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCChain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCAdj

set_option backward.do.legacy false

/-!
# The simulation along the path of `λ`

`sim_chain`: every item `A` of the tree of `X` on the path from a first item `F` down to the
level `e + 2`, holding `λ` in its target, has a similar item `B` in the tree of `Y` (reached
from the same first item). The step is `step` (`LRCStep.lean`); the hypotheses supply its
inputs along the path.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

theorem region_sub_of_child {ctx : Context} {d : Nat} {K : Item} {cs : List Item}
    {s : List Nat} {t : Cell} {root : Ref} (hctx : RunCtx s ctx t root)
    (hK : ItemOK ctx (official t.row) (d + 2) K) (hcs : childItems ctx (d + 2) K = .ok cs)
    {j : Nat} (hj : j < cs.length) {r : Row} (hr : inRegion (d + 1) cs[j].target r = true) :
    inRegion (d + 2) K.target r = true := by
  obtain ⟨_, htg⟩ := child_itemOK hctx hK hcs j hj
  rw [htg] at hr
  exact region_of_slot hr

/-- **The simulation of the path.** -/
theorem sim_chain {cX cY : Context} (P : Pair cX cY) {s : List Nat} {t : Cell} {root : Ref}
    (hctx : RunCtx s cX t root) {F : Nat × Item} (hF : F ∈ lowerItems (official t.row))
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : Anch cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a) {lam : Row} {e : Nat}
    (hEOK : ∀ d A, Desc cX F.1 F.2 d A → e + 2 ≤ d → inRegion d A.target lam = true →
      Inner.EmitOK cX.source cX.rootColumn d A θp)
    (hY : ∀ d B, Desc cY F.1 F.2 (d + 2) B → ∃ csY, childItems cY (d + 2) B = .ok csY)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hwa : ∀ q, e < q → (official wq.2.row).coeff q = a.coeff q)
    (hnt : ∀ d A cs j, Desc cX F.1 F.2 (d + 2) A → childItems cX (d + 2) A = .ok cs →
      ∀ hj : j < cs.length, e + 2 ≤ d + 1 → inRegion (d + 1) cs[j].target lam = true →
        A.clean = some a → j + 1 < cs.length)
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
    ∀ m d A, d + m = F.1 → Desc cX F.1 F.2 d A → e + 2 ≤ d → inRegion d A.target lam = true →
      ∃ B, Desc cY F.1 F.2 d B ∧ Sim cX cY d A B := by
  intro m
  induction m with
  | zero =>
    intro d A hd hD _ _
    subst hd
    have := desc_eq hD
    subst this
    exact ⟨F.2, .refl _ _, Or.inl rfl⟩
  | succ m ih =>
    intro d A hd hD hed hlA
    obtain ⟨K, csK, hDK, hcsK, hAm⟩ := desc_parent hD (by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hAm
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    have hDK' : Desc cX F.1 F.2 (d'' + 2) K := hDK
    have hcsK' : childItems cX (d'' + 2) K = .ok csK := hcsK
    have hKt : InTree cX (official t.row) (d'' + 2) K := ⟨F, hF, hDK'⟩
    obtain ⟨_, hKOK⟩ := LowerLeftProof.inTree_itemOK hctx hKt
    have hlK := region_sub_of_child hctx hKOK hcsK' hj hlA
    obtain ⟨BK, hDBK, hsimK⟩ := ih (d'' + 2) K (by omega) hDK' (by omega) hlK
    obtain ⟨csY, hcsY⟩ := hY d'' BK hDBK
    obtain ⟨ax, hax⟩ : ∃ ax, topIn cX.source cX.x (d'' + 2) K.source = some ax := by
      cases h : topIn cX.source cX.x (d'' + 2) K.source with
      | none =>
        have := childItems_none hcsK' h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    have hEA := hEOK (d'' + 2) K hDK' (by omega) hlK
    have hEc := hEOK (d'' + 1) csK[j] hD hed hlA
    have hw : inRegion (d'' + 1) csK[j].source (official wq.2.row) = true := by
      obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
      rw [hθa] at haReg
      rw [inRegion_iff'] at haReg ⊢
      intro q hq
      rw [hwa q (by omega), haReg q hq]
    have hnt' : ∀ C, K.clean = some C → C = a → j + 1 < csK.length := by
      intro C hC hCa
      exact hnt d'' K csK j hDK' hcsK' hj (by omega) hlA (by rw [hC, hCa])
    have hBs := hsimK.source
    obtain ⟨hjY, hsim, _⟩ := step P hb H hcθ hθa hsimK hcsK' hcsY hax le_rfl (by omega) hj
      hEA hEc hwq hw hnt' (hMDX d'' K · · hDK') (fun r cl hρ hasc => by
        have := hMDY d'' BK r cl hDBK (by rw [hBs]; exact hρ) hasc
        rw [hBs] at this; exact this) (hMHY d'' BK hDBK)
    exact ⟨csY[j], LowerLeftProof.desc_snoc hDBK hcsY (List.getElem_mem hjY), hsim⟩

end OmegaY.Official.Recon.LRC
