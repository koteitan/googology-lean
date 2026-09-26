/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4Pair.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Legs
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerChainCross

set_option backward.do.legacy false

/-!
# `PairOld` holds

`CrossPlainPos.PairOld K` (`CrossPlainPosSim.lean`): a node `u⁺` of a new column `x + w·i`
(`i ≥ 1`) with an origin of kind `K` and the source `N`, and a node `B` of `M(s)` at or left of
`c_r` with the stored left end and the row of `N`: the copy `u⁺` has the row of `N`.

The stored left end `l` of `N` is the stored left end of `B`, so it is left of `B`, hence left
of `c_r`. A plain copy whose origin has its leg left of `c_r` keeps the row of its origin
(`emitsT_plainLeft`); a clean copy has an origin with its leg at or right of `c_r`
(`emitsT_cleanLeg`), so it does not occur.

`pairOld_all : ∀ K, (∀ o, K o → LowKind o) → PairOld K`, `pairOld_plain`, `pairOld_clean`.
The hypothesis `Lex N B` is not used.
-/

namespace OmegaY.Official.Recon.Pk4

open Canonical Expansion Geometry Frame Classification
open CrossPlainPos (LowKind lowKind_notUpper)

/-- The height of a node of a new column is the stored row of its emit. -/
theorem height_of_emit {R : Mountain} {ctx : Context} {es : List (Emit × Origin)} {X : Nat}
    {colX : Column} (hRX : R[X]? = some colX)
    (hasm : assemble ctx (es.map Prod.fst) = .ok colX) (U : (Frame.ofMountain R).Node)
    (hU : U.1.val = X) (hj : U.2.val - 1 < es.length) (hU1 : 1 ≤ U.2.val) :
    (Frame.ofMountain R).height U = Official.stored es[U.2.val - 1].1.row := by
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, hrow, _⟩ := hcells (U.2.val - 1) (by simpa using hj)
  have h1 := LowerChainRecon.cell?_ref U
  have h2 : Reserve.cell? R (Frame.ref U) = some cell := by
    simp only [Reserve.cell?, Frame.ref, hU, hRX, Option.bind_eq_bind, Option.bind_some]
    rw [show U.2.val = U.2.val - 1 + 1 by omega]
    exact hcellX
  have he := Option.some.inj (h1.symm.trans h2)
  show ((Frame.ofMountain R).cell U).row = _
  rw [he, hrow]
  simp

/-- The origin of a lower emit of a column `x > c_r` has a stored left end. -/
theorem left_of_lower {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {ctx : Context} (hsrc : ctx.source = M)
    (hcx : root.column < ctx.x) {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {p : Emit × Origin} (hp : p ∈ es) (hnu : p.2.isUpper = false)
    {cv : Cell} (hcv : Reserve.cell? M p.2.src = some cv) : ∃ l, cv.left = some l := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  obtain ⟨hvcol, hvidx, cv', hcv', hleftcv⟩ := emitsT_good h p hp
  rw [hsrc] at hcv'
  have hcc : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst hcc
  simp only [hnu, Bool.false_eq_true, if_false] at hvcol
  rcases hleftcv with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
  · exact ⟨l, hl⟩
  · have hi1 := index_one_of_official_zero hV hcv' hvidx h0
    exact ⟨_, bottom_left hTop.build hcv' hi1 (by omega)⟩

/-- **`PairOld K` for every kind `K` of plain or clean copies.** -/
theorem pairOld_all (K : Origin → Prop) (hK : ∀ o, K o → LowKind o) : CrossPlainPos.PairOld K := by
  intro s n R hrun M t root hTop i x hi hxb up o hX hup1 ho hKo N B hN hleft _ hBN hBcr _
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hG : (Frame.ofMountain M).Ordered := (build_normal_of_success hTop.build).toOrdered
  obtain ⟨es, em, colX, hes, hRX, hasm, hj⟩ := LowerChainRecon.originAt_unpack2 hTop hxb hX ho
  have hjl : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hj
    exact Option.some.inj hj
  have hhu := height_of_emit hRX hasm up rfl hjl hup1
  have hmem := List.getElem_mem hjl
  have hnu : o.isUpper = false := lowKind_notUpper o (hK o hKo)
  -- the cell of the origin `N`
  have hcN : Reserve.cell? M es[up.2.val - 1].2.src = some ((Frame.ofMountain M).cell N) := by
    rw [hej]
    show Reserve.cell? M o.src = _
    rw [← hN]
    exact LowerChainRecon.cell?_ref N
  obtain ⟨l, hl⟩ := left_of_lower hTop (ctx := ctxAt M R x i root.column
    (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl (by simp only [ctxAt]; omega) hes hmem
    (by rw [hej]; exact hnu) hcN
  -- the left end is left of `B`, so left of `c_r`
  have hlB : ((Frame.ofMountain M).cell B).left = some l := by rw [← hleft]; exact hl
  obtain ⟨left, hlk, hlc, _⟩ := hG.stored_valid B l hlB
  have hlref : Frame.ref left = l := Frame.lookup_spec hlk
  have hlcol : l.column < root.column := by
    rw [← hlref]
    show left.1.val < root.column
    omega
  rcases hK o hKo with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- a plain copy keeps the row of its origin
    have hrow := emitsT_plainLeft hTop (ctx := ctxAt M R x i root.column
      (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl rfl (by simp only [ctxAt]; omega)
      (by simp only [ctxAt]; omega) hes _ hmem r (by rw [hej, hr]) _
      (by rw [hej, hr] at hcN; exact hcN) l hl hlcol
    rw [hhu, hrow]
    have hN1 : (1 : Row) ≤ ((Frame.ofMountain M).cell N).row := by
      have h1 : 1 ≤ (Frame.ref N).index := by
        obtain ⟨_, hidx, _⟩ := emitsT_good hes _ hmem
        rw [hej] at hidx
        change 1 ≤ o.src.index at hidx
        rw [← hN] at hidx
        exact hidx
      exact one_le_row hV (LowerChainRecon.cell?_ref N) h1
    exact stored_official hN1
  · -- a clean copy has an origin with its leg at or right of `c_r`
    exfalso
    have hge := emitsT_cleanLeg hTop (ctx := ctxAt M R x i root.column
      (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl rfl (by simp only [ctxAt]; omega)
      hes _ hmem (by rw [hej, hr]; rfl) _ hcN l hl
    omega

theorem pairOld_plain : CrossPlainPos.PairOld IsPlain :=
  pairOld_all _ (fun _ h => Or.inl h)

theorem pairOld_clean : CrossPlainPos.PairOld IsClean :=
  pairOld_all _ (fun _ h => Or.inr h)

end OmegaY.Official.Recon.Pk4

#print axioms OmegaY.Official.Recon.Pk4.pairOld_plain
#print axioms OmegaY.Official.Recon.Pk4.pairOld_clean
