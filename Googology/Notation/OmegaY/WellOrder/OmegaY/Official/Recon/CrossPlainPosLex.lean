/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainPosLex.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPos

set_option backward.do.legacy false

/-!
# `PosLexAt` from the transport of `Lex` to the images of block `i`

`PosLexAt K` (`CrossPlainPos.lean`) asks for `Lex u⁺ c⁺` in the output `R`. By `PosChainImg`,
`u⁺` is the copy of the origin `N` and `c⁺` is the image of `c_M⁺`, and in `M = M(s)` the two
nodes `N`, `c_M⁺` have the same stored left end `p_M`, the same row, and `Lex N c_M⁺`
(`normal_crossLex`, `M(s)` is normal). So `PosLexAt` follows from one statement that does not
mention the cross case:

* `LexImg K`: for a node `z` of a new column `x + w·i` (`i ≥ 1`) with an origin `A` of kind
  `K`, and a node `B` of `M(s)` left of `A` with the stored left end and the row of `A` and
  `Lex A B` in `M(s)`, the image `W` of `B` in block `i` (`ImgAt`) satisfies `Lex z W` in `R`.

The path of `Lex` in `R` is not the image of the path in `M(s)` (gap copies and the upper
part enter it); `LexImg` only transports the truth of `Lex`.

`posLexAt_of_imgLex : PosChainImg K → LexImg K → PosLexAt K`: the node `c` of the chain
from `q` with stored parent `p` is unique (`rawChain_last_unique`), and the node given by
`PosChainImg` has the stored parent `p` (`leftCol_of_img`, `parent_of_leftCol`).

## Numerical check

`reference/official/cross-plain-pos-img.cjs` checks `LexImg` for every copy `z` of kind plain
or clean in a new column and every node `B` as above (results in `CrossPlainPos.lean`).
-/

namespace OmegaY.Official.Recon.CrossPlainPos

open Canonical Expansion Geometry Frame Classification

/-- **Open.** `Lex` transports from `M(s)` to the images of block `i`. -/
def LexImg (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (z W : (Frame.ofMountain R).Node) (o : Origin),
      z.1.val = x + (M.size - 1 - root.column) * i → 1 ≤ z.2.val →
      OriginAt s n R z.1.val (z.2.val - 1) o → K o →
    ∀ A B : (Frame.ofMountain M).Node, Frame.ref A = o.src →
      ((Frame.ofMountain M).cell A).left = ((Frame.ofMountain M).cell B).left →
      (Frame.ofMountain M).height A = (Frame.ofMountain M).height B →
      B.1.val < A.1.val → Lex (Frame.ofMountain M) A B →
      ImgAt s n R M root i LowKind W B → Lex (Frame.ofMountain R) z W

/-- **`PosLexAt` from `PosChainImg` and `LexImg`.** -/
theorem posLexAt_of_imgLex {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hC : PosChainImg K) (hL : LexImg K) : PosLexAt K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo c cp hc hcp hcu hh
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  obtain ⟨M, t, root, i, x, N, hTop, hI, hxb, hX, hNref, hNx⟩ :=
    img_setup hK hrun (by rw [hup1]; omega) ho hKo
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  obtain ⟨uM, pM, qM, cM, cMp, huM, hNu, hpM, hqM, _, hcM, hcMp, hcMu, hcMh, c', cp', hc',
    hc'u, hh', himg⟩ := hC s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x
    hTop hxb hX N hNref
  -- the node `c'` of `PosChainImg` is `c`
  have hqr := Q_real hF hu hq
  have hc'r : Real c' := (hc'.value_le hB.valid hB.sums hqr).1
  obtain ⟨_, hc'u2⟩ := upper_spec hc'u
  have hlc := leftCol_of_img hK lowKind_notUpper hTop hI (by unfold Real at hu; omega) (by omega) ho hKo
    (by rw [hX, hNx]) hNref huM hNu hpM hcMp hcMu hcMh himg
  have hraw' := parent_of_leftCol hrun hu hc'r hraw hup hc'u hh' hlc
  have hcc : c = c' := CrossUpper.rawChain_last_unique hF hc hc' hcp hraw'
  subst hcc
  rw [hcu] at hc'u
  obtain rfl := Option.some.inj hc'u
  -- `Lex N c_M⁺` in `M(s)`
  have hNM : (Frame.ofMountain M).Normal :=
    build_normal_of_legal (build_success_legal hTop.build) hTop.build
  obtain ⟨_, _, hlexM⟩ := CrossPlain.normal_crossLex hNM huM hNu hpM hqM hcM hcMp hcMu
  -- the block is `i ≥ 1`
  have hMs := Canonical.build_size hTop.build
  have hupc : up.1.val = u.1.val := congrArg Fin.val hup1
  have hXgt : M.size - 1 < up.1.val := by
    have h1 := hx
    have h2 := hMs
    have h3 := hupc
    have h4 := hTop.lt
    omega
  obtain ⟨hi0, _⟩ := originAt_unpack hTop hxb hX hXgt ho
  -- the stored left ends and columns in `M(s)`
  obtain ⟨N', hN', hNl⟩ := rawParent_spec hpM
  rw [hNu] at hN'
  obtain rfl := Option.some.inj hN'
  obtain ⟨cMp', hcMu', hcMl⟩ := rawParent_spec hcMp
  rw [hcMu] at hcMu'
  obtain rfl := Option.some.inj hcMu'
  have hcol' : cMp.1.val < N.1.val := by
    obtain ⟨h1, _⟩ := upper_spec hcMu
    obtain ⟨h2, _⟩ := upper_spec hNu
    have h3 := hcM.column_le hG
    have h4 := Q_column_lt hG hqM
    rw [h1, h2]
    omega
  exact hL s n R hrun M t root hTop i x hi0 hxb up cp o hX (by omega) ho hKo N cMp hNref
    (by rw [hNl, hcMl]) hcMh.symm hcol' hlexM himg

/-- **`CrossLexFor IsPlain`** from `PosChainImg IsPlain` and `LexImg IsPlain`. -/
theorem crossLexFor_plain_of_imgLex (hC : PosChainImg IsPlain) (hL : LexImg IsPlain) :
    CrossLexFor IsPlain :=
  crossLexFor_plain_of_img hC (posLexAt_of_imgLex CrossPlain.isPlain_notUpper hC hL)

/-- **`CrossLexFor IsClean`** from `PosChainImg IsClean` and `LexImg IsClean`. -/
theorem crossLexFor_clean_of_imgLex (hC : PosChainImg IsClean) (hL : LexImg IsClean) :
    CrossLexFor IsClean :=
  crossLexFor_clean_of_img hC (posLexAt_of_imgLex CrossPlain.isClean_notUpper hC hL)

end OmegaY.Official.Recon.CrossPlainPos

#print axioms OmegaY.Official.Recon.CrossPlainPos.posLexAt_of_imgLex
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_of_imgLex
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_of_imgLex
