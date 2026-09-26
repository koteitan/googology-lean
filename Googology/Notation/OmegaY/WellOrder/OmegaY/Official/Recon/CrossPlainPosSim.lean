/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainPosSim.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimStep

set_option backward.do.legacy false

/-!
# `PosImgR` from the simulation of the chain of `M(s)`

`PosImgR K` (`CrossPlainPos.lean`) asks that the chain of stored parents of the output `R`
from `q = Q u` reach a node `c` whose upper node `c⁺` is the image of `c_M⁺` (the end of the
chain `q_M → … → c_M` of `M = M(s)`) and has the row of `u⁺`.

The chain of `R` is the simulation of the chain of `M` given by the stand-in relation
`CrossUpperSim.Cp` of `CrossUpperSimDefs.lean` (left of `c_r`: the node itself; in `c_r`: a
node of the column `c_r + w·i` whose chain reaches the image of the stored parent; right of
`c_r`: the top copy below `τ`). `CrossUpperSim.cp_chain` (proved there from the two open
statements `CopyTop`, `CopyStepLower`) carries `Cp` along a chain of `M`. So `PosImgR` needs
only a start and an end:

* `QStand K` (start): for a real node `u` of a new column whose upper node `u⁺` has an origin
  of kind `K` with the source `N`, and the node `z` below `N`: `Q u` stands for `Q z`
  (`Cp`). It is the analogue of `CrossUpperSim.CopyQLower` (there `row z⁺ ≥ τ`); here `z⁺`
  is below `τ`, and the kind of the copy of `z⁺` is plain or clean.
* the end, split by the column `y` of `c_M`. In `M`, `N` and `c_M⁺` have the same stored left
  end, the same row, and `Lex N c_M⁺` (`normal_crossLex`).
  - `PairAbove K` (`y > c_r`): for nodes `N`, `B` of `M` with these three properties,
    `B` right of `c_r`, and a node `C` standing for the node `B⁻` below `B`: the node above
    `C` has the row of `u⁺` and an origin of kind plain or clean with the source `B` (the
    kind can differ from `K`: `s = (1,3,27,11,22,30)`, `n = 1`);
  - `PairOld K` (`y ≤ c_r`): for such `N`, `B` with `B` at or left of `c_r`, the copy `u⁺`
    of `N` has the row of `N` (it is not lifted);
  - `RootPass K` (`y = c_r`): the chain of `R` from the stand-in `C` of `c_M` (a node of the
    column `c_r + w·i`) passes through the node `c_M` itself (an old column). A general form
    (every `Cp C z` with `z` in `c_r`) is false (`reference/official/cross-plain-pos-sim.cjs`,
    `RootPassGen`, e.g. `s = (1,3,9,11,9)`, `n = 1`, `Z = (4, bottom)`, `z = (1,1)`), so
    it is stated in the setting of `PosImgR`.

`posImgR_of_sim : CopyTop → CopyStepLower → QStand K → PairAbove K → PairOld K → RootPass K →
PosImgR K`, and the main theorems `crossLexPos_plain_sim`, `crossLexPos_clean_sim`,
`crossLexFor_plain_sim`, `crossLexFor_clean_sim`.

## Numerical check

`reference/official/cross-plain-pos-sim.cjs` checks `QStand` (`QGen`, every node, cross case
or not), the simulation along the chain (`ChainCp`), `PairAbove` and `PairOld` (`Pair`, every
pair `N`, `B` as above), and `RootPass` (`EndCp`, `cM =cr`). No failure on:

| sample | `n` | cross cases | `QStand` | `PairAbove` | `PairOld` | `RootPass` |
|---|---|---:|---:|---:|---:|---:|
| standard, the 64 `LegBelowTop` inputs, the MA inputs | 1,2,3 | 20550 | 552492 | 32103 | 588 | 402 |
| legal, length `≤ 6`, entries `≤ 12` (248831 inputs) | 1,2 | SIM612 |
| `(1,3,a,b,c,d)`, entries `≤ 40`, 3000 random | 1,2 | 6048 | 46248 | 21016 | 222 | 204 |
| random, length `≤ 7`, entries `≤ 40`, 1500 draws | 1,2 | 1270 | 11674 | 4296 | 0 | 0 |

(`PairAbove` counts pairs with and without `Lex N B`; `QStand` counts every node, cross case or
not.) The kind of the image differs from the kind of `u⁺` in 54 cross cases of the last sample.
`CopyTop` and `CopyStepLower` are tested by `reference/official/cross-upper-sim.cjs`.
-/

namespace OmegaY.Official.Recon.CrossPlainPos

open Canonical Expansion Geometry Frame Classification
open CrossUpper (shiftCol shiftCol_of_le shiftCol_of_lt twin_of_agree twin_of_agree'
  node_eq_of_height)
open CrossUpperSim (Cp CopyTop CopyStepLower Env env_of block_le cp_chain rawChain_trans)

/-! ## The open statements -/

/-- **Open (start).** For a real node `u` of a new column `x + w·i` (`i ≥ 1`) whose upper node
`u⁺` has an origin of kind `K` with the source `N`, and the node `z` below `N`: the candidate
`Q u` stands for the candidate `Q z` (`CrossUpperSim.Cp`). -/
def QStand (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (u up : (Frame.ofMountain R).Node) (o : Origin), Real u →
      (Frame.ofMountain R).upper u = some up →
      up.1.val = x + (M.size - 1 - root.column) * i →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
    ∀ z N : (Frame.ofMountain M).Node, Frame.ref N = o.src → Real z →
      (Frame.ofMountain M).upper z = some N →
    ∀ a A, (Frame.ofMountain M).Q z = some a → (Frame.ofMountain R).Q u = some A →
      Cp s n R M t root i A a

/-- **Open (end, right of `c_r`).** Let `u⁺` be a node of a new column `x + w·i` (`i ≥ 1`)
with an origin of kind `K` and the source `N`, and `B` a node of `M(s)` left of `N` and right
of `c_r`, with the stored left end and the row of `N` and `Lex N B`. For every node `C` that
stands for the node `B⁻` below `B`, the node above `C` has the row of `u⁺` and an origin of
kind plain or clean (`LowKind`, not necessarily the kind `K`) with the source `B`. -/
def PairAbove (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (up : (Frame.ofMountain R).Node) (o : Origin),
      up.1.val = x + (M.size - 1 - root.column) * i → 1 ≤ up.2.val →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
    ∀ N B Bm : (Frame.ofMountain M).Node, Frame.ref N = o.src →
      ((Frame.ofMountain M).cell N).left = ((Frame.ofMountain M).cell B).left →
      (Frame.ofMountain M).height N = (Frame.ofMountain M).height B →
      B.1.val < N.1.val → root.column < B.1.val → Lex (Frame.ofMountain M) N B →
      (Frame.ofMountain M).upper Bm = some B →
    ∀ C : (Frame.ofMountain R).Node, Cp s n R M t root i C Bm →
      ∃ C', (Frame.ofMountain R).upper C = some C' ∧
        (Frame.ofMountain R).height C' = (Frame.ofMountain R).height up ∧
        ∃ o', OriginAt s n R C'.1.val (C'.2.val - 1) o' ∧ LowKind o' ∧ o'.src = Frame.ref B

/-- **Open (end, at or left of `c_r`).** With `u⁺`, `N` as in `PairAbove`, if some node `B` of
`M(s)` at or left of `c_r` has the stored left end and the row of `N` and `Lex N B`, then the
copy `u⁺` has the row of `N`. -/
def PairOld (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (up : (Frame.ofMountain R).Node) (o : Origin),
      up.1.val = x + (M.size - 1 - root.column) * i → 1 ≤ up.2.val →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
    ∀ N B : (Frame.ofMountain M).Node, Frame.ref N = o.src →
      ((Frame.ofMountain M).cell N).left = ((Frame.ofMountain M).cell B).left →
      (Frame.ofMountain M).height N = (Frame.ofMountain M).height B →
      B.1.val < N.1.val → B.1.val ≤ root.column → Lex (Frame.ofMountain M) N B →
      (Frame.ofMountain R).height up = (Frame.ofMountain M).height N

/-- **Open (end, in `c_r`).** In the setting of `PosImgR K`, when the end `c_M` of the chain of
`M(s)` is in the root column, the chain of `R` from a node `C` that stands for `c_M` (reached
from `q`) passes through the node `c_M` of the old column `c_r`. -/
def RootPass (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∀ (M : Mountain) (t : Cell) (root : Ref) (i x : Nat), Top s M t root →
        x ∈ blockColumns root.column (M.size - 1) n i →
        up.1.val = x + (M.size - 1 - root.column) * i →
        ∀ N uM pM qM cM : (Frame.ofMountain M).Node, Frame.ref N = o.src → Real uM →
          (Frame.ofMountain M).upper uM = some N →
          (Frame.ofMountain M).rawParent uM = some pM → (Frame.ofMountain M).Q uM = some qM →
          qM.1 ≠ pM.1 → RawChain (Frame.ofMountain M) qM cM →
          (Frame.ofMountain M).rawParent cM = some pM → cM.1.val = root.column →
        ∀ C : (Frame.ofMountain R).Node, RawChain (Frame.ofMountain R) q C →
          Cp s n R M t root i C cM →
          ∃ c : (Frame.ofMountain R).Node, RawChain (Frame.ofMountain R) C c ∧
            c.1.val = cM.1.val ∧ c.2.val = cM.2.val

/-! ## Tools -/

/-- The source of a copy of the lower part is in the column `x` of its block. -/
theorem src_column {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false) {s : List Nat}
    {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root) {i x : Nat}
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i) {up : (Frame.ofMountain R).Node}
    {o : Origin} (hX : up.1.val = x + (M.size - 1 - root.column) * i)
    (hXgt : M.size - 1 < up.1.val) (ho : OriginAt s n R up.1.val (up.2.val - 1) o) (hKo : K o)
    {N : (Frame.ofMountain M).Node} (hN : Frame.ref N = o.src) : N.1.val = x := by
  obtain ⟨_, es, em, _, hes, _, _, hj⟩ := originAt_unpack hTop hxb hX hXgt ho
  have hjlt : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  obtain ⟨hsc, _⟩ := emitsT_good hes _ (List.getElem_mem hjlt)
  rw [hej] at hsc
  simp only [hK o hKo, Bool.false_eq_true, if_false] at hsc
  change o.src.column = x at hsc
  rw [← hsc, ← hN]
  rfl

/-- **The end in an old column.** A node `c` of `R` at the column and index of a node `c_M` of
an old column has the upper node at the column and index of `c_M⁺`, with its row. -/
theorem old_end {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {c : (Frame.ofMountain R).Node} {cM cMp : (Frame.ofMountain M).Node}
    (hcx : cM.1.val < M.size - 1) (h1 : c.1.val = cM.1.val) (h2 : c.2.val = cM.2.val)
    (hcMu : (Frame.ofMountain M).upper cM = some cMp) :
    ∃ cp : (Frame.ofMountain R).Node, (Frame.ofMountain R).upper c = some cp ∧
      cp.1.val = cMp.1.val ∧ cp.2.val = cMp.2.val ∧
      (Frame.ofMountain R).height cp = (Frame.ofMountain M).height cMp := by
  obtain ⟨hu1, hu2⟩ := upper_spec hcMu
  have hcMpx : cMp.1.val < M.size - 1 := by rw [hu1]; exact hcx
  obtain ⟨Z, hZ1, hZ2, hZc⟩ := twin_of_agree' (E.agree _ hcMpx) cMp rfl
  refine ⟨Z, ?_, hZ1, hZ2, ?_⟩
  · refine Classification.ControlProof.upper_eq_of_index (Fin.ext ?_) ?_
    · rw [h1, hZ1, hu1]
    · rw [hZ2, hu2, h2]
  · show ((Frame.ofMountain R).cell Z).row = ((Frame.ofMountain M).cell cMp).row
    rw [hZc]

/-! ## The reduction -/

/-- **`PosImgR K` from the simulation**, for every kind of the lower part. -/
theorem posImgR_of_sim {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hCT : CopyTop) (hSL : CopyStepLower) (hQ : QStand K) (hPA : PairAbove K)
    (hPO : PairOld K) (hRP : RootPass K) : PosImgR K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq
    N uM pM qM cM cMp hN huM hNu hpM hqM hne hcM hcMp hcMu
  have hMs := Canonical.build_size hTop.build
  have hcr := hTop.lt
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc : up.1.val = u.1.val := congrArg Fin.val hup1
  have hXgt : M.size - 1 < up.1.val := by omega
  obtain ⟨hi0, _⟩ := originAt_unpack hTop hxb hXeq hXgt ho
  have hXR : up.1.val < R.size := up.1.isLt
  have E := env_of hrun hTop hXR hXgt.le
  have hG := E.G
  obtain ⟨hxc, hxle⟩ := mem_blockColumns hcr hxb
  have hin : i ≤ n := block_le E hxc hxle (by rw [← hXeq]; exact hXR) (by rw [← hXeq]; omega)
  -- the columns of `M(s)`
  have hNx : N.1.val = x := src_column hK hTop hxb hXeq hXgt ho hKo hN
  obtain ⟨hN1, _⟩ := upper_spec hNu
  have huMx : uM.1.val = x := by rw [← hNx, hN1]
  have hqMr : Real qM := Q_real hG huM hqM
  have hqMlt : qM.1.val < uM.1.val := Q_column_lt hG hqM
  have hcMle : cM.1.val ≤ qM.1.val := hcM.column_le hG
  have hqMx : qM.1.val < M.size - 1 := by omega
  -- the start and the simulation of the chain
  have hstart : Cp s n R M t root i q qM :=
    hQ s n R hrun M t root hTop i x hi0 hxb u up o hu hup hXeq ho hKo uM N hN huM hNu qM q hqM hq
  obtain ⟨C, hqC, hCC⟩ := cp_chain E hCT hSL hi0 hin hcM hqMr hqMx hstart
  -- the facts of `M(s)` at the end
  obtain ⟨_, hrow, hlexM⟩ := CrossPlain.normal_crossLex E.NM huM hNu hpM hqM hcM hcMp hcMu
  obtain ⟨N', hN', hNl⟩ := rawParent_spec hpM
  rw [hNu] at hN'
  obtain rfl := Option.some.inj hN'
  obtain ⟨cMp', hcMu', hcMl⟩ := rawParent_spec hcMp
  rw [hcMu] at hcMu'
  obtain rfl := Option.some.inj hcMu'
  have hleft : ((Frame.ofMountain M).cell N).left = ((Frame.ofMountain M).cell cMp).left := by
    rw [hNl, hcMl]
  obtain ⟨hcMp1, _⟩ := upper_spec hcMu
  have hcMpc : cMp.1.val = cM.1.val := congrArg Fin.val hcMp1
  have hBN : cMp.1.val < N.1.val := by omega
  have hup1' : 1 ≤ up.2.val := by omega
  -- the end, by the column of `c_M`
  rcases Nat.lt_trichotomy root.column cM.1.val with hgt | heq | hlt
  · -- right of `c_r`: the node above the stand-in of `c_M`
    obtain ⟨C', hCu, hC'h, o', ho', hKo', hsrc'⟩ := hPA s n R hrun M t root hTop i x hi0 hxb up o
      hXeq hup1' ho hKo N cMp cM hN hleft hrow (by omega) (by omega) hlexM hcMu C hCC
    refine ⟨C, C', hqC, hCu, hC'h, Or.inr ⟨by omega, ?_, o', ho', hKo', hsrc'⟩⟩
    obtain ⟨hC'1, _⟩ := upper_spec hCu
    have hCcol := hCC.column
    rw [shiftCol_of_le hgt.le] at hCcol
    rw [congrArg Fin.val hC'1, hCcol, hcMpc]
  · -- in `c_r`: the chain passes through `c_M` itself
    obtain ⟨c, hCc, hc1, hc2⟩ := hRP s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root
      i x hTop hxb hXeq N uM pM qM cM hN huM hNu hpM hqM hne hcM hcMp heq.symm C hqC hCC
    obtain ⟨cp, hcu, hcp1, hcp2, hcph⟩ := old_end E (by omega) hc1 hc2 hcMu
    have hro := hPO s n R hrun M t root hTop i x hi0 hxb up o hXeq hup1' ho hKo N cMp hN hleft
      hrow hBN (by omega) hlexM
    refine ⟨c, cp, rawChain_trans hqC hCc, hcu, ?_, Or.inl ⟨by omega, hcp1, hcp2⟩⟩
    rw [hcph, ← hrow, hro]
  · -- left of `c_r`: the stand-in of `c_M` is `c_M` itself
    have hC : C.1.val = cM.1.val ∧
        (Frame.ofMountain R).height C = (Frame.ofMountain M).height cM := by
      rcases hCC with ⟨_, h2, h3⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact ⟨h2, h3⟩
      · omega
      · omega
    obtain ⟨z, hz1, hz2, hzc⟩ := twin_of_agree (E.agree _ (by omega)) C hC.1
    have hzh : (Frame.ofMountain M).height z = (Frame.ofMountain M).height cM := by
      rw [← hC.2]
      show ((Frame.ofMountain M).cell z).row = ((Frame.ofMountain R).cell C).row
      rw [hzc]
    have hzc' : z = cM := node_eq_of_height hG (Fin.ext (by rw [hz1])) hzh
    subst hzc'
    obtain ⟨cp, hcu, hcp1, hcp2, hcph⟩ := old_end E (by omega) hC.1 hz2.symm hcMu
    have hro := hPO s n R hrun M t root hTop i x hi0 hxb up o hXeq hup1' ho hKo N cMp hN hleft
      hrow hBN (by omega) hlexM
    refine ⟨C, cp, hqC, hcu, ?_, Or.inl ⟨by omega, hcp1, hcp2⟩⟩
    rw [hcph, ← hrow, hro]

/-! ## The main theorems -/

/-- **`CrossLexPos IsPlain`** (blocks `i ≥ 1`) from the open statements. -/
theorem crossLexPos_plain_sim (hE : EmitBelow IsPlain) (hCT : CopyTop) (hSL : CopyStepLower)
    (hQ : QStand IsPlain) (hPA : PairAbove IsPlain) (hPO : PairOld IsPlain)
    (hRP : RootPass IsPlain) (hL : LexImg IsPlain) : CrossPlain.CrossLexPos IsPlain :=
  crossLexPos_plain_main hE
    (posImgR_of_sim CrossPlain.isPlain_notUpper hCT hSL hQ hPA hPO hRP) hL

/-- **`CrossLexPos IsClean`** (blocks `i ≥ 1`) from the open statements. -/
theorem crossLexPos_clean_sim (hE : EmitBelow IsClean) (hCF : CleanFirst) (hCT : CopyTop)
    (hSL : CopyStepLower) (hQ : QStand IsClean) (hPA : PairAbove IsClean)
    (hPO : PairOld IsClean) (hRP : RootPass IsClean) (hL : LexImg IsClean) :
    CrossPlain.CrossLexPos IsClean :=
  crossLexPos_clean_main hE hCF
    (posImgR_of_sim CrossPlain.isClean_notUpper hCT hSL hQ hPA hPO hRP) hL

/-- **`CrossLexFor IsPlain`** from the open statements. -/
theorem crossLexFor_plain_sim (hE : EmitBelow IsPlain) (hCT : CopyTop) (hSL : CopyStepLower)
    (hQ : QStand IsPlain) (hPA : PairAbove IsPlain) (hPO : PairOld IsPlain)
    (hRP : RootPass IsPlain) (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  CrossPlain.crossLexFor_plain_of_pos (crossLexPos_plain_sim hE hCT hSL hQ hPA hPO hRP hL)

/-- **`CrossLexFor IsClean`** from the open statements. -/
theorem crossLexFor_clean_sim (hE : EmitBelow IsClean) (hCF : CleanFirst) (hCT : CopyTop)
    (hSL : CopyStepLower) (hQ : QStand IsClean) (hPA : PairAbove IsClean)
    (hPO : PairOld IsClean) (hRP : RootPass IsClean) (hL : LexImg IsClean) :
    CrossLexFor IsClean :=
  CrossPlain.crossLexFor_clean_of_pos (crossLexPos_clean_sim hE hCF hCT hSL hQ hPA hPO hRP hL)

end OmegaY.Official.Recon.CrossPlainPos

#print axioms OmegaY.Official.Recon.CrossPlainPos.posImgR_of_sim
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexPos_plain_sim
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexPos_clean_sim
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_sim
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_sim
