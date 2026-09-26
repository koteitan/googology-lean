/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainPos.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainBlock0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpper

set_option backward.do.legacy false

/-!
# `CrossLexPos IsPlain` and `CrossLexPos IsClean` (blocks `i ≥ 1`)

`CrossLexPos K` (`CrossPlainBlock0.lean`) is the cross case of the chain condition for the
nodes `u` of a new column `X = x + w·i`, `i ≥ 1`, whose upper node `u⁺` has an origin of kind
`K` (plain or clean: a copy of the lower part that is not a gap copy). Let `p = π(u⁺)` and
`q = Q u` be in different columns. The claim is a chain of stored parents `q → … → c` with
`π(c⁺) = p`, `row c⁺ = row u⁺` and `Lex u⁺ c⁺`.

## The shape found numerically

`reference/official/cross-plain-pos-img.cjs`. Let `N` be the origin of `u⁺` (a node of
`M = M(s)` in the column `x`), `u_M` the node below `N`, `p_M = π_M(N)`, `q_M = Q_M u_M`.

* `M` is in the cross case at `u_M` (`q_M`, `p_M` in different columns), so its chain
  `q_M → … → c_M` with `π_M(c_M⁺) = p_M` exists (`normal_chain_exists`).
* The chain of `R` from `q` ends at the **image** of `c_M⁺`: with `y` the column of `c_M`,
  - `y > c_r`: `c⁺` is the node of the column `y + w·i` whose origin is plain or clean
    (`LowKind`) with the source `c_M⁺` (the non-gap copy of `c_M⁺` in block `i`). Its kind
    can differ from the kind of `u⁺` (`s = (1,3,27,11,22,30)`, `n = 1`: `u⁺` plain, `c⁺`
    clean); a first version of `ImgAt` asked for the kind of `u⁺` and was false;
  - `y ≤ c_r`: `c⁺` is `c_M⁺` itself (an old column). This case occurs only with large
    values (the 64 sequences that refute `LegBelowTop`); there the chain of `R` passes
    through the boundary column `c_r + w·i`, so it is **not** the image of the chain of `M`
    node by node, while for `y > c_r` it is in every test.
* `row c⁺ = row u⁺`, and `Lex u⁺ c⁺` in `R`. The path of `Lex` in `R` differs from the path
  of `Lex N c_M⁺` in `M` (gap copies and the upper part enter it), so `Lex` is not
  transported node by node.

## What is proved

* `crossLexPos_of_at : PosChainAt K → PosLexAt K → CrossLexPos K`. `PosChainAt` asks only
  for a chain from `q` to a node `c` whose upper node has the row of `u⁺` and its stored left
  end in the column of `p`; then `π(c⁺) = p` (`parent_of_leftCol`: both are the highest nodes
  of that column below the same row, `hb_run`, `hb_eq`). `PosLexAt` is `Lex u⁺ c⁺` for that
  `c`.
* `posChainAt_of_img : PosChainImg K → PosChainAt K` for the kinds of the lower part.
  `PosChainImg` is the precise shape above (the chain ends at the image of `c_M⁺`); the
  stored left ends of `u⁺` and of the image of `c_M⁺` are both in the column
  `shiftCol c_r w i (col p_M)` (`leftCol_of_img`): for a new column from the emitted leg
  (`Good`, `assemble_spec`), for an old column from the cell of `M` (`y ≤ c_r`, so
  `col p_M < c_r`).
* `posChainImg_of_parts : PosCrossM K → PosImgR K → PosChainImg K`: the chain of `M` and
  `row c_M⁺ = row N` come from the normality of `M(s)` (`normal_chain_exists`,
  `normal_crossLex`).
* `posCrossM_of_belowSrc : BelowSrc K → PosCrossM K`: if the emit of `u` has the origin
  `u_M = N⁻`, the stored left ends of `u` and `u⁺` are the images of those of `u_M` and `N`
  under `shiftCol c_r w i` (injective), so the cross case of the output at `u` is the cross
  case of `M(s)` at `u_M`.
* `CrossPlainPosColumn.lean`: `BelowSrc` from `EmitBelow` (and `CleanFirst` for the clean
  kind), with the order of the origins (`emitsT_order`).
* `CrossPlainPosLex.lean`: `PosLexAt` from `PosChainImg` and `LexImg` (the transport of `Lex`
  from `M(s)` to the images of block `i`; `Lex N c_M⁺` in `M(s)` is `normal_crossLex`).
* `CrossPlainPosMain.lean`: `crossLexPos_plain_main`, `crossLexPos_clean_main`,
  `crossLexFor_plain_main`, `crossLexFor_clean_main`.

## What is open

`EmitBelow IsPlain`, `EmitBelow IsClean`, `CleanFirst` (one column each), `PosImgR IsPlain`,
`PosImgR IsClean` (the chain of the output; reduced further in `CrossPlainPosSim.lean`),
`LexImg IsPlain`, `LexImg IsClean` (the transport of `Lex`). The weaker intermediate statements (`PosChainAt`, `PosLexAt`,
`PosChainImg`, `PosCrossM`, `BelowSrc`) follow from them.

## Numerical check

`reference/official/cross-plain-pos-img.cjs` (`n = 1, 2, 3`) checks `PosChainImg` (strong
form: for the unique chain end `c_M`, which implies `PosCrossM` and `PosImgR`), `PosLexAt`,
`BelowSrc`, `EmitBelow`, `CleanFirst` and `LexImg` (the image of kind plain or clean). No
failure on: the standard samples (13030 inputs, `n = 1,2,3`), all legal inputs of length `≤ 6`
with entries `≤ 6` and of length `≤ 5` with entries `≤ 8`, all legal inputs of length `≤ 7` with
entries `≤ 7` (117648 inputs; 340897 `PosChainImg` cases), the 64 inputs on which `LegBelowTop`
fails (402 cases with the column of `c_M` at most `c_r`), the inputs where MA fails
(`(1,3,6,13,15,13)`, `(1,2,4,10,11,14,10)`), and 3000 random inputs `(1,3,a,b,c,d)` with
entries `≤ 40` (`n = 1,2`), where the kind of the image of `c_M⁺` differs from the kind of `u⁺`
in some cases (`(1,3,27,11,22,30)`).

`CrossPlainPosSim.lean` reduces `PosImgR` further to local statements
(`posImgR_of_sim`).
-/

namespace OmegaY.Official.Recon.CrossPlainPos

open Canonical Expansion Geometry Frame Classification
open CrossUpper (shiftCol hb_run hb_eq)
open CrossPlain (CrossLexPos)

/-! ## The open statements -/

/-- **Open (weak form).** In the setting of `CrossLexPos K`, the chain of stored parents from
`q` reaches a node `c` whose upper node `c⁺` has the row of `u⁺` and its stored left end in
the column of the stored left end of `u⁺`. -/
def PosChainAt (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up ∧
        ((Frame.ofMountain R).cell cp).left.map Ref.column =
          ((Frame.ofMountain R).cell up).left.map Ref.column

/-- **Open.** In the setting of `CrossLexPos K`, `Lex u⁺ c⁺` for the node `c` of the chain
from `q` whose stored parent is `p`, when `row c⁺ = row u⁺`. -/
def PosLexAt (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∀ c cp, RawChain (Frame.ofMountain R) q c → (Frame.ofMountain R).rawParent c = some p →
        (Frame.ofMountain R).upper c = some cp →
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up →
        Lex (Frame.ofMountain R) up cp

/-- The kinds of the image of a node of `M(s)` right of `c_r`: plain, or clean without the cut
flag. The image of `c_M⁺` need not have the kind of `u⁺`: for `s = (1,3,27,11,22,30)`, `n = 1`,
`u⁺ = (8, ω)` is a plain copy and `c⁺ = (7, ω)` a clean copy
(`reference/official/cross-plain-pos-sim.cjs`). -/
def LowKind (o : Origin) : Prop := IsPlain o ∨ IsClean o

theorem lowKind_notUpper : ∀ o, LowKind o → o.isUpper = false := by
  rintro o (h | h)
  · exact CrossPlain.isPlain_notUpper o h
  · exact CrossPlain.isClean_notUpper o h

/-- `cp` is the image in block `i` of the node `B` of `M(s)`: `B` itself when the column of
`B` is at most `c_r` (an old column of the output), otherwise a node of the column
`col B + w·i` whose origin has kind `K` and the source `B` (used with `K = LowKind`). -/
def ImgAt (s : List Nat) (n : Nat) (R M : Mountain) (root : Ref) (i : Nat)
    (K : Origin → Prop) (cp : (Frame.ofMountain R).Node) (B : (Frame.ofMountain M).Node) :
    Prop :=
  (B.1.val ≤ root.column ∧ cp.1.val = B.1.val ∧ cp.2.val = B.2.val) ∨
    (root.column < B.1.val ∧ cp.1.val = B.1.val + (M.size - 1 - root.column) * i ∧
      ∃ o', OriginAt s n R cp.1.val (cp.2.val - 1) o' ∧ K o' ∧ o'.src = Frame.ref B)

/-- **Open (precise form).** In the setting of `CrossLexPos K`, with `M = M(s)`, the block
`i` of `u⁺` and the origin `N` of `u⁺`: the node `u_M` below `N` is real, `M` is in the
cross case at `u_M` (`q_M = Q u_M` and `p_M = π_M(N)` in different columns), its chain
`q_M → … → c_M` with `π_M(c_M⁺) = p_M` and `row c_M⁺ = row N` exists, and the chain of the
output from `q` reaches a node `c` whose upper node `c⁺` is the image of `c_M⁺` and has the
row of `u⁺`. -/
def PosChainImg (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∀ (M : Mountain) (t : Cell) (root : Ref) (i x : Nat), Top s M t root →
        x ∈ blockColumns root.column (M.size - 1) n i →
        up.1.val = x + (M.size - 1 - root.column) * i →
        ∀ N : (Frame.ofMountain M).Node, Frame.ref N = o.src →
        ∃ uM pM qM cM cMp : (Frame.ofMountain M).Node, Real uM ∧
          (Frame.ofMountain M).upper uM = some N ∧
          (Frame.ofMountain M).rawParent uM = some pM ∧ (Frame.ofMountain M).Q uM = some qM ∧
          qM.1 ≠ pM.1 ∧ RawChain (Frame.ofMountain M) qM cM ∧
          (Frame.ofMountain M).rawParent cM = some pM ∧
          (Frame.ofMountain M).upper cM = some cMp ∧
          (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N ∧
          ∃ c cp : (Frame.ofMountain R).Node, RawChain (Frame.ofMountain R) q c ∧
            (Frame.ofMountain R).upper c = some cp ∧
            (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up ∧
            ImgAt s n R M root i LowKind cp cMp

/-! ## The stored parent of `c` -/

/-- **The stored parent of `c`.** If `c⁺` has the row of `u⁺` and its stored left end in the
column of `p = π(u⁺)`, then `π(c⁺) = p`. -/
theorem parent_of_leftCol {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u p c up cp : (Frame.ofMountain R).Node}
    (hu : Real u) (hc : Real c) (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hup : (Frame.ofMountain R).upper u = some up) (hcu : (Frame.ofMountain R).upper c = some cp)
    (hh : (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up)
    (hlc : ((Frame.ofMountain R).cell cp).left.map Ref.column =
      ((Frame.ofMountain R).cell up).left.map Ref.column) :
    (Frame.ofMountain R).rawParent c = some p := by
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  rw [hpl] at hlc
  cases hcl : ((Frame.ofMountain R).cell cp).left with
  | none =>
    rw [hcl] at hlc
    cases hlc
  | some r =>
    rw [hcl] at hlc
    obtain ⟨B, hBl, _, _⟩ := hF.stored_valid cp r hcl
    have hBr : Frame.ref B = r := lookup_spec hBl
    have hrawc : (Frame.ofMountain R).rawParent c = some B :=
      rawParent_eq_of_upper_left hcu (by rw [hBr]; exact hcl)
    have hBc : B.1 = p.1 := by
      apply Fin.ext
      have e := Option.some.inj hlc
      rw [← hBr] at e
      exact e
    have hBp : B = p := hb_eq (hb_run hrun c hc) (hb_run hrun u hu) hcu hup hh hrawc hraw hBc
    rw [← hBp]
    exact hrawc


/-- **`CrossLexPos K` from the chain and `Lex`.** The node `c` given by `PosChainAt` has the
stored parent `p`: both `π(c⁺)` and `π(u⁺) = p` are the highest nodes of one column below the
row `row c⁺ = row u⁺`. -/
theorem crossLexPos_of_at {K : Origin → Prop} (hC : PosChainAt K) (hL : PosLexAt K) :
    CrossLexPos K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo
  obtain ⟨c, cp, hc, hcu, hh, hlc⟩ := hC s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  have hqr := Q_real hF hu hq
  have hcr : Real c := (hc.value_le hB.valid hB.sums hqr).1
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  rw [hpl] at hlc
  cases hcl : ((Frame.ofMountain R).cell cp).left with
  | none =>
    rw [hcl] at hlc
    cases hlc
  | some r =>
    rw [hcl] at hlc
    obtain ⟨B, hBl, _, _⟩ := hF.stored_valid cp r hcl
    have hBr : Frame.ref B = r := lookup_spec hBl
    have hrawc : (Frame.ofMountain R).rawParent c = some B :=
      rawParent_eq_of_upper_left hcu (by rw [hBr]; exact hcl)
    have hBc : B.1 = p.1 := by
      apply Fin.ext
      have e := Option.some.inj hlc
      rw [← hBr] at e
      exact e
    have hBp : B = p := hb_eq (hb_run hrun c hcr) (hb_run hrun u hu) hcu hup hh hrawc hraw hBc
    subst hBp
    exact ⟨c, cp, hc, hrawc, hcu, hh.symm,
      hL s n R hrun u B q up o hx hu hraw hq hcol hup ho hKo c cp hc hrawc hcu hh⟩

/-! ## The stored left ends of the images -/

/-- **The stored left end of a copy.** A node `v` of a new column of the output whose origin
`o` is not of the upper kind, with the source `N` of `M(s)` above the bottom row and
`π_M(N) = P`, is in a column `col N + w·i` and has its stored left end in the column
`shiftCol c_r w i (col P)`. -/
theorem left_of_originAt {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {v : (Frame.ofMountain R).Node} {o : Origin} (hv : 1 ≤ v.2.val)
    (ho : OriginAt s n R v.1.val (v.2.val - 1) o) (hnu : o.isUpper = false)
    {N P : (Frame.ofMountain M).Node} (hN : Frame.ref N = o.src)
    (hl : ((Frame.ofMountain M).cell N).left = some (Frame.ref P))
    (h1 : (1 : Row) < (Frame.ofMountain M).height N) :
    ∃ i, v.1.val = N.1.val + (M.size - 1 - root.column) * i ∧
      ((Frame.ofMountain R).cell v).left.map Ref.column =
        some (shiftCol root.column (M.size - 1 - root.column) i P.1.val) := by
  obtain ⟨M', col, t', root', x, i, es, em, hM', hcol, ht', hroot', _, _, hX, hes,
    ⟨colX, hRX, _, hasm⟩, hj⟩ := ho
  have hMM : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  subst hMM
  have htt : t = t' := by
    have h := hTop.top
    rw [hcol] at h
    simp only [Option.bind_some] at h
    exact Option.some.inj (h.symm.trans ht')
  subst htt
  have hrr : root = root' := Option.some.inj (hTop.left.symm.trans hroot')
  subst hrr
  have hjlt : v.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[v.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  obtain ⟨hsc, _, cv, hcv, hleg⟩ := emitsT_good hes _ (List.getElem_mem hjlt)
  rw [hej] at hsc hcv hleg
  simp only [hnu, Bool.false_eq_true, if_false] at hsc
  change o.src.column = x at hsc
  change Reserve.cell? M o.src = some cv at hcv
  have hcvN : cv = (Frame.ofMountain M).cell N := by
    have e := ControlProof.cell?_ref N
    rw [hN, hcv] at e
    exact Option.some.inj e
  subst hcvN
  have hlc : em.leftColumn = some P.1.val := by
    rcases hleg with ⟨l, hl', hlc⟩ | ⟨_, h0, _⟩
    · rw [hl] at hl'
      rw [hlc, ← Option.some.inj hl']
      rfl
    · exact absurd h0 (official_ne_zero_of_one_lt h1)
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcell, _, ref, href, hrefc⟩ := hcells (v.2.val - 1) (by simpa using hjlt)
  have hcv' : (Frame.ofMountain R).cell v = cell := by
    refine frame_cell_of hRX ?_
    rw [show v.2.val = v.2.val - 1 + 1 by omega]
    exact hcell
  refine ⟨i, ?_, ?_⟩
  · rw [hX]
    congr 1
    rw [← hsc, ← hN]
    rfl
  · rw [hcv', href]
    simp only [Option.map_some, hrefc, List.getElem_map, hej, legColumn, hlc]
    rfl

theorem block_eq {w a b i j : Nat} (hw : 0 < w) (h1 : a + w * i = b + w * j) (h2 : a = b) :
    i = j := by
  subst h2
  exact Nat.eq_of_mul_eq_mul_left hw (by omega)

/-- The data of the block of `u⁺` and its origin `N`. -/
theorem img_setup {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false) {s : List Nat}
    {n : Nat} {R : Mountain} (hrun : Official.expandDiagram s n = .ok R)
    {up : (Frame.ofMountain R).Node} {o : Origin} (hx : s.length - 1 ≤ up.1.val)
    (ho : OriginAt s n R up.1.val (up.2.val - 1) o) (hKo : K o) :
    ∃ (M : Mountain) (t : Cell) (root : Ref) (i x : Nat) (N : (Frame.ofMountain M).Node),
      Top s M t root ∧ Inv M (M.size - 1) R ∧
      x ∈ blockColumns root.column (M.size - 1) n i ∧
      up.1.val = x + (M.size - 1 - root.column) * i ∧ Frame.ref N = o.src ∧ N.1.val = x := by
  obtain ⟨M, _, t, root, hM, _, _, hTop, _, hI⟩ := run_new_column hrun up.1.isLt hx
  have ho0 := ho
  obtain ⟨M', col', t', root', x, i, es, em, hM', hcol', ht', hroot', _, hxb, hX, hes,
    _, hj⟩ := ho0
  have hMM : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  subst hMM
  have htt : t = t' := by
    have h := hTop.top
    rw [hcol'] at h
    simp only [Option.bind_some] at h
    exact Option.some.inj (h.symm.trans ht')
  subst htt
  have hrr : root = root' := Option.some.inj (hTop.left.symm.trans hroot')
  subst hrr
  have hjlt : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  obtain ⟨hsc, _, cv, hcv, _⟩ := emitsT_good hes _ (List.getElem_mem hjlt)
  rw [hej] at hcv hsc
  change Reserve.cell? M o.src = some cv at hcv
  simp only [hK o hKo, Bool.false_eq_true, if_false] at hsc
  change o.src.column = x at hsc
  obtain ⟨N, hNref, _⟩ := ControlProof.node_of_cell? hcv
  refine ⟨M, t, root, i, x, N, hTop, hI, hxb, hX, hNref, ?_⟩
  rw [← hsc, ← hNref]
  rfl

/-- **The stored left ends of `u⁺` and of the image of `c_M⁺` are in one column.** -/
theorem leftCol_of_img {K K' : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hK' : ∀ o, K' o → o.isUpper = false) {s : List Nat}
    {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root)
    (hI : Inv M (M.size - 1) R) {i : Nat} {up cp : (Frame.ofMountain R).Node} {o : Origin}
    (hup2 : 2 ≤ up.2.val) (hcp2 : 1 ≤ cp.2.val)
    (ho : OriginAt s n R up.1.val (up.2.val - 1) o) (hKo : K o)
    {N uM pM cM cMp : (Frame.ofMountain M).Node}
    (hX : up.1.val = N.1.val + (M.size - 1 - root.column) * i) (hNref : Frame.ref N = o.src)
    (huM : Real uM) (hNu : (Frame.ofMountain M).upper uM = some N)
    (hpM : (Frame.ofMountain M).rawParent uM = some pM)
    (hcMp : (Frame.ofMountain M).rawParent cM = some pM)
    (hcMu : (Frame.ofMountain M).upper cM = some cMp)
    (hcMh : (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N)
    (himg : ImgAt s n R M root i K' cp cMp) :
    ((Frame.ofMountain R).cell cp).left.map Ref.column =
      ((Frame.ofMountain R).cell up).left.map Ref.column := by
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  have hw : 0 < M.size - 1 - root.column := by have := hTop.lt; omega
  -- `π_M(N) = p_M`, and `N` is above the bottom row
  obtain ⟨N', hN', hNl⟩ := rawParent_spec hpM
  rw [hNu] at hN'
  obtain rfl := Option.some.inj hN'
  have h1N : (1 : Row) < (Frame.ofMountain M).height N := by
    obtain ⟨hc1, hc2⟩ := upper_spec hNu
    exact lt_of_le_of_lt (one_le_height hG huM)
      (ControlProof.height_lt_of_index hG hc1.symm (by omega))
  -- the stored left end of `u⁺`
  obtain ⟨i1, hupx, hupl⟩ := left_of_originAt hTop (by omega) ho (hK o hKo) hNref hNl h1N
  have hi1 : i = i1 := Eq.symm <| block_eq hw (a := N.1.val) (b := N.1.val)
    (by rw [← hupx]; exact hX) rfl
  subst hi1
  rw [hupl]
  -- the stored left end of `c⁺`
  obtain ⟨cMp', hcMu', hcMl⟩ := rawParent_spec hcMp
  rw [hcMu] at hcMu'
  obtain rfl := Option.some.inj hcMu'
  obtain ⟨hcM1, _⟩ := upper_spec hcMu
  have hpc : pM.1.val < cM.1.val := rawParent_column_lt hG hcMp
  rcases himg with ⟨hle, hc1, hc2⟩ | ⟨_, hc1, o', ho', hKo', hsrc'⟩
  · -- an old column: `c⁺` is `c_M⁺`
    have hagree : R[cp.1.val]? = M[cp.1.val]? := hI.2.1 _ (by have := hTop.lt; omega)
    obtain ⟨z, hz1, hz2, hzc⟩ := CrossUpper.twin_of_agree hagree cp rfl
    have hz : z = cMp := ControlProof.node_eq_of_index (Fin.ext (by rw [hz1, hc1]))
      (by rw [hz2, hc2])
    subst hz
    rw [← hzc, hcMl]
    simp only [Option.map_some]
    change some pM.1.val = _
    rw [CrossUpper.shiftCol_of_lt (by rw [hcM1] at hle; omega)]
  · -- a new column: the stored left end of the copy of `c_M⁺`
    have h1c : (1 : Row) < (Frame.ofMountain M).height cMp := by rw [hcMh]; exact h1N
    obtain ⟨i2, hcpx, hcpl⟩ :=
      left_of_originAt hTop hcp2 ho' (hK' o' hKo') hsrc'.symm hcMl h1c
    have hi2 : i = i2 := Eq.symm <| block_eq hw (a := cMp.1.val) (b := cMp.1.val)
      (by rw [← hcpx]; exact hc1) rfl
    subst hi2
    exact hcpl

/-- **`PosChainAt` from `PosChainImg`** for every kind of the lower part. -/
theorem posChainAt_of_img {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (h : PosChainImg K) : PosChainAt K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  obtain ⟨M, t, root, i, x, N, hTop, hI, hxb, hX, hNref, hNx⟩ :=
    img_setup hK hrun (by rw [hup1]; omega) ho hKo
  obtain ⟨uM, pM, qM, cM, cMp, huM, hNu, hpM, _, _, _, hcMp, hcMu, hcMh, c, cp, hc, hcu,
    hh, himg⟩ := h s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb
    hX N hNref
  refine ⟨c, cp, hc, hcu, hh, ?_⟩
  obtain ⟨_, hcu2⟩ := upper_spec hcu
  exact leftCol_of_img hK lowKind_notUpper hTop hI (by unfold Real at hu; omega) (by omega) ho hKo
    (by rw [hX, hNx]) hNref huM hNu hpM hcMp hcMu hcMh himg

/-! ## The main theorems -/

/-- **`CrossLexPos K` from the precise chain and `Lex`**, for every kind of the lower part. -/
theorem crossLexPos_of_img {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hC : PosChainImg K) (hL : PosLexAt K) : CrossLexPos K :=
  crossLexPos_of_at (posChainAt_of_img hK hC) hL

/-- **`CrossLexFor IsPlain`** from `PosChainImg IsPlain` and `PosLexAt IsPlain`. -/
theorem crossLexFor_plain_of_img (hC : PosChainImg IsPlain) (hL : PosLexAt IsPlain) :
    CrossLexFor IsPlain :=
  CrossPlain.crossLexFor_plain_of_pos (crossLexPos_of_img CrossPlain.isPlain_notUpper hC hL)

/-- **`CrossLexFor IsClean`** from `PosChainImg IsClean` and `PosLexAt IsClean`. -/
theorem crossLexFor_clean_of_img (hC : PosChainImg IsClean) (hL : PosLexAt IsClean) :
    CrossLexFor IsClean :=
  CrossPlain.crossLexFor_clean_of_pos (crossLexPos_of_img CrossPlain.isClean_notUpper hC hL)

/-! ## `PosChainImg` from the cross case of `M(s)` and the image in the output -/

/-- **Open.** In the setting of `CrossLexPos K`, the origin `N` of `u⁺` is above a real node
`u_M` of `M(s)`, and `M(s)` is in the cross case at `u_M`. -/
def PosCrossM (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∀ (M : Mountain) (t : Cell) (root : Ref) (i x : Nat), Top s M t root →
        x ∈ blockColumns root.column (M.size - 1) n i →
        up.1.val = x + (M.size - 1 - root.column) * i →
        ∀ N : (Frame.ofMountain M).Node, Frame.ref N = o.src →
        ∃ uM pM qM : (Frame.ofMountain M).Node, Real uM ∧
          (Frame.ofMountain M).upper uM = some N ∧
          (Frame.ofMountain M).rawParent uM = some pM ∧ (Frame.ofMountain M).Q uM = some qM ∧
          qM.1 ≠ pM.1

/-- **Open.** In the setting of `CrossLexPos K`, for the cross case of `M(s)` at the node
`u_M` below the origin `N` of `u⁺` and its chain `q_M → … → c_M` (`π_M(c_M⁺) = p_M`), the
chain of the output from `q` reaches a node `c` whose upper node is the image of `c_M⁺` and
has the row of `u⁺`. -/
def PosImgR (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∀ (M : Mountain) (t : Cell) (root : Ref) (i x : Nat), Top s M t root →
        x ∈ blockColumns root.column (M.size - 1) n i →
        up.1.val = x + (M.size - 1 - root.column) * i →
        ∀ N uM pM qM cM cMp : (Frame.ofMountain M).Node, Frame.ref N = o.src → Real uM →
          (Frame.ofMountain M).upper uM = some N →
          (Frame.ofMountain M).rawParent uM = some pM → (Frame.ofMountain M).Q uM = some qM →
          qM.1 ≠ pM.1 → RawChain (Frame.ofMountain M) qM cM →
          (Frame.ofMountain M).rawParent cM = some pM →
          (Frame.ofMountain M).upper cM = some cMp →
          ∃ c cp : (Frame.ofMountain R).Node, RawChain (Frame.ofMountain R) q c ∧
            (Frame.ofMountain R).upper c = some cp ∧
            (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up ∧
            ImgAt s n R M root i LowKind cp cMp

/-- **`PosChainImg` from `PosCrossM` and `PosImgR`.** The chain of `M(s)` and the row
`row c_M⁺ = row N` come from the normality of `M(s)` (`normal_chain_exists`,
`normal_crossLex`). -/
theorem posChainImg_of_parts {K : Origin → Prop} (hX : PosCrossM K) (hI : PosImgR K) :
    PosChainImg K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq N hN
  obtain ⟨uM, pM, qM, huM, hNu, hpM, hqM, hne⟩ :=
    hX s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq N hN
  have hNM : (Frame.ofMountain M).Normal :=
    build_normal_of_legal (build_success_legal hTop.build) hTop.build
  have hne' : qM ≠ pM := fun h => hne (by rw [h])
  obtain ⟨cM, hcM, hcMp⟩ := CrossPlain.normal_chain_exists hNM huM hpM hqM hne'
  obtain ⟨cMp, hcMu, _⟩ := rawParent_spec hcMp
  obtain ⟨_, hrow, _⟩ := CrossPlain.normal_crossLex hNM huM hNu hpM hqM hcM hcMp hcMu
  obtain ⟨c, cp, hc, hcu, hh, himg⟩ :=
    hI s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq
      N uM pM qM cM cMp hN huM hNu hpM hqM hne hcM hcMp hcMu
  exact ⟨uM, pM, qM, cM, cMp, huM, hNu, hpM, hqM, hne, hcM, hcMp, hcMu, hrow.symm,
    c, cp, hc, hcu, hh, himg⟩

/-- **`CrossLexFor IsPlain`** from `PosCrossM`, `PosImgR` and `PosLexAt` for `IsPlain`. -/
theorem crossLexFor_plain_of_parts (hX : PosCrossM IsPlain) (hI : PosImgR IsPlain)
    (hL : PosLexAt IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_plain_of_img (posChainImg_of_parts hX hI) hL

/-- **`CrossLexFor IsClean`** from `PosCrossM`, `PosImgR` and `PosLexAt` for `IsClean`. -/
theorem crossLexFor_clean_of_parts (hX : PosCrossM IsClean) (hI : PosImgR IsClean)
    (hL : PosLexAt IsClean) : CrossLexFor IsClean :=
  crossLexFor_clean_of_img (posChainImg_of_parts hX hI) hL

/-! ## `PosCrossM` from the shape of one copied column -/

/-- **Open (one column).** In a new column `X = x + w·i`, `i ≥ 1`, every emit `k ≥ 1` whose
origin `N` has kind `K` has `N` above the bottom row, and the emit `k - 1` has the origin
`N⁻`, the node below `N`. -/
def BelowSrc (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es →
    ∀ k (hk : k < es.length), 0 < k → K es[k].2 →
      2 ≤ es[k].2.src.index ∧
        es[k - 1].2.src = ⟨es[k].2.src.column, es[k].2.src.index - 1⟩

/-- The data of `OriginAt` in a known block. -/
theorem originAt_unpack {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i x X j : Nat} {o : Origin}
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = x + (M.size - 1 - root.column) * i) (hXgt : M.size - 1 < X)
    (ho : OriginAt s n R X j o) :
    0 < i ∧ ∃ es em colX,
      emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (Official.official t.row) = .ok es ∧ R[X]? = some colX ∧
      assemble (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (es.map Prod.fst) = .ok colX ∧ es[j]? = some (em, o) := by
  obtain ⟨M', col', t', root', x', i', es, em, hM', hcol', ht', hroot', _, hxb', hX', hes,
    ⟨colX, hRX, _, hasm⟩, hj⟩ := ho
  have hMM : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  subst hMM
  have htt : t = t' := by
    have h := hTop.top
    rw [hcol'] at h
    simp only [Option.bind_some] at h
    exact Option.some.inj (h.symm.trans ht')
  subst htt
  have hrr : root = root' := Option.some.inj (hTop.left.symm.trans hroot')
  subst hrr
  have hcr := hTop.lt
  have hpos : ∀ {a b}, a ∈ blockColumns root.column (M.size - 1) n b →
      X = a + (M.size - 1 - root.column) * b → 0 < b := by
    intro a b ha hXa
    by_contra h0
    have hb0 : b = 0 := by omega
    subst hb0
    simp [blockColumns] at ha
    omega
  have hi := hpos hxb hX
  have hi' := hpos hxb' hX'
  obtain ⟨h1, h2⟩ := mem_blockColumns hcr hxb
  obtain ⟨h1', h2'⟩ := mem_blockColumns hcr hxb'
  have hdec := CrossUpper.decomp_eq (w := M.size - 1 - root.column) (a := x - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      generalize (M.size - 1 - root.column) * i = P at hX ⊢
      generalize (M.size - 1 - root.column) * i' = Q at hX' ⊢
      omega)
  have hxx : x = x' := by omega
  obtain ⟨_, rfl⟩ := hdec
  subst hxx
  exact ⟨hi, es, em, colX, hes, hRX, hasm, hj⟩

/-- **`PosCrossM` from `BelowSrc`**, for every kind of the lower part. The node `u` below
`u⁺` is emitted from `u_M = N⁻`, so the stored left ends of `u` and `u⁺` are the images
(under `shiftCol c_r w i`) of the columns of the left ends of `u_M` and `N`; the cross case
of the output at `u` is the cross case of `M(s)` at `u_M`. -/
theorem posCrossM_of_belowSrc {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hB : BelowSrc K) : PosCrossM K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq N hN
  obtain ⟨_, _, _, _, hBR⟩ := run_basic hrun
  have hF := hBR.valid.toOrdered
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  have hMs := Canonical.build_size hTop.build
  have hcr := hTop.lt
  set w := M.size - 1 - root.column with hw
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hXgt : M.size - 1 < up.1.val := by rw [hup1]; omega
  obtain ⟨hi0, es, em, colX, hes, hRX, hasm, hj⟩ := originAt_unpack hTop hxb hXeq hXgt ho
  obtain ⟨hxc, hxle⟩ := mem_blockColumns hcr hxb
  have hjlt : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  have hk0 : 0 < up.2.val - 1 := by unfold Real at hu; omega
  have hes' := hes
  rw [hXeq] at hes'
  obtain ⟨h2, hsrc⟩ := hB s n R hrun M t root hTop i x hi0 hxb es hes' (up.2.val - 1) hjlt hk0
    (by rw [hej]; exact hKo)
  rw [hej] at h2 hsrc
  simp only at h2 hsrc
  -- the node `u_M` below `N`
  have hNi : N.2.val = o.src.index := by rw [← hN]; rfl
  have hNc : N.1.val = o.src.column := by rw [← hN]; rfl
  have hlenN : N.2.val - 1 < (Frame.ofMountain M).length N.1 := by
    have := N.2.isLt
    omega
  let uM : (Frame.ofMountain M).Node := ⟨N.1, ⟨N.2.val - 1, hlenN⟩⟩
  have huM : Real uM := by show 0 < N.2.val - 1; omega
  have hNu : (Frame.ofMountain M).upper uM = some N :=
    ControlProof.upper_eq_of_index rfl (by show N.2.val = N.2.val - 1 + 1; omega)
  have hlow : (Frame.ofMountain M).height uM < (Frame.ofMountain M).height N :=
    ControlProof.height_lt_of_index hG rfl (by show N.2.val - 1 < N.2.val; omega)
  have h1N : (1 : Row) < (Frame.ofMountain M).height N :=
    lt_of_le_of_lt (one_le_height hG huM) hlow
  -- the stored left end of `N` and `p_M`
  obtain ⟨_, _, cv, hcv, hleg⟩ := emitsT_good hes _ (List.getElem_mem hjlt)
  rw [hej] at hcv hleg
  change Reserve.cell? M o.src = some cv at hcv
  have hcvN : cv = (Frame.ofMountain M).cell N := by
    have e := ControlProof.cell?_ref N
    rw [hN, hcv] at e
    exact Option.some.inj e
  subst hcvN
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell N).left = some l := by
    rcases hleg with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
    · exact ⟨l, hl⟩
    · exact absurd h0 (official_ne_zero_of_one_lt h1N)
  obtain ⟨pM, hpMl, _, _⟩ := hG.stored_valid N l hl
  have hpMr : Frame.ref pM = l := lookup_spec hpMl
  have hNl : ((Frame.ofMountain M).cell N).left = some (Frame.ref pM) := by rw [hpMr]; exact hl
  have hpM : (Frame.ofMountain M).rawParent uM = some pM := rawParent_eq_of_upper_left hNu hNl
  -- the column of `p`
  obtain ⟨i1, hupx, hupl⟩ := left_of_originAt hTop (by omega) ho (hK o hKo) hN hNl h1N
  have hsrcx : N.1.val = x := by
    obtain ⟨hsc, _⟩ := emitsT_good hes _ (List.getElem_mem hjlt)
    rw [hej] at hsc
    simp only [hK o hKo, Bool.false_eq_true, if_false] at hsc
    change o.src.column = x at hsc
    rw [hNc, hsc]
  have hi1 : i = i1 := Eq.symm <| block_eq (w := w) (by omega) (a := N.1.val) (b := N.1.val)
    (by rw [← hupx, hsrcx]; exact hXeq) rfl
  subst hi1
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  rw [hpl] at hupl
  have hpcol : p.1.val = shiftCol root.column w i pM.1.val := Option.some.inj hupl
  -- the emit of `u` and the stored left end of `u_M`
  have hk1 : up.2.val - 1 - 1 < es.length := by omega
  obtain ⟨_, _, cv', hcv', hleg'⟩ := emitsT_good hes _ (List.getElem_mem hk1)
  have hsrcu : es[up.2.val - 1 - 1].2.src = Frame.ref uM := by
    refine hsrc.trans ?_
    show (⟨o.src.column, o.src.index - 1⟩ : Ref) = ⟨N.1.val, N.2.val - 1⟩
    rw [hNc, hNi]
  change Reserve.cell? M es[up.2.val - 1 - 1].2.src = some cv' at hcv'
  rw [hsrcu, ControlProof.cell?_ref uM] at hcv'
  obtain rfl := Option.some.inj hcv'
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcell, _, ref, href, hrefc⟩ := hcells (up.2.val - 1 - 1) (by simpa using hk1)
  have hucell : (Frame.ofMountain R).cell u = cell := by
    refine frame_cell_of (by rw [← hup1]; exact hRX) ?_
    rw [show u.2.val = up.2.val - 1 - 1 + 1 by omega]
    exact hcell
  -- the left end `l'` of `u_M`, and the column of the left end of `u`
  obtain ⟨l', hl', hucol⟩ : ∃ l' : Ref, ((Frame.ofMountain M).cell uM).left = some l' ∧
      ref.column = shiftCol root.column w i l'.column := by
    rw [hrefc]
    simp only [List.getElem_map]
    rcases hleg' with ⟨l', hl', hlc'⟩ | ⟨hnone, h0, _⟩
    · refine ⟨l', hl', ?_⟩
      simp only [legColumn, hlc']
      rfl
    · -- `u_M` is the bottom node: its left end is in the column `x - 1`
      have hidx : N.2.val - 1 = 1 := by
        by_contra hne
        have hb : 1 < (Frame.ofMountain M).length N.1 := by
          have := hG.length_ge_two N.1
          omega
        let b1 : (Frame.ofMountain M).Node := ⟨N.1, ⟨1, hb⟩⟩
        have hlt : (Frame.ofMountain M).height b1 < (Frame.ofMountain M).height uM :=
          ControlProof.height_lt_of_index hG rfl (by show 1 < N.2.val - 1; unfold Real at huM; omega)
        have hb1 : (Frame.ofMountain M).height b1 = 1 := hG.bottom_row N.1 hb
        rw [hb1] at hlt
        exact official_ne_zero_of_one_lt hlt h0
      have hbl := bottom_left hTop.build (ControlProof.cell?_ref uM) (by exact hidx)
        (by show N.1.val ≠ 0; omega)
      refine ⟨_, hbl, ?_⟩
      simp only [legColumn, hnone]
      show (R.extract 0 up.1.val).size - 1 = _
      rw [Array.size_extract, CrossUpper.shiftCol_of_le (by show root.column ≤ N.1.val - 1; omega)]
      have := up.1.isLt
      change up.1.val < R.size at this
      simp only [Nat.sub_zero, Nat.min_eq_left this.le]
      show up.1.val - 1 = N.1.val - 1 + w * i
      omega
  -- `q_M`, and the cross case of `M(s)`
  obtain ⟨qM, hqM⟩ := Q_exists_of_left hG ⟨l', hl'⟩
  refine ⟨uM, pM, qM, huM, hNu, hpM, hqM, ?_⟩
  obtain ⟨leftM, hleftM, _, _, hqM1, _⟩ := Q_spec hG hqM
  obtain ⟨leftR, hleftR, _, _, hq1, _⟩ := Q_spec hF hq
  rw [hucell, href] at hleftR
  have hlr : ref = Frame.ref leftR := Option.some.inj hleftR
  have hll : l' = Frame.ref leftM := Option.some.inj (hl'.symm.trans hleftM)
  have hqcol : q.1.val = shiftCol root.column w i qM.1.val := by
    rw [hq1, hqM1]
    show leftR.1.val = shiftCol root.column w i leftM.1.val
    have e1 : leftR.1.val = ref.column := by rw [hlr]; rfl
    have e2 : leftM.1.val = l'.column := by rw [hll]; rfl
    rw [e1, e2, hucol]
  intro hqp
  apply hcol
  apply Fin.ext
  rw [hqcol, hpcol, hqp]

theorem posChainImg_of_belowSrc {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hB : BelowSrc K) (hI : PosImgR K) : PosChainImg K :=
  posChainImg_of_parts (posCrossM_of_belowSrc hK hB) hI

/-- **`CrossLexFor IsPlain`** from `BelowSrc`, `PosImgR` and `PosLexAt` for `IsPlain`. -/
theorem crossLexFor_plain_of_below (hB : BelowSrc IsPlain) (hI : PosImgR IsPlain)
    (hL : PosLexAt IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_plain_of_img (posChainImg_of_belowSrc CrossPlain.isPlain_notUpper hB hI) hL

/-- **`CrossLexFor IsClean`** from `BelowSrc`, `PosImgR` and `PosLexAt` for `IsClean`. -/
theorem crossLexFor_clean_of_below (hB : BelowSrc IsClean) (hI : PosImgR IsClean)
    (hL : PosLexAt IsClean) : CrossLexFor IsClean :=
  crossLexFor_clean_of_img (posChainImg_of_belowSrc CrossPlain.isClean_notUpper hB hI) hL

end OmegaY.Official.Recon.CrossPlainPos

#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexPos_of_at
#print axioms OmegaY.Official.Recon.CrossPlainPos.posChainAt_of_img
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_of_img
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_of_img
#print axioms OmegaY.Official.Recon.CrossPlainPos.posChainImg_of_parts
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_of_parts
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_of_parts
#print axioms OmegaY.Official.Recon.CrossPlainPos.posCrossM_of_belowSrc
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_of_below
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_of_below
