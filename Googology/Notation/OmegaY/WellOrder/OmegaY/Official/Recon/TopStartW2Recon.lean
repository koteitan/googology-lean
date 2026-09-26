/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/TopStartW2Recon.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.FinalStageE
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartW2

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The plain and clean parent chains with the weaker start `TopStart''`

`TopStartFixRecon.lean` and `RPLRoot.lean` start the simulation of the chain of `M(s)` by
`QStand K` (`CrossPlainPosSim.lean`): the candidate `q = Q u` stands for `q_M = Q z` in the
sense of `CrossUpperSim.Cp`, which asks the **top copy** right of `c_r`. `QStand IsPlain` is
**false**: for `s = (1,4,18,56,18)`, `n = 1` (JS indices), the plain top copy `u = (6,5)` of
`z = (3,4)` (row `ω`), `u⁺ = (6,6)` a plain copy of `N = (3,5)` (row `ω² < τ`), has
`q = (5,4)`, the clean copy of `q_M = (2,3)`, below the gap copy `(5,5)` of `(2,3)`
(`reference/official/cross-plain-pos-sim.cjs`: `QCp plain qM >cr false`). The targets hold on
this input. So the start is weakened.

## The weak start

`CpW i Z z`: `Cp i Z z`, or `z` is right of `c_r` and `Z` is a non-gap copy of `z` (`CopyNode`)
that is not its top copy (`NonTopCopy`). `QStandW K` is `QStand K` with `CpW`.
**`qStandW_of_topStart'' : TopStart'' → BelowSrc K → QStandW K`** (proved; `TopStart''` is
proved in `TopStartW2.lean`).

## The chain after a non-top start

* `NonTopPass` (**proved**, `nonTopPass_holds`): for a non-top non-gap copy `Z` of `z` (right of
  `c_r`, block `i ≥ 1`) and a node `c` of the chain of stored parents of `M(s)` from `z` that is
  left of `c_r`, or in `c_r` with its upper node below `τ`, the chain of stored parents of `R`
  from `Z` passes through the node `c` itself (the columns left of `x₀` are shared). It holds
  for every copy: `ChainOK` (`Seam.chainOK_of_step` with the proved steps `stepBlock0`,
  `stepUpper`, `stepTop`, `stepCleanNT`, `stepX0Top`, `CPN.stepCutNT`) for `c` left of `c_r`,
  and `PassOK` (`Seam.Pass.passOK_all` with `CPN.cutParentNT`) for `c` in `c_r`.
* `NoEndRight K` (**proved** in `TopStartW2NoEnd.lean`, `TSQ.W2.noEndRight_holds`): in the
  setting of `QStandW K`, if `Q u` is a non-top non-gap copy of `a = Q z`, then every node `c_M`
  of the chain of stored parents of `M(s)` from `a` whose stored parent is the stored parent `p_M`
  of `z` is at or left of `c_r`. (If `c_M` were right of `c_r`, `p_M = P(z)` would lie on the
  path of numerical parents from `a` to `g = (c_r, row a)`, so `v(g) < v(z)`; then the column of
  `z` passes the ascension test and `Q u` is the top copy of `a`.)

## Results

* `posImgR_of_simW : CopyTop → CopyStepLower → QStandW K → NonTopPass → NoEndRight K →
  PairAbove K → PairOld K → RootPass K → PosImgR K` (the non-top start goes directly to the end
  through `NonTopPass`);
* `rootPass_plain_of_qStandW : CopyStepLower → QStandW IsPlain → NonTopPass → SeamStep →
  SeamStart → RootPass IsPlain`;
* **`rootPass_plain'' : RootPass IsPlain`** (no hypothesis);
* `crossLexFor_plain'' : NoEndRight IsPlain → CrossLexFor IsPlain`;
* `crossLexFor_clean'' : NoEndRight IsClean → CrossLexFor IsClean`
  (everything else proved: `TopStep`, `TopStart''`, `CutParentNT`, `CopyCountLe`, package 4;
  with `NoEndRight` both hold outright, `TopStartW2Final.lean`).

## Numerical checks (timeout 60 s each)

Scratch harnesses derived from `reference/official/cross-plain-pos-sim.cjs`; inputs: the sample
files `known-counterexamples`, `legbelowtop-bad64`, `tsq-counterexamples`, `s1`, `s2`, `s3`,
`s6`, the inputs `(1,4,18,56,18)`, `(1,21,5,20,59,20)`, and all legal sequences of length `≤ 6`
with entries `≤ 8` (`n = 1, 2`, outputs of at most 400 nodes).

* `QStandW`: no failure (the cross cases and all other nodes); the chain simulation over `CpW`
  and its end: no failure.
* The chain from a non-top clean copy: 80918 such copies (legal inputs) and 684 (sample files);
  it passes every node of the chain of `M(s)` in `c_r` itself (80582 and 435 instances; for 231
  and 24 of them no `Cp` stand-in is passed, e.g. `(1,1,1,3,8,8)[1]`, `Z = (6,1)`, `c = (3,1)`)
  and every node left of `c_r`.
* `NoEndRight`: no failure; the hypothesis is rare: 6 instances, all for `K` plain and all in
  `(1,4,18,56,18)[n]`, `n = 1, 2, 3`; none among the legal inputs; none for `K` clean.
-/

namespace OmegaY.Official.Recon.TopStartW2R

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim
open LowerChainRecon
open CrossPlainPos (BelowSrc QStand PairAbove PairOld RootPass EmitBelow CleanFirst LexImg
  PosImgR)
open Classification.Proofs.ChainCorr.LowerChain (TopStep IsTopAt above TopNode Rel)
open Classification.Proofs.ChainCorr (CopyNode)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopStartW2 (TopStart'' StandQ)
open TopStartFixRecon (srcRow_lt_of_not_upper hasAboveLow_of_upper)
open Classification.ControlProof (height_lt_of_index node_eq_of_index)

/-! ## Definitions -/

/-- `Z` is a non-gap copy (`CopyNode`) of the node `z` right of `c_r` that is not the top copy
of `z` in its column. -/
def NonTopCopy (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (Z : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node) : Prop :=
  root.column < z.1.val ∧ z.1.val < M.size - 1 ∧
    CopyNode M R n root.column (M.size - 1) (Official.official t.row) i (Frame.ref Z)
      (Frame.ref z) ∧
    ¬ TopCopy s n R M Z z

/-- **The weak stand-in relation**: `Cp`, or a non-top non-gap copy right of `c_r`. -/
def CpW (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (Z : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node) : Prop :=
  Cp s n R M t root i Z z ∨ NonTopCopy s n R M t root i Z z

/-- **The weak start** (`QStand K` with `CpW`). For a real node `u` of a new column `x + w·i`
(`i ≥ 1`) whose upper node `u⁺` has an origin of kind `K` with the source `N`, and the node `z`
below `N`: `Q u` stands for `Q z` in the sense of `CpW`. -/
def QStandW (K : Origin → Prop) : Prop :=
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
      CpW s n R M t root i A a

/-- **(proved: `nonTopPass_holds`).** For a non-top non-gap copy `Z` of `z` (right of `c_r`,
block `i ≥ 1`) and a node `c` of the chain of stored parents of `M(s)` from `z` that is left of
`c_r`, or in `c_r` with its upper node below `τ`, the chain of stored parents of `R` from `Z`
passes through the node `c` itself. (It holds for every copy; `¬ TopCopy` is not used.) -/
def NonTopPass : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i → i ≤ n →
    ∀ (Z : (Frame.ofMountain R).Node) (z c : (Frame.ofMountain M).Node),
      NonTopCopy s n R M t root i Z z → RawChain (Frame.ofMountain M) z c →
      (c.1.val < root.column ∨ (c.1.val = root.column ∧
        ∃ c', (Frame.ofMountain M).upper c = some c' ∧ (Frame.ofMountain M).height c' < t.row)) →
      ∃ C, RawChain (Frame.ofMountain R) Z C ∧ C.1.val = c.1.val ∧ C.2.val = c.2.val

/-- **(proved in `TopStartW2NoEnd.lean`).** In the setting of `QStandW K`: if `Q u` is a non-top
non-gap copy of
`a = Q z`, then every node `c_M` of the chain of stored parents of `M(s)` from `a` whose stored
parent is the stored parent `p_M` of `z` is at or left of `c_r`. -/
def NoEndRight (K : Origin → Prop) : Prop :=
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
      NonTopCopy s n R M t root i A a →
    ∀ pM cM : (Frame.ofMountain M).Node, (Frame.ofMountain M).rawParent z = some pM →
      RawChain (Frame.ofMountain M) a cM → (Frame.ofMountain M).rawParent cM = some pM →
      cM.1.val ≤ root.column

/-! ## `StandQ` gives `CpW` -/

/-- **`StandQ` gives `CpW`** (for a node `a` below `τ`). -/
theorem cpW_of_standQ {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {A : (Frame.ofMountain R).Node} {a : (Frame.ofMountain M).Node}
    (hax : a.1.val < M.size - 1) (hlow : (Frame.ofMountain M).height a < t.row)
    (hS : StandQ M R n root.column (M.size - 1) (Official.official t.row) t.row i (Frame.ref A)
      (Frame.ref a)) :
    CpW s n R M t root i A a := by
  by_cases hg : root.column < a.1.val
  · rcases hS.2.2 hg with hC | hT
    · by_cases hTC : TopCopy s n R M A a
      · left
        have hAc := Classification.Proofs.ChainCorr.copyNode_column hC
        have hg' : root.column ≤ (Frame.ref a).column := hg.le
        rw [Classification.Proofs.ChainCorr.mapColumn_of_ge hg'] at hAc
        exact Or.inr (Or.inr ⟨hg, hax, hAc, fun hθ => absurd hθ (not_le.mpr hlow),
          fun _ => hTC⟩)
      · exact Or.inr ⟨hg, hax, hC, hTC⟩
    · exact Or.inl (cp_of_stand E hi1 hin hax (TopStartFixParts.stand_of_right hg hT))
  · exact Or.inl (cp_of_stand E hi1 hin hax ⟨hS.1, hS.2.1, fun h => absurd h hg⟩)

/-! ## The weak start from `TopStart''` -/

/-- **`QStandW K` from `TopStart''` and `BelowSrc K`.** -/
theorem qStandW_of_topStart'' {K : Origin → Prop} (hTSt : TopStart'') (hB : BelowSrc K)
    (hK : ∀ o, K o → o.isUpper = false) : QStandW K := by
  intro s n R hrun M t root hTop i x hi0 hxb u up o hu hup hupc ho hKo z N hN hz hzN a A ha hA
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc' : up.1.val = u.1.val := congrArg Fin.val hup1
  have E := env_of hrun hTop up.1.isLt (by rw [hupc]; omega)
  have hG := E.G
  have hF := E.FR
  have hV := build_valid_of_success hTop.build
  have hin : i ≤ n := block_le E hxg hxl (by rw [← hupc]; exact up.1.isLt) (by omega)
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hxb hupc ho
  set k := up.2.val - 1 with hkdef
  have hkl : k < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hek : es[k] = (em, o) := by
    rw [List.getElem?_eq_getElem hkl] at hjo
    exact Option.some.inj hjo
  have hk0 : 0 < k := by unfold Real at hu; omega
  have hes' : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
    rw [← hupc]; exact hes
  obtain ⟨h2, hbelow⟩ := hB s n R hrun M t root hTop i x hi0 hxb es hes' k hkl hk0
    (by rw [hek]; exact hKo)
  have hsrcN : es[k].2.src = Frame.ref N := by rw [hek]; exact hN.symm
  have hsrcz : es[k - 1].2.src = Frame.ref z := by
    rw [hbelow, hsrcN]
    obtain ⟨hz1, hz2⟩ := upper_spec hzN
    simp only [Frame.ref, hz1, hz2]
    congr 1
  have hIT := isTopAt_of_above hV (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
    (M.size - 1) up.1.val) rfl hes hkl hk0 hbelow h2
  have hjl : k - 1 < es.length := by omega
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcz] at hcz
  obtain ⟨hvcol, _, cv', hcv', hleft⟩ := emitsT_good hes es[k - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, hlow⟩
    · exact ⟨l, hl⟩
    · have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcz]; exact hz) h0
      rw [hlow] at hvcol
      simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hvcol]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop (by omega) hxb hupc hes hRX hasm hjl hcz hl
  have hcuU : Reserve.cell? R ⟨up.1.val, k - 1 + 1⟩ = some ((Frame.ofMountain R).cell u) := by
    have := cell?_ref u
    rwa [show (Frame.ref u : Ref) = ⟨up.1.val, k - 1 + 1⟩ by
      simp only [Frame.ref, hupc']; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell u := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hpe := Q_eq_highestAtMost hF hu hA href
  rw [hrefc] at hpe
  have hNτ : (Frame.ofMountain M).height N < t.row := by
    obtain ⟨cN, hcN, hNlt⟩ := srcRow_lt_of_not_upper E (by omega) hin hxb
      (by rw [← hupc]; exact up.1.isLt) hes' hkl (by rw [hek]; exact hK o hKo)
    rw [hsrcN, LowerChainRecon.cell?_ref N] at hcN
    rw [← Option.some.inj hcN] at hNlt
    exact hNlt
  have hab : HasAboveLow M t.row es[k - 1].2.src := by
    rw [hsrcz]
    exact hasAboveLow_of_upper hzN hNτ
  have hS := (hTSt s n R M t root i x hrun hTop hi0 hin hxb es hes' (k - 1) hjl hIT
    ((Frame.ofMountain R).cell u) ((Frame.ofMountain M).cell z) l (Frame.ref A) (Frame.ref a)
    (by rw [← hupc]; exact hcuU) hcz hl hpa hpe).2 hab
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, _, hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    have hz1 : z.1.val < M.size := z.1.isLt
    rw [hql]
    omega
  have hzτ : (Frame.ofMountain M).height z < t.row := by
    obtain ⟨hz1, hz2⟩ := upper_spec hzN
    exact lt_trans (height_lt_of_index hG hz1.symm (by omega)) hNτ
  have haz : (Frame.ofMountain M).height a ≤ (Frame.ofMountain M).height z := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := Frame.Q_spec hG ha
    exact h
  exact cpW_of_standQ E (by omega) hin hax (lt_of_le_of_lt haz hzτ) hS


/-- **`PosImgR K` with the weak start.** -/
theorem posImgR_of_simW {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hCT : CopyTop) (hSL : CopyStepLower) (hQ : QStandW K) (hNTP : NonTopPass)
    (hNE : NoEndRight K) (hPA : PairAbove K) (hPO : PairOld K) (hRP : RootPass K) :
    PosImgR K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hXeq
    N uM pM qM cM cMp hN huM hNu hpM hqM hne hcM hcMp hcMu
  have hMs := Canonical.build_size hTop.build
  have hcr := hTop.lt
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc : up.1.val = u.1.val := congrArg Fin.val hup1
  have hXgt : M.size - 1 < up.1.val := by omega
  obtain ⟨hi0, _⟩ := CrossPlainPos.originAt_unpack hTop hxb hXeq hXgt ho
  have hXR : up.1.val < R.size := up.1.isLt
  have E := env_of hrun hTop hXR hXgt.le
  have hG := E.G
  obtain ⟨hxc, hxle⟩ := mem_blockColumns hcr hxb
  have hin : i ≤ n := block_le E hxc hxle (by rw [← hXeq]; exact hXR) (by rw [← hXeq]; omega)
  -- the columns of `M(s)`
  have hNx : N.1.val = x := CrossPlainPos.src_column hK hTop hxb hXeq hXgt ho hKo hN
  obtain ⟨hN1, _⟩ := upper_spec hNu
  have huMx : uM.1.val = x := by rw [← hNx, hN1]
  have hqMr : Real qM := Q_real hG huM hqM
  have hqMlt : qM.1.val < uM.1.val := Q_column_lt hG hqM
  have hcMle : cM.1.val ≤ qM.1.val := hcM.column_le hG
  have hqMx : qM.1.val < M.size - 1 := by omega
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
  -- the start: a stand-in (`Cp`), or a non-top non-gap copy
  rcases hQ s n R hrun M t root hTop i x hi0 hxb u up o hu hup hXeq ho hKo uM N hN huM hNu qM q
    hqM hq with hstart | hnt
  swap
  · -- a non-top copy: the end is at or left of `c_r`, and the chain passes through `c_M`
    have hcMr : cM.1.val ≤ root.column := hNE s n R hrun M t root hTop i x hi0 hxb u up o hu hup
      hXeq ho hKo uM N hN huM hNu qM q hqM hq hnt pM cM hpM hcM hcMp
    have hNτ : (Frame.ofMountain M).height N < t.row := by
      obtain ⟨_, es, em, colX, hes, hRX, hasm, hjo⟩ :=
        CrossPlainPos.originAt_unpack hTop hxb hXeq hXgt ho
      have hkl : up.2.val - 1 < es.length := by
        by_contra hn
        rw [List.getElem?_eq_none (by omega)] at hjo
        cases hjo
      have hek : es[up.2.val - 1] = (em, o) := by
        rw [List.getElem?_eq_getElem hkl] at hjo
        exact Option.some.inj hjo
      obtain ⟨cv, hcv, hlt⟩ := Pk4.below_of_notUpper hes (List.getElem_mem hkl)
        (by rw [hek]; exact hK o hKo)
      have hcvN : cv = (Frame.ofMountain M).cell N := by
        have h1 := LowerChainRecon.cell?_ref N
        rw [hN] at h1
        have h2 : Reserve.cell? M o.src = some cv := by
          have h3 := hcv
          rw [hek] at h3
          exact h3
        exact Option.some.inj (h2.symm.trans h1)
      subst hcvN
      by_contra hn
      push Not at hn
      exact absurd (official_mono hTop.row_one_le hn) (not_le.mpr hlt)
    have hcM' : cM.1.val < root.column ∨ (cM.1.val = root.column ∧
        ∃ c', (Frame.ofMountain M).upper cM = some c' ∧
          (Frame.ofMountain M).height c' < t.row) := by
      rcases Nat.lt_or_eq_of_le hcMr with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, cMp, hcMu, ?_⟩
        rw [← hrow]
        exact hNτ
    obtain ⟨c, hqc, hc1, hc2⟩ := hNTP s n R M t root i hrun hTop hi0 hin q qM cM hnt hcM hcM'
    obtain ⟨cp, hcu, hcp1, hcp2, hcph⟩ := CrossPlainPos.old_end E (by omega) hc1 hc2 hcMu
    have hro := hPO s n R hrun M t root hTop i x hi0 hxb up o hXeq hup1' ho hKo N cMp hN hleft
      hrow hBN (by omega) hlexM
    refine ⟨c, cp, hqc, hcu, ?_, Or.inl ⟨by omega, hcp1, hcp2⟩⟩
    rw [hcph, ← hrow, hro]
  -- the simulation of the chain
  obtain ⟨C, hqC, hCC⟩ := cp_chain E hCT hSL hi0 hin hcM hqMr hqMx hstart
  -- the end, by the column of `c_M`
  rcases Nat.lt_trichotomy root.column cM.1.val with hgt | heq | hlt
  · -- right of `c_r`: the node above the stand-in of `c_M`
    obtain ⟨C', hCu, hC'h, o', ho', hKo', hsrc'⟩ := hPA s n R hrun M t root hTop i x hi0 hxb up o
      hXeq hup1' ho hKo N cMp cM hN hleft hrow (by omega) (by omega) hlexM hcMu C hCC
    refine ⟨C, C', hqC, hCu, hC'h, Or.inr ⟨by omega, ?_, o', ho', hKo', hsrc'⟩⟩
    obtain ⟨hC'1, _⟩ := upper_spec hCu
    have hCcol := hCC.column
    rw [CrossUpper.shiftCol_of_le hgt.le] at hCcol
    rw [congrArg Fin.val hC'1, hCcol, hcMpc]
  · -- in `c_r`: the chain passes through `c_M` itself
    obtain ⟨c, hCc, hc1, hc2⟩ := hRP s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root
      i x hTop hxb hXeq N uM pM qM cM hN huM hNu hpM hqM hne hcM hcMp heq.symm C hqC hCC
    obtain ⟨cp, hcu, hcp1, hcp2, hcph⟩ := CrossPlainPos.old_end E (by omega) hc1 hc2 hcMu
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
    obtain ⟨z, hz1, hz2, hzc⟩ := CrossUpper.twin_of_agree (E.agree _ (by omega)) C hC.1
    have hzh : (Frame.ofMountain M).height z = (Frame.ofMountain M).height cM := by
      rw [← hC.2]
      show ((Frame.ofMountain M).cell z).row = ((Frame.ofMountain R).cell C).row
      rw [hzc]
    have hzc' : z = cM := CrossUpper.node_eq_of_height hG (Fin.ext (by rw [hz1])) hzh
    subst hzc'
    obtain ⟨cp, hcu, hcp1, hcp2, hcph⟩ := CrossPlainPos.old_end E (by omega) hC.1 hz2.symm hcMu
    have hro := hPO s n R hrun M t root hTop i x hi0 hxb up o hXeq hup1' ho hKo N cMp hN hleft
      hrow hBN (by omega) hlexM
    refine ⟨C, cp, hqC, hcu, ?_, Or.inl ⟨by omega, hcp1, hcp2⟩⟩
    rw [hcph, ← hrow, hro]


/-- **`RootPass IsPlain` with the weak start.** -/
theorem rootPass_plain_of_qStandW (hSL : CopyStepLower) (hQS : QStandW IsPlain)
    (hNTP : NonTopPass) (hSS : RPLRoot.SeamStep) (hSt : RPLRoot.SeamStart) :
    RootPass IsPlain := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo M t root i x hTop hxb hX N uM pM qM cM
    hN huM hNu hpM hqM hne hcM hcMp hcMc C hqC hCC
  have hMs := Canonical.build_size hTop.build
  have hcr := hTop.lt
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc : up.1.val = u.1.val := congrArg Fin.val hup1
  have hXgt : M.size - 1 < up.1.val := by omega
  obtain ⟨hi0, es, em, colX, hes, hRX, hasm, hjo⟩ :=
    CrossPlainPos.originAt_unpack hTop hxb hX hXgt ho
  have E := env_of hrun hTop up.1.isLt hXgt.le
  have hG := E.G
  have hF := E.FR
  have hV : MountainValid M := build_valid_of_success hTop.build
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hin : i ≤ n := block_le E hxg hxl (by rw [← hX]; exact up.1.isLt) (by rw [← hX]; omega)
  -- the columns of `M(s)`
  have hNx : N.1.val = x :=
    CrossPlainPos.src_column CrossPlain.isPlain_notUpper hTop hxb hX hXgt ho hKo hN
  obtain ⟨hN1, hN2⟩ := upper_spec hNu
  have huMx : uM.1.val = x := by rw [← hNx, hN1]
  have hqMr : Real qM := Q_real hG huM hqM
  have hqMlt : qM.1.val < uM.1.val := Q_column_lt hG hqM
  have hcMle : cM.1.val ≤ qM.1.val := hcM.column_le hG
  -- the node above `c_M` is below `τ`
  obtain ⟨cMp, hcMu, _⟩ := rawParent_spec hcMp
  obtain ⟨_, hrow, _⟩ := CrossPlain.normal_crossLex E.NM huM hNu hpM hqM hcM hcMp hcMu
  set k := up.2.val - 1 with hkdef
  have hkl : k < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hek : es[k] = (em, o) := by
    rw [List.getElem?_eq_getElem hkl] at hjo
    exact Option.some.inj hjo
  have hNτ : (Frame.ofMountain M).height N < t.row := by
    obtain ⟨cv, hcv, hlt⟩ := Pk4.below_of_notUpper hes (List.getElem_mem hkl)
      (by rw [hek]; exact CrossPlain.isPlain_notUpper o hKo)
    have hcvN : cv = (Frame.ofMountain M).cell N := by
      have h1 := LowerChainRecon.cell?_ref N
      rw [hN] at h1
      have h2 : Reserve.cell? M o.src = some cv := by
        have h3 := hcv
        rw [hek] at h3
        exact h3
      exact Option.some.inj (h2.symm.trans h1)
    subst hcvN
    by_contra hn
    push Not at hn
    exact absurd (official_mono hTop.row_one_le hn) (not_le.mpr hlt)
  have hcMτ : (Frame.ofMountain M).height cMp < t.row := by rw [← hrow]; exact hNτ
  have huMτ : (Frame.ofMountain M).height uM < t.row :=
    lt_trans (height_lt_of_index hG hN1.symm (by omega)) hNτ
  -- the chain of `R` from `q` passes through `c_M`
  have key : ∃ c, RawChain (Frame.ofMountain R) q c ∧ c.1.val = cM.1.val ∧
      c.2.val = cM.2.val := by
    by_cases hqc : qM = cM
    · subst hqc
      -- the top copy `u` of `u_M`
      have hk0 : 0 < k := by unfold Real at hu; omega
      have hes' : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
          (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
        rw [← hX]; exact hes
      obtain ⟨h2, hbelow⟩ := CrossPlainPos.belowSrc_plain Pk4.emitBelow_plain s n R hrun M t root
        hTop i x hi0 hxb es hes' k hkl hk0 (by rw [hek]; exact hKo)
      have hsrcN : es[k].2.src = Frame.ref N := by rw [hek]; exact hN.symm
      have hsrcz : es[k - 1].2.src = Frame.ref uM := by
        rw [hbelow, hsrcN]
        simp only [Frame.ref, hN1, hN2]
        congr 1
      have hIT := LowerChainRecon.isTopAt_of_above hV (ctx := ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl hes hkl hk0 hbelow h2
      have huc : u.1.val = x + (M.size - 1 - root.column) * i := by rw [← hupc, hX]
      have hu1 : u.2.val = k - 1 + 1 := by omega
      have hesu : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
          u.1.val) (Official.official t.row) = .ok es := by rw [← hupc]; exact hes
      have hTC : TopCopy s n R M u uM := by
        exact RPLRoot.topCopy_of_isTopAt E (by omega) hxb huc hesu hu1 (by omega) hsrcz hIT
      exact hSt s n R M t root i x hrun hTop (by omega) hxb u q uM qM cMp huc huMx huM huMτ hTC
        hqM hcMc hcMu hcMτ hq
    · rcases hQS s n R hrun M t root hTop i x hi0 hxb u up o hu hup hX ho hKo uM N hN huM hNu qM q
        hqM hq with hqq | hnt
      · exact RPLRoot.sim_root E (copyTop_of_emitted Classification.Proofs.CopyShape.Found.emitted)
          hSL hSS (by omega) hin hcMc hcMu hcMτ hcM hqc hqMr (by omega) hqq
      · exact hNTP s n R M t root i hrun hTop (by omega) hin q qM cM hnt hcM
          (Or.inr ⟨hcMc, cMp, hcMu, hcMτ⟩)
  obtain ⟨c, hqc, hc1, hc2⟩ := key
  refine ⟨c, RPLRoot.rawChain_tail hF hqC hqc ?_, hc1, hc2⟩
  have hCcol := hCC.column
  rw [CrossUpper.shiftCol_of_le (le_of_eq hcMc.symm)] at hCcol
  omega


/-! ## `NonTopPass` holds -/

/-- A chain of stored parents of `M(s)` is a reach (at some scale). -/
theorem reach_of_rawChain {M : Mountain} (hG : (Frame.ofMountain M).Ordered)
    {a c : (Frame.ofMountain M).Node} (h : RawChain (Frame.ofMountain M) a c) :
    SeamPass.Reach M (Frame.ref a) (Frame.ref c) := by
  induction h with
  | here a => exact SeamPass.Reach.refl M _
  | @step a b c hraw _ ih =>
    have hr := reserve_rawParent_of_frame hraw
    have hba : b.1.val < a.1.val := Frame.rawParent_column_lt hG hraw
    refine SeamPass.Reach.trans ⟨_, Classification.Proofs.ScaleReach.step hr
      (LowerChainRecon.cell?_ref a) (LowerChainRecon.cell?_ref b) le_rfl
      (by simp only [Frame.ref]; omega) (Classification.Proofs.ScaleReach.refl _)⟩ ih

/-- **`NonTopPass` holds** (from `ChainOK` and `PassOK` for every node of a new column: the
proved steps of `SeamChain.lean` and `SeamPassMain.lean`, with `CutParentNT`). -/
theorem nonTopPass_holds : NonTopPass := by
  intro s n R M t root i hrun hTop hi1 hin Z z c hnt hzc hcc
  obtain ⟨_, _, hCN, _⟩ := hnt
  obtain ⟨y, es, j, _, _, hyb, hv, hvi, hes, hj, hsrc, _⟩ := hCN
  have hO : TopChain.Seam.OrigAt M R n root.column (M.size - 1) (Official.official t.row)
      (Frame.ref Z) (Frame.ref z) :=
    ⟨i, y, es, j, hyb, hv, hvi, hes, ⟨_, LowerChainRecon.cell?_ref Z⟩, hj, hsrc⟩
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  have hzc' := reach_of_rawChain hG hzc
  rcases hcc with hlt | ⟨heq, c', hcu, hc'τ⟩
  · have hall := TopChain.Seam.chainOK_of_step (TopChain.Seam.stepOK_of_cases
      TopChain.Seam.stepBlock0 TopChain.Seam.stepUpper TopChain.Seam.stepTop
      (TopChain.Seam.stepNonTop_of TopChain.Seam.stepCleanNT TopChain.Seam.CPN.stepCutNT)
      (TopChain.Seam.stepX0_of TopChain.Seam.stepX0Top TopChain.Seam.stepCleanNT
        TopChain.Seam.CPN.stepCutNT) hrun hTop)
    obtain ⟨k, hk⟩ := hzc'
    exact TopChain.Seam.Pass.rawChain_of_reach ⟨k, hall _ _ hO k (Frame.ref c) hlt hk⟩
  · have hP := TopChain.Seam.Pass.passOK_all TopChain.Seam.CPN.cutParentNT hrun hTop _ _ hO
    have hca' : Reserve.cell? M (above (Frame.ref c)) = some ((Frame.ofMountain M).cell c') := by
      rw [← LowerChainRecon.above_of_upper hcu]; exact LowerChainRecon.cell?_ref c'
    exact TopChain.Seam.Pass.rawChain_of_reach (hP (Frame.ref c) heq _ hca' hc'τ hzc')

/-! ## The consequences -/

/-- **`CrossLexFor IsPlain`** from the open statements, with the weak start. -/
theorem crossLexFor_plain_simW (hE : EmitBelow IsPlain) (hCT : CopyTop) (hSL : CopyStepLower)
    (hQ : QStandW IsPlain) (hNTP : NonTopPass) (hNE : NoEndRight IsPlain)
    (hPA : PairAbove IsPlain) (hPO : PairOld IsPlain) (hRP : RootPass IsPlain)
    (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  CrossPlain.crossLexFor_plain_of_pos (CrossPlainPos.crossLexPos_plain_main hE
    (posImgR_of_simW CrossPlain.isPlain_notUpper hCT hSL hQ hNTP hNE hPA hPO hRP) hL)

/-- **`CrossLexFor IsClean`** from the open statements, with the weak start. -/
theorem crossLexFor_clean_simW (hE : EmitBelow IsClean) (hCF : CleanFirst) (hCT : CopyTop)
    (hSL : CopyStepLower) (hQ : QStandW IsClean) (hNTP : NonTopPass)
    (hNE : NoEndRight IsClean) (hPA : PairAbove IsClean) (hPO : PairOld IsClean)
    (hRP : RootPass IsClean) (hL : LexImg IsClean) : CrossLexFor IsClean :=
  CrossPlain.crossLexFor_clean_of_pos (CrossPlainPos.crossLexPos_clean_main hE hCF
    (posImgR_of_simW CrossPlain.isClean_notUpper hCT hSL hQ hNTP hNE hPA hPO hRP) hL)

/-- **`QStandW IsPlain`** holds. -/
theorem qStandW_plain : QStandW IsPlain :=
  qStandW_of_topStart'' TopStartW2.topStart''_holds
    (CrossPlainPos.belowSrc_plain Pk4.emitBelow_plain) CrossPlain.isPlain_notUpper

/-- **`QStandW IsClean`** holds. -/
theorem qStandW_clean : QStandW IsClean :=
  qStandW_of_topStart'' TopStartW2.topStart''_holds
    (CrossPlainPos.belowSrc_clean Pk4.emitBelow_clean CrossPlainPos.Pk4CF.cleanFirst_holds)
    CrossPlain.isClean_notUpper

/-- **`RootPass IsPlain` holds** (`TopStep`, `TopStart''`, `CutParentNT`, `NonTopPass` proved). -/
theorem rootPass_plain'' : RootPass IsPlain :=
  rootPass_plain_of_qStandW (copyStepLower_of_topStep FinalStageE.topStep_final) qStandW_plain
    nonTopPass_holds (TopChain.Seam.Pass.seamStep_of_cutParent TopChain.Seam.CPN.cutParentNT)
    (TopChain.Seam.Pass.seamStart_of_cutParent TopChain.Seam.CPN.cutParentNT)

/-- **`CrossLexFor IsPlain` from `NoEndRight IsPlain`.** -/
theorem crossLexFor_plain'' (hNE : NoEndRight IsPlain) :
    CrossLexFor IsPlain :=
  crossLexFor_plain_simW Pk4.emitBelow_plain
    (copyTop_of_emitted Classification.Proofs.CopyShape.Found.emitted)
    (copyStepLower_of_topStep FinalStageE.topStep_final) qStandW_plain nonTopPass_holds hNE
    Pk4.pairAbove_plain Pk4.pairOld_plain rootPass_plain'' CCL.lexImg_plain_final

/-- **`CrossLexFor IsClean` from `NoEndRight IsClean`.** -/
theorem crossLexFor_clean'' (hNE : NoEndRight IsClean) :
    CrossLexFor IsClean :=
  crossLexFor_clean_simW Pk4.emitBelow_clean CrossPlainPos.Pk4CF.cleanFirst_holds
    (copyTop_of_emitted Classification.Proofs.CopyShape.Found.emitted)
    (copyStepLower_of_topStep FinalStageE.topStep_final) qStandW_clean nonTopPass_holds hNE
    Pk4.pairAbove_clean Pk4.pairOld_clean Pk4.rootPass_clean CCL.lexImg_clean_final

end OmegaY.Official.Recon.TopStartW2R

#print axioms OmegaY.Official.Recon.TopStartW2R.cpW_of_standQ
#print axioms OmegaY.Official.Recon.TopStartW2R.qStandW_of_topStart''
#print axioms OmegaY.Official.Recon.TopStartW2R.posImgR_of_simW
#print axioms OmegaY.Official.Recon.TopStartW2R.rootPass_plain_of_qStandW
#print axioms OmegaY.Official.Recon.TopStartW2R.nonTopPass_holds
#print axioms OmegaY.Official.Recon.TopStartW2R.qStandW_plain
#print axioms OmegaY.Official.Recon.TopStartW2R.qStandW_clean
#print axioms OmegaY.Official.Recon.TopStartW2R.rootPass_plain''
#print axioms OmegaY.Official.Recon.TopStartW2R.crossLexFor_plain''
#print axioms OmegaY.Official.Recon.TopStartW2R.crossLexFor_clean''
