/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Main

set_option backward.do.legacy false

/-!
# `RootPass IsPlain` from two seam statements

`CrossPlainPos.RootPass K` (`CrossPlainPosSim.lean`): in the setting of `PosImgR K`, when the end
`c_M` of the chain `q_M → … → c_M` of `M = M(s)` (with `π_M(c_M⁺) = p_M`) is in the root column
`c_r`, the chain of the output `R` from the stand-in `C` of `c_M` passes through the node `c_M`
of the old column `c_r`.

The stand-in relation `Cp` of a node of `c_r` does not fix the node of `R` (its general form is
false, `RootPassGen`), so the proof follows the chain of `M` itself and uses the step into `c_r`:

* the chain of `R` from `q = Q u` simulates the chain of `M` from `q_M` (`QStand` from `TopStart`,
  `CopyStepLower` from `TopStep`, `CopyTop` from the proved `Emitted`), up to the node `m` of the
  chain of `M` just before `c_M`; `m` is right of `c_r`, and its stand-in `D` is the top copy of
  `m` (`row m < row m⁺ ≤ row c_M⁺ < τ`, since `c_M` is the highest node of `c_r` below `m⁺`);
* **`SeamStep`** (open, new): for the top copy `Z` of a node `z` below `τ` of an inner column whose
  stored parent `a` is in `c_r`, with the node `a⁺` above `a` below `τ`, the chain of `R` from
  the stored parent of `Z` passes through the node `a` of the old column `c_r`;
* if `q_M = c_M` there is no such `m`; then **`SeamStart`** (open, new): for the top copy `U` of a
  node `z` below `τ` whose candidate `Q z` is in `c_r` with the node above it below `τ`, the chain
  of `R` from `Q U` passes through `Q z`.

The chain of `R` from `q` is unique, so it passes through `C` (in `c_r + w·i`) and then through
`c_M` (in `c_r`) (`rawChain_tail`).

Both seam statements are about the step into the root column: `TopStepLoRoot` and
`TopStartLoRoot` (`TopChainMain.lean`, open) ask there only for the stand-in relation `Stand`,
which does not fix the node of `c_r`. The condition `row a⁺ < τ` is needed: without it both
statements are false (`s = (1,3,9,11,16,8)`, `n = 1`, `z = (2,1)`, `a = (1,1)`, `A = (5,2)`;
the rows are the official rows, the indices those of the harness).

## Numerical check

`SeamPassStep` and `SeamPassStart` of the harness `seam2.cjs` of this task (the rule of
`reference/official/omegay-trace.cjs`); counts in the final report of this task.

## Results

* `rootPass_plain_of_seam : TopStep → TopStart → SeamStep → SeamStart → RootPass IsPlain`
* `crossLexFor_plain_seam : TopStep → TopStart → SeamStep → SeamStart → LexImg IsPlain →
  CrossLexFor IsPlain`
-/

namespace OmegaY.Official.Recon.RPLRoot

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim (Cp TopCopy IsCopy Env env_of block_le cp_step CopyTop CopyStepLower
  copyTop_of_emitted)
open CrossPlainPos (RootPass LexImg)
open Classification.Proofs.ChainCorr.LowerChain (TopStep TopStart IsTopAt)
open Classification.ControlProof (height_lt_of_index node_eq_of_index)

/-! ## The open statements -/

/-- **Open (new).** The step from the top copy `Z` of a node `z` below `τ` of an inner column
of block `i ≥ 1` into the root column: if the stored parent `a` of `z` is in `c_r` and the node
`a⁺` above `a` is below `τ`, the chain of `R` from the stored parent `A` of `Z` passes through
the node `a` of the old column `c_r`. -/
def SeamStep : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i → i ≤ n →
    ∀ (Z : (Frame.ofMountain R).Node) (z a a' : (Frame.ofMountain M).Node),
      root.column < z.1.val → z.1.val < M.size - 1 →
      Z.1.val = z.1.val + (M.size - 1 - root.column) * i →
      (Frame.ofMountain M).height z < t.row → TopCopy s n R M Z z →
      (Frame.ofMountain M).rawParent z = some a → a.1.val = root.column →
      (Frame.ofMountain M).upper a = some a' → (Frame.ofMountain M).height a' < t.row →
      ∀ A, (Frame.ofMountain R).rawParent Z = some A →
        ∃ c, RawChain (Frame.ofMountain R) A c ∧ c.1.val = a.1.val ∧ c.2.val = a.2.val

/-- **Open (new).** The start from the top copy `U` of a node `z` below `τ` (in a column `y` of
block `i ≥ 1`, `x₀` included): if the candidate `pa = Q z` is in `c_r` and the node above `pa` is
below `τ`, the chain of `R` from the candidate `pe = Q U` passes through the node `pa` of the old
column `c_r`. -/
def SeamStart : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U pe : (Frame.ofMountain R).Node) (z pa pa' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → TopCopy s n R M U z →
      (Frame.ofMountain M).Q z = some pa → pa.1.val = root.column →
      (Frame.ofMountain M).upper pa = some pa' → (Frame.ofMountain M).height pa' < t.row →
      (Frame.ofMountain R).Q U = some pe →
      ∃ c, RawChain (Frame.ofMountain R) pe c ∧ c.1.val = pa.1.val ∧ c.2.val = pa.2.val

/-! ## Chains -/

/-- **The chain of stored parents is unique**: a node of the chain from `a` at or left of a
node `b` of the same chain is on the chain from `b`. -/
theorem rawChain_tail {F : Frame} (hF : F.Ordered) {a b c : F.Node} (hab : RawChain F a b)
    (hac : RawChain F a c) (hcb : c.1.val ≤ b.1.val) : RawChain F b c := by
  induction hab with
  | here _ => exact hac
  | @step a a' b hraw rest ih =>
    cases hac with
    | here _ =>
      exfalso
      have h1 := rest.column_le hF
      have h2 := rawParent_column_lt hF hraw
      omega
    | step hraw' rest' =>
      rw [hraw] at hraw'
      obtain rfl := Option.some.inj hraw'
      exact ih rest' hcb

/-! ## The simulation up to the root column -/

section Sim

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The chain of `R` passes through the end `c_M` in `c_r`.** For a node `m ≠ c_M` of the
chain of `M` to `c_M` and a stand-in `Z` of `m`, the chain of `R` from `Z` passes through the
node `c_M` of the old column `c_r`. -/
theorem sim_root (E : Env s n R M t root) (hCT : CopyTop) (hSL : CopyStepLower)
    (hSS : SeamStep) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {cM cMp : (Frame.ofMountain M).Node}
    (hcM : cM.1.val = root.column) (hcMu : (Frame.ofMountain M).upper cM = some cMp)
    (hcMτ : (Frame.ofMountain M).height cMp < t.row) :
    ∀ {m : (Frame.ofMountain M).Node}, RawChain (Frame.ofMountain M) m cM → m ≠ cM → Real m →
      m.1.val < M.size - 1 → ∀ {Z : (Frame.ofMountain R).Node}, Cp s n R M t root i Z m →
        ∃ c, RawChain (Frame.ofMountain R) Z c ∧ c.1.val = cM.1.val ∧ c.2.val = cM.2.val := by
  intro m h
  induction h with
  | here _ => intro hne; exact absurd rfl hne
  | @step m b cM' hraw rest ih =>
    intro _ hm hmx Z hC
    have hG := E.G
    have hbm : b.1.val < m.1.val := rawParent_column_lt hG hraw
    have hcb : cM'.1.val ≤ b.1.val := rest.column_le hG
    by_cases hb : b = cM'
    · subst hb
      -- `m` is right of `c_r` and below `τ`
      have hmg : root.column < m.1.val := by omega
      obtain ⟨mp, hmu, _⟩ := rawParent_spec hraw
      obtain ⟨hmp1, hmp2⟩ := upper_spec hmu
      have hHB := CrossUpper.hbAt_of_normal E.NM hm mp b hmu hraw
      obtain ⟨hcMp1, hcMp2⟩ := upper_spec hcMu
      have hmpτ : (Frame.ofMountain M).height mp < t.row := by
        by_contra hn
        push Not at hn
        have := hHB.2 cMp hcMp1 (lt_of_lt_of_le hcMτ hn)
        omega
      have hmτ : (Frame.ofMountain M).height m < t.row :=
        lt_trans (height_lt_of_index hG hmp1.symm (by omega)) hmpτ
      -- the stand-in of `m` is its top copy
      have hTC : TopCopy s n R M Z m := by
        rcases hC with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, _, _, h5⟩
        · omega
        · omega
        · exact h5 hmτ
      have hZc : Z.1.val = m.1.val + (M.size - 1 - root.column) * i := by
        rcases hC with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h3, _, _⟩
        · omega
        · omega
        · exact h3
      obtain ⟨A, hA, _⟩ := hSL s n R M t root i E.run E.top hi1 hin Z m b hmg hmx hZc hmτ hTC hraw
      obtain ⟨c, hAc, hc1, hc2⟩ := hSS s n R M t root i E.run E.top hi1 hin Z m b cMp hmg hmx hZc
        hmτ hTC hraw hcM hcMu hcMτ A hA
      exact ⟨c, .step hA hAc, hc1, hc2⟩
    · obtain ⟨A, hZA, hCA⟩ := cp_step E hCT hSL hi1 hin hm hmx hC hraw
      have hPa : (Frame.ofMountain M).P m = some b := (E.NM.rawParent_eq_P hm).symm.trans hraw
      have hbr : Real b := real_of_value_pos hG (P_value hG hPa).1
      obtain ⟨c, hAc, hc1, hc2⟩ := ih hcM hcMu hb hbr (by omega) hCA
      exact ⟨c, CrossUpperSim.rawChain_trans hZA hAc, hc1, hc2⟩

/-- **The top copy from the emits.** A node `U` of a new column whose emit is the top copy of its
source `z` (`IsTopAt`) is the top copy of `z` (`TopCopy`). -/
theorem topCopy_of_isTopAt (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i)
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i) {U : (Frame.ofMountain R).Node}
    (hUc : U.1.val = y + (M.size - 1 - root.column) * i)
    {z : (Frame.ofMountain M).Node} {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      U.1.val) (Official.official t.row) = .ok es) {j : Nat} (hUj : U.2.val = j + 1)
    (hj : j < es.length) (hsrc : es[j].2.src = Frame.ref z)
    (hIT : IsTopAt es j) : TopCopy s n R M U z := by
  have hU : Real U := by unfold Real; omega
  obtain ⟨hj', hoU⟩ := LowerChainRecon.originAt_of_emits E hi1 hyb hUc hU hes
  have hjj : U.2.val - 1 = j := by omega
  have hsrc' : es[U.2.val - 1].2.src = Frame.ref z := by
    have : es[U.2.val - 1] = es[j] := by simp only [hjj]
    rw [this]; exact hsrc
  refine ⟨⟨by omega, _, hoU, hsrc'⟩, ?_⟩
  rintro Z' hZ'c hZ'i ⟨hZ'1, o', ho', hsrc''⟩
  have hZ'c' : Z'.1.val = y + (M.size - 1 - root.column) * i := by rw [hZ'c]; exact hUc
  obtain ⟨es', em', hes', hj''⟩ := LowerChainRecon.originAt_unpack' E.top hyb hZ'c' ho'
  have hes'' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      Z'.1.val) (Official.official t.row) = .ok es := by rw [hZ'c]; exact hes
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes'')
  subst hee
  have hjl : Z'.2.val - 1 < es'.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj''
    cases hj''
  rw [List.getElem?_eq_getElem hjl] at hj''
  have ho : es'[Z'.2.val - 1].2 = o' := by rw [Option.some.inj hj'']
  exact hIT (Z'.2.val - 1) hjl hj (by omega) (by rw [ho, hsrc'', hsrc])

end Sim

/-! ## `RootPass IsPlain` -/

/-- **`RootPass IsPlain` from `CopyStepLower`, `QStand IsPlain` and the two seam statements.**
(`CopyStepLower` follows from `TopStep`, `QStand IsPlain` from `TopStart` or from the corrected
`TopStart'` of `TopStartFix.lean`.) -/
theorem rootPass_plain_of_qStand (hSL : CopyStepLower) (hQS : CrossPlainPos.QStand IsPlain)
    (hSS : SeamStep) (hSt : SeamStart) : RootPass IsPlain := by
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
        exact topCopy_of_isTopAt E (by omega) hxb huc hesu hu1 (by omega) hsrcz hIT
      exact hSt s n R M t root i x hrun hTop (by omega) hxb u q uM qM cMp huc huMx huM huMτ hTC
        hqM hcMc hcMu hcMτ hq
    · have hqq : Cp s n R M t root i q qM :=
        hQS s n R hrun M t root hTop i x hi0 hxb u up o hu hup hX ho hKo uM N hN huM hNu qM q hqM hq
      exact sim_root E (copyTop_of_emitted Classification.Proofs.CopyShape.Found.emitted)
        hSL hSS (by omega) hin hcMc hcMu hcMτ hcM hqc hqMr (by omega) hqq
  obtain ⟨c, hqc, hc1, hc2⟩ := key
  refine ⟨c, rawChain_tail hF hqC hqc ?_, hc1, hc2⟩
  have hCcol := hCC.column
  rw [CrossUpper.shiftCol_of_le (le_of_eq hcMc.symm)] at hCcol
  omega

/-- **`RootPass IsPlain` from `TopStep`, `TopStart` and the two seam statements.** (`TopStart`
is false, `TopStartLoRightFalse.lean`; see `rootPass_plain_of_qStand` for the form used with the
corrected start.) -/
theorem rootPass_plain_of_seam (hTS : TopStep) (hTSt : TopStart) (hSS : SeamStep)
    (hSt : SeamStart) : RootPass IsPlain :=
  rootPass_plain_of_qStand (LowerChainRecon.copyStepLower_of_topStep hTS)
    (LowerChainRecon.qStand_of_topStart hTSt (CrossPlainPos.belowSrc_plain Pk4.emitBelow_plain))
    hSS hSt

/-- **`CrossLexFor IsPlain`** from `TopStep`, `TopStart`, the two seam statements and
`LexImg IsPlain`. -/
theorem crossLexFor_plain_seam (hTS : TopStep) (hTSt : TopStart) (hSS : SeamStep)
    (hSt : SeamStart) (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  Pk4.crossLexFor_plain_pk4 hTS hTSt (rootPass_plain_of_seam hTS hTSt hSS hSt) hL

end OmegaY.Official.Recon.RPLRoot

#print axioms OmegaY.Official.Recon.RPLRoot.rawChain_tail
#print axioms OmegaY.Official.Recon.RPLRoot.rootPass_plain_of_qStand
#print axioms OmegaY.Official.Recon.RPLRoot.rootPass_plain_of_seam
#print axioms OmegaY.Official.Recon.RPLRoot.crossLexFor_plain_seam
