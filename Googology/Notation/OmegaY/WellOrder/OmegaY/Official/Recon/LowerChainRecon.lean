/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LowerChainRecon.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyQLower_of_topStart` one goal is closed by `exact heq.trans hsrcj` instead of `rw [heq, hsrcj]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimLow

set_option backward.do.legacy false

/-!
# The parent-chain side of the shared chain correspondence

`Classification/Proofs/LowerChain.lean` states the chain correspondence in the lower part of the
copied columns once (`TopStep`, `TopStart`, for the diagram `R = expandDiagram s n`) and derives
the `KeyLeRest` side from it. This file derives the parent-chain side of the reconstruction:

* `copyStepLow_of_topStep : TopStep → CrossUpperSim.CopyStepLow`;
* `copyStepLower_of_topStep : TopStep → CrossUpperSim.CopyStepLower` (the case `row z⁺ ≥ τ` is
  also a case of `TopStep`);
* `copyQLower_of_topStart : TopStart → CrossUpperSim.CopyQLower`;
* `crossLexFor_upper_of_lower`, `seamLastPos_of_lower`, `inner_of_lower`: `CrossLexFor IsUpper`,
  `SeamLastPosHolds`, `InnerHolds` from `LowerPB.Emitted`, `TopStep`, `TopStart`.

The bridge between the two languages:

* `isCopy_iff`: `CrossUpperSim.IsCopy Z z` (an `OriginAt` with the source `z`) is
  `LowerChain.CopyOf (ref Z) (ref z)` in an inner column of block `i`;
* `topCopy_iff`: `CrossUpperSim.TopCopy Z z` is `LowerChain.TopNode (ref Z) (ref z)` for a node `z`
  below `τ`;
* `cp_of_stand`: `LowerChain.Stand (ref A) (ref a)` gives `CrossUpperSim.Cp A a`.
-/

namespace OmegaY.Official.Recon.LowerChainRecon

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim
open Classification.Proofs.ChainCorr (MStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt copyOf_column copyOf_src_column)
open Classification.ControlProof (node_eq_of_index upper_eq_of_index)

/-! ## Nodes and references -/

section Mountain

variable {M : Mountain}

theorem cell?_ref (u : (Frame.ofMountain M).Node) :
    Reserve.cell? M (Frame.ref u) = some ((Frame.ofMountain M).cell u) :=
  Classification.ControlProof.cell?_ref u

theorem node_of_cell {r : Ref} {c : Cell} (h : Reserve.cell? M r = some c) :
    ∃ u : (Frame.ofMountain M).Node, Frame.ref u = r ∧ (Frame.ofMountain M).cell u = c := by
  unfold Reserve.cell? at h
  cases hcol : M[r.column]? with
  | none => rw [hcol] at h; cases h
  | some col =>
    rw [hcol] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨hcs, hce⟩ := Array.getElem?_eq_some_iff.mp hcol
    obtain ⟨his, hie⟩ := Array.getElem?_eq_some_iff.mp h
    subst hce
    exact ⟨⟨⟨r.column, hcs⟩, ⟨r.index, his⟩⟩, rfl, hie⟩

theorem ref_inj {u v : (Frame.ofMountain M).Node} (h : Frame.ref u = Frame.ref v) : u = v := by
  have h1 : u.1.val = v.1.val := congrArg Ref.column h
  have h2 : u.2.val = v.2.val := congrArg Ref.index h
  exact node_eq_of_index (Fin.ext h1) h2

theorem reserve_rawParent_of_frame {u p : (Frame.ofMountain M).Node}
    (h : (Frame.ofMountain M).rawParent u = some p) :
    Reserve.rawParent M (Frame.ref u) = some (Frame.ref p) := by
  obtain ⟨up, hup, hleft⟩ := Frame.rawParent_spec h
  rw [Classification.ControlProof.rawParent_ref, hup]
  simpa only [Option.bind_some] using hleft

theorem frame_rawParent_of_reserve {u p : (Frame.ofMountain M).Node}
    (h : Reserve.rawParent M (Frame.ref u) = some (Frame.ref p)) :
    (Frame.ofMountain M).rawParent u = some p := by
  rw [Classification.ControlProof.rawParent_ref] at h
  cases hup : (Frame.ofMountain M).upper u with
  | none => rw [hup] at h; cases h
  | some v =>
    rw [hup, Option.bind_some] at h
    exact Frame.rawParent_eq_of_upper_left hup h

/-- A scale-`k` chain of references is a chain of stored parents of nodes. -/
theorem rawChain_of_scaleReach {k : Nat} :
    ∀ {p q : Ref}, ScaleReach M k p q → ∀ U : (Frame.ofMountain M).Node, Frame.ref U = p →
      ∃ B, Frame.ref B = q ∧ RawChain (Frame.ofMountain M) U B := by
  intro p q h
  induction h with
  | refl p => intro U hU; exact ⟨U, hU, .here U⟩
  | step hpar _ hcp _ _ _ ih =>
    intro U hU
    obtain ⟨P, hP, _⟩ := node_of_cell hcp
    have hraw : (Frame.ofMountain M).rawParent U = some P :=
      frame_rawParent_of_reserve (by rw [hU, hP]; exact hpar)
    obtain ⟨B, hB, hch⟩ := ih P hP
    exact ⟨B, hB, .step hraw hch⟩

theorem upper_of_above {U V : (Frame.ofMountain M).Node} (h : Frame.ref V = above (Frame.ref U)) :
    (Frame.ofMountain M).upper U = some V := by
  have h1 : V.1.val = U.1.val := congrArg Ref.column h
  have h2 : V.2.val = U.2.val + 1 := congrArg Ref.index h
  exact upper_eq_of_index (Fin.ext h1.symm) h2

theorem above_of_upper {U V : (Frame.ofMountain M).Node} (h : (Frame.ofMountain M).upper U = some V) :
    Frame.ref V = above (Frame.ref U) := by
  obtain ⟨h1, h2⟩ := upper_spec h
  simp only [Frame.ref, above, h1, h2]

end Mountain

/-- Cells of the shared columns agree. -/
theorem cell_agree {R M : Mountain} {B : Nat} (hag : ∀ c, c < B → R[c]? = M[c]?) {r : Ref}
    (hr : r.column < B) : Reserve.cell? R r = Reserve.cell? M r := by
  unfold Reserve.cell?
  rw [hag r.column hr]

/-! ## `OriginAt` in a known block -/

theorem originAt_unpack' {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i x X j : Nat} {o : Origin}
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = x + (M.size - 1 - root.column) * i)
    (ho : OriginAt s n R X j o) :
    ∃ es em,
      emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (Official.official t.row) = .ok es ∧ es[j]? = some (em, o) := by
  obtain ⟨M', col', t', root', x', i', es, em, hM', hcol', ht', hroot', _, hxb', hX', hes,
    _, hj⟩ := ho
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
      X = a + (M.size - 1 - root.column) * b → 0 < b ∨ (b = 0 ∧ a = M.size - 1) := by
    intro a b ha _
    by_cases h0 : b = 0
    · subst h0
      simp [blockColumns] at ha
      exact Or.inr ⟨rfl, ha⟩
    · exact Or.inl (by omega)
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
  exact ⟨es, em, hes, hj⟩

/-! ## Copies -/

section Copies

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **`IsCopy` is `CopyOf`** in an inner column of block `i`. -/
theorem isCopy_iff (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1) {Z : (Frame.ofMountain R).Node}
    {z : (Frame.ofMountain M).Node} (hZc : Z.1.val = y + (M.size - 1 - root.column) * i) :
    IsCopy s n R M Z z ↔
      CopyOf M R n root.column (M.size - 1) (Official.official t.row) i (Frame.ref Z)
        (Frame.ref z) := by
  have hyb : y ∈ blockColumns root.column (M.size - 1) n i :=
    mem_blockColumns_of_inner (cr := root.column) (x0 := M.size - 1) (n := n) (i := i) (by omega)
      (by omega) hcy hyx
  constructor
  · rintro ⟨hZ1, o, ho, hsrc⟩
    obtain ⟨es, em, hes, hj⟩ := originAt_unpack' E.top hyb hZc ho
    have hjl : Z.2.val - 1 < es.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hj
      cases hj
    have hej : es[Z.2.val - 1] = (em, o) := by
      rw [List.getElem?_eq_getElem hjl] at hj
      exact Option.some.inj hj
    refine ⟨y, es, Z.2.val - 1, hcy, hyx, hyb, hZc, by simp [Frame.ref]; omega, ?_, hjl, ?_⟩
    · exact hes
    · rw [hej]
      exact hsrc
  · rintro ⟨y', es, j, hcy', hyx', _, hv, hidx, hes, hj, hsrc⟩
    have hv' : Z.1.val = y' + (M.size - 1 - root.column) * i := hv
    have hyy : y' = y := by omega
    subst hyy
    have hZ1 : 1 ≤ Z.2.val := by
      have : Z.2.val = j + 1 := hidx
      omega
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hX0 : M.size - 1 ≤ Z.1.val := by
      have h1 : Z.1.val = y' + (M.size - 1 - root.column) * i := hv'
      rw [h1]
      omega
    obtain ⟨o', ho'⟩ := originAt_exists E.run (v := Z) (by rw [← E.Ms]; exact hX0)
      (by unfold Real; omega)
    obtain ⟨es', em', hes', hj'⟩ := originAt_unpack' E.top hyb hZc ho'
    have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
    subst hee
    have hjj : Z.2.val - 1 = j := by
      have : Z.2.val = j + 1 := hidx
      omega
    rw [hjj, List.getElem?_eq_getElem hj] at hj'
    have ho : es'[j].2 = o' := by rw [Option.some.inj hj']
    refine ⟨hZ1, o', ho', ?_⟩
    rw [← ho]
    exact hsrc

/-- **`TopCopy` is `TopNode`** for a node below `τ`. -/
theorem topCopy_iff (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1) {Z : (Frame.ofMountain R).Node}
    {z : (Frame.ofMountain M).Node} (hZc : Z.1.val = y + (M.size - 1 - root.column) * i)
    (_hzy : z.1.val = y) (hzτ : (Frame.ofMountain M).height z < t.row) :
    TopCopy s n R M Z z ↔
      TopNode M R n root.column (M.size - 1) (Official.official t.row) t.row i (Frame.ref Z)
        (Frame.ref z) := by
  constructor
  · rintro ⟨hC, hTop⟩
    refine ⟨(isCopy_iff E hi1 hin hcy hyx hZc).mp hC, ?_, ?_⟩
    · rintro v' hv'c hv'i ⟨c', hc'⟩ hcopy
      obtain ⟨V, hV, _⟩ := node_of_cell hc'
      subst hV
      have hVc : V.1 = Z.1 := Fin.ext hv'c
      have hVc' : V.1.val = y + (M.size - 1 - root.column) * i := by rw [hVc]; exact hZc
      exact hTop V hVc hv'i ((isCopy_iff E hi1 hin hcy hyx hVc').mpr hcopy)
    · intro cm cv hcm _ hθ
      rw [cell?_ref] at hcm
      have : (Frame.ofMountain M).cell z = cm := Option.some.inj hcm
      exact absurd (lt_of_lt_of_le hzτ (by rw [Frame.height, this]; exact hθ)) (lt_irrefl _)
  · rintro ⟨hC, hTop, _⟩
    refine ⟨(isCopy_iff E hi1 hin hcy hyx hZc).mpr hC, fun Z' hZ'c hZ'i hZ'C => ?_⟩
    have hZ'c' : Z'.1.val = y + (M.size - 1 - root.column) * i := by rw [hZ'c]; exact hZc
    exact hTop (Frame.ref Z') (congrArg Fin.val hZ'c) hZ'i ⟨_, cell?_ref Z'⟩
      ((isCopy_iff E hi1 hin hcy hyx hZ'c').mp hZ'C)

/-- **`Stand` gives `Cp`.** -/
theorem cp_of_stand (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {A : (Frame.ofMountain R).Node} {a : (Frame.ofMountain M).Node}
    (hax : a.1.val < M.size - 1)
    (hS : Stand M R n root.column (M.size - 1) (Official.official t.row) t.row i (Frame.ref A)
      (Frame.ref a)) :
    Cp s n R M t root i A a := by
  obtain ⟨hlt, heq, hgt⟩ := hS
  rcases Nat.lt_trichotomy a.1.val root.column with hl | he | hg
  · have hAa : Frame.ref A = Frame.ref a := hlt hl
    have hc : A.1.val = a.1.val := congrArg Ref.column hAa
    refine Or.inl ⟨hl, hc, ?_⟩
    have h1 := cell?_ref A
    rw [hAa, cell_agree E.agree (by show a.1.val < M.size - 1; exact hax), cell?_ref a] at h1
    unfold Frame.height
    rw [Option.some.inj h1]
  · obtain ⟨hcol, hup, hch⟩ := heq he
    refine Or.inr (Or.inl ⟨he, hcol, fun z' hz' hθ => ?_, fun b hb => ?_⟩)
    · have hc := cell?_ref z'
      rw [above_of_upper hz'] at hc
      obtain ⟨cA, hcA, hrow⟩ := hup _ hc hθ
      obtain ⟨Z', hZ', hZ'c⟩ := node_of_cell hcA
      refine ⟨Z', upper_of_above hZ', ?_⟩
      unfold Frame.height
      rw [hZ'c, hrow]
    · have hbr := reserve_rawParent_of_frame hb
      obtain ⟨B, hB, hch'⟩ := rawChain_of_scaleReach
        (hch (Frame.ref b) _ _ hbr (cell?_ref a) (cell?_ref b)) A rfl
      have hbc : b.1.val < root.column := by
        have := Frame.rawParent_column_lt E.G hb
        omega
      refine ⟨B, hch', congrArg Ref.column hB, ?_⟩
      have h1 := cell?_ref B
      rw [hB, cell_agree E.agree (by show b.1.val < M.size - 1; omega), cell?_ref b] at h1
      unfold Frame.height
      rw [Option.some.inj h1]
  · have hT := hgt hg
    have hAc := copyOf_column hT.1
    have hg' : root.column ≤ (Frame.ref a).column := hg.le
    rw [Classification.Proofs.ChainCorr.mapColumn_of_ge hg'] at hAc
    refine Or.inr (Or.inr ⟨hg, hax, hAc, fun hθ => ?_, fun hτ => ?_⟩)
    · exact hT.2.2 _ _ (cell?_ref a) (cell?_ref A) hθ
    · exact (topCopy_iff E hi1 hin hg hax hAc rfl hτ).mpr hT

end Copies

/-! ## `CopyStepLow` and `CopyStepLower` from `TopStep` -/

theorem copyStepLower_of_topStep (hTS : TopStep) : CopyStepLower := by
  intro s n R M t root i hrun hTop hi1 hin Z z a hcz hzx hZc hzτ hTC hraw
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop Z.1.isLt (by rw [hZc]; omega)
  have hTN := (topCopy_iff E hi1 hin hcz hzx hZc rfl hzτ).mp hTC
  obtain ⟨A, hMS, hS⟩ := hTS s n R M t root i hrun hTop (by omega) hin (Frame.ref Z)
    (Frame.ref z) hTN (Frame.ref a) _ _ (reserve_rawParent_of_frame hraw) (cell?_ref z)
    (cell?_ref a)
  obtain ⟨hpar, _, cA, _, hcA, _, _⟩ := hMS
  obtain ⟨AN, hAN, _⟩ := node_of_cell hcA
  subst hAN
  have hax : a.1.val < M.size - 1 := by
    have := Frame.rawParent_column_lt E.G hraw
    omega
  exact ⟨AN, frame_rawParent_of_reserve hpar, cp_of_stand E hi1 hin hax hS⟩

theorem copyStepLow_of_topStep (hTS : TopStep) : CopyStepLow := by
  intro s n R M t root i hrun hTop hi1 hin Z z z' a hcz hzx hZc hzu hz'τ hTC hraw
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  have hzz : (Frame.ofMountain M).height z < (Frame.ofMountain M).height z' := by
    obtain ⟨h1, h2⟩ := upper_spec hzu
    exact Classification.ControlProof.height_lt_of_index hG h1.symm (by omega)
  exact copyStepLower_of_topStep hTS s n R M t root i hrun hTop hi1 hin Z z a hcz hzx hZc
    (lt_trans hzz hz'τ) hTC hraw

/-! ## `CopyQLower` from `TopStart` -/

/-- The data of `OriginAt` in a known block, with the assembled column. -/
theorem originAt_unpack2 {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i x X j : Nat} {o : Origin}
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = x + (M.size - 1 - root.column) * i)
    (ho : OriginAt s n R X j o) :
    ∃ es em colX,
      emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (Official.official t.row) = .ok es ∧ R[X]? = some colX ∧
      assemble (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (es.map Prod.fst) = .ok colX ∧ es[j]? = some (em, o) := by
  obtain ⟨es0, em0, hes0, _⟩ := originAt_unpack' hTop hxb hX ho
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
  exact ⟨es, em, colX, hes, hRX, hasm, hj⟩

/-- The emits of a node of a new column give its origin. -/
theorem originAt_of_emits {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i)
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i) {Z : (Frame.ofMountain R).Node}
    (hZc : Z.1.val = y + (M.size - 1 - root.column) * i) (hZ : Real Z)
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      Z.1.val) (Official.official t.row) = .ok es) :
    ∃ hj : Z.2.val - 1 < es.length, OriginAt s n R Z.1.val (Z.2.val - 1) es[Z.2.val - 1].2 := by
  have hcr := E.top.lt
  obtain ⟨hyg, _⟩ := mem_blockColumns hcr hyb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hX0 : M.size - 1 ≤ Z.1.val := by rw [hZc]; omega
  obtain ⟨o', ho'⟩ := originAt_exists E.run (v := Z) (by rw [← E.Ms]; exact hX0) hZ
  obtain ⟨es', em', hes', hj'⟩ := originAt_unpack' E.top hyb hZc ho'
  have hee : es' = es := Except.ok.inj (hes'.symm.trans hes)
  subst hee
  have hjl : Z.2.val - 1 < es'.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj'
    cases hj'
  rw [List.getElem?_eq_getElem hjl] at hj'
  have ho : es'[Z.2.val - 1].2 = o' := by rw [Option.some.inj hj']
  exact ⟨hjl, by rw [ho]; exact ho'⟩

/-- The highest node of a column at or below a row is `highestAtMost`. -/
theorem highestAtMost_of_highestIn {M : Mountain} {q : (Frame.ofMountain M).Node} {row : Row}
    (hq : Real q) (hH : HighestIn (Frame.ofMountain M) (· ≤ row) q) :
    Reserve.highestAtMost M q.1.val row = some (Frame.ref q) := by
  have hcolq : M[q.1.val]? = some M[q.1.val] := Array.getElem?_eq_getElem q.1.isLt
  cases hh : Reserve.highestAtMost M q.1.val row with
  | some p =>
    obtain ⟨hpc, hp0, col, hcol, hp, hprow, hpmax⟩ :=
      Classification.Proofs.ChainCorr.highestAtMost_spec hh
    have hc : col = M[q.1.val] := Option.some.inj (hcol.symm.trans hcolq)
    subst hc
    have h1 : q.2.val ≤ p.index := hpmax q.2.val q.2.isLt hq hH.1
    have h2 : p.index ≤ q.2.val := hH.2 ⟨q.1, ⟨p.index, hp⟩⟩ rfl hprow
    have hi : p.index = q.2.val := by omega
    have : p = Frame.ref q := by
      cases p with
      | mk pc pi =>
        simp only [Frame.ref] at hpc hi ⊢
        rw [hpc, hi]
    rw [this]
  | none =>
    exfalso
    have hq' : 0 < q.2.val := hq
    have hle : (M[q.1.val][q.2.val]'q.2.isLt).row ≤ row := hH.1
    simp only [Reserve.highestAtMost, hcolq, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def] at hh
    rw [Option.bind_eq_none_iff] at hh
    have hl := Option.eq_none_iff_forall_ne_some.mpr (fun a ha => by simpa using hh a ha)
    rw [List.getLast?_eq_none_iff] at hl
    have := List.filter_eq_nil_iff.mp hl q.2.val (List.mem_range.mpr q.2.isLt)
    simp [hq', Array.getElem?_eq_getElem q.2.isLt, hle] at this

/-- The candidate `Q` of a real node is `highestAtMost` in its left column. -/
theorem Q_eq_highestAtMost {M : Mountain} (hF : (Frame.ofMountain M).Ordered)
    {u q : (Frame.ofMountain M).Node} (hu : Real u) (hq : (Frame.ofMountain M).Q u = some q)
    {l : Ref} (hl : ((Frame.ofMountain M).cell u).left = some l) :
    Reserve.highestAtMost M l.column ((Frame.ofMountain M).cell u).row = some (Frame.ref q) := by
  obtain ⟨left, hleft, _, _, hql, _, _, _⟩ := Frame.Q_spec hF hq
  have hll : l = Frame.ref left := Option.some.inj (hl.symm.trans hleft)
  have hcol : l.column = q.1.val := by rw [hll, hql]; rfl
  rw [hcol]
  exact highestAtMost_of_highestIn (Frame.Q_real hF hu hq) (highestIn_of_Q hF hq)

/-- **The leg of a node of a new column is the image of the leg of its origin** (in a run). -/
theorem leg_image_run {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i y X : Nat} (hi1 : 1 ≤ i)
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = y + (M.size - 1 - root.column) * i) {es : List (Emit × Origin)} {colX : Column}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (Official.official t.row) = .ok es) (hRX : R[X]? = some colX)
    (hasm : assemble (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (es.map Prod.fst) = .ok colX) {j : Nat} (hj : j < es.length) {cv : Cell} {l : Ref}
    (hcv : Reserve.cell? M es[j].2.src = some cv) (hl : cv.left = some l) :
    ∃ cu ref, Reserve.cell? R ⟨X, j + 1⟩ = some cu ∧ cu.left = some ref ∧
      ref.column = Reserve.mapColumn root.column ((M.size - 1 - root.column) * i) l.column := by
  have hV := build_valid_of_success hTop.build
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hyb
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcellX, _, ref', hrefl, hrefc⟩ := hcells j (by simpa using hj)
  simp only [List.getElem_map] at hrefc
  have hcu : Reserve.cell? R ⟨X, j + 1⟩ = some cell := by
    simp only [Reserve.cell?, hRX, Option.bind_eq_bind, Option.bind_some]
    exact hcellX
  refine ⟨cell, ref', hcu, hrefl, ?_⟩
  rw [hrefc]
  obtain ⟨hvcol, hvidx, cv', hcv', hleft⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hcvv : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst hcvv
  rcases hleft with ⟨l', hl', hlc⟩ | ⟨hnone, h0, hlow⟩
  · have hll : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst hll
    simp only [legColumn, hlc, ctxAt]
    unfold Reserve.mapColumn
    by_cases h : root.column ≤ l'.column
    · have h' : ¬ l'.column < root.column := by omega
      simp [h, h']
    · have h' : l'.column < root.column := by omega
      simp [h, h']
  · rw [hlow] at hvcol
    simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
    have hi1' := index_one_of_official_zero hV hcv' hvidx h0
    have hbl := bottom_left hTop.build hcv' hi1' (by omega)
    have hll : l = ⟨es[j].2.src.column - 1, 0⟩ := Option.some.inj (hl.symm.trans hbl)
    rw [hll]
    have hXR : X < R.size := by
      rcases Array.getElem?_eq_some_iff.mp hRX with ⟨h, _⟩
      exact h
    simp only [legColumn, hnone, ctxAt, Array.size_extract]
    rw [hvcol, Classification.Proofs.ChainCorr.mapColumn_of_ge (by omega)]
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- **`CopyQLower` from `TopStart`.** -/
theorem copyQLower_of_topStart (hTSt : TopStart) : CopyQLower := by
  intro s n R M t root i y hrun hTop hi1 hy U z z' hU1 hz1 hz hzτ hzu hθ hTC
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hG := E.G
  have hF := E.FR
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hU1]; exact U.1.isLt) (by rw [← hU1, hU1]; omega)
  obtain ⟨⟨hU0, o, ho, hsrc⟩, hTop'⟩ := hTC
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hy hU1 ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcj : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  -- the emit of `U` is the top copy of its source
  have hsize : colX.size = es.length + 1 := by
    have := (assemble_spec hasm).1
    simpa using this
  have hRXe : R[U.1.val] = colX := by
    rcases Array.getElem?_eq_some_iff.mp hRX with ⟨_, h⟩
    exact h
  have hIT : IsTopAt es (U.2.val - 1) := by
    intro j' hj' _ hlt heq
    have hlen : j' + 1 < (Frame.ofMountain R).length U.1 := by
      change j' + 1 < R[U.1.val].size
      rw [hRXe, hsize]
      omega
    let Z' : (Frame.ofMountain R).Node := ⟨U.1, ⟨j' + 1, hlen⟩⟩
    have hZ'c : Z'.1.val = y + (M.size - 1 - root.column) * i := hU1
    have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
        Z'.1.val) (Official.official t.row) = .ok es := hes
    obtain ⟨_, hoZ⟩ := originAt_of_emits E hi1 hy hZ'c (by show 0 < j' + 1; omega) hes'
    apply hTop' Z' rfl (by show U.2.val < j' + 1; omega)
    refine ⟨by show 1 ≤ j' + 1; omega, es[j'].2, hoZ, ?_⟩
    exact heq.trans hsrcj
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcj] at hcz
  obtain ⟨_, _, cv', hcv', hleft⟩ := emitsT_good hes es[U.2.val - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
    · exact ⟨l, hl⟩
    · have hV := build_valid_of_success hTop.build
      have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcj]; exact hz) h0
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hsrcj]; simp [Frame.ref]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop hi1 hy hU1 hes hRX hasm hjl hcv' hl
  have hcuU : Reserve.cell? R ⟨U.1.val, U.2.val - 1 + 1⟩ = some ((Frame.ofMountain R).cell U) := by
    have := cell?_ref U
    rwa [show (Frame.ref U : Ref) = ⟨U.1.val, U.2.val - 1 + 1⟩ by
      simp only [Frame.ref]; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell U := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  obtain ⟨a, ha⟩ := Frame.Q_exists_of_left hG ⟨l, hl⟩
  obtain ⟨A, hA⟩ := Frame.Q_exists_of_left hF ⟨ref, href⟩
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hUr : Real U := by unfold Real; omega
  have hpe := Q_eq_highestAtMost hF hUr hA href
  rw [hrefc] at hpe
  have hS := hTSt s n R M t root i y hrun hTop (by omega) hin hy es (by rw [← hU1]; exact hes)
    (U.2.val - 1) hjl hIT ((Frame.ofMountain R).cell U) ((Frame.ofMountain M).cell z) l
    (Frame.ref A) (Frame.ref a) (by rw [← hU1]; exact hcuU) hcv' hl hpa hpe
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, hleft', hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    rw [hql]
    omega
  exact ⟨a, A, ha, hA, cp_of_stand E hi1 hin hax hS⟩

/-! ## The consequences on the parent-chain side -/

theorem crossLexFor_upper_of_lower (hE : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart) :
    CrossLexFor IsUpper :=
  crossLexFor_upper_of_low hE (copyQLower_of_topStart hTSt) (copyStepLow_of_topStep hTS)

theorem seamLastPos_of_lower (hE : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart) :
    CrossUpper.SeamLastPosHolds :=
  seamLastPos_of_low hE (copyQLower_of_topStart hTSt) (copyStepLow_of_topStep hTS)

theorem inner_of_lower (hE : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart) :
    CrossUpper.InnerHolds :=
  inner_of_low hE (copyQLower_of_topStart hTSt) (copyStepLow_of_topStep hTS)

end OmegaY.Official.Recon.LowerChainRecon

#print axioms OmegaY.Official.Recon.LowerChainRecon.isCopy_iff
#print axioms OmegaY.Official.Recon.LowerChainRecon.cp_of_stand
#print axioms OmegaY.Official.Recon.LowerChainRecon.copyStepLower_of_topStep
#print axioms OmegaY.Official.Recon.LowerChainRecon.copyStepLow_of_topStep
#print axioms OmegaY.Official.Recon.LowerChainRecon.copyQLower_of_topStart
#print axioms OmegaY.Official.Recon.LowerChainRecon.crossLexFor_upper_of_lower
#print axioms OmegaY.Official.Recon.LowerChainRecon.seamLastPos_of_lower
#print axioms OmegaY.Official.Recon.LowerChainRecon.inner_of_lower
