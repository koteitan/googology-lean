/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSimStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSimDefs

set_option backward.do.legacy false

/-!
# Copies of block `i ≥ 1`: one step of a chain

With the notation of `CrossUpperSimDefs.lean`, this file proves:

* `cp_of_highest`: if `a` is the highest node of its column in `M` with a row property `P`
  (downward closed, true below `τ`), and `A` the highest node with `P` of the column
  `f(col a)` of `R`, then `Cp i A a` (from `CopyTop` for an inner column and a row `< τ`);
* `cp_step`: one stored-parent step `z → a` of `M` from a node `z` with `Cp i Z z` is matched
  by a chain `Z → … → A` of `R` with `Cp i A a` (one step from `CopyStepLower` when `z` is an
  inner node below `τ`; one step, proved, when `z` is left of `c_r` or an inner node at a row
  `≥ τ`; the chain clause of `Cp` when `z` is in `c_r`);
* `cp_chain`: a chain of stored parents of `M` is matched by a chain of `R`;
* `cp_end`: if `Cp i C c` and the node `c⁺` above `c` is at a row `≥ τ`, the node `C⁺` above
  `C` has the row of `c⁺` and is in the column `f(col c)`.
-/

namespace OmegaY.Official.Recon.CrossUpperSim

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The facts of a run -/

/-- The facts of a splice run used below. -/
structure Env (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) : Prop where
  run : Official.expandDiagram s n = .ok R
  top : Top s M t root
  CI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
    (Official.official t.row) R
  agree : ∀ c, c < M.size - 1 → R[c]? = M[c]?
  FR : (Frame.ofMountain R).Ordered
  NM : (Frame.ofMountain M).Normal
  HB : ∀ Z : (Frame.ofMountain R).Node, Real Z → HBAt (Frame.ofMountain R) Z
  Ms : M.size = s.length

theorem Env.G {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) : (Frame.ofMountain M).Ordered := E.NM.toOrdered

theorem Env.cop {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) :
    Copies (Frame.ofMountain M) (Frame.ofMountain R) (fun _ => 0) id (M.size - 1) :=
  fun y hy => upperCopy_old (build_valid_of_success E.top.build) (E.agree y hy) (fun _ _ => rfl)

theorem top_unique {s : List Nat} {M M' : Mountain} {t t' : Cell} {root root' : Ref}
    (h : Top s M t root) (h' : Top s M' t' root') : M = M' ∧ t = t' ∧ root = root' := by
  have hM : M = M' := Except.ok.inj (h.build.symm.trans h'.build)
  subst hM
  have ht : t = t' := Option.some.inj (h.top.symm.trans h'.top)
  subst ht
  exact ⟨rfl, rfl, Option.some.inj (h.left.symm.trans h'.left)⟩

/-- The facts of a run with a new column. -/
theorem env_of {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {X : Nat}
    (hX : X < R.size) (hx : M.size - 1 ≤ X) : Env s n R M t root := by
  have hMs := Canonical.build_size hTop.build
  obtain ⟨M', col, t', root', _, _, _, hTop', hCI, _⟩ :=
    run_new_column hrun hX (by rw [← hMs]; exact hx)
  obtain ⟨rfl, rfl, rfl⟩ := top_unique hTop hTop'
  obtain ⟨M'', hM'', _, hI, hB⟩ := run_basic hrun
  have hMM : M = M'' := Except.ok.inj (hTop.build.symm.trans hM'')
  subst hMM
  exact ⟨hrun, hTop, hCI, hI.2.1, hB.valid.toOrdered,
    build_normal_of_legal (build_success_legal hTop.build) hTop.build, hb_run hrun, hMs⟩

theorem tau_gt_one {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) : (1 : Row) < t.row := by
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  rcases lt_or_eq_of_le ht1 with h | h
  · exact h
  · exfalso
    apply hTop.real
    rw [← h]
    exact official_one

/-- A node whose upper node is above the bottom row is real. -/
theorem real_of_upper_gt {F : Frame} (hF : F.Ordered) {Z Z' : F.Node}
    (hu : F.upper Z = some Z') (h : (1 : Row) < F.height Z') : Real Z := by
  by_contra hn
  obtain ⟨hc, hi⟩ := upper_spec hu
  have h0 : Z.2.val = 0 := by unfold Real at hn; omega
  have hlen : 1 < F.length Z'.1 := by have := Z'.2.isLt; omega
  have hb := hF.bottom_row Z'.1 hlen
  have e : F.height Z' = 1 := by
    change (F.cells Z'.1 Z'.2).row = 1
    rw [show Z'.2 = ⟨1, hlen⟩ from Fin.ext (by rw [hi, h0])]
    exact hb
  rw [e] at h
  exact lt_irrefl _ h

/-- A chain of stored parents to a different node ends further left. -/
theorem RawChain.column_lt_of_ne {F : Frame} (hF : F.Ordered) {a c : F.Node}
    (h : RawChain F a c) (hne : a ≠ c) : c.1.val < a.1.val := by
  cases h with
  | here => exact absurd rfl hne
  | step hraw rest =>
    exact lt_of_le_of_lt (rest.column_le hF) (rawParent_column_lt hF hraw)

/-! ## The copied columns of block `i` -/

theorem mem_blockColumns_of_inner {cr x0 n i y : Nat} (hi0 : 0 < i) (_hi : i < n + 1)
    (hcy : cr < y) (hyx : y < x0) : y ∈ blockColumns cr x0 n i := by
  unfold blockColumns
  rw [if_neg (by omega)]
  simp only [List.mem_range'_1]
  split <;> omega

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **An inner column is copied** above `τ` to `y + w·i`. -/
theorem upperCopy_inner (E : Env s n R M t root) {y i : Nat} (hcy : root.column < y)
    (hyx : y < M.size - 1) (hi1 : 1 ≤ i) (hlt : y + (M.size - 1 - root.column) * i < R.size) :
    UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) y
      (y + (M.size - 1 - root.column) * i) := by
  have hcr := E.top.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨i', x', hx'b, hYeq, C⟩ := upperCopy_new E.top E.CI E.FR hlt (by omega)
  obtain ⟨hx'gt, hx'le⟩ := mem_blockColumns hcr hx'b
  have hdec := decomp_eq (w := M.size - 1 - root.column) (a := y - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      generalize (M.size - 1 - root.column) * i = P at hYeq ⊢
      generalize (M.size - 1 - root.column) * i' = Q at hYeq ⊢
      omega)
  obtain ⟨h1, rfl⟩ := hdec
  have hx' : x' = y := by omega
  subst hx'
  have hs : srcCol M root x' = x' := by unfold srcCol; rw [if_neg (by omega)]
  rw [hs] at C
  exact C

/-- The block of a new column is at most `n`. -/
theorem block_le (E : Env s n R M t root) {x i : Nat} (hcx : root.column < x)
    (hxx : x ≤ M.size - 1) (hlt : x + (M.size - 1 - root.column) * i < R.size)
    (hX0 : M.size - 1 ≤ x + (M.size - 1 - root.column) * i) : i ≤ n := by
  have hcr := E.top.lt
  obtain ⟨i', x', hi', hx'b, hXeq, _⟩ := E.CI.2.2 _ hlt hX0
  obtain ⟨hx'gt, hx'le⟩ := mem_blockColumns hcr hx'b
  have hdec := decomp_eq (w := M.size - 1 - root.column) (a := x - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      generalize (M.size - 1 - root.column) * i = P at hXeq ⊢
      generalize (M.size - 1 - root.column) * i' = Q at hXeq ⊢
      omega)
  omega

/-- The stored parent read through an upper copy of the node above. -/
theorem rawParent_of_upperCopy {G F : Frame} (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {z z' a : G.Node} {Z Z' : F.Node}
    (hzu : G.upper z = some z') (hZu : F.upper Z = some Z') (hz' : z'.1.val = y)
    (hZ' : Z'.1.val = Y) (hθ : θ ≤ G.height z') (hh : F.height Z' = G.height z')
    (hraw : G.rawParent z = some a) : ∃ A, F.rawParent Z = some A ∧ A.1.val = f a.1.val := by
  obtain ⟨z'', hzu', hl⟩ := rawParent_spec hraw
  rw [hzu] at hzu'
  obtain rfl := Option.some.inj hzu'
  obtain ⟨Aref, hA, hAc⟩ := C.par z' Z' (Frame.ref a) hz' hZ' hθ hh hl
  obtain ⟨A, hAl, _, _⟩ := hF.stored_valid Z' Aref hA
  have hAr : Frame.ref A = Aref := lookup_spec hAl
  refine ⟨A, rawParent_eq_of_upper_left hZu (by rw [hAr]; exact hA), ?_⟩
  have e : A.1.val = Aref.column := by rw [← hAr]; rfl
  rw [e, hAc]
  rfl

/-- **`Cp` from highest nodes.** `a` is the highest node of its column (left of `x₀`) with
the row property `P`, `A` the highest node with `P` of the column `f(col a)` of `R`. If `P` is
downward closed and true below `τ`, then `Cp i A a`. -/
theorem cp_of_highest (E : Env s n R M t root) (hCT : CopyTop) {i : Nat} (hi1 : 1 ≤ i)
    (hin : i ≤ n) {P : Row → Prop} (hPd : ∀ r r', r ≤ r' → P r' → P r)
    (hP : ∀ r, r < t.row → P r) {a : (Frame.ofMountain M).Node}
    {A : (Frame.ofMountain R).Node} (har : Real a) (hax : a.1.val < M.size - 1)
    (hAc : A.1.val = shiftCol root.column (M.size - 1 - root.column) i a.1.val)
    (ha : HighestIn (Frame.ofMountain M) P a) (hA : HighestIn (Frame.ofMountain R) P A) :
    Cp s n R M t root i A a := by
  have hG := E.G
  have hF := E.FR
  have hcr := E.top.lt
  have hALt : A.1.val < R.size := A.1.isLt
  rcases Nat.lt_trichotomy a.1.val root.column with hl | he | hg
  · -- left of `c_r`: the shared columns
    rw [shiftCol_of_lt hl] at hAc
    exact Or.inl ⟨hl, hAc, highestIn_twin (E.agree _ hax) hAc rfl hA ha⟩
  · -- the root column: the boundary column `c_r + w·i`
    rw [shiftCol_of_le (le_of_eq he.symm), he] at hAc
    have CY := upperCopy_root E.top E.CI E.FR (i := i) (by rw [← hAc]; exact hALt)
    have hup : ∀ a', (Frame.ofMountain M).upper a = some a' →
        t.row ≤ (Frame.ofMountain M).height a' → ∃ A', (Frame.ofMountain R).upper A = some A' ∧
          (Frame.ofMountain R).height A' = (Frame.ofMountain M).height a' :=
      fun a' hau hθ => highestIn_upperCopy_upper hG hF CY hPd hP he hAc ha hA hau hθ
    refine Or.inr (Or.inl ⟨he, hAc, hup, ?_⟩)
    intro b hb
    obtain ⟨a', hau, _⟩ := rawParent_spec hb
    obtain ⟨ha'1, ha'2⟩ := upper_spec hau
    have hθ : t.row ≤ (Frame.ofMountain M).height a' := by
      by_contra hn
      have := ha.2 a' ha'1 (hP _ (lt_of_not_ge hn))
      omega
    obtain ⟨A', hAu, hA'h⟩ := hup a' hau hθ
    obtain ⟨hA'1, _⟩ := upper_spec hAu
    obtain ⟨B, hB, hBc⟩ := rawParent_of_upperCopy hF CY hau hAu (by rw [ha'1]; exact he)
      (by rw [hA'1]; exact hAc) hθ hA'h hb
    have hbc : b.1.val < root.column := by have := rawParent_column_lt hG hb; omega
    rw [shiftCol_of_lt hbc] at hBc
    have hAr : Real A :=
      real_of_upper_gt hF hAu (by rw [hA'h]; exact lt_of_lt_of_le (tau_gt_one E.top) hθ)
    have hBR := highestIn_of_hb (E.HB A hAr) hAu hB
    have hbM := highestIn_of_hb (hbAt_of_normal E.NM har) hau hb
    rw [hA'h] at hBR
    exact ⟨B, .step hB (.here B), hBc, highestIn_twin (E.agree _ (by omega)) hBc rfl hBR hbM⟩
  · -- an inner column
    rw [shiftCol_of_le hg.le] at hAc
    have Ca := upperCopy_inner E hg hax hi1 (by rw [← hAc]; exact hALt)
    refine Or.inr (Or.inr ⟨hg, hax, hAc, ?_, ?_⟩)
    · intro hθ
      exact highestIn_upperCopy_ge hG hF Ca rfl hAc ha hA hθ
    · intro hlt
      obtain ⟨hTa, hTA⟩ := highestIn_upperCopy_lt hG Ca hP rfl hAc ha hA hlt
      exact hCT s n R M t root i a.1.val E.run E.top hi1
        (mem_blockColumns_of_inner (by omega) (by omega) hg hax)
        A a hAc rfl hTA hTa

/-! ## One step -/

/-- **One step of the chains.** -/
theorem cp_step (E : Env s n R M t root) (hCT : CopyTop) (hSL : CopyStepLower) {i : Nat}
    (hi1 : 1 ≤ i) (hin : i ≤ n) {Z : (Frame.ofMountain R).Node}
    {z a : (Frame.ofMountain M).Node} (hz : Real z) (hzx : z.1.val < M.size - 1)
    (hC : Cp s n R M t root i Z z) (hraw : (Frame.ofMountain M).rawParent z = some a) :
    ∃ A, RawChain (Frame.ofMountain R) Z A ∧ Cp s n R M t root i A a := by
  have hG := E.G
  have hF := E.FR
  have hcr := E.top.lt
  have ht1 := tau_gt_one E.top
  have haz : a.1.val < z.1.val := rawParent_column_lt hG hraw
  obtain ⟨z', hzu, _⟩ := rawParent_spec hraw
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  have hzz' : (Frame.ofMountain M).height z < (Frame.ofMountain M).height z' :=
    height_lt_of_index hG hz'1.symm (by omega)
  have haM : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height z') a :=
    highestIn_of_hb (hbAt_of_normal E.NM hz) hzu hraw
  have har : Real a :=
    real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hz).symm.trans hraw)).1
  have hPd : ∀ r r' : Row, r ≤ r' → r' < (Frame.ofMountain M).height z' →
      r < (Frame.ofMountain M).height z' := fun r r' h1 h2 => lt_of_le_of_lt h1 h2
  rcases hC with ⟨hl, hZc, hZh⟩ | ⟨he, hZc, _, hch⟩ | ⟨hg, _, hZc, hU, hL⟩
  · -- left of `c_r`
    have hZr : Real Z := real_of_one_le hF (by rw [hZh]; exact one_le_height hG hz)
    obtain ⟨A, hA, hI⟩ := img_step hG hF E.cop hzx (Row.zero_le _) (Row.zero_le _)
      (hbAt_of_normal E.NM hz) (E.HB Z hZr) ⟨hZc, hZh⟩ hraw
    exact ⟨A, .step hA (.here A), Or.inl ⟨by omega, hI.1, hI.2⟩⟩
  · -- the root column: the chain clause of `Cp`
    obtain ⟨B, hB, hBc, hBh⟩ := hch a hraw
    exact ⟨B, hB, Or.inl ⟨by omega, hBc, hBh⟩⟩
  · -- an inner column
    by_cases hθz : t.row ≤ (Frame.ofMountain M).height z
    · have hZh := hU hθz
      have hZr : Real Z := real_of_one_le hF (by rw [hZh]; exact one_le_height hG hz)
      have Cz := upperCopy_inner E hg hzx hi1 (by rw [← hZc]; exact Z.1.isLt)
      obtain ⟨Z', hZu, hZ'c, hZ'h⟩ := Cz.upper hG hF rfl hZc hθz hZh hzu
      obtain ⟨A, hA, hAc⟩ := rawParent_of_upperCopy hF Cz hzu hZu (by rw [hz'1]) hZ'c
        (hθz.trans hzz'.le) hZ'h hraw
      have hAR := highestIn_of_hb (E.HB Z hZr) hZu hA
      rw [hZ'h] at hAR
      exact ⟨A, .step hA (.here A), cp_of_highest E hCT hi1 hin hPd
        (fun r hr => lt_of_lt_of_le hr (hθz.trans hzz'.le)) har (by omega) hAc haM hAR⟩
    · obtain ⟨A, hA, hCA⟩ := hSL s n R M t root i E.run E.top hi1 hin Z z a hg hzx hZc
        (lt_of_not_ge hθz) (hL (lt_of_not_ge hθz)) hraw
      exact ⟨A, .step hA (.here A), hCA⟩

/-! ## Chains -/

/-- **A chain of stored parents of `M` is matched by a chain of `R`.** -/
theorem cp_chain (E : Env s n R M t root) (hCT : CopyTop) (hSL : CopyStepLower) {i : Nat}
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∀ {m c : (Frame.ofMountain M).Node}, RawChain (Frame.ofMountain M) m c → Real m →
      m.1.val < M.size - 1 → ∀ {Z : (Frame.ofMountain R).Node}, Cp s n R M t root i Z m →
        ∃ C, RawChain (Frame.ofMountain R) Z C ∧ Cp s n R M t root i C c := by
  intro m c h
  induction h with
  | here c => intro _ _ Z hC; exact ⟨Z, .here Z, hC⟩
  | @step a b c hraw _ ih =>
    intro ha hax Z hC
    have hG := E.G
    have hba : b.1.val < a.1.val := rawParent_column_lt hG hraw
    obtain ⟨A, hA, hCA⟩ := cp_step E hCT hSL hi1 hin ha hax hC hraw
    have hPa : (Frame.ofMountain M).P a = some b := (E.NM.rawParent_eq_P ha).symm.trans hraw
    have hb : Real b := real_of_value_pos hG (P_value hG hPa).1
    obtain ⟨C, hCc, hCC⟩ := ih hb (by omega) hCA
    exact ⟨C, rawChain_trans hA hCc, hCC⟩

/-- **The last node.** If `Cp i C c` and `c⁺` is at a row `≥ τ`, then `C⁺` is in the
column `f(col c)` at the row of `c⁺`. -/
theorem cp_end (E : Env s n R M t root) (hCT : CopyTop) {i : Nat} (hi1 : 1 ≤ i)
    (hin : i ≤ n) {C : (Frame.ofMountain R).Node} {c c' : (Frame.ofMountain M).Node}
    (hcx : c.1.val < M.size - 1) (hC : Cp s n R M t root i C c)
    (hcu : (Frame.ofMountain M).upper c = some c') (hθ : t.row ≤ (Frame.ofMountain M).height c') :
    ∃ C', (Frame.ofMountain R).upper C = some C' ∧
      C'.1.val = shiftCol root.column (M.size - 1 - root.column) i c.1.val ∧
      (Frame.ofMountain R).height C' = (Frame.ofMountain M).height c' := by
  have hG := E.G
  have hF := E.FR
  have hcr := E.top.lt
  have hCcol := hC.column
  obtain ⟨hc'1, hc'2⟩ := upper_spec hcu
  rcases hC with ⟨hl, hCc, hCh⟩ | ⟨he, hCc, hup, _⟩ | ⟨hg, _, hCc, hU, hL⟩
  · obtain ⟨C', hCu, hC'c, hC'h⟩ := (E.cop _ hcx).upper hG hF rfl hCc (Row.zero_le _) hCh hcu
    exact ⟨C', hCu, by rw [hC'c, shiftCol_of_lt hl]; rfl, hC'h⟩
  · obtain ⟨C', hCu, hC'h⟩ := hup c' hcu hθ
    obtain ⟨hC'1, _⟩ := upper_spec hCu
    exact ⟨C', hCu, by rw [hC'1, hCcol], hC'h⟩
  · have Cc := upperCopy_inner E hg hcx hi1 (by rw [← hCc]; exact C.1.isLt)
    by_cases hθc : t.row ≤ (Frame.ofMountain M).height c
    · obtain ⟨C', hCu, hC'c, hC'h⟩ := Cc.upper hG hF rfl hCc hθc (hU hθc) hcu
      exact ⟨C', hCu, by rw [hC'c, shiftCol_of_le hg.le], hC'h⟩
    · have hlt : (Frame.ofMountain M).height c < t.row := lt_of_not_ge hθc
      have hTc : TopBelow (Frame.ofMountain M) t.row c := by
        refine ⟨hlt, fun v hv hvl => ?_⟩
        have := index_lt_of_height_lt hG (hv.trans hc'1.symm) (lt_of_lt_of_le hvl hθ)
        omega
      have h0 : 0 < (Frame.ofMountain R).length C.1 := by have := C.2.isLt; omega
      obtain ⟨T, hTc1, hT⟩ := exists_highestIn (Frame.ofMountain R) (· < t.row) C.1 h0 (by
        have := hF.phantom C.1 h0
        change ((Frame.ofMountain R).cells C.1 ⟨0, h0⟩).row < t.row
        rw [this]
        exact lt_of_lt_of_le Row.zero_lt_one (le_of_lt (tau_gt_one E.top)))
      have hTC : TopCopy s n R M T c := hCT s n R M t root i c.1.val E.run E.top hi1
        (mem_blockColumns_of_inner (by omega) (by omega) hg hcx)
        T c (by rw [hTc1]; exact hCc) rfl hT hTc
      have hTe : T = C := TopCopy.unique hTC (hL hlt) hTc1
      subst hTe
      obtain ⟨C', hCu, hC'h⟩ := highestIn_upperCopy_upper hG hF Cc
        (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun r hr => hr) rfl hCc hTc hT hcu hθ
      obtain ⟨hC'1, _⟩ := upper_spec hCu
      exact ⟨C', hCu, by rw [hC'1, hCcol], hC'h⟩

end Run

end OmegaY.Official.Recon.CrossUpperSim
