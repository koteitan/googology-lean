/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperCopy.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperNormal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowUpper

set_option backward.do.legacy false

/-!
# Copies of the upper part of a column

Two frames `G` (the source mountain `M(s)`) and `F` (the output `R`). A column `Y` of `F`
is an **upper copy** of a column `y` of `G` above the row `θ`, with the column map `f`
(`UpperCopy G F θ f y Y`), if

* the rows `≥ θ` of `y` and of `Y` are the same (`fwd`, `bwd`), and
* the stored left end of a node of `Y` at such a row is in the column `f(l)`, where `l` is
  the column of the stored left end of the node of `y` at the same row (`par`).

In the official expansion, the upper part of a new column `X = x + w·i` (rows `≥ τ`) is an
upper copy of the column `x' = x` (or `c_r` for `x = x₀`) with the column map
`f = shiftCol c_r w i` (`CrossUpperColumns.lean`), and every old column `y < c_r` is an
upper copy of itself above the row `0`.

This file proves, for any two frames:

* `UpperCopy.upper`, `UpperCopy.top`, `UpperCopy.rawParent`: the node above a copy is the
  copy of the node above, and the stored parent of a copy is in the column `f(l)`;
* `lex_transport`: if `f` is strictly increasing and the stored parents of `F` are the
  highest nodes of their columns below the row of the node above (`HBAt`), then `Lex`
  in `G` between two nodes at rows `≥ θ` gives `Lex` in `F` between their copies;
* `chain_transport`: a chain of stored parents of `G` whose nodes are all copied (and whose
  parents are the highest nodes below, `HBAt` in `G`) gives the chain of the copies in `F`.
-/

namespace OmegaY.Official.Recon.CrossUpper

open Canonical Geometry Frame
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

section Generic

variable {G F : Frame}

/-! ## Rows determine the nodes of a column -/

theorem index_lt_of_height_lt (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (h : F.height a < F.height b) : a.2.val < b.2.val := by
  by_contra hn
  exact absurd h (not_lt.mpr (height_le_of_index hF hc.symm (by omega)))

theorem node_eq_of_height (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (hh : F.height a = F.height b) : a = b := by
  rcases lt_trichotomy a.2.val b.2.val with h | h | h
  · exact absurd hh (ne_of_lt (height_lt_of_index hF hc h))
  · exact node_eq_of_index hc h
  · exact absurd hh (ne_of_gt (height_lt_of_index hF hc.symm h))

theorem real_of_one_le (hF : F.Ordered) {a : F.Node} (h : (1 : Row) ≤ F.height a) : Real a := by
  by_contra hn
  have h0 : a.2.val = 0 := by unfold Real at hn; omega
  have hph := hF.phantom a.1 (by have := a.2.isLt; omega)
  have hz : F.height a = 0 := by
    change (F.cells a.1 a.2).row = 0
    rw [show a.2 = ⟨0, by have := a.2.isLt; omega⟩ from Fin.ext h0, hph]
    rfl
  rw [hz] at h
  exact absurd (lt_of_lt_of_le Row.zero_lt_one h) (lt_irrefl _)

/-! ## Upper copies -/

/-- The column `Y` of `F` copies the rows `≥ θ` of the column `y` of `G`, with the columns
of the stored left ends mapped by `f`. -/
structure UpperCopy (G F : Frame) (θ : Row) (f : Nat → Nat) (y Y : Nat) : Prop where
  fwd : ∀ z : G.Node, z.1.val = y → θ ≤ G.height z →
    ∃ Z : F.Node, Z.1.val = Y ∧ F.height Z = G.height z
  bwd : ∀ Z : F.Node, Z.1.val = Y → θ ≤ F.height Z →
    ∃ z : G.Node, z.1.val = y ∧ G.height z = F.height Z
  par : ∀ (z : G.Node) (Z : F.Node) (a : Ref), z.1.val = y → Z.1.val = Y → θ ≤ G.height z →
    F.height Z = G.height z → (G.cell z).left = some a →
    ∃ A : Ref, (F.cell Z).left = some A ∧ A.column = f a.column

theorem UpperCopy.mono {θ θ' : Row} {f : Nat → Nat} {y Y : Nat} (h : UpperCopy G F θ f y Y)
    (hle : θ ≤ θ') : UpperCopy G F θ' f y Y :=
  ⟨fun z hz hθ => h.fwd z hz (hle.trans hθ), fun Z hZ hθ => h.bwd Z hZ (hle.trans hθ),
    fun z Z a hz hZ hθ hh hl => h.par z Z a hz hZ (hle.trans hθ) hh hl⟩

/-- Only the columns left of `y` matter for the column map. -/
theorem UpperCopy.congr (hG : G.Ordered) {θ : Row} {f g : Nat → Nat} {y Y : Nat}
    (h : UpperCopy G F θ f y Y) (hfg : ∀ a, a < y → f a = g a) : UpperCopy G F θ g y Y := by
  refine ⟨h.fwd, h.bwd, ?_⟩
  intro z Z a hz hZ hθ hh hl
  obtain ⟨A, hA, hAc⟩ := h.par z Z a hz hZ hθ hh hl
  obtain ⟨left, hlk, hlc, _⟩ := hG.stored_valid z a hl
  have e : left.1.val = a.column := by rw [← lookup_spec hlk]; rfl
  exact ⟨A, hA, by rw [hAc, hfg]; omega⟩

theorem UpperCopy.upper (hG : G.Ordered) (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {z z' : G.Node} {Z : F.Node} (hz : z.1.val = y)
    (hZ : Z.1.val = Y) (hθ : θ ≤ G.height z) (hh : F.height Z = G.height z)
    (hzu : G.upper z = some z') :
    ∃ Z', F.upper Z = some Z' ∧ Z'.1.val = Y ∧ F.height Z' = G.height z' := by
  obtain ⟨hz1, hz2⟩ := upper_spec hzu
  have hlt : G.height z < G.height z' := height_lt_of_index hG hz1.symm (by omega)
  obtain ⟨Z', hZ'c, hZ'h⟩ := C.fwd z' (by rw [hz1]; exact hz) (hθ.trans hlt.le)
  refine ⟨Z', ?_, hZ'c, hZ'h⟩
  have hcol : Z.1 = Z'.1 := Fin.ext (by rw [hZ, hZ'c])
  have hgt : Z.2.val < Z'.2.val :=
    index_lt_of_height_lt hF hcol (by rw [hh, hZ'h]; exact hlt)
  apply upper_eq_of_index hcol
  by_contra hne
  have hlen : F.length Z'.1 = F.length Z.1 := by rw [hcol]
  have hmid : Z.2.val + 1 < F.length Z.1 := by have := Z'.2.isLt; omega
  let V : F.Node := ⟨Z.1, ⟨Z.2.val + 1, hmid⟩⟩
  have h1 : F.height Z < F.height V := height_lt_of_index hF rfl (by simp [V])
  have h2 : F.height V < F.height Z' := height_lt_of_index hF hcol (by simp [V]; omega)
  obtain ⟨v, hvc, hvh⟩ := C.bwd V hZ (by rw [hh] at h1; exact hθ.trans h1.le)
  have e1 : z.1 = v.1 := Fin.ext (by rw [hz, hvc])
  have i1 := index_lt_of_height_lt hG e1 (by rw [hvh, ← hh]; exact h1)
  have i2 := index_lt_of_height_lt hG (e1.symm.trans hz1.symm) (by rw [hvh, ← hZ'h]; exact h2)
  omega

theorem UpperCopy.top (hG : G.Ordered) (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {z : G.Node} {Z : F.Node} (hz : z.1.val = y)
    (hZ : Z.1.val = Y) (hθ : θ ≤ G.height z) (hh : F.height Z = G.height z)
    (hzu : G.upper z = none) : F.upper Z = none := by
  cases hZu : F.upper Z with
  | none => rfl
  | some Z' =>
    exfalso
    obtain ⟨hc, hi⟩ := upper_spec hZu
    have hlt : F.height Z < F.height Z' := height_lt_of_index hF hc.symm (by omega)
    obtain ⟨z', hz'c, hz'h⟩ := C.bwd Z' (by rw [hc]; exact hZ)
      (by rw [hh] at hlt; exact hθ.trans hlt.le)
    have e : z.1 = z'.1 := Fin.ext (by rw [hz, hz'c])
    have hlt' := index_lt_of_height_lt hG e (by rw [hz'h, ← hh]; exact hlt)
    have hlen' : G.length z'.1 = G.length z.1 := by rw [e]
    have hlen : z.2.val + 1 < G.length z.1 := by have := z'.2.isLt; omega
    simp [Frame.upper, hlen] at hzu

/-- The stored parent of a copy is in the column `f(l)`. -/
theorem UpperCopy.rawParent (hG : G.Ordered) (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {z a : G.Node} {Z : F.Node} (hz : z.1.val = y)
    (hZ : Z.1.val = Y) (hθ : θ ≤ G.height z) (hh : F.height Z = G.height z)
    (hraw : G.rawParent z = some a) :
    ∃ z' Z' A, G.upper z = some z' ∧ F.upper Z = some Z' ∧ Z'.1.val = Y ∧
      F.height Z' = G.height z' ∧ F.rawParent Z = some A ∧ A.1.val = f a.1.val := by
  obtain ⟨z', hzu, hl⟩ := rawParent_spec hraw
  obtain ⟨Z', hZu, hZ'c, hZ'h⟩ := C.upper hG hF hz hZ hθ hh hzu
  obtain ⟨hz1, hz2⟩ := upper_spec hzu
  have hlt : G.height z < G.height z' := height_lt_of_index hG hz1.symm (by omega)
  obtain ⟨Aref, hA, hAc⟩ := C.par z' Z' (ref a) (by rw [hz1]; exact hz) hZ'c
    (hθ.trans hlt.le) hZ'h hl
  obtain ⟨A, hAl, _, _⟩ := hF.stored_valid Z' Aref hA
  have hAr : ref A = Aref := lookup_spec hAl
  refine ⟨z', Z', A, hzu, hZu, hZ'c, hZ'h, rawParent_eq_of_upper_left hZu (by rw [hAr]; exact hA),
    ?_⟩
  have : A.1.val = Aref.column := by rw [← hAr]; rfl
  rw [this, hAc]
  rfl

/-! ## Stored parents that are the highest nodes below -/

/-- The stored parent of `Z` is the highest node of its column below the row of the node
above `Z`. -/
def HBAt (F : Frame) (Z : F.Node) : Prop :=
  ∀ Z' A, F.upper Z = some Z' → F.rawParent Z = some A →
    F.height A < F.height Z' ∧
      ∀ v : F.Node, v.1 = A.1 → F.height v < F.height Z' → v.2.val ≤ A.2.val

theorem hbAt_of_normal (hF : F.Normal) {Z : F.Node} (hZ : Real Z) : HBAt F Z :=
  fun _ _ hu hr => Classification.Proofs.Normal.rawParent_highest_below hF hZ hu hr

/-- Two stored parents in the same column, below the same row, are equal. -/
theorem hb_eq {Z W Z' W' A B : F.Node} (hZ : HBAt F Z) (hW : HBAt F W)
    (hZu : F.upper Z = some Z') (hWu : F.upper W = some W') (hh : F.height Z' = F.height W')
    (hA : F.rawParent Z = some A) (hB : F.rawParent W = some B) (hc : A.1 = B.1) : A = B := by
  obtain ⟨hA1, hA2⟩ := hZ Z' A hZu hA
  obtain ⟨hB1, hB2⟩ := hW W' B hWu hB
  have h1 := hA2 B hc.symm (by rw [hh]; exact hB1)
  have h2 := hB2 A hc (by rw [← hh]; exact hA1)
  exact node_eq_of_index hc (by omega)

/-! ## `Lex` of copies -/

/-- **`Lex` of copies.** -/
theorem lex_transport (hG : G.Ordered) (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    (hf : ∀ a b, a < b → f a < f b) (hθ1 : (1 : Row) ≤ θ)
    (hHB : ∀ Z : F.Node, Real Z → HBAt F Z) :
    ∀ {z w : G.Node}, Lex G z w → ∀ {y1 Y1 y2 Y2 : Nat} {Z W : F.Node},
      UpperCopy G F θ f y1 Y1 → UpperCopy G F θ f y2 Y2 → z.1.val = y1 → w.1.val = y2 →
      Z.1.val = Y1 → W.1.val = Y2 → θ ≤ G.height z → θ ≤ G.height w →
      F.height Z = G.height z → F.height W = G.height w → Lex F Z W := by
  intro z w hlex
  induction hlex with
  | top hzu =>
    intro y1 Y1 y2 Y2 Z W C1 _ hz _ hZ _ hθz _ hhZ _
    exact .top (C1.top hG hF hz hZ hθz hhZ hzu)
  | left ha hb hab =>
    intro y1 Y1 y2 Y2 Z W C1 C2 hz hw hZ hW hθz hθw hhZ hhW
    obtain ⟨_, _, A, _, _, _, _, hA, hAc⟩ := C1.rawParent hG hF hz hZ hθz hhZ ha
    obtain ⟨_, _, B, _, _, _, _, hB, hBc⟩ := C2.rawParent hG hF hw hW hθw hhW hb
    exact .left hA hB (by rw [hAc, hBc]; exact hf _ _ hab)
  | @same z w z' w' a hzu hwu ha hb hh _ ih =>
    intro y1 Y1 y2 Y2 Z W C1 C2 hz hw hZ hW hθz hθw hhZ hhW
    obtain ⟨z1, Z', A, hzu1, hZu, hZ'c, hZ'h, hA, hAc⟩ := C1.rawParent hG hF hz hZ hθz hhZ ha
    obtain ⟨w1, W', B, hwu1, hWu, hW'c, hW'h, hB, hBc⟩ := C2.rawParent hG hF hw hW hθw hhW hb
    rw [hzu] at hzu1
    obtain rfl := Option.some.inj hzu1
    rw [hwu] at hwu1
    obtain rfl := Option.some.inj hwu1
    have hZr : Real Z := real_of_one_le hF (by rw [hhZ]; exact hθ1.trans hθz)
    have hWr : Real W := real_of_one_le hF (by rw [hhW]; exact hθ1.trans hθw)
    have hAB : A = B := hb_eq (hHB Z hZr) (hHB W hWr) hZu hWu (by rw [hZ'h, hW'h, hh]) hA hB
      (Fin.ext (by rw [hAc, hBc]))
    subst hAB
    obtain ⟨hz1, hz2⟩ := upper_spec hzu
    obtain ⟨hw1, hw2⟩ := upper_spec hwu
    have hzlt : G.height z < G.height z' := height_lt_of_index hG hz1.symm (by omega)
    have hwlt : G.height w < G.height w' := height_lt_of_index hG hw1.symm (by omega)
    exact .same hZu hWu hA hB (by rw [hZ'h, hW'h, hh])
      (ih C1 C2 (by rw [hz1]; exact hz) (by rw [hw1]; exact hw) hZ'c hW'c
        (hθz.trans hzlt.le) (hθw.trans hwlt.le) hZ'h hW'h)

/-! ## Chains of copies -/

/-- A family of upper copies `y ↦ f y` below the column bound `K`, with a threshold per
column. -/
def Copies (G F : Frame) (θ : Nat → Row) (f : Nat → Nat) (K : Nat) : Prop :=
  ∀ y, y < K → UpperCopy G F (θ y) f y (f y)

/-- `Z` is the copy of `z`. -/
def Img (G F : Frame) (f : Nat → Nat) (z : G.Node) (Z : F.Node) : Prop :=
  Z.1.val = f z.1.val ∧ F.height Z = G.height z

/-- **One step of a chain of copies.** -/
theorem img_step (hG : G.Ordered) (hF : F.Ordered) {θ : Nat → Row} {f : Nat → Nat} {K : Nat}
    (hC : Copies G F θ f K) {z a : G.Node} {Z : F.Node} (hzK : z.1.val < K)
    (hz : θ z.1.val ≤ G.height z) (ha : θ a.1.val ≤ G.height a) (hHG : HBAt G z)
    (hHF : HBAt F Z) (hI : Img G F f z Z) (hraw : G.rawParent z = some a) :
    ∃ A, F.rawParent Z = some A ∧ Img G F f a A := by
  have C := hC _ hzK
  obtain ⟨z', Z', A, hzu, hZu, _, hZ'h, hA, hAc⟩ :=
    C.rawParent hG hF rfl hI.1 hz hI.2 hraw
  refine ⟨A, hA, hAc, ?_⟩
  have haK : a.1.val < K := lt_of_lt_of_le (rawParent_column_lt hG hraw) hzK.le
  have Ca := hC _ haK
  obtain ⟨hGa1, hGa2⟩ := hHG z' a hzu hraw
  obtain ⟨hFa1, hFa2⟩ := hHF Z' A hZu hA
  obtain ⟨Â, hÂc, hÂh⟩ := Ca.fwd a rfl ha
  have hcol : Â.1 = A.1 := Fin.ext (by rw [hÂc, hAc])
  -- `Â` is at or below `A`
  have h1 : Â.2.val ≤ A.2.val := hFa2 Â hcol (by rw [hÂh, hZ'h]; exact hGa1)
  -- `A` is at or below `Â`
  have h2 : A.2.val ≤ Â.2.val := by
    by_contra hn
    have hlt : F.height Â < F.height A := height_lt_of_index hF hcol (by omega)
    obtain ⟨a', ha'c, ha'h⟩ := Ca.bwd A hAc (by rw [hÂh] at hlt; exact ha.trans hlt.le)
    have hle := hGa2 a' (Fin.ext ha'c) (by rw [ha'h, ← hZ'h]; exact hFa1)
    have := height_le_of_index hG (Fin.ext ha'c) hle
    rw [ha'h, ← hÂh] at this
    exact absurd hlt (not_lt.mpr this)
  have hAÂ : A = Â := node_eq_of_index hcol.symm (le_antisymm h2 h1)
  rw [hAÂ, hÂh]

theorem real_of_img (hG : G.Ordered) (hF : F.Ordered) {f : Nat → Nat} {z : G.Node}
    {Z : F.Node} (hI : Img G F f z Z) (hz : Real z) : Real Z :=
  real_of_one_le hF (by rw [hI.2]; exact one_le_height hG hz)

/-- **A chain of copies.** A chain of stored parents of a normal frame `G` whose nodes are
all copied gives the chain of their copies. -/
theorem chain_transport (hG : G.Normal) (hF : F.Ordered) {θ : Nat → Row} {f : Nat → Nat}
    {K : Nat} (hC : Copies G F θ f K) (hHF : ∀ Z : F.Node, Real Z → HBAt F Z) :
    ∀ {z c : G.Node}, RawChain G z c → z.1.val < K →
      (∀ v, RawChain G z v → RawChain G v c → θ v.1.val ≤ G.height v) → Real z →
      ∀ {Z : F.Node}, Img G F f z Z → ∃ C, RawChain F Z C ∧ Img G F f c C := by
  intro z c h
  induction h with
  | here c => intro _ _ _ Z hI; exact ⟨Z, .here Z, hI⟩
  | @step a b c hraw rest ih =>
    intro haK hD ha Z hI
    have hO := hG.toOrdered
    have hPa : G.P a = some b := (hG.rawParent_eq_P ha).symm.trans hraw
    have hb : Real b := real_of_value_pos hO (P_value hO hPa).1
    obtain ⟨A, hA, hIA⟩ := img_step hO hF hC haK (hD a (.here a) (.step hraw rest))
      (hD b (.step hraw (.here b)) rest) (hbAt_of_normal hG ha)
      (hHF Z (real_of_img hO hF hI ha)) hI hraw
    have hbK : b.1.val < K := lt_trans (rawParent_column_lt hO hraw) haK
    obtain ⟨C, hCc, hCI⟩ := ih hbK (fun v h1 h2 => hD v (.step hraw h1) h2) hb hIA
    exact ⟨C, .step hA hCc, hCI⟩

/-- **The candidate of a copy.** If `U` copies `n` and the candidate `Q n` is copied, then
`Q U` is the copy of `Q n`. -/
theorem q_transport (hG : G.Ordered) (hF : F.Ordered) {θ0 : Row} {θ : Nat → Row}
    {f : Nat → Nat} {K y0 Y0 : Nat} (hC : Copies G F θ f K)
    (C0 : UpperCopy G F θ0 f y0 Y0) {n qM : G.Node} {U : F.Node} (hn : n.1.val = y0)
    (hU : U.1.val = Y0) (hθn : θ0 ≤ G.height n) (hh : F.height U = G.height n)
    (hq : G.Q n = some qM) (hqD : θ qM.1.val ≤ G.height qM) (hqK : qM.1.val < K) :
    ∃ qF, F.Q U = some qF ∧ Img G F f qM qF := by
  obtain ⟨L, hL, _, _, hqL, _, hqn, hqmax⟩ := Q_spec hG hq
  obtain ⟨Aref, hA, hAc⟩ := C0.par n U (ref L) hn hU hθn hh hL
  obtain ⟨q', hq'⟩ := Q_exists_of_left hF ⟨Aref, hA⟩
  obtain ⟨L', hL', _, _, hq'L', _, hq'U, hq'max⟩ := Q_spec hF hq'
  have hAL' : Aref = ref L' := Option.some.inj (hA.symm.trans hL')
  have Cq := hC _ hqK
  obtain ⟨qF, hqFc, hqFh⟩ := Cq.fwd qM rfl hqD
  have hcol : q'.1 = qF.1 := by
    apply Fin.ext
    rw [hq'L', hqFc]
    have e1 : L'.1.val = Aref.column := by rw [hAL']; rfl
    rw [e1, hAc]
    have e2 : (ref L).column = L.1.val := rfl
    rw [e2, hqL]
  refine ⟨qF, ?_, hqFc, hqFh⟩
  rw [hq']
  congr 1
  apply node_eq_of_index hcol
  apply le_antisymm
  · by_contra hn'
    have hlt : F.height qF < F.height q' := height_lt_of_index hF hcol.symm (by omega)
    obtain ⟨v, hvc, hvh⟩ := Cq.bwd q' (by rw [hcol]; exact hqFc)
      (by rw [hqFh] at hlt; exact hqD.trans hlt.le)
    have hvq : qM.1 = v.1 := Fin.ext hvc.symm
    have hvi := index_lt_of_height_lt hG hvq (by rw [hvh, ← hqFh]; exact hlt)
    have hlen' : G.length v.1 = G.length qM.1 := by rw [hvq]
    have hlen : qM.2.val + 1 < G.length qM.1 := by have := v.2.isLt; omega
    let V : G.Node := ⟨qM.1, ⟨qM.2.val + 1, hlen⟩⟩
    have hV := hqmax V (upper_eq_of_index rfl rfl)
    have hVv : G.height V ≤ G.height v := height_le_of_index hG hvq (by simp [V]; omega)
    rw [hvh] at hVv
    exact absurd (lt_of_lt_of_le hV (hVv.trans (hq'U.trans hh.le))) (lt_irrefl _)
  · by_contra hn'
    have hlen' : F.length qF.1 = F.length q'.1 := by rw [hcol]
    have hlen : q'.2.val + 1 < F.length q'.1 := by have := qF.2.isLt; omega
    let V : F.Node := ⟨q'.1, ⟨q'.2.val + 1, hlen⟩⟩
    have hV := hq'max V (upper_eq_of_index rfl rfl)
    have hVQ : F.height V ≤ F.height qF := height_le_of_index hF hcol (by simp [V]; omega)
    rw [hqFh] at hVQ
    exact absurd (lt_of_lt_of_le hV (hVQ.trans (hqn.trans hh.symm.le))) (lt_irrefl _)

end Generic

/-! ## Chains in one frame -/

section Chains

variable {F : Frame}

/-- The last node before `p` on a chain of stored parents is unique. -/
theorem rawChain_last_unique (hF : F.Ordered) {a c1 c2 p : F.Node} (h1 : RawChain F a c1)
    (h2 : RawChain F a c2) (hp1 : F.rawParent c1 = some p) (hp2 : F.rawParent c2 = some p) :
    c1 = c2 := by
  induction h1 generalizing c2 with
  | here a =>
    cases h2 with
    | here _ => rfl
    | step hraw rest =>
      rw [hp1] at hraw
      obtain rfl := Option.some.inj hraw
      have := rest.column_le hF
      have := rawParent_column_lt hF hp2
      omega
  | @step a b c1 hraw rest ih =>
    cases h2 with
    | here _ =>
      rw [hp2] at hraw
      obtain rfl := Option.some.inj hraw
      have := rest.column_le hF
      have := rawParent_column_lt hF hp1
      omega
    | step hraw' rest' =>
      rw [hraw] at hraw'
      obtain rfl := Option.some.inj hraw'
      exact ih rest' hp1 hp2

/-- `Lex z z` in a normal frame. -/
theorem lex_refl (hF : F.Normal) :
    ∀ (k : Nat) (z : F.Node), F.length z.1 - z.2.val = k → Real z → Lex F z z := by
  intro k
  induction k with
  | zero =>
    intro z hk _
    have := z.2.isLt
    omega
  | succ k ih =>
    intro z hk hz
    cases hzu : F.upper z with
    | none => exact .top hzu
    | some z1 =>
      obtain ⟨p, _, _, _, hl⟩ := hF.upper_step z z1 hz hzu
      have hraw : F.rawParent z = some p := rawParent_eq_of_upper_left hzu hl
      obtain ⟨hc, hi⟩ := upper_spec hzu
      refine .same hzu hzu hraw hraw rfl (ih z1 ?_ (real_of_upper hzu))
      obtain ⟨c1, i1⟩ := z1
      simp only at hc hi
      subst hc
      show F.length z.1 - i1.val = k
      omega

end Chains

end OmegaY.Official.Recon.CrossUpper
