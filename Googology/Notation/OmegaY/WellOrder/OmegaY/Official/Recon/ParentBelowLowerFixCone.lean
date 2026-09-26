/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowLowerFixCone.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.Executable

set_option backward.do.legacy false

/-!
# Legs inside an ascending region (canonical frames)

A statement about canonical mountains (normal frames) only. It is the core of `LowAsc`
(`ParentBelowLowerFixRule.lean`) and of `LiftLegRight` (`ChainCorrLegLeftItems.lean`), see
`ParentBelowLowerFixConeApply.lean`.

## Setting (`Setup`)

A real node `root` of a column `c_r` at height `L`, a node `ρ` of the same column at height `C`
with either `ρ = root` (`C = L`) or `ρ` the node just above `root` with `C = bump L 0` (`= L + 1`),
and a row `cap > C` such that the node above `ρ` (if any) is at or above `cap`: so `ρ` is the only
node of `c_r` with height in `[C, cap)` (`Setup.only`).

A column `c` is in the *cone* (`Cone`) if it has a real node at height `L` from which the
numerical parents reach `root` (through nodes of height `L`). The column `c_r` is in the cone.

## The theorem (`main`)

For a node `u` of a cone column with `C ≤ height u < cap` and parent `p = P(u)`: either `p` is in
a cone column with `height p ≥ L`, or the node above `u` is at or above `cap`.

The proof is by induction on the column, then on the index. Let `u` be in a cone column
`c ≠ c_r` (in `c_r` the only candidate is `ρ`, whose upper node is at or above `cap`).

* The left end `pl` of the edge below `u` (the parent of the node `w` below `u`) is in a cone
  column with height `≥ L`: by induction if `height w ≥ C`; otherwise `w` is the node of `c` at
  height `L`, whose parent is the next node of the path to `root`.
* So the candidate `Q(u)` is in a cone column, with height in `[C, height u]` (`Q_control`: if
  `height pl = L < C`, the node above `pl` has height `C` and is a candidate).
* The search from `Q(u)` (`trace`) stays in cone columns with heights in `[C, height u]`, by the
  same argument, until it hits `p` (then `p` is in the cone) or reaches `c_r`, i.e. `ρ`. At the
  height `L` (only when `C = L`) the search is continued from the parent of the rejected node
  (`Hit.loosen`). If `ρ` is rejected, `v(ρ) ≥ v(u)`, so the parent of `u` is at or after the
  parent `r` of `ρ` in the search, and `B(height u, height p) ≥ B(C, height r) = height(ρ⁺) ≥ cap`
  (`B_subinterval`).

`legRight`: the left end of the edge below a node `u` of a cone column with `C < height u < cap`
is at or right of `c_r`.
-/

namespace OmegaY.Official.Recon.LowerPB.Cone

open OmegaY.Geometry OmegaY.Geometry.Frame

variable {F : Frame}

/-! ## Rows and indices -/

theorem row_eq_of_lt_bump0 {L h : Row} (h1 : L ≤ h) (h2 : h < Row.bump L 0) : h = L := by
  have hj := Row.jump_le_of_lt_bump h1 h2
  apply Row.ext
  intro i
  exact (Row.jump_le_iff.mp hj i (Nat.zero_le i)).symm

theorem height_lt_of_index_lt (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (hi : u.2.val < v.2.val) : F.height u < F.height v := by
  rcases u with ⟨c, i⟩
  rcases v with ⟨d, j⟩
  dsimp only at hc
  subst d
  exact hF.rows_strict c hi

theorem height_le_of_index_le (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (hi : u.2.val ≤ v.2.val) : F.height u ≤ F.height v := by
  rcases Nat.lt_or_eq_of_le hi with h | h
  · exact le_of_lt (height_lt_of_index_lt hF hc h)
  · rcases u with ⟨c, i⟩
    rcases v with ⟨d, j⟩
    dsimp only at hc h
    subst d
    have : i = j := Fin.ext h
    subst this
    exact le_rfl

theorem index_le_of_height_le (hF : F.Ordered) {u v : F.Node} (hc : u.1 = v.1)
    (hh : F.height u ≤ F.height v) : u.2.val ≤ v.2.val := by
  by_contra hn
  exact absurd hh (not_le.mpr (height_lt_of_index_lt hF hc.symm (by omega)))

theorem real_of_one_le_height (hF : F.Ordered) {u : F.Node} (h : (1 : Row) ≤ F.height u) :
    Real u := by
  by_contra hn
  have hi : u.2.val = 0 := by unfold Real at hn; omega
  have hlen : 0 < F.length u.1 := by have := u.2.isLt; omega
  have hu : u.2 = ⟨0, hlen⟩ := Fin.ext hi
  have h0 : F.height u = 0 := by
    change (F.cells u.1 u.2).row = 0
    rw [hu, hF.phantom u.1 hlen]
    rfl
  rw [h0] at h
  exact absurd h (not_le.mpr Row.zero_lt_one)

/-- The node above `u`, when the column has one. -/
theorem upper_of_lt {u : F.Node} (h : u.2.val + 1 < F.length u.1) :
    F.upper u = some ⟨u.1, ⟨u.2.val + 1, h⟩⟩ := by
  simp [upper, h]

/-- `Q(u)` is the highest candidate: a node of its column not above `u` is not above it. -/
theorem Q_max (hF : F.Ordered) {u q w : F.Node} (hq : F.Q u = some q) (hw : w.1 = q.1)
    (hwh : F.height w ≤ F.height u) : w.2.val ≤ q.2.val := by
  by_contra hn
  have hlt : q.2.val + 1 < F.length q.1 := by
    have := w.2.isLt
    rcases w with ⟨c, i⟩
    dsimp only at hw
    subst hw
    dsimp only at hn this ⊢
    omega
  have hup := upper_of_lt hlt
  have hgt := Q_upper_gt hF hq hup
  have hle : F.height ⟨q.1, ⟨q.2.val + 1, hlt⟩⟩ ≤ F.height w :=
    height_le_of_index_le hF hw.symm (by dsimp only; omega)
  exact absurd (lt_of_lt_of_le hgt hle) (not_lt.mpr hwh)

/-- In a normal frame, the stored left end of the node above `w` is the parent of `w`. -/
theorem left_of_parent (hF : F.Normal) {w u p : F.Node} (hw : Real w)
    (hwu : F.upper w = some u) (hp : F.P w = some p) : (F.cell u).left = some (ref p) := by
  obtain ⟨p', hp', _, _, hleft⟩ := hF.upper_step w u hw hwu
  have : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst this
  exact hleft

/-! ## The setting -/

/-- The cone of `root`: columns with a real node at the height of `root` from which the
numerical parents reach `root`. -/
def Cone (F : Frame) (root : F.Node) (c : Fin F.width) : Prop :=
  ∃ low : F.Node, Real low ∧ low.1 = c ∧ F.height low = F.height root ∧ ParentPath F low root

structure Setup (F : Frame) (root rho : F.Node) (cap : Row) : Prop where
  normal : F.Normal
  rootReal : Real root
  col : rho.1 = root.1
  shape : rho = root ∨ (F.upper root = some rho ∧ F.height rho = Row.bump (F.height root) 0)
  capGt : F.height rho < cap
  barrier : ∀ v, F.upper rho = some v → cap ≤ F.height v

namespace Setup

variable {root rho : F.Node} {cap : Row}

theorem ordered (S : Setup F root rho cap) : F.Ordered := S.normal.toOrdered

theorem L_le_C (S : Setup F root rho cap) : F.height root ≤ F.height rho := by
  rcases S.shape with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact le_of_lt (Row.lt_bump _ 0)

theorem C_cases (S : Setup F root rho cap) :
    F.height rho = F.height root ∨ F.height rho = Row.bump (F.height root) 0 := by
  rcases S.shape with h | ⟨_, h⟩
  · left; rw [h]
  · right; exact h

theorem rhoReal (S : Setup F root rho cap) : Real rho :=
  real_of_one_le_height S.ordered ((one_le_height S.ordered S.rootReal).trans S.L_le_C)

theorem cone_root (S : Setup F root rho cap) : Cone F root root.1 :=
  ⟨root, S.rootReal, rfl, rfl, .refl _⟩

/-- `ρ` is the only node of the root column with height in `[C, cap)`. -/
theorem only (S : Setup F root rho cap) {w : F.Node} (hw : w.1 = root.1)
    (h1 : F.height rho ≤ F.height w) (h2 : F.height w < cap) : w = rho := by
  have hwr : w.1 = rho.1 := hw.trans S.col.symm
  rcases Nat.lt_trichotomy w.2.val rho.2.val with h | h | h
  · exact absurd h1 (not_le.mpr (height_lt_of_index_lt S.ordered hwr h))
  · rcases w with ⟨c, i⟩
    rcases rho with ⟨d, j⟩
    dsimp only at hwr h
    subst d
    have : i = j := Fin.ext h
    subst this
    rfl
  · have hlt : rho.2.val + 1 < F.length rho.1 := by
      have := w.2.isLt
      rcases w with ⟨c, i⟩
      dsimp only at hwr
      subst hwr
      dsimp only at h this ⊢
      omega
    have hb := S.barrier _ (upper_of_lt hlt)
    have hle : F.height ⟨rho.1, ⟨rho.2.val + 1, hlt⟩⟩ ≤ F.height w :=
      height_le_of_index_le S.ordered hwr.symm (by dsimp only; omega)
    exact absurd (lt_of_lt_of_le h2 (hb.trans hle)) (lt_irrefl _)

/-- The node of a cone column at height `L`, outside the root column: its parent is the next node
of the path, in a cone column at height `L`. -/
theorem low_parent (S : Setup F root rho cap) {low : F.Node} (hlr : Real low)
    (hlh : F.height low = F.height root) (hlp : ParentPath F low root) (hne : low.1 ≠ root.1) :
    ∃ next, F.P low = some next ∧ Real next ∧ F.height next = F.height root ∧
      ParentPath F next root ∧ next.1.val < low.1.val := by
  cases hlp with
  | refl => exact absurd rfl hne
  | @cons _ next _ hp rest =>
    have hv := P_value S.ordered hp
    refine ⟨next, hp, real_of_value_pos S.ordered hv.1, ?_, rest, P_column_lt S.ordered hp⟩
    exact le_antisymm ((P_height_le S.ordered hp).trans hlh.le) (rest.height_le S.ordered)

/-- The node above the node `low` of a cone column at height `L` (outside the root column) has
height `bump L 0`. -/
theorem low_upper (S : Setup F root rho cap) {low : F.Node} (hlr : Real low)
    (hlh : F.height low = F.height root) (hlp : ParentPath F low root) (hne : low.1 ≠ root.1) :
    ∃ v, F.upper low = some v ∧ F.height v = Row.bump (F.height root) 0 := by
  obtain ⟨next, hp, _, hnh, _, _⟩ := S.low_parent hlr hlh hlp hne
  obtain ⟨v, hv⟩ := S.normal.upper_of_parent hp
  refine ⟨v, hv, ?_⟩
  rw [← aboveHeight_of_upper hv, S.normal.above_row hp, hlh, hnh, Row.B_self]

/-- A node of the column of `root` at height `L` is `root`. -/
theorem eq_root (S : Setup F root rho cap) {w : F.Node} (hw : w.1 = root.1)
    (hh : F.height w = F.height root) : w = root :=
  node_eq_of_column_height S.ordered hw hh

/-- **The candidate stays in the cone.** If the stored left end `pl` of `y` is in a cone column
with `height pl ≥ L`, and `height y ≥ C`, then `Q(y)` is in the column of `pl`, with height in
`[C, height y]`. -/
theorem Q_control (S : Setup F root rho cap) {y pl : F.Node} (hcone : Cone F root pl.1)
    (hL : F.height root ≤ F.height pl) (hleft : (F.cell y).left = some (ref pl))
    (hC : F.height rho ≤ F.height y) :
    ∃ q, F.Q y = some q ∧ q.1 = pl.1 ∧ F.height rho ≤ F.height q ∧ F.height q ≤ F.height y := by
  obtain ⟨q, hq⟩ := Q_exists_of_left S.ordered ⟨_, hleft⟩
  obtain ⟨left, hl, _, _, hqc, hqi, hqy, _⟩ := Q_spec S.ordered hq
  have hlp : left = pl := Executable.ref_injective F (Option.some.inj (hl.symm.trans hleft))
  subst hlp
  refine ⟨q, hq, hqc, ?_, hqy⟩
  by_cases hpC : F.height rho ≤ F.height left
  · exact hpC.trans (height_le_of_index_le S.ordered hqc.symm hqi)
  · have hlt := lt_of_not_ge hpC
    rcases S.C_cases with hCL | hCL
    · exact absurd (by rw [hCL]; exact hL) (not_le.mpr hlt)
    · have hlL : F.height left = F.height root := row_eq_of_lt_bump0 hL (by rw [← hCL]; exact hlt)
      -- the node above `left` has height `C` and is a candidate
      obtain ⟨v, hv, hvh⟩ : ∃ v, F.upper left = some v ∧ F.height v = F.height rho := by
        by_cases hlr : left.1 = root.1
        · have he := S.eq_root hlr hlL
          subst he
          rcases S.shape with h | ⟨h, _⟩
          · rw [h] at hCL
            exact absurd hCL (ne_of_lt (Row.lt_bump _ 0))
          · exact ⟨rho, h, rfl⟩
        · obtain ⟨low, hlr', hlc, hlh, hlpath⟩ := hcone
          have he : low = left := node_eq_of_column_height S.ordered hlc (hlh.trans hlL.symm)
          subst he
          obtain ⟨v, hv, hvh⟩ := S.low_upper hlr' hlh hlpath hlr
          exact ⟨v, hv, hvh.trans hCL.symm⟩
      obtain ⟨hvc, _⟩ := upper_spec hv
      have hvq : v.2.val ≤ q.2.val := Q_max S.ordered hq (hvc.trans hqc.symm) (by rw [hvh]; exact hC)
      rw [← hvh]
      exact height_le_of_index_le S.ordered (hvc.trans hqc.symm) hvq

/-- The node below a node `y` of a cone column above the height `L`. -/
theorem lower (S : Setup F root rho cap) {y : F.Node} (hcone : Cone F root y.1)
    (hL : F.height root < F.height y) :
    ∃ w, Real w ∧ F.upper w = some y ∧ w.1 = y.1 ∧ F.height root ≤ F.height w := by
  obtain ⟨low, hlr, hlc, hlh, _⟩ := hcone
  have hlt : F.height low < F.height y := by rw [hlh]; exact hL
  obtain ⟨w, hwr, hwu, hwc, _⟩ := real_lower_of_height_lt S.ordered (u := y) hlr hlt
  refine ⟨w, hwr, hwu, hwc, ?_⟩
  rw [← hlh]
  exact height_le_lower_of_lt_upper S.ordered (w := low) hwu hlc hlt

/-- The conclusion of `main` for a node `u` with parent `p`. -/
def Concl (F : Frame) (root : F.Node) (cap : Row) (u p : F.Node) : Prop :=
  (Cone F root p.1 ∧ F.height root ≤ F.height p) ∨ cap ≤ F.aboveHeight u

/-- The left end of the edge below a node `y` of a cone column (`y` not in the root column,
`C ≤ height y < cap`, `L < height y`) is in a cone column at height `≥ L`, given `main` for the
node below `y`. -/
theorem left_in_cone (S : Setup F root rho cap) {y w pl : F.Node} (hcone : Cone F root y.1)
    (hyr : y.1 ≠ root.1) (hwr : Real w) (hwy : F.upper w = some y) (hwc : w.1 = y.1)
    (hLw : F.height root ≤ F.height w) (hycap : F.height y < cap) (hpl : F.P w = some pl)
    (hIH : F.height rho ≤ F.height w → Concl F root cap w pl) :
    Cone F root pl.1 ∧ F.height root ≤ F.height pl := by
  by_cases hwC : F.height rho ≤ F.height w
  · rcases hIH hwC with h | h
    · exact h
    · rw [aboveHeight_of_upper hwy] at h
      exact absurd hycap (not_lt.mpr h)
  · have hwL : F.height w = F.height root := by
      rcases S.C_cases with hCL | hCL
      · exact absurd (by rw [hCL]; exact hLw) hwC
      · exact row_eq_of_lt_bump0 hLw (by rw [← hCL]; exact lt_of_not_ge hwC)
    obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
    have he : low = w := node_eq_of_column_height S.ordered (hlc.trans hwc.symm)
      (hlh.trans hwL.symm)
    subst he
    obtain ⟨next, hnext, hnr, hnh, hnpath, _⟩ :=
      S.low_parent hlr hlh hlpath (by rw [hwc]; exact hyr)
    have : next = pl := Option.some.inj (hnext.symm.trans hpl)
    subst this
    exact ⟨⟨next, hnr, rfl, hnh, hnpath⟩, hnh.ge⟩

/-! ## The search -/

/-- **The search from a candidate in the cone.** -/
theorem trace (S : Setup F root rho cap) {u p : F.Node} (hcap : F.height u < cap)
    (hIH : ∀ (w pw : F.Node), w.1.val < u.1.val → Cone F root w.1 → Real w →
      F.height rho ≤ F.height w → F.height w < cap → F.P w = some pw → Concl F root cap w pw)
    (hpu : 0 < F.value p ∧ F.value p < F.value u) :
    ∀ (c : Nat) (y : F.Node), y.1.val = c → y.1.val < u.1.val → Cone F root y.1 →
      F.height rho ≤ F.height y → F.height y ≤ F.height u → Hit F (F.value u) y p →
      (Cone F root p.1 ∧ F.height root ≤ F.height p) ∨
        cap ≤ Row.B (F.height u) (F.height p) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
  intro y hyc hyu hcone hyC hyh hit
  have hO := S.ordered
  have hyreal : Real y :=
    real_of_one_le_height hO ((one_le_height hO S.rhoReal).trans hyC)
  cases hit with
  | here _ _ => exact Or.inl ⟨hcone, S.L_le_C.trans hyC⟩
  | @next _ y' _ hreject hQ rest =>
    have hvy : F.value u ≤ F.value y := by
      by_contra h
      exact hreject ⟨hO.real_positive y hyreal, lt_of_not_ge h⟩
    by_cases hyr : y.1 = root.1
    · -- `y = ρ`
      have he := S.only hyr hyC (lt_of_le_of_lt hyh hcap)
      subst he
      obtain ⟨r, h1, h2⟩ := rest.loosen hvy
      have hr : F.P y = some r := (P_iff hO).mpr ⟨y', hQ, h1⟩
      obtain ⟨v, hv⟩ := S.normal.upper_of_parent hr
      have hb := S.barrier v hv
      rw [← aboveHeight_of_upper hv, S.normal.above_row hr] at hb
      exact Or.inr (hb.trans (B_subinterval hyh (P_height_le hO hr) (h2.height_le hO)))
    · obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
      rcases eq_or_lt_of_le (S.L_le_C.trans hyC) with hL | hL
      · -- `height y = L`: continue from the parent of `y`
        have he : low = y := node_eq_of_column_height hO hlc (hlh.trans hL)
        subst he
        obtain ⟨next, hnext, hnr, hnh, hnpath, hncol⟩ := S.low_parent hlr hlh hlpath hyr
        have hfull : Hit F (F.value u) low p := .next hreject hQ rest
        obtain ⟨r, h1, h2⟩ := hfull.loosen hvy
        have hr : F.P low = some r := by
          cases h1 with
          | here _ hs => exact absurd hs (lt_irrefl _)
          | next _ hQ2 rest2 => exact (P_iff hO).mpr ⟨_, hQ2, rest2⟩
        have : r = next := Option.some.inj (hr.symm.trans hnext)
        subst this
        exact ih r.1.val (by omega) r rfl (by omega) ⟨r, hnr, rfl, hnh, hnpath⟩
          (by rw [hnh, hL]; exact hyC) (by rw [hnh, hL]; exact hyh) h2
      · -- `height y > L`: the candidate of `y` stays in the cone
        obtain ⟨w, hwr, hwy, hwc, hLw⟩ := S.lower ⟨low, hlr, hlc, hlh, hlpath⟩ hL
        obtain ⟨pl, hpl, _, _, hleft⟩ := S.normal.upper_step w y hwr hwy
        have hin := S.left_in_cone ⟨low, hlr, hlc, hlh, hlpath⟩ hyr hwr hwy hwc hLw
          (lt_of_le_of_lt hyh hcap) hpl
          (fun hwC => hIH w pl (by rw [hwc]; exact hyu) (by rw [hwc]; exact ⟨low, hlr, hlc, hlh, hlpath⟩)
            hwr hwC (lt_of_lt_of_le (height_lt_of_index_lt hO hwc
              (by obtain ⟨_, hi⟩ := upper_spec hwy; omega)) (le_of_lt (lt_of_le_of_lt hyh hcap)))
            hpl)
        obtain ⟨q, hq, hqc, hqC, hqy⟩ := S.Q_control hin.1 hin.2 hleft hyC
        have : y' = q := Option.some.inj (hQ.symm.trans hq)
        subst this
        have hqcol := Q_column_lt hO hq
        exact ih y'.1.val (by omega) y' rfl (by omega) (by rw [hqc]; exact hin.1) hqC
          (hqy.trans hyh) rest

/-! ## The theorem -/

/-- **Parents inside the cone.** -/
theorem main (S : Setup F root rho cap) :
    ∀ (c : Nat) (u p : F.Node), u.1.val = c → Cone F root u.1 → Real u →
      F.height rho ≤ F.height u → F.height u < cap → F.P u = some p → Concl F root cap u p := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c outer =>
  intro u
  generalize hi : u.2.val = i
  induction i using Nat.strongRecOn generalizing u with
  | ind i inner =>
  intro p hc hcone hreal hC hcap hp
  have hO := S.ordered
  by_cases hroot : u.1 = root.1
  · have he := S.only hroot hC hcap
    subst he
    right
    obtain ⟨v, hv⟩ := S.normal.upper_of_parent hp
    rw [aboveHeight_of_upper hv]
    exact S.barrier v hv
  · obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
    rcases eq_or_lt_of_le (S.L_le_C.trans hC) with hL | hL
    · -- `u` is the node of its column at height `L`
      have he : low = u := node_eq_of_column_height hO hlc (hlh.trans hL)
      subst he
      obtain ⟨next, hnext, hnr, hnh, hnpath, _⟩ := S.low_parent hlr hlh hlpath hroot
      have : next = p := Option.some.inj (hnext.symm.trans hp)
      subst this
      exact Or.inl ⟨⟨next, hnr, rfl, hnh, hnpath⟩, hnh.ge⟩
    · obtain ⟨w, hwr, hwu, hwc, hLw⟩ := S.lower ⟨low, hlr, hlc, hlh, hlpath⟩ hL
      obtain ⟨pl, hpl, _, _, hleft⟩ := S.normal.upper_step w u hwr hwu
      have hwi : w.2.val < i := by obtain ⟨_, hi'⟩ := upper_spec hwu; omega
      have hin := S.left_in_cone ⟨low, hlr, hlc, hlh, hlpath⟩ hroot hwr hwu hwc hLw hcap hpl
        (fun hwC => inner w.2.val hwi w rfl pl (by rw [hwc]; exact hc)
          (by rw [hwc]; exact ⟨low, hlr, hlc, hlh, hlpath⟩) hwr hwC
          (lt_trans (height_lt_of_index_lt hO hwc (by omega)) hcap) hpl)
      obtain ⟨q, hq, hqc, hqC, hqu⟩ := S.Q_control hin.1 hin.2 hleft hC
      obtain ⟨q', hQ', hit⟩ := (P_iff hO).mp hp
      have : q' = q := Option.some.inj (hQ'.symm.trans hq)
      subst this
      have hqcol := Q_column_lt hO hq
      have hT := trace S hcap
        (fun w pw hw hwc' hwr' hwC' hwcap' hpw =>
          outer w.1.val (by omega) w pw rfl hwc' hwr' hwC' hwcap' hpw)
        (P_value hO hp) q'.1.val q' rfl hqcol (by rw [hqc]; exact hin.1) hqC hqu hit
      rcases hT with h | h
      · exact Or.inl h
      · right
        rw [S.normal.above_row hp]
        exact h

/-- **Legs inside the cone.** The left end of the edge below a node `u` of a cone column with
`C < height u < cap` is at or right of the root column. -/
theorem legRight (S : Setup F root rho cap) {v u p : F.Node} (hvu : F.upper v = some u)
    (hv : Real v) (hcone : Cone F root u.1) (hC : F.height rho < F.height u)
    (hcap : F.height u < cap) (hp : F.P v = some p) : root.1.val ≤ p.1.val := by
  have hO := S.ordered
  have hur : u.1 ≠ root.1 := by
    intro h
    have he := S.only h (le_of_lt hC) hcap
    subst he
    exact lt_irrefl _ hC
  obtain ⟨hvc, _⟩ := upper_spec hvu
  have hL : F.height root < F.height u := lt_of_le_of_lt S.L_le_C hC
  obtain ⟨w, hwr, hwu, hwc, hLw⟩ := S.lower hcone hL
  have hwv : w = v := by
    obtain ⟨_, h1⟩ := upper_spec hwu
    obtain ⟨_, h2⟩ := upper_spec hvu
    rcases w with ⟨c1, i1⟩
    rcases v with ⟨c2, i2⟩
    dsimp only at hwc hvc h1 h2
    have hc12 : c1 = c2 := hwc.trans hvc
    subst hc12
    have : i1 = i2 := Fin.ext (by omega)
    subst this
    rfl
  subst hwv
  have hin := S.left_in_cone hcone hur hv hvu hwc hLw hcap hp
    (fun hwC => main S w.1.val w p rfl (by rw [hwc]; exact hcone) hv hwC
      (lt_trans (height_lt_of_index_lt hO hwc
        (by obtain ⟨_, h⟩ := upper_spec hvu; omega)) hcap) hp)
  obtain ⟨low, _, hlc, _, hlpath⟩ := hin.1
  rw [← hlc]
  exact hlpath.column_le hO

end Setup

end OmegaY.Official.Recon.LowerPB.Cone

#print axioms OmegaY.Official.Recon.LowerPB.Cone.Setup.main
#print axioms OmegaY.Official.Recon.LowerPB.Cone.Setup.legRight
