/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeMD.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RootInterval
import Googology.Notation.OmegaY.WellOrder.OmegaY.Rows.EdgeTransport
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawAscend

set_option backward.do.legacy false

/-!
# (MD) from the source mountain

`MDSource`: in the canonical mountain `M(s)`, in every region `S` of level `≥ 2` below `τ`
that contains a node of the root column, the top of the last column `x₀` is in a higher slot
than the top `ρ` of the root column. `mdHolds_of_source`: this gives `MDHolds`.

The proof (`md_core`) works in Phyrion's frame of `M(s)`:

* the top edge `t⁻ → t` has the father `r` (the root); by the row shadow of this edge
  (`P_rowShadow`), the column `x₀` has a node `v` at the row of `ρ` with a parent path to `ρ`;
  so `x₀` is in the root cone of `ρ`;
* level 2: the node above `v` has the row `row ρ + 1`, in the next slot;
* level `d + 2 ≥ 3`: if the top `κ` of `x₀` in `S` were in the slot of `ρ`, the node above `κ`
  leaves `S`. By the root-interval closure (`root_interval_parent_bump`, cap
  `bump(row ρ, d)`), the father `p` of that edge is either in the interval, and then the node
  above `κ` stays below the cap (`B_le_cap_of_same_interval`), or left of the root column.
  Up a column the fathers move left (`P_upper_column_le`), so the father `r` of the top edge
  would also be left of the root column: a contradiction.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs Geometry

/-! ## Frame facts -/

/-- Up a column, the fathers of the edges move left. -/
theorem P_upper_column_le {F : Frame} (hF : F.Normal) {u v p p' : F.Node} (hu : Frame.Real u)
    (hv : F.upper u = some v) (hp : F.P u = some p) (hp' : F.P v = some p') :
    p'.1.val ≤ p.1.val := by
  obtain ⟨p0, hp0, _, _, hleft⟩ := hF.upper_step u v hu hv
  rw [hp] at hp0
  cases hp0
  obtain ⟨q, hQ, hit⟩ := (Frame.P_iff hF.toOrdered).mp hp'
  obtain ⟨left, hcell, _, _, hq1, _⟩ := Frame.Q_spec hF.toOrdered hQ
  rw [hleft] at hcell
  have href : Frame.ref p = Frame.ref left := Option.some.inj hcell
  have hcol : p.1.val = left.1.val := congrArg Canonical.Ref.column href
  have h1 := hit.column_le hF.toOrdered
  rw [hq1] at h1
  omega

/-- Along a column, the father of a higher edge is not right of the father of a lower one. -/
theorem P_column_le_of_index {F : Frame} (hF : F.Normal) :
    ∀ (n : Nat) (a b : F.Node), a.1 = b.1 → b.2.val = a.2.val + n → Frame.Real a →
      (∃ w, F.upper b = some w) → ∀ pa pb, F.P a = some pa → F.P b = some pb →
        pb.1.val ≤ pa.1.val
  | 0, a, b, hc, hi, _, _, pa, pb, ha, hb => by
      have hab : a = b := by
        rcases a with ⟨c, i⟩
        rcases b with ⟨c', i'⟩
        dsimp only at hc hi
        subst hc
        have : i = i' := Fin.ext (by omega)
        subst this
        rfl
      subst hab
      rw [ha] at hb
      cases hb
      exact le_rfl
  | n + 1, a, b, hc, hi, hreal, hup, pa, pb, ha, hb => by
      rcases a with ⟨c, i⟩
      rcases b with ⟨c', j⟩
      dsimp only at hc hi hreal
      subst hc
      obtain ⟨⟨wc, wi⟩, hw⟩ := hup
      obtain ⟨hwc, hwi⟩ := Frame.upper_spec hw
      dsimp only at hwc hwi
      cases hwc
      have hjlt : j.val + 1 < F.length c := by have := wi.isLt; omega
      have hlt : i.val + 1 < F.length c := by omega
      let a' : F.Node := ⟨c, ⟨i.val + 1, hlt⟩⟩
      have hup' : F.upper ⟨c, i⟩ = some a' := ControlProof.upper_eq_of_index rfl rfl
      have hreal' : Frame.Real a' := by show 0 < i.val + 1; omega
      have hlt2 : i.val + 1 + 1 < F.length c := by omega
      let a'' : F.Node := ⟨c, ⟨i.val + 1 + 1, hlt2⟩⟩
      have hup'' : F.upper a' = some a'' := ControlProof.upper_eq_of_index rfl rfl
      obtain ⟨pa', hpa', _, _, _⟩ := hF.upper_step a' a'' hreal' hup''
      have h1 := P_upper_column_le hF hreal hup' ha hpa'
      have h2 := P_column_le_of_index hF n a' ⟨c, j⟩ rfl (by show j.val = i.val + 1 + n; omega)
        hreal' ⟨_, hw⟩ pa' pb hpa' hb
      omega

/-- **The core of (MD)**, in the frame. -/
theorem md_core {F : Frame} (hF : F.Normal) {d : Nat} (hd : 1 ≤ d)
    {ρ tm r κ κu : F.Node} (hρ : Frame.Real ρ) (hr : F.P tm = some r)
    (htmup : ∃ w, F.upper tm = some w)
    (hrcol : r.1 = ρ.1) (hρr : F.height ρ ≤ F.height r)
    (hbar : ∀ w, F.upper ρ = some w → Row.bump (F.height ρ) d ≤ F.height w)
    (hκ : Frame.Real κ) (hκcol : κ.1 = tm.1) (hκidx : κ.2.val ≤ tm.2.val)
    (hκlo : F.height ρ ≤ F.height κ) (hκhi : F.height κ < Row.bump (F.height ρ) d)
    (hκu : F.upper κ = some κu) (hκuhi : Row.bump (F.height ρ) (d + 1) ≤ F.height κu) :
    False := by
  -- the column of `t` is in the root cone of `ρ`
  obtain ⟨v, hv, hvcol, _, hvh, hpath⟩ :=
    Frame.P_rowShadow hF hr ρ hρ hrcol.symm hρr
  have hcone : Frame.RootCone F ρ κ := ⟨v, hv, hvcol.trans hκcol.symm, hvh, hpath⟩
  have hint : Frame.RootInterval F ρ (Row.bump (F.height ρ) d) κ := ⟨hcone, hκlo, hκhi⟩
  obtain ⟨p, hp, hrow, _, _⟩ := hF.upper_step κ κu hκ hκu
  rcases Frame.root_interval_parent_bump hF hρ (by omega) hbar hp hint with hpi | ⟨hbr, _⟩
  · -- the father is in the interval: the edge stays below the cap
    obtain ⟨_, hplo, hphi⟩ := hpi
    have hle := Row.B_le_cap_of_same_interval hκlo hκhi hplo hphi
    rw [← hrow] at hle
    have := Row.bump_strictMono_exponent (F.height ρ) (show d < d + 1 by omega)
    exact absurd (lt_of_le_of_lt hle this) (not_lt.mpr hκuhi)
  · -- the father is left of the root column; so is the father of the top edge
    have hmono := P_column_le_of_index hF (tm.2.val - κ.2.val) κ tm hκcol (by omega) hκ htmup
      p r hp hr
    have := hbr.1
    rw [hrcol] at hmono
    omega

/-- Level 2: the node above the shadow of `ρ` in the column of `t` has the row `row ρ + 1`. -/
theorem md_two {F : Frame} (hF : F.Normal) {ρ tm r : F.Node} (hρ : Frame.Real ρ)
    (hr : F.P tm = some r) {tt : F.Node} (htt : F.upper tm = some tt)
    (hrcol : r.1 = ρ.1) (hρr : F.height ρ ≤ F.height r) :
    ∃ v v' : F.Node, Frame.Real v ∧ v.1 = tm.1 ∧ F.height v = F.height ρ ∧
      F.upper v = some v' ∧ F.height v' = Row.bump (F.height ρ) 0 := by
  obtain ⟨v, hv, hvcol, hvle, hvh, hpath⟩ := Frame.P_rowShadow hF hr ρ hρ hrcol.symm hρr
  -- `v` is below `tt`, so it has an upper node
  obtain ⟨htc, hti⟩ := Frame.upper_spec htt
  have hvidx : v.2.val ≤ tm.2.val := by
    by_contra hn
    have hlt : tm.2.val < v.2.val := by omega
    rcases v with ⟨vc, vi⟩
    rcases tm with ⟨tc, ti⟩
    dsimp only at hvcol hlt hvle
    subst hvcol
    exact absurd hvle (not_le.mpr (hF.rows_strict vc hlt))
  have hlen : v.2.val + 1 < F.length v.1 := by
    rcases v with ⟨vc, vi⟩
    rcases tt with ⟨c1, i1⟩
    rcases tm with ⟨tc, ti⟩
    dsimp only at hvcol htc hti hvidx ⊢
    subst hvcol
    subst htc
    have := i1.isLt
    omega
  let v' : F.Node := ⟨v.1, ⟨v.2.val + 1, hlen⟩⟩
  have hup : F.upper v = some v' := ControlProof.upper_eq_of_index rfl rfl
  obtain ⟨q, hq, hrow, _, _⟩ := hF.upper_step v v' hv hup
  -- the first step of the parent path stays in the row of `ρ`
  have hqh : F.height q = F.height v := by
    cases hpath with
    | refl =>
        exfalso
        have := Frame.P_column_lt hF.toOrdered hr
        rw [hrcol, ← hvcol] at this
        exact lt_irrefl _ this
    | cons hq' rest =>
        rw [hq] at hq'
        cases hq'
        exact le_antisymm (Frame.P_height_le hF.toOrdered hq)
          (by rw [hvh]; exact rest.height_le hF.toOrdered)
  refine ⟨v, v', hv, hvcol, hvh, hup, ?_⟩
  rw [hrow, hqh, hvh, Row.B_self]

/-! ## Rows -/

theorem official_le_self (a : Row) : official a ≤ a := by
  apply Row.le_of_coeff_le
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · by_cases hf : isFinite a = true
    · rw [Recon.coeff_official_zero a hf]; omega
    · unfold official; rw [if_neg hf]
  · rw [Recon.coeff_official_pos a hi]

theorem bump_official {a : Row} {d : Nat} (hd : 1 ≤ d) :
    Row.bump (official a) d = Row.bump a d := by
  apply Row.ext
  intro k
  rcases Nat.lt_trichotomy k d with hk | rfl | hk
  · rw [Row.coeff_bump_low hk, Row.coeff_bump_low hk]
  · rw [Row.coeff_bump_at, Row.coeff_bump_at, Recon.coeff_official_pos a hd]
  · rw [Row.coeff_bump_high hk, Row.coeff_bump_high hk, Recon.coeff_official_pos a (by omega)]

theorem lt_bump_of_official_lt {a b : Row} {d : Nat} (hd : 1 ≤ d)
    (h : official a < Row.bump b d) : a < Row.bump b d := by
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [Row.coeff_bump_low (show 0 < d by omega)] at hlt
    omega
  · refine Row.lt_iff.mpr ⟨i, fun j hj => ?_, ?_⟩
    · rw [← Recon.coeff_official_pos a (by omega : 1 ≤ j)]
      exact hi j hj
    · rw [← Recon.coeff_official_pos a hpos]
      exact hlt

/-- A row above a row of a region, outside the region, is at or above the next region. -/
theorem bump_le_of_not_mem {d : Nat} {S ρ w : Row} (hρ : inRegion (d + 2) S ρ = true)
    (hw : inRegion (d + 2) S w = false) (hlt : ρ < w) : Row.bump ρ (d + 1) ≤ w := by
  obtain ⟨i, hi, hlti⟩ := Row.lt_iff.mp hlt
  have hid : d + 1 ≤ i := by
    by_contra hn
    have : inRegion (d + 2) S w = true := by
      rw [Recon.RowLaw.inRegion_iff'] at hρ ⊢
      intro k hk
      rw [← hi k (by omega)]
      exact hρ k hk
    rw [this] at hw
    cases hw
  calc Row.bump ρ (d + 1) ≤ Row.bump ρ i := Row.bump_mono_exponent ρ hid
    _ ≤ w := by
      apply Row.le_of_coeff_le
      intro j
      rcases Nat.lt_trichotomy j i with hj | rfl | hj
      · rw [Row.coeff_bump_low hj]; exact Nat.zero_le _
      · rw [Row.coeff_bump_at]; omega
      · rw [Row.coeff_bump_high hj, hi j hj]

/-- A row in the slot of `ρ` is below the next slot. -/
theorem lt_bump_of_same_slot {d : Nat} {S ρ κ : Row} (hρ : inRegion (d + 2) S ρ = true)
    (hκ : inRegion (d + 2) S κ = true) (hσ : κ.coeff d = ρ.coeff d) : κ < Row.bump ρ d := by
  refine Row.lt_iff.mpr ⟨d, fun j hj => ?_, ?_⟩
  · rw [Row.coeff_bump_high hj, Recon.RowLaw.inRegion_iff'.mp hκ j (by omega),
      Recon.RowLaw.inRegion_iff'.mp hρ j (by omega)]
  · rw [Row.coeff_bump_at, hσ]
    omega

/-- In a region of level 2, a larger row has a larger height. -/
theorem coeff_lt_of_lt_two {S a b : Row} (ha : inRegion 2 S a = true) (hb : inRegion 2 S b = true)
    (h : a < b) : a.coeff 0 < b.coeff 0 := by
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp h
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hlt
  · rw [Recon.RowLaw.inRegion_iff'.mp ha i (by omega),
      Recon.RowLaw.inRegion_iff'.mp hb i (by omega)] at hlt
    exact absurd hlt (lt_irrefl _)

/-! ## Frame nodes of the mountain -/

theorem frame_of_mem {M : Mountain} {c : Nat} {p : Ref × Cell} (hp : p ∈ realNodes M c) :
    ∃ n : (Frame.ofMountain M).Node, Frame.ref n = p.1 ∧ (Frame.ofMountain M).cell n = p.2 ∧
      Frame.Real n ∧ n.1.val = c := by
  obtain ⟨col, k, hcol, hcell, hp1⟩ := Recon.mem_realNodes_iff.mp hp
  obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hcol
  have hks : k + 1 < M[c].size := by
    rw [hcolEq]; exact (Array.getElem?_eq_some_iff.mp hcell).1
  refine ⟨⟨⟨c, hcs⟩, ⟨k + 1, hks⟩⟩, by rw [hp1]; rfl, ?_, by show 0 < k + 1; omega, rfl⟩
  show M[c][k + 1] = p.2
  have := hcell
  rw [← hcolEq] at this
  exact Option.some.inj ((Array.getElem?_eq_getElem hks).symm.trans this)

theorem mem_of_frame {M : Mountain} (n : (Frame.ofMountain M).Node) (hn : Frame.Real n) :
    (Frame.ref n, (Frame.ofMountain M).cell n) ∈ realNodes M n.1.val :=
  mem_realNodes_of_cell' (ControlProof.cell?_ref n) hn

theorem height_le_of_index {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (hi : a.2.val ≤ b.2.val) : F.height a ≤ F.height b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨c', j⟩
  dsimp only at hc hi
  subst hc
  exact (hF.rows_strict c).monotone (show i ≤ j from hi)

theorem height_lt_of_index {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (hi : a.2.val < b.2.val) : F.height a < F.height b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨c', j⟩
  dsimp only at hc hi
  subst hc
  exact hF.rows_strict c (show i < j from hi)

theorem index_lt_of_height {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (h : F.height a < F.height b) : a.2.val < b.2.val := by
  by_contra hn
  exact absurd h (not_lt.mpr (height_le_of_index hF hc.symm (by omega)))

/-! ## (MD) in the source mountain -/

/-- (MD, source form) In every region of level `≥ 2` below `τ` that contains a node of the
root column, the top of the last column is in a higher slot than the top of the root column. -/
def MDSource : Prop :=
  ∀ (s : List Nat) (M : Mountain), Canonical.build s = .ok M →
    ∀ (col : Column) (t : Cell), M[M.size - 1]? = some col → col.back? = some t →
    ∀ root : Ref, t.left = some root → official t.row ≠ 0 →
    ∀ (d : Nat) (S : Row), (∀ r, inRegion (d + 2) S r = true → r < official t.row) →
    ∀ ρr ρc, topIn M root.column (d + 2) S = some (ρr, ρc) →
      heightOf (d + 2) (some (ρr, ρc)) < heightOf (d + 2) (topIn M (M.size - 1) (d + 2) S)

theorem md_source : MDSource := by
  intro s M hb col t hcol ht root htl h0 d S hbelow ρr ρc hρ
  have hV := build_valid_of_success hb
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hXs, hcolEq⟩ := column_of_getElem? hcol
  obtain ⟨hpos, htop⟩ := back?_spec ht
  have hCV : ColumnValid M (M.size - 1) col := hcolEq ▸ hV _ hXs
  have hsz := hCV.size_ge_two
  -- `t` is not the bottom
  have hk2 : 2 ≤ col.size - 1 := by
    by_contra hn
    have he : col.size - 1 = 1 := by omega
    rw [he] at htop
    apply h0
    rw [hCV.bottom_row t htop]
    exact official_one
  -- the frame nodes of the top edge
  have hkF : col.size - 1 < M[M.size - 1].size := by rw [hcolEq]; omega
  have hk1F : col.size - 1 - 1 < M[M.size - 1].size := by rw [hcolEq]; omega
  let nt : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hXs⟩, ⟨col.size - 1, hkF⟩⟩
  let ntm : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hXs⟩, ⟨col.size - 1 - 1, hk1F⟩⟩
  have hup : (Frame.ofMountain M).upper ntm = some nt :=
    ControlProof.upper_eq_of_index rfl (by show col.size - 1 = col.size - 1 - 1 + 1; omega)
  have hntcell : (Frame.ofMountain M).cell nt = t := by
    have h1 : cell? M ⟨M.size - 1, col.size - 1⟩ = some t := by simp [cell?, hcol, htop]
    exact Option.some.inj ((ControlProof.cell?_ref nt).symm.trans h1)
  have hleft' : ((Frame.ofMountain M).cell nt).left = some root := by rw [hntcell]; exact htl
  obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid nt root hleft'
  have hnr : Frame.ref nr = root := Frame.lookup_spec hlk
  have hleft'' : ((Frame.ofMountain M).cell nt).left = some (Frame.ref nr) := by
    rw [hnr]; exact hleft'
  have hrawF : (Frame.ofMountain M).rawParent ntm = some nr :=
    Frame.rawParent_eq_of_upper_left hup hleft''
  have hntmReal : Frame.Real ntm := by show 0 < col.size - 1 - 1; omega
  have hP : (Frame.ofMountain M).P ntm = some nr :=
    (hN.rawParent_eq_P hntmReal).symm.trans hrawF
  -- the rows of `t`
  have ht1 : (1 : Row) ≤ t.row := by
    have := mem_of_frame nt (show 0 < col.size - 1 by omega)
    rw [hntcell] at this
    exact Recon.realNodes_row_one_le hV this
  -- the node `ρ`
  obtain ⟨hρmem, hρreg, hρmax⟩ := Recon.RowLaw.topIn_spec hρ
  simp only at hρreg
  obtain ⟨nρ, hnρref, hnρcell, hnρreal, hnρcol⟩ := frame_of_mem hρmem
  simp only at hnρref hnρcell
  have hρ1 : (1 : Row) ≤ ρc.row := Recon.realNodes_row_one_le hV hρmem
  have hrcol : nr.1 = nρ.1 := Fin.ext (by
    rw [hnρcol]
    show (Frame.ref nr).column = root.column
    rw [hnr])
  -- `ρ` is at or below the root `r`
  have hρt : ρc.row < t.row := by
    by_contra hn
    have := Recon.official_mono ht1 (not_lt.mp hn)
    exact absurd (hbelow _ hρreg) (not_lt.mpr this)
  have hraw : Reserve.rawParent M (Frame.ref ntm) = some root := by
    rw [ControlProof.rawParent_ref, hup]
    simpa using hleft'
  have hvt : cell? M ⟨(Frame.ref ntm).column, (Frame.ref ntm).index + 1⟩ = some t := by
    have := ControlProof.cell?_ref nt
    rw [hntcell] at this
    have e : (⟨(Frame.ref ntm).column, (Frame.ref ntm).index + 1⟩ : Ref) = Frame.ref nt := by
      show (⟨M.size - 1, col.size - 1 - 1 + 1⟩ : Ref) = ⟨M.size - 1, col.size - 1⟩
      congr 1
      omega
    rw [e]
    exact this
  obtain ⟨cp, hcp, _, hcpmax⟩ :=
    canonical_rawParent_highest_below (build_success_legal hb) hb hvt hraw
  obtain ⟨hρc, _, hρcell⟩ := mem_realNodes hρmem
  simp only at hρc hρcell
  have hρidx : ρr.index ≤ root.index := by
    apply hcpmax ρr.index ρc _ hρt
    rw [← hρc]
    exact hρcell
  have hρr : (Frame.ofMountain M).height nρ ≤ (Frame.ofMountain M).height nr := by
    apply height_le_of_index hO hrcol.symm
    show (Frame.ref nρ).index ≤ (Frame.ref nr).index
    rw [hnρref, hnr]
    exact hρidx
  have hhρ : (Frame.ofMountain M).height nρ = ρc.row := by
    unfold Frame.height; rw [hnρcell]
  -- the shadow of `ρ` in the last column
  obtain ⟨v, hv, hvcol, _, hvh, _⟩ := Frame.P_rowShadow hN hP nρ hnρreal hrcol.symm hρr
  have hvmem := mem_of_frame v hv
  have hvX : v.1.val = M.size - 1 := by rw [hvcol]
  rw [hvX] at hvmem
  have hvrow : ((Frame.ofMountain M).cell v).row = ρc.row := by
    have := hvh
    unfold Frame.height at this
    rw [this, hnρcell]
  have hvreg : inRegion (d + 2) S (official ((Frame.ofMountain M).cell v).row) = true := by
    rw [hvrow]; exact hρreg
  -- the top of the last column in `S`
  cases hκ : topIn M (M.size - 1) (d + 2) S with
  | none =>
      exfalso
      have := Recon.RowLaw.topIn_none hκ _ hvmem
      simp only at this
      rw [hvreg] at this
      cases this
  | some κ =>
      obtain ⟨κr, κc⟩ := κ
      obtain ⟨hκmem, hκreg, hκmax⟩ := Recon.RowLaw.topIn_spec hκ
      simp only at hκreg
      simp only [heightOf, Recon.RowLaw.height_eq]
      obtain ⟨nκ, hnκref, hnκcell, hnκreal, hnκcol⟩ := frame_of_mem hκmem
      simp only at hnκref hnκcell
      have hκ1 : (1 : Row) ≤ κc.row := Recon.realNodes_row_one_le hV hκmem
      -- `v ≤ κ`
      have hvκ : v.2.val ≤ nκ.2.val := by
        have := hκmax _ hvmem hvreg
        simp only at this
        rw [← hnκref] at this
        exact this
      have hvκc : v.1 = nκ.1 := Fin.ext (by rw [hvX, hnκcol])
      have hρκ : ρc.row ≤ κc.row := by
        have := height_le_of_index hO hvκc hvκ
        unfold Frame.height at this
        rw [hnκcell, hvrow] at this
        exact this
      have hσ : (official ρc.row).coeff d ≤ (official κc.row).coeff d :=
        Recon.RowLaw.coeff_le_of_inRegion hρreg hκreg (Recon.official_mono hρ1 hρκ)
      by_contra hle
      have hσeq : (official κc.row).coeff d = (official ρc.row).coeff d := by omega
      -- `κ` is below `t`
      have hκt : κc.row < t.row := by
        by_contra hn
        have := Recon.official_mono ht1 (not_lt.mp hn)
        exact absurd (hbelow _ hκreg) (not_lt.mpr this)
      have hκntc : nκ.1 = nt.1 := Fin.ext (by rw [hnκcol])
      have hκidx : nκ.2.val < col.size - 1 := by
        have := index_lt_of_height hO hκntc (by
          unfold Frame.height
          rw [hnκcell, hntcell]
          exact hκt)
        exact this
      have hκlen : nκ.2.val + 1 < (Frame.ofMountain M).length nt.1 := by
        show nκ.2.val + 1 < M[M.size - 1].size
        rw [hcolEq]
        omega
      let nκu : (Frame.ofMountain M).Node := ⟨nt.1, ⟨nκ.2.val + 1, hκlen⟩⟩
      have hκup : (Frame.ofMountain M).upper nκ = some nκu :=
        ControlProof.upper_eq_of_index hκntc rfl
      have hκureal : Frame.Real nκu := by show 0 < nκ.2.val + 1; omega
      have hκumem := mem_of_frame nκu hκureal
      have hκuX : nκu.1.val = M.size - 1 := rfl
      rw [hκuX] at hκumem
      have hκulow : κc.row < ((Frame.ofMountain M).cell nκu).row := by
        have := height_lt_of_index hO (show nκ.1 = nκu.1 from hκntc)
          (show nκ.2.val < nκ.2.val + 1 by omega)
        unfold Frame.height at this
        rw [hnκcell] at this
        exact this
      have hκuout : inRegion (d + 2) S (official ((Frame.ofMountain M).cell nκu).row) = false := by
        by_contra hin
        have hin' : inRegion (d + 2) S (official ((Frame.ofMountain M).cell nκu).row) = true := by
          simpa using hin
        have := hκmax _ hκumem hin'
        simp only at this
        rw [← hnκref] at this
        exact absurd this (by show ¬ (nκ.2.val + 1 ≤ nκ.2.val); omega)
      have hκuhi : Row.bump (official ρc.row) (d + 1) ≤
          official ((Frame.ofMountain M).cell nκu).row :=
        bump_le_of_not_mem hρreg hκuout
          (lt_of_le_of_lt (Recon.official_mono hρ1 hρκ) (Recon.official_strictMono hκ1 hκulow))
      rcases Nat.eq_zero_or_pos d with hd0 | hd1
      · -- level 2: the node above the shadow is in the next slot
        subst hd0
        obtain ⟨v2, v2', hv2, hv2col, hv2h, hv2up, hv2'h⟩ :=
          md_two hN hnρreal hP hup hrcol hρr
        have hv2'real : Frame.Real v2' := by
          obtain ⟨_, hi2⟩ := Frame.upper_spec hv2up
          show 0 < v2'.2.val
          omega
        have hv2'mem := mem_of_frame v2' hv2'real
        have hv2'X : v2'.1.val = M.size - 1 := by
          obtain ⟨hc2, _⟩ := Frame.upper_spec hv2up
          rw [hc2, hv2col]
        rw [hv2'X] at hv2'mem
        have hrow2 : ((Frame.ofMountain M).cell v2').row = Row.bump ρc.row 0 := by
          have := hv2'h
          unfold Frame.height at this
          rw [this, hnρcell]
        have hreg2 : inRegion (0 + 2) S (official ((Frame.ofMountain M).cell v2').row) = true := by
          rw [Recon.RowLaw.inRegion_iff'] at hρreg ⊢
          intro k hk
          rw [Recon.coeff_official_pos _ (by omega), hrow2, Row.coeff_bump_high (by omega),
            ← Recon.coeff_official_pos _ (by omega)]
          exact hρreg k hk
        have hlt2 : official ρc.row < official ((Frame.ofMountain M).cell v2').row := by
          apply Recon.official_strictMono hρ1
          rw [hrow2]
          exact Row.lt_bump _ 0
        have h2 := coeff_lt_of_lt_two hρreg hreg2 hlt2
        -- `v2'` is at or below `κ`
        have hmax2 := hκmax _ hv2'mem hreg2
        simp only at hmax2
        rw [← hnκref] at hmax2
        have hv2'κc : v2'.1 = nκ.1 := Fin.ext (by rw [hv2'X, hnκcol])
        have hle2 := height_le_of_index hO hv2'κc hmax2
        unfold Frame.height at hle2
        rw [hnκcell] at hle2
        have h3 := Recon.RowLaw.coeff_le_of_inRegion hreg2 hκreg
          (Recon.official_mono (one_le_row hV (ControlProof.cell?_ref v2') hv2'real) hle2)
        omega
      · -- level `d + 2 ≥ 3`: the root-interval argument
        apply md_core hN (d := d) hd1 hnρreal hP ⟨nt, hup⟩ hrcol hρr ?_ hnκreal
          (show nκ.1 = ntm.1 from hκntc) (show nκ.2.val ≤ col.size - 1 - 1 by omega) ?_ ?_ hκup ?_
        · -- the barrier above `ρ`
          intro w hw
          obtain ⟨hwc, hwi⟩ := Frame.upper_spec hw
          have hwreal : Frame.Real w := by show 0 < w.2.val; omega
          have hwmem := mem_of_frame w hwreal
          have hwcr : w.1.val = root.column := by rw [hwc, hnρcol]
          rw [hwcr] at hwmem
          have hwlow : ρc.row < ((Frame.ofMountain M).cell w).row := by
            have := height_lt_of_index hO hwc.symm (show nρ.2.val < w.2.val by omega)
            unfold Frame.height at this
            rw [hnρcell] at this
            exact this
          have hwout : inRegion (d + 2) S (official ((Frame.ofMountain M).cell w).row) = false := by
            by_contra hin
            have hin' : inRegion (d + 2) S (official ((Frame.ofMountain M).cell w).row) = true := by
              simpa using hin
            have := hρmax _ hwmem hin'
            simp only at this
            rw [← hnρref] at this
            exact absurd this (by show ¬ (w.2.val ≤ nρ.2.val); omega)
          have := bump_le_of_not_mem hρreg hwout (Recon.official_strictMono hρ1 hwlow)
          rw [hhρ, ← bump_official (a := ρc.row) hd1]
          calc Row.bump (official ρc.row) d ≤ Row.bump (official ρc.row) (d + 1) :=
                Row.bump_mono_exponent _ (by omega)
            _ ≤ official ((Frame.ofMountain M).cell w).row := this
            _ ≤ ((Frame.ofMountain M).cell w).row := official_le_self _
        · -- `ρ ≤ κ`
          unfold Frame.height
          rw [hnρcell, hnκcell]
          exact hρκ
        · -- `κ` is in the slot of `ρ`
          unfold Frame.height
          rw [hnρcell, hnκcell, ← bump_official (a := ρc.row) hd1]
          exact lt_bump_of_official_lt hd1 (lt_bump_of_same_slot hρreg hκreg hσeq)
        · -- the node above `κ` leaves the region
          unfold Frame.height
          rw [hnρcell, ← bump_official (a := ρc.row) (by omega)]
          exact hκuhi.trans (official_le_self _)

/-! ## `MDHolds` -/

/-- The regions of the reached items lie below `τ`. -/
theorem reach_below {ctx : Context} {τ : Row} {d : Nat} {it : Item} (h : Reach ctx τ d it) :
    BelowTau τ d it := by
  induction h with
  | top h => exact lowerItems_below τ _ h
  | child _ hch hc ih => exact ih.child (by omega) (childItems_ok hch _ hc)

/-- The root data of a splice expansion. -/
theorem splice_root {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : ChainCorr.SpliceData s n D M out ρ R t) :
    ∃ (col : Column) (root : Ref), M[M.size - 1]? = some col ∧ col.back? = some t ∧
      t.left = some root ∧ official t.row ≠ 0 ∧ ρ.cr = root.column ∧ ρ.x0 = M.size - 1 := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col, hcol, ht⟩ := hS.last
  have h0 : official t.row ≠ 0 := by
    intro h
    have := root?_none_of_official_zero hV D hcol ht h
    rw [hS.splice.root] at this
    cases this
  cases hl : t.left with
  | none =>
      exfalso
      have : root? M D = none := by
        unfold root?
        obtain ⟨_, htop⟩ := back?_spec ht
        simp [hcol, htop, hl]
      rw [hS.splice.root] at this
      cases this
  | some root =>
      obtain ⟨ρ', hr', hx0, hcr'⟩ := root?_of_official_ne_zero hV D hcol ht h0 hl
      have := Option.some.inj (hr'.symm.trans hS.splice.root)
      subst this
      exact ⟨col, root, hcol, ht, rfl, h0, hcr', hx0⟩

theorem mdHolds_of_source (h : MDSource) : MDHolds := by
  intro s n D M out ρ R t hS i hi0 hi y hy d it hRe ρr ρc hρ _
  obtain ⟨col, root, hcol, ht, htl, h0, hcr, hx0⟩ := splice_root hS
  have hbel := (reach_below hRe).1
  have := h s M hS.splice.build col t hcol ht root htl h0 d it.source hbel ρr ρc
    (by rw [← hcr]; exact hρ)
  rw [← hx0] at this
  exact this

/-- **(MD) holds.** -/
theorem mdHolds : MDHolds := mdHolds_of_source md_source

/-! ## The three statements from MA and MH -/

/-- **`CopyOrder` from MA and MH.** -/
theorem copyOrder_of_MA_MH (hMA : MAHolds) (hMH : MHHolds) : ChainCorr.CopyOrder :=
  copyOrder_of_facts hMA mdHolds hMH

/-- **`CopyEmitted` from MA and MH.** -/
theorem copyEmitted_of_MA_MH (hMA : MAHolds) (hMH : MHHolds) : ChainCorr.CopyEmitted :=
  copyEmitted_of_facts hMA mdHolds hMH

/-- **`CopyFirst` from MA and MH.** -/
theorem copyFirst_of_MA_MH (hMA : MAHolds) (hMH : MHHolds) : ChainCorr.CopyFirst :=
  copyFirst_of_facts hMA mdHolds hMH

/-- **`ChainCorr.Inner.CopyEmitted` from MA and MH.** -/
theorem inner_copyEmitted_of_MA_MH (hMA : MAHolds) (hMH : MHHolds) : ChainCorr.Inner.CopyEmitted :=
  inner_copyEmitted_of_facts hMA mdHolds hMH

/-- **`ChainCorr.Inner.CopyFirst` from MA and MH.** -/
theorem inner_copyFirst_of_MA_MH (hMA : MAHolds) (hMH : MHHolds) : ChainCorr.Inner.CopyFirst :=
  inner_copyFirst_of_facts hMA mdHolds hMH

end OmegaY.Official.Classification.Proofs.CopyShape

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.mdHolds
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyOrder_of_MA_MH
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyEmitted_of_MA_MH
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.copyFirst_of_MA_MH
