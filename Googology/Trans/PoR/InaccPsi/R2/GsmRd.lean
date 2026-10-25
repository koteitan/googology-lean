import Googology.Trans.PoR.InaccPsi.R2.GsmIdx

/-!
# (port of `R2.GmRd` to `R2.GsD` / `GsCS`: the base read only above the gate)

Every proof is that of `R2.GmRd` with the names of `R2.GsmAt` … `R2.GsLoc` (code system `GsCS`).

Port of `R2.GiRd` to the code systems `GsCS` of `R2.GmAt`, whose bound may pass `Γ_{Ω₁+1}` (codes may contain
atoms), and, for the layers, to offsets below `Γ_{x+2}` (`R2.GmGq`, `R2.GmU`); the proofs are those of `R2.GiRd`.

For a strongly critical `y < Ω₁` the atoms over `y` are `Γ_{Ω₁+1+c}`, `c < K.B` with `K.gt c < y` (`R2.GmAt`).

* `gsmTh_G` / `gsmTh_At` (**the reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`**; the
  countability is the field `K.count`), `gsmTh_lt_Om1`;
* `gsmCl_lt_G` (**a code over `Z` below `Γ_{Ω₁+1+c}`, `c ≤ K.B` a limit, is below some `Γ_{Ω₁+1+b}`, `b < c`,
  `K.gt b < Z`**);
* `GsmPolyG` (**terms for the codes below `E` in a gated system**), `gsmPoly_of_SC`.

No new axiom.  New definition: `GsmPolyG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {y : Ordinal.{0}} {K : GsCS}

/-- **The reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`.** -/
theorem gsmTh_G (hy : SC y) (hy1 : y < Om 1) : ∀ c : Ordinal.{0}, c < K.B → K.gt c < y →
    SC (gxTh y (K.At y) (gcG c)) ∧ y < gxTh y (K.At y) (gcG c) ∧ gxTh y (K.At y) (gcG c) < Om 1 := by
  have hAt := gsmAt_GxAt (K := K) y
  have hyE := gg_SC_eps hy
  have hy1' := Lp.lp_y1 hy1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hgc
  have hSC : SC (gxTh y (K.At y) (gcG c)) := gxTh_SC hy hAt (gcG_SC c) (hy1.trans (gcG_Om1_lt c))
  have hyl : y < gxTh y (K.At y) (gcG c) := by
    have := gxTh_lt (GxCl.om (Z := y) (At := K.At y)) (gcG_Om1_lt c)
    rwa [gxTh_Om1 hy hy1 hAt] at this
  refine ⟨hSC, hyl, ?_⟩
  have hatom : ∀ t ∈ K.At y, t < gcG c → ∃ b : {b : Iio c // K.gt b.1 < y}, t = gcG b.1.1 := by
    rintro t ⟨b, -, hgb, rfl⟩ htk
    exact ⟨⟨⟨b, gcG_lt_iff.1 htk⟩, hgb⟩, rfl⟩
  haveI := K.count c y hc.le hyE hy1'
  by_cases hne : Nonempty {b : Iio c // K.gt b.1 < y}
  · set z := ⨆ b : {b : Iio c // K.gt b.1 < y}, gxTh y (K.At y) (gcG b.1.1) with hz
    have hbdd : BddAbove (range fun b : {b : Iio c // K.gt b.1 < y} => gxTh y (K.At y) (gcG b.1.1)) :=
      Ordinal.bddAbove_of_small
    have hIH : ∀ b : {b : Iio c // K.gt b.1 < y}, SC (gxTh y (K.At y) (gcG b.1.1)) ∧
        y < gxTh y (K.At y) (gcG b.1.1) ∧ gxTh y (K.At y) (gcG b.1.1) < Om 1 := fun b =>
      IH b.1.1 b.1.2 (b.1.2.trans hc) b.2
    have hzS : SC z := gc_SC_iSup fun b => (hIH b).1
    have hz1 : z < Om 1 := by
      have := Ordinal.iSup_lt_omega_one (f := fun b : {b : Iio c // K.gt b.1 < y} => gxTh y (K.At y) (gcG b.1.1))
        fun b => by
          have h := (hIH b).2.2
          rwa [← ph_Om1_eq] at h
      rwa [← ph_Om1_eq]
    obtain ⟨b0⟩ := hne
    have hyz : y < z := (hIH b0).2.1.trans_le (le_ciSup hbdd b0)
    have hXS := Lp.lpG_SC hzS hz1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hzS hz1
    refine (Ld.ldAtom_le hy hy1 hAt hXS (hyz.trans hX1) fun t ht htk => ?_).trans_lt hX2
    obtain ⟨b, rfl⟩ := hatom t ht htk
    exact (le_ciSup hbdd b).trans_lt hX1
  · have hXS := Lp.lpG_SC hy hy1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hy hy1
    refine (Ld.ldAtom_le hy hy1 hAt hXS hX1 fun t ht htk => ?_).trans_lt hX2
    obtain ⟨b, -⟩ := hatom t ht htk
    exact absurd ⟨b⟩ hne

theorem gsmTh_At (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ K.At y) :
    SC (gxTh y (K.At y) s) ∧ y < gxTh y (K.At y) s ∧ gxTh y (K.At y) s < Om 1 := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  exact gsmTh_G hy hy1 c hc hg

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem gsmTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y (K.At y) c) :
    gxTh y (K.At y) c < Om 1 := by
  have hAt := gsmAt_GxAt (K := K) y
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (gsmTh_At hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## The codes below a limit atom -/

/-- **A code over a strongly critical `Z` below `Γ_{Ω₁+1+c}` (`c ≤ K.B` a limit) is below some `Γ_{Ω₁+1+b}`
with `b < c` and `K.gt b < Z`.** -/
theorem gsmCl_lt_G {Z c : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hc : IsSuccLimit c) (hcB : c ≤ K.B)
    {d : Ordinal.{0}}
    (hd : GxCl Z (K.At Z) d) : d < gcG c → ∃ b < c, K.gt b < Z ∧ d < gcG b := by
  have hZl : IsSuccLimit Z := hZ.isSuccLimit
  have hmax : ∀ b1 b2 : Ordinal.{0}, K.gt b1 < Z → K.gt b2 < Z → K.gt (max b1 b2) < Z := fun b1 b2 h1 h2 => by
    rcases le_total b1 b2 with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  induction hd with
  | @small x h => exact fun _ => ⟨0, hc.bot_lt, by rw [K.gt_zero]; exact hZ.1,
      (h.trans_le hZ1).trans (gcG_Om1_lt 0)⟩
  | om => exact fun _ => ⟨0, hc.bot_lt, by rw [K.gt_zero]; exact hZ.1, gcG_Om1_lt 0⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, -, hgb, rfl⟩ := hs
    have hbc := gcG_lt_iff.1 h
    exact ⟨b + 1, hc.add_one_lt hbc, K.gt_succ b Z hZl (lt_of_lt_of_le (hc.add_one_lt hbc) hcB) hgb,
      gcG_lt (lt_add_one b)⟩
  | @add x y _ _ ihx ihy =>
    intro h
    obtain ⟨β1, h1, g1, hx⟩ := ihx (lt_of_le_of_lt le_self_add h)
    obtain ⟨β2, h2, g2, hy'⟩ := ihy (lt_of_le_of_lt le_add_self h)
    exact ⟨max β1 β2, max_lt h1 h2, hmax _ _ g1 g2, (gcG_SC _).isPrincipal
      (hx.trans_le (gcG_le (le_max_left _ _))) (hy'.trans_le (gcG_le (le_max_right _ _)))⟩
  | @phi x y _ _ ihx ihy =>
    intro h
    obtain ⟨β1, h1, g1, hx⟩ := ihx (lt_of_le_of_lt (left_le_veblen x y) h)
    obtain ⟨β2, h2, g2, hy'⟩ := ihy (lt_of_le_of_lt (right_le_veblen x y) h)
    exact ⟨max β1 β2, max_lt h1 h2, hmax _ _ g1 g2, (gcG_SC _).2 _ (hx.trans_le (gcG_le (le_max_left _ _))) _
      (hy'.trans_le (gcG_le (le_max_right _ _)))⟩

/-- **Terms for the codes below `E` above a gate** (atoms `K.At`). -/
def GsmPolyG (K : GsCS) {g : Ordinal.{0}} (X : Gd.GdSys g) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, g < Z → GxCl Z (K.At Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (K.At y) c

/-- **Reduction to strongly critical bases below `Ω₁`.** -/
theorem gsmPoly_of_SC {T : Type 1} (CB : T → Ordinal.{0} → Prop) (val : T → Ordinal.{0} → Ordinal.{0}) (t0 : T)
    {g E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (K.At Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 →
      Z ≤ y → CB s y ∧ val s y = gxTh y (K.At y) c) :
    ∀ Z c, g < Z → GxCl Z (K.At Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 → Z ≤ y →
      CB s y ∧ val s y = gxTh y (K.At y) c := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (gsmCl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨t0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

end Googology.Trans.PoR.InaccPsi.R2.Gs
