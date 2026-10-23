import Googology.Trans.PoR.InaccPsi.R2.GeIdx

/-!
# The readings of the atoms over the base, for every code below `Ω₁^ω`

For a strongly critical `y < Ω₁` the atoms over `y` are `Γ_{Ω₁+1+c}`, `c < Ω₁^ω` with digits below `y`.

* `geTh_At` (**the reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`**; by induction on the
  code, the sup over the countably many smaller atoms (`R2.GeDig.ge_count`), `Ld.ldAtom_le` and the next strongly
  critical `Lp.lgG`), `geTh_lt_Om1`;
* `geTh_eq_gdTh` (**below `Γ_{Ω₁·2+1}` the readings with `geAt` are those with the atoms `gdAt` of `R2.GdAt`**);
* `geCl_lt_G` (**a code over `Z` below `Γ_{Ω₁+1+c}`, `c` a limit code, is below some `Γ_{Ω₁+1+b}`, `b < c`,
  digits of `b` below `Z`**);
* `GePolyG` (**terms for the codes below `E` in a gated system**), `gePoly_of_SC`.

No new axiom.  New definition: `GePolyG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {y : Ordinal.{0}}

/-- **The reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`.** -/
theorem geTh_G (hy : SC y) (hy1 : y < Om 1) : ∀ c : Ordinal.{0}, c < geW → gate c < y →
    SC (gxTh y (geAt y) (gcG c)) ∧ y < gxTh y (geAt y) (gcG c) ∧ gxTh y (geAt y) (gcG c) < Om 1 := by
  have hAt := geAt_GxAt y
  have hyE := gg_SC_eps hy
  have hy1' := Lp.lp_y1 hy1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hgc
  have hSC : SC (gxTh y (geAt y) (gcG c)) := gxTh_SC hy hAt (gcG_SC c) (hy1.trans (gcG_Om1_lt c))
  have hyl : y < gxTh y (geAt y) (gcG c) := by
    have := gxTh_lt (GxCl.om (Z := y) (At := geAt y)) (gcG_Om1_lt c)
    rwa [gxTh_Om1 hy hy1 hAt] at this
  refine ⟨hSC, hyl, ?_⟩
  have hatom : ∀ t ∈ geAt y, t < gcG c → ∃ b : {b : Iio c // gate b.1 < y}, t = gcG b.1.1 := by
    rintro t ⟨b, -, hgb, rfl⟩ htk
    exact ⟨⟨⟨b, gcG_lt_iff.1 htk⟩, hgb⟩, rfl⟩
  haveI := ge_count hc hyE hy1'
  by_cases hne : Nonempty {b : Iio c // gate b.1 < y}
  · set z := ⨆ b : {b : Iio c // gate b.1 < y}, gxTh y (geAt y) (gcG b.1.1) with hz
    have hbdd : BddAbove (range fun b : {b : Iio c // gate b.1 < y} => gxTh y (geAt y) (gcG b.1.1)) :=
      Ordinal.bddAbove_of_small
    have hIH : ∀ b : {b : Iio c // gate b.1 < y}, SC (gxTh y (geAt y) (gcG b.1.1)) ∧
        y < gxTh y (geAt y) (gcG b.1.1) ∧ gxTh y (geAt y) (gcG b.1.1) < Om 1 := fun b =>
      IH b.1.1 b.1.2 (b.1.2.trans hc) b.2
    have hzS : SC z := gc_SC_iSup fun b => (hIH b).1
    have hz1 : z < Om 1 := by
      have := Ordinal.iSup_lt_omega_one (f := fun b : {b : Iio c // gate b.1 < y} => gxTh y (geAt y) (gcG b.1.1))
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

theorem geTh_At (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ geAt y) :
    SC (gxTh y (geAt y) s) ∧ y < gxTh y (geAt y) s ∧ gxTh y (geAt y) s < Om 1 := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  exact geTh_G hy hy1 c hc hg

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem geTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y (geAt y) c) :
    gxTh y (geAt y) c < Om 1 := by
  have hAt := geAt_GxAt y
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (geTh_At hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Below `Γ_{Ω₁·2+1}` the atoms `geAt` are those of `R2.GdAt` -/

theorem gdCl_of_geCl {Z x : Ordinal.{0}} (hx : GxCl Z (geAt Z) x) : x < gdV → GxCl Z (gdAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨c, hc, hgc, rfl⟩ := hs
    have hcO : c ≤ Om1 := by
      have h1 := gcG_lt_iff.1 h
      rw [← Br.Om1_eq] at h1
      exact Order.lt_add_one_iff.1 h1
    rcases hcO.lt_or_eq with hlt | heq
    · rw [(sb_const hlt 0).2] at hgc
      exact GxCl.atom (gdG_atom hgc)
    · rw [heq, Br.Om1_eq]; exact GxCl.atom (gdD_atom Z)
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **`Θ_y` with the atoms `geAt` is `Θ_y` with the atoms `gdAt` up to `Γ_{Ω₁·2+1}`.** -/
theorem geTh_eq_gdTh (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : c ≤ gdV) :
    gxTh y (geAt y) c = gxTh y (gdAt y) c :=
  ggOtp_congr c fun _ hx => ⟨fun h => gdCl_of_geCl h (hx.trans_le hc),
    fun h => h.mono le_rfl (gdAt_sub_geAt (gg_one_lt_of_SC hy) (by rw [Br.Om1_eq]; exact hy1.le))⟩

/-! ## The codes below a limit atom -/

/-- **A code over a strongly critical `Z` below `Γ_{Ω₁+1+c}` (`c ≤ Ω₁^ω` a limit) is below some `Γ_{Ω₁+1+b}` with
`b < c` and digits of `b` below `Z`.** -/
theorem geCl_lt_G {Z c : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hc : IsSuccLimit c) (hcW : c ≤ geW)
    {d : Ordinal.{0}}
    (hd : GxCl Z (geAt Z) d) : d < gcG c → ∃ b < c, gate b < Z ∧ d < gcG b := by
  have hZl : IsSuccLimit Z := hZ.isSuccLimit
  have hmax : ∀ b1 b2 : Ordinal.{0}, gate b1 < Z → gate b2 < Z → gate (max b1 b2) < Z := fun b1 b2 h1 h2 => by
    rcases le_total b1 b2 with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  induction hd with
  | @small x h => exact fun _ => ⟨0, hc.bot_lt, by rw [gate_zero]; exact hZ.1,
      (h.trans_le hZ1).trans (gcG_Om1_lt 0)⟩
  | om => exact fun _ => ⟨0, hc.bot_lt, by rw [gate_zero]; exact hZ.1, gcG_Om1_lt 0⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, hbW, hgb, rfl⟩ := hs
    have hbc := gcG_lt_iff.1 h
    have hb1 : b + 1 < geW := hc.add_one_lt hbc |>.trans_le hcW
    refine ⟨b + 1, hc.add_one_lt hbc, ?_, gcG_lt (lt_add_one b)⟩
    exact (sb_succ hb1 0).2.2.trans_lt (hZl.add_one_lt hgb)
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

/-- **Terms for the codes below `E` above a gate** (atoms `geAt`). -/
def GePolyG {g : Ordinal.{0}} (X : Gd.GdSys g) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, g < Z → GxCl Z (geAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (geAt y) c

/-- **Reduction to strongly critical bases below `Ω₁`.** -/
theorem gePoly_of_SC {T : Type 1} (CB : T → Ordinal.{0} → Prop) (val : T → Ordinal.{0} → Ordinal.{0}) (t0 : T)
    {g E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (geAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 →
      Z ≤ y → CB s y ∧ val s y = gxTh y (geAt y) c) :
    ∀ Z c, g < Z → GxCl Z (geAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 → Z ≤ y →
      CB s y ∧ val s y = gxTh y (geAt y) c := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (geCl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨t0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

end Googology.Trans.PoR.InaccPsi.R2.Ge
