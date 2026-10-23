import Googology.Trans.PoR.InaccPsi.R2.GdIdx
import Googology.Trans.PoR.InaccPsi.R2.GdTm

/-!
# The readings of the atoms over the base

For a strongly critical `y < Ω₁` the atoms over `y` are `Γ_{Ω₁+1+a}` (`a < y`) and `Γ_{Ω₁·2}`.

* `gdTh_G` (**the reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`**; by induction on the
  index, the sup of the readings of the smaller atoms, `Ld.ldAtom_le` and the next strongly critical `Lp.lgG`);
* `gdTh_lt_Om1` (every reading of a code over `y` is below `Ω₁`);
* `gd_eps0_lt` (`ε₀ < y` for every strongly critical `y`), `gdCl_of_gc`, `gc_of_gdCl`, `gdTh_eq_gcTh`
  (**below `Γ_{Ω₁+ε₀}` the codes and readings with the atoms over the base are those of `R2.GcAt`**);
* `gdCl_lt_G` (**a code over `Z` below `Γ_{Ω₁·2}` is below some `Γ_{Ω₁+1+β}`, `β < Z`**, for a strongly critical `Z`),
  `gdTh_G_ge` (**`Θ_y(Γ_{Ω₁+1+b}) = Θ_y(Γ_{Ω₁+1+y})` for every `y ≤ b ≤ Ω₁`**), `gdTh_Gy`
  (`Θ_y(Γ_{Ω₁+1+y}) = sup_{b<y} Θ_y(Γ_{Ω₁+1+b})`);
* `GdPolyG` (**terms for the codes below `E` in a gated system**, at bases above the gate), `gdPoly_of_SC`.

No new axiom.  New definition: `GdPolyG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc

variable {y : Ordinal.{0}}

theorem gdAt_cases {s : Ordinal.{0}} (hs : s ∈ gdAt y) (hsD : s < gcG (Om 1)) : ∃ b < y, s = gcG b := by
  obtain ⟨b, hb, rfl⟩ := hs
  rcases hb with hb | rfl
  · exact ⟨b, hb, rfl⟩
  · exact absurd hsD (lt_irrefl _)

/-- **The reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`.** -/
theorem gdTh_G (hy : SC y) (hy1 : y < Om 1) : ∀ a : Ordinal.{0}, (a < y ∨ a = Om 1) →
    SC (gxTh y (gdAt y) (gcG a)) ∧ y < gxTh y (gdAt y) (gcG a) ∧ gxTh y (gdAt y) (gcG a) < Om 1 := by
  have hAt := gdAt_GxAt y
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha
  have hSC : SC (gxTh y (gdAt y) (gcG a)) := gxTh_SC hy hAt (gcG_SC a) (hy1.trans (gcG_Om1_lt a))
  have hyl : y < gxTh y (gdAt y) (gcG a) := by
    have := gxTh_lt (GxCl.om (Z := y) (At := gdAt y)) (gcG_Om1_lt a)
    rwa [gxTh_Om1 hy hy1 hAt] at this
  refine ⟨hSC, hyl, ?_⟩
  set m := if a = Om 1 then y else a with hm
  have hmy : m ≤ y := by
    rw [hm]; split_ifs with h
    · exact le_rfl
    · exact (ha.resolve_right h).le
  have hma : ∀ b, b < m → b < a ∧ b < y := by
    intro b hb
    rw [hm] at hb
    split_ifs at hb with h
    · exact ⟨hb.trans (h ▸ hy1), hb⟩
    · exact ⟨hb, hb.trans (ha.resolve_right h)⟩
  have hatom : ∀ t ∈ gdAt y, t < gcG a → ∃ b < m, t = gcG b := by
    intro t ht htk
    have htD : t < gcG (Om 1) := htk.trans_le (gcG_le (by rcases ha with h | h; exact (h.trans hy1).le; exact h.le))
    obtain ⟨b, hby, rfl⟩ := gdAt_cases ht htD
    refine ⟨b, ?_, rfl⟩
    have hba := gcG_lt_iff.1 htk
    rw [hm]; split_ifs with h
    · exact hby
    · exact hba
  have hmΩ : m < Om (1 : Ordinal.{0}) := hmy.trans_lt hy1
  haveI := gc_countable hmΩ
  rcases eq_or_ne m 0 with h0 | h0
  · have hXS := Lp.lpG_SC hy hy1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hy hy1
    refine (Ld.ldAtom_le hy hy1 hAt hXS hX1 fun t ht htk => ?_).trans_lt hX2
    obtain ⟨b, hb, -⟩ := hatom t ht htk
    rw [h0] at hb
    exact absurd hb (not_lt.2 zero_le)
  · haveI : Nonempty (Iio m) := ⟨⟨0, pos_iff_ne_zero.2 h0⟩⟩
    set z := ⨆ β : Iio m, gxTh y (gdAt y) (gcG β.1) with hz
    have hbdd : BddAbove (range fun β : Iio m => gxTh y (gdAt y) (gcG β.1)) := Ordinal.bddAbove_of_small
    have hIH : ∀ β : Iio m, SC (gxTh y (gdAt y) (gcG β.1)) ∧ y < gxTh y (gdAt y) (gcG β.1) ∧
        gxTh y (gdAt y) (gcG β.1) < Om 1 := fun β =>
      IH β.1 (hma β.1 β.2).1 (Or.inl (hma β.1 β.2).2)
    have hzS : SC z := gc_SC_iSup fun β => (hIH β).1
    have hz1 : z < Om 1 := by
      have := Ordinal.iSup_lt_omega_one (f := fun β : Iio m => gxTh y (gdAt y) (gcG β.1)) fun β => by
        have h := (hIH β).2.2
        rwa [← ph_Om1_eq] at h
      rwa [← ph_Om1_eq]
    have hyz : y < z := (hIH ⟨0, pos_iff_ne_zero.2 h0⟩).2.1.trans_le (le_ciSup hbdd ⟨0, pos_iff_ne_zero.2 h0⟩)
    have hXS := Lp.lpG_SC hzS hz1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hzS hz1
    refine (Ld.ldAtom_le hy hy1 hAt hXS (hyz.trans hX1) fun t ht htk => ?_).trans_lt hX2
    obtain ⟨b, hb, rfl⟩ := hatom t ht htk
    exact (le_ciSup hbdd ⟨b, hb⟩).trans_lt hX1

theorem gdTh_At (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ gdAt y) :
    SC (gxTh y (gdAt y) s) ∧ y < gxTh y (gdAt y) s ∧ gxTh y (gdAt y) s < Om 1 := by
  obtain ⟨a, ha, rfl⟩ := hs
  exact gdTh_G hy hy1 a ha

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem gdTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y (gdAt y) c) :
    gxTh y (gdAt y) c < Om 1 := by
  have hAt := gdAt_GxAt y
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (gdTh_At hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Below `Γ_{Ω₁+ε₀}` the atoms over the base are those of `R2.GcAt` -/

theorem gd_eps0_lt (hy : SC y) : ε₀ < y := by
  have hE : InE y := gg_SC_eps hy
  rcases (gc_eps0_le hE).lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 : (1 : Ordinal.{0}) < y := gg_one_lt_of_SC hy
    have h2 := hy.2 1 h1 0 hy.1
    rw [← h] at h2
    have h3 : veblen 1 0 = (ε₀ : Ordinal.{0}) := rfl
    rw [h3] at h2
    exact lt_irrefl _ h2

theorem gc_of_gdCl {Z x : Ordinal.{0}} (hx : GxCl Z (gdAt Z) x) : x < gcV → GxCl Z gcAt x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨b, -, rfl⟩ := hs
    exact GxCl.atom (gcG_atom (gcG_lt_iff.1 h))
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem gdCl_of_gc {Z x : Ordinal.{0}} (hZ : ε₀ ≤ Z) (hx : GxCl Z gcAt x) : GxCl Z (gdAt Z) x := by
  refine hx.mono le_rfl ?_
  rintro s ⟨α, hα, rfl⟩
  exact gdG_atom (hα.trans_le hZ)

/-- **`Θ_y` with the atoms over `y` is `Θ_y` with the atoms `gcAt` below `Γ_{Ω₁+ε₀}`.** -/
theorem gdTh_eq_gcTh (hy : SC y) {c : Ordinal.{0}} (hc : c ≤ gcV) : gxTh y (gdAt y) c = gxTh y gcAt c :=
  ggOtp_congr c fun _ hx => ⟨fun h => gc_of_gdCl h (hx.trans_le hc),
    fun h => gdCl_of_gc (gd_eps0_lt hy).le h⟩

/-! ## The codes below `Γ_{Ω₁·2}` -/

/-- **A code over a strongly critical `Z` below `Γ_{Ω₁·2}` is below some `Γ_{Ω₁+1+β}` with `β < Z`.** -/
theorem gdCl_lt_G {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) {d : Ordinal.{0}} (hd : GxCl Z (gdAt Z) d) :
    d < gcG (Om 1) → ∃ β < Z, d < gcG β := by
  have hZl : IsSuccLimit Z := hZ.isSuccLimit
  induction hd with
  | @small x h => exact fun _ => ⟨0, hZ.1, (h.trans hZ1).trans (gcG_Om1_lt 0)⟩
  | om => exact fun _ => ⟨0, hZ.1, gcG_Om1_lt 0⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, hb, rfl⟩ := gdAt_cases hs h
    exact ⟨b + 1, hZl.add_one_lt hb, gcG_lt (lt_add_one b)⟩
  | @add x y _ _ ihx ihy =>
    intro h
    obtain ⟨β1, h1, hx⟩ := ihx (lt_of_le_of_lt le_self_add h)
    obtain ⟨β2, h2, hy'⟩ := ihy (lt_of_le_of_lt le_add_self h)
    exact ⟨max β1 β2, max_lt h1 h2, (gcG_SC _).isPrincipal (hx.trans_le (gcG_le (le_max_left _ _)))
      (hy'.trans_le (gcG_le (le_max_right _ _)))⟩
  | @phi x y _ _ ihx ihy =>
    intro h
    obtain ⟨β1, h1, hx⟩ := ihx (lt_of_le_of_lt (left_le_veblen x y) h)
    obtain ⟨β2, h2, hy'⟩ := ihy (lt_of_le_of_lt (right_le_veblen x y) h)
    exact ⟨max β1 β2, max_lt h1 h2, (gcG_SC _).2 _ (hx.trans_le (gcG_le (le_max_left _ _))) _
      (hy'.trans_le (gcG_le (le_max_right _ _)))⟩

/-- **`Θ_y(Γ_{Ω₁+1+b}) = Θ_y(Γ_{Ω₁+1+y})` for every `y ≤ b ≤ Ω₁`**: no code over `y` lies in between. -/
theorem gdTh_G_ge (hy : SC y) (hy1 : y < Om 1) {b : Ordinal.{0}} (hyb : y ≤ b) (hb : b ≤ Om 1) :
    gxTh y (gdAt y) (gcG b) = gxTh y (gdAt y) (gcG y) := by
  unfold gxTh
  refine (cdOtp_eq_of_gap (gxSet y (gdAt y)) (gcG_le hyb) fun c hc h1 h2 => ?_).symm
  obtain ⟨β, hβ, hcβ⟩ := gdCl_lt_G hy hy1 hc (h2.trans_le (gcG_le hb))
  exact absurd (h1.trans_lt hcβ) (not_lt.2 (gcG_le hβ.le))

/-- **`Θ_y(Γ_{Ω₁+1+y}) = sup_{b<y} Θ_y(Γ_{Ω₁+1+b})`.** -/
theorem gdTh_Gy (hy : SC y) : gxTh y (gdAt y) (gcG y) = ⨆ b : Iio y, gxTh y (gdAt y) (gcG b.1) :=
  gcTh_limit hy.isSuccLimit

/-- **Terms for the codes below `E` above a gate**: for every code `c < E` over a base `Z` above the gate some term
has the value `Θ_y(c)` at every strongly critical `y ≥ Z`. -/
def GdPolyG {g : Ordinal.{0}} (X : GdSys g) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, g < Z → GxCl Z (gdAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (gdAt y) c

/-- **Reduction to strongly critical bases below `Ω₁`.** -/
theorem gdPoly_of_SC {T : Type 1} (CB : T → Ordinal.{0} → Prop) (val : T → Ordinal.{0} → Ordinal.{0}) (t0 : T)
    {g E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (gdAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 →
      Z ≤ y → CB s y ∧ val s y = gxTh y (gdAt y) c) :
    ∀ Z c, g < Z → GxCl Z (gdAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 → Z ≤ y →
      CB s y ∧ val s y = gxTh y (gdAt y) c := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (gdCl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨t0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

end Googology.Trans.PoR.InaccPsi.R2.Gd
