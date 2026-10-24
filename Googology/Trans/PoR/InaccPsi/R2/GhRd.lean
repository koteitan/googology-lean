import Googology.Trans.PoR.InaccPsi.R2.GhIdx

/-!
# The readings of the atoms over the base, for every code below `ε_{Ω₁+1}·ω`

For a strongly critical `y < Ω₁` the atoms over `y` are `Γ_{Ω₁+1+c}`, `c < ε_{Ω₁+1}·ω` with `ghg c < y`
(`R2.GhAt`).

* `gh_count` (**the codes below `c` with gate below `y` are countably many**: quotient `< ω` and the reading of the
  remainder), `ghTh_G` / `ghTh_At` (**the reading of every atom over `y` is strongly critical, above `y`, below
  `Ω₁`**), `ghTh_lt_Om1`;
* `gfCl_of_ghCl`, `ghTh_eq_gfTh` (**below `Γ_{Ω₁+1+ε_{Ω₁+1}}` the readings with `ghAt` are those with `Gf.gfAt`**);
* `ghCl_lt_G` (**a code over `Z` below `Γ_{Ω₁+1+c}`, `c ≤ ε_{Ω₁+1}·ω` a limit, is below some `Γ_{Ω₁+1+b}`, `b < c`,
  `ghg b < Z`**);
* `GhPolyG` (**terms for the codes below `E` in a gated system**), `ghPoly_of_SC`.

No new axiom.  New definition: `GhPolyG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Lu
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {y : Ordinal.{0}}

theorem ghg_zero : ghg 0 = 0 := by rw [ghg, Ordinal.zero_mod, gtc_zero]

/-- **The codes below `c ≤ ε_{Ω₁+1}·ω` with gate below `y < Ω₁` are countably many.** -/
theorem gh_count {c : Ordinal.{0}} (hc : c ≤ ghE) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // ghg b.1 < y} := by
  have hyn : eN y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact Ge.eN_lt_Om1' hy hy1
  have hwn : ω < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact omega_lt_Om1
  haveI := Gc.gc_countable hyn
  haveI := Gc.gc_countable hwn
  have hq : ∀ b : {b : Iio c // ghg b.1 < y}, b.1.1 / gfE < ω := fun b =>
    (Ordinal.div_lt gfE_ne).2 (lt_of_lt_of_le b.1.2 hc)
  let f : {b : Iio c // ghg b.1 < y} → Iio ω × Iio (eN y) := fun b =>
    (⟨b.1.1 / gfE, hq b⟩, ⟨rdc (b.1.1 % gfE) y, rdc_lt_eN hy _ b.2⟩)
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e1 : b.1.1 / gfE = b'.1.1 / gfE := congrArg (fun p => p.1.1) hbb
  have e2 : rdc (b.1.1 % gfE) y = rdc (b'.1.1 % gfE) y := congrArg (fun p => p.2.1) hbb
  have e3 : b.1.1 % gfE = b'.1.1 % gfE := by
    rcases lt_trichotomy (b.1.1 % gfE) (b'.1.1 % gfE) with h | h | h
    · exact absurd e2 (rdc_mono hy (gh_mod_lt _) h b'.2 b.2).ne
    · exact h
    · exact absurd e2 (rdc_mono hy (gh_mod_lt _) h b.2 b'.2).ne'
  refine Subtype.ext (Subtype.ext ?_)
  rw [← Ordinal.div_add_mod b.1.1 gfE, ← Ordinal.div_add_mod b'.1.1 gfE, e1, e3]

/-- **The reading of every atom over `y` is strongly critical, above `y`, below `Ω₁`.** -/
theorem ghTh_G (hy : SC y) (hy1 : y < Om 1) : ∀ c : Ordinal.{0}, c < ghE → ghg c < y →
    SC (gxTh y (ghAt y) (gcG c)) ∧ y < gxTh y (ghAt y) (gcG c) ∧ gxTh y (ghAt y) (gcG c) < Om 1 := by
  have hAt := ghAt_GxAt y
  have hyE := gg_SC_eps hy
  have hy1' := Lp.lp_y1 hy1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hgc
  have hSC : SC (gxTh y (ghAt y) (gcG c)) := gxTh_SC hy hAt (gcG_SC c) (hy1.trans (gcG_Om1_lt c))
  have hyl : y < gxTh y (ghAt y) (gcG c) := by
    have := gxTh_lt (GxCl.om (Z := y) (At := ghAt y)) (gcG_Om1_lt c)
    rwa [gxTh_Om1 hy hy1 hAt] at this
  refine ⟨hSC, hyl, ?_⟩
  have hatom : ∀ t ∈ ghAt y, t < gcG c → ∃ b : {b : Iio c // ghg b.1 < y}, t = gcG b.1.1 := by
    rintro t ⟨b, -, hgb, rfl⟩ htk
    exact ⟨⟨⟨b, gcG_lt_iff.1 htk⟩, hgb⟩, rfl⟩
  haveI := gh_count hc.le hyE hy1'
  by_cases hne : Nonempty {b : Iio c // ghg b.1 < y}
  · set z := ⨆ b : {b : Iio c // ghg b.1 < y}, gxTh y (ghAt y) (gcG b.1.1) with hz
    have hbdd : BddAbove (range fun b : {b : Iio c // ghg b.1 < y} => gxTh y (ghAt y) (gcG b.1.1)) :=
      Ordinal.bddAbove_of_small
    have hIH : ∀ b : {b : Iio c // ghg b.1 < y}, SC (gxTh y (ghAt y) (gcG b.1.1)) ∧
        y < gxTh y (ghAt y) (gcG b.1.1) ∧ gxTh y (ghAt y) (gcG b.1.1) < Om 1 := fun b =>
      IH b.1.1 b.1.2 (b.1.2.trans hc) b.2
    have hzS : SC z := gc_SC_iSup fun b => (hIH b).1
    have hz1 : z < Om 1 := by
      have := Ordinal.iSup_lt_omega_one (f := fun b : {b : Iio c // ghg b.1 < y} => gxTh y (ghAt y) (gcG b.1.1))
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

theorem ghTh_At (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ ghAt y) :
    SC (gxTh y (ghAt y) s) ∧ y < gxTh y (ghAt y) s ∧ gxTh y (ghAt y) s < Om 1 := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  exact ghTh_G hy hy1 c hc hg

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem ghTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y (ghAt y) c) :
    gxTh y (ghAt y) c < Om 1 := by
  have hAt := ghAt_GxAt y
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (ghTh_At hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Below `Γ_{Ω₁+1+ε_{Ω₁+1}}` the atoms `ghAt` are those of `Gf.gfAt` -/

theorem gfCl_of_ghCl {Z x : Ordinal.{0}} (hx : GxCl Z (ghAt Z) x) : x < gfV → GxCl Z (gfAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨c, -, hgc, rfl⟩ := hs
    have hcE : c < gfE := gcG_lt_iff.1 h
    rw [ghg_of_lt hcE] at hgc
    exact GxCl.atom (gfG_atom hcE hgc)
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **`Θ_y` with the atoms `ghAt` is `Θ_y` with the atoms `gfAt` up to `Γ_{Ω₁+1+ε_{Ω₁+1}}`.** -/
theorem ghTh_eq_gfTh {c : Ordinal.{0}} (hc : c ≤ gfV) : gxTh y (ghAt y) c = gxTh y (gfAt y) c :=
  ggOtp_congr c fun _ hx => ⟨fun h => gfCl_of_ghCl h (hx.trans_le hc), fun h => gfCl_ghCl h⟩

/-! ## The codes below a limit atom -/

theorem ghg_succ {b Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (hg : ghg b < Z) : ghg (b + 1) < Z := by
  have h1 : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  rw [ghg, gh_mod_small b h1]
  exact (rdc_succ _ (gh_mod_lt b) 0).2.2.trans_lt (hZ.add_one_lt hg)

/-- **A code over a strongly critical `Z` below `Γ_{Ω₁+1+c}` (`c ≤ ε_{Ω₁+1}·ω` a limit) is below some `Γ_{Ω₁+1+b}`
with `b < c` and `ghg b < Z`.** -/
theorem ghCl_lt_G {Z c : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hc : IsSuccLimit c)
    {d : Ordinal.{0}}
    (hd : GxCl Z (ghAt Z) d) : d < gcG c → ∃ b < c, ghg b < Z ∧ d < gcG b := by
  have hZl : IsSuccLimit Z := hZ.isSuccLimit
  have hmax : ∀ b1 b2 : Ordinal.{0}, ghg b1 < Z → ghg b2 < Z → ghg (max b1 b2) < Z := fun b1 b2 h1 h2 => by
    rcases le_total b1 b2 with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  induction hd with
  | @small x h => exact fun _ => ⟨0, hc.bot_lt, by rw [ghg_zero]; exact hZ.1,
      (h.trans_le hZ1).trans (gcG_Om1_lt 0)⟩
  | om => exact fun _ => ⟨0, hc.bot_lt, by rw [ghg_zero]; exact hZ.1, gcG_Om1_lt 0⟩
  | @atom s hs =>
    intro h
    obtain ⟨b, -, hgb, rfl⟩ := hs
    have hbc := gcG_lt_iff.1 h
    exact ⟨b + 1, hc.add_one_lt hbc, ghg_succ hZl hgb, gcG_lt (lt_add_one b)⟩
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

/-- **Terms for the codes below `E` above a gate** (atoms `ghAt`). -/
def GhPolyG {g : Ordinal.{0}} (X : Gd.GdSys g) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, g < Z → GxCl Z (ghAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (ghAt y) c

/-- **Reduction to strongly critical bases below `Ω₁`.** -/
theorem ghPoly_of_SC {T : Type 1} (CB : T → Ordinal.{0} → Prop) (val : T → Ordinal.{0} → Ordinal.{0}) (t0 : T)
    {g E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → g < Z → ∀ c, GxCl Z (ghAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 →
      Z ≤ y → CB s y ∧ val s y = gxTh y (ghAt y) c) :
    ∀ Z c, g < Z → GxCl Z (ghAt Z) c → c < E → ∃ s : T, ∀ y, SC y → y < Om 1 → Z ≤ y →
      CB s y ∧ val s y = gxTh y (ghAt y) c := by
  intro Z c hg hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 (hg.trans_le h3) c (ghCl_mono h3 hc) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨t0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

end Googology.Trans.PoR.InaccPsi.R2.Gh
