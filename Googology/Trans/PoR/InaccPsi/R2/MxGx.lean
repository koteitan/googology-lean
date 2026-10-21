import Googology.Trans.PoR.InaccPsi.R2.MxRead

/-!
# Codes with strongly critical atoms: the reading is additive, keeps `ω^·` and the φ-law

`GxCl Z At` are the codes over `Z` with the atoms `At` (generated from the ordinals below `Z`, `Ω₁` and the
members of `At` by `+` and `φ = veblen`); `gxTh Z At c` is their order type below `c`.  The atoms are strongly
critical and above `Ω₁` (`GxAt At`).  With `At = ∅` these are the codes `GgCl Z` of `R2.GgCl`.

* `GxCl.mono`, `GxCl.zero`, `GxCl.opow`, `GxCl.lt_of_lt_Om1` (a countable code over a strongly critical `Z` is
  below `Z`), `gxSC_atom` (**a strongly critical code above `Ω₁` is an atom**);
* `gxDec` (**decomposition**: `w − x` and `log_ω w` are codes), `gxDecV` (**the Veblen decomposition**:
  `x = φ(a, b)` a code with `b < x` gives codes `a`, `b`);
* `gxTh_small`, `gxTh_Om1` (`Θ(Ω₁) = Z`), `gxTh_add`, `gxTh_opow`, `gxTh_lt`, `gxTh_onto`, `gxTh_phi`
  (**the φ-law** `Θ(φ(a, b)) = φ(Θ a, Θ b)`, by the proof of `Ph.phTh_phi`), `gxTh_SC` (**the reading of a
  strongly critical code is strongly critical**).

No new axiom.  New definitions: `GxCl`, `GxAt`, `gxSet`, `gxTh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **The codes over `Z` with the atoms `At`**: from the ordinals below `Z`, `Ω₁` and the atoms by `+` and `φ`. -/
inductive GxCl (Z : Ordinal.{0}) (At : Set Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → GxCl Z At x
  | om : GxCl Z At (Om 1)
  | atom {s : Ordinal.{0}} : s ∈ At → GxCl Z At s
  | add {x y : Ordinal.{0}} : GxCl Z At x → GxCl Z At y → GxCl Z At (x + y)
  | phi {x y : Ordinal.{0}} : GxCl Z At x → GxCl Z At y → GxCl Z At (veblen x y)

/-- The atoms are strongly critical and above `Ω₁`. -/
def GxAt (At : Set Ordinal.{0}) : Prop := ∀ s ∈ At, SC s ∧ Om 1 < s

/-- The set of codes. -/
def gxSet (Z : Ordinal.{0}) (At : Set Ordinal.{0}) : Set Ordinal.{0} := {x | GxCl Z At x}

/-- **The reading**: the order type of the codes below `c`. -/
noncomputable def gxTh (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (c : Ordinal.{0}) : Ordinal.{0} :=
  cdOtp (gxSet Z At) c

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}}

theorem GxCl.mono {Z' : Ordinal.{0}} {At' : Set Ordinal.{0}} (h : Z ≤ Z') (hA : At ⊆ At') {x : Ordinal.{0}}
    (hx : GxCl Z At x) : GxCl Z' At' x := by
  induction hx with
  | small h' => exact GxCl.small (lt_of_lt_of_le h' h)
  | om => exact GxCl.om
  | atom hs => exact GxCl.atom (hA hs)
  | add _ _ ihx ihy => exact GxCl.add ihx ihy
  | phi _ _ ihx ihy => exact GxCl.phi ihx ihy

theorem GxCl.zero (hZ : 0 < Z) : GxCl Z At 0 := GxCl.small hZ

theorem GxCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : GxCl Z At c) : GxCl Z At (ω ^ c) := by
  have := GxCl.phi (GxCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem GxCl.of_gg {x : Ordinal.{0}} (h : GgCl Z x) : GxCl Z At x := by
  induction h with
  | small h' => exact GxCl.small h'
  | om => exact GxCl.om
  | add _ _ ihx ihy => exact GxCl.add ihx ihy
  | phi _ _ ihx ihy => exact GxCl.phi ihx ihy

/-- A countable code over a strongly critical `Z` is below `Z`. -/
theorem GxCl.lt_of_lt_Om1 (hZ : SC Z) (hAt : GxAt At) {x : Ordinal.{0}} (hx : GxCl Z At x) :
    x < Om 1 → x < Z := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | atom hs => exact fun h => absurd h (not_lt.2 (hAt _ hs).2.le)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1))
      (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))

/-- **A strongly critical code above `Ω₁` is an atom.** -/
theorem gxSC_atom (hZ1 : Z < Om 1) {x : Ordinal.{0}} (hx : GxCl Z At x) :
    SC x → Om 1 < x → x ∈ At := by
  induction hx with
  | small h => exact fun _ h1 => absurd ((h.trans hZ1).trans h1) (lt_irrefl _)
  | om => exact fun _ h1 => absurd h1 (lt_irrefl _)
  | atom hs => exact fun _ _ => hs
  | @add u v _ _ ihu ihv =>
    intro hs h1
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at hs h1 ⊢; exact ihu hs h1
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hs.isPrincipal hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at hs h1 ⊢
      exact ihv hs h1
  | @phi a b _ _ iha ihb =>
    intro hs h1
    by_cases ha : a < veblen a b
    · by_cases hb : b < veblen a b
      · exact absurd (hs.2 a ha b hb) (lt_irrefl _)
      · have e : b = veblen a b := le_antisymm (right_le_veblen _ _) (not_lt.1 hb)
        rw [← e] at hs h1 ⊢
        exact ihb hs h1
    · have e : a = veblen a b := le_antisymm (left_le_veblen _ _) (not_lt.1 ha)
      rw [← e] at hs h1 ⊢
      exact iha hs h1

/-! ## Decomposition -/

/-- **Decomposition**: for a strongly critical `Z`, a code `w` has `w − x` (for every code `x ≤ w`) and `log_ω w`
codes. -/
theorem gxDec (hZ : SC Z) (hAt : GxAt At) : ∀ w, GxCl Z At w →
    (∀ x, GxCl Z At x → x ≤ w → GxCl Z At (w - x)) ∧ GxCl Z At (log ω w) := by
  have h0 : GxCl Z At 0 := GxCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, GxCl Z At v → v ≤ w →
      (∀ x, GxCl Z At x → x ≤ v → GxCl Z At (v - x)) ∧ GxCl Z At (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => GxCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      GxCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
      rw [← Bt.Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact GxCl.om
      · exact h0
    · have : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
        conv_lhs => rw [← Bt.Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact GxCl.om
  | @atom s hs =>
    intro _
    have hSC := (hAt s hs).1
    have hE : ω ^ s = s := gg_SC_eps hSC
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hSC.isPrincipal hx with e | e <;> rw [e]
      · exact GxCl.atom hs
      · exact h0
    · have : log ω s = s := by
        conv_lhs => rw [← hE]
        exact log_opow one_lt_omega0 _
      rw [this]; exact GxCl.atom hs
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact GxCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : GxCl Z At (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact h0
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2
  | @phi a b ha hb iha ihb =>
    intro hle
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact GxCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact GxCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact GxCl.phi ha hb

/-- **The Veblen decomposition of a code**: `x = φ(a, b)` a code with `b < x` gives codes `a`, `b`. -/
theorem gxDecV (hZ : 0 < Z) (hAt : GxAt At) {x : Ordinal.{0}} (hx : GxCl Z At x) :
    ∀ a b, veblen a b = x → b < x → GxCl Z At a ∧ GxCl Z At b := by
  induction hx with
  | @small x h =>
    intro a b e hb
    exact ⟨GxCl.small ((e ▸ left_le_veblen a b).trans_lt h), GxCl.small (hb.trans h)⟩
  | om =>
    intro a b e hb
    have ha : a = Om 1 := by
      rcases lt_trichotomy a (Om 1) with h | h | h
      · exact absurd e (Ph.ph_SC_Om1.2 a h b hb).ne
      · exact h
      · exact absurd (e ▸ left_le_veblen a b) (not_le.2 h)
    subst ha
    have hb0 : b = 0 := by
      have h1 : veblen (Om 1) 0 = veblen (Om 1) b := by rw [Ph.ph_SC_Om1.veblen_zero, e]
      exact (veblen_inj.1 h1).symm
    exact ⟨GxCl.om, hb0 ▸ GxCl.zero hZ⟩
  | @atom s hs =>
    intro a b e hb
    have hSC := (hAt s hs).1
    have ha : a = s := by
      rcases lt_trichotomy a s with h | h | h
      · exact absurd e (hSC.2 a h b hb).ne
      · exact h
      · exact absurd (e ▸ left_le_veblen a b) (not_le.2 h)
    subst ha
    have hb0 : b = 0 := by
      have h1 : veblen a 0 = veblen a b := by rw [hSC.veblen_zero, e]
      exact (veblen_inj.1 h1).symm
    exact ⟨GxCl.atom hs, hb0 ▸ GxCl.zero hZ⟩
  | @add u v hu hv ihu ihv =>
    intro a b e hb
    have hp : IsPrincipal (· + ·) (u + v) := e ▸ Ph.ph_veblen_prin a b
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at e hb; exact ihu a b e hb
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hp hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at e hb
      exact ihv a b e hb
  | @phi a' b' ha' hb' _ ihb =>
    intro a b e hb
    rcases veblen_eq_veblen_iff.1 e with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h1, h2]; exact ⟨ha', hb'⟩
    · rw [h2] at hb; exact absurd hb (lt_irrefl _)
    · exact ihb a b h2 (by rw [← h2, e]; exact hb)

/-! ## The reading -/

theorem gx_set_add (x z : Ordinal.{0}) (hx : x ∈ gxSet Z At) (hz : z ∈ gxSet Z At) :
    x + z ∈ gxSet Z At := GxCl.add hx hz

theorem gx_set_sub (hZ : SC Z) (hAt : GxAt At) (x w : Ordinal.{0}) (hx : x ∈ gxSet Z At)
    (hw : w ∈ gxSet Z At) (hxw : x ≤ w) : w - x ∈ gxSet Z At := (gxDec hZ hAt w hw).1 x hx hxw

theorem gxTh_small {c : Ordinal.{0}} (hc : c ≤ Z) : gxTh Z At c = c :=
  cdOtp_of_Iio _ c fun _ hx => GxCl.small (lt_of_lt_of_le hx hc)

theorem gxTh_zero : gxTh Z At 0 = 0 := gxTh_small zero_le

/-- `Θ(Ω₁) = Z` for a strongly critical `Z < Ω₁`. -/
theorem gxTh_Om1 (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At) : gxTh Z At (Om 1) = Z := by
  unfold gxTh
  rw [← cdOtp_eq_of_gap (gxSet Z At) hZ1.le fun c hc h1 h2 =>
    absurd (GxCl.lt_of_lt_Om1 hZ hAt hc h2) (not_lt.2 h1)]
  exact gxTh_small le_rfl

theorem gxTh_lt {c d : Ordinal.{0}} (hc : GxCl Z At c) (hcd : c < d) : gxTh Z At c < gxTh Z At d :=
  cdOtp_lt_of_mem hc hcd

theorem gxTh_mono {c d : Ordinal.{0}} (hcd : c ≤ d) : gxTh Z At c ≤ gxTh Z At d := cdOtp_mono _ hcd

theorem gxTh_onto {m v : Ordinal.{0}} (hv : v < gxTh Z At m) :
    ∃ c, GxCl Z At c ∧ c < m ∧ gxTh Z At c = v := by
  obtain ⟨c, hc, hcm, e⟩ := ggOtp_onto (gxSet Z At) m v hv
  exact ⟨c, hc, hcm, e⟩

/-- **`Θ(u + v) = Θ u + Θ v`** for a code `u`. -/
theorem gxTh_add (hZ : SC Z) (hAt : GxAt At) {u : Ordinal.{0}} (hu : GxCl Z At u) (v : Ordinal.{0}) :
    gxTh Z At (u + v) = gxTh Z At u + gxTh Z At v :=
  ggOtp_add gx_set_add (gx_set_sub hZ hAt) hu v

/-- **`Θ(ω^a) = ω^{Θ a}`** for a code `a`. -/
theorem gxTh_opow (hZ : SC Z) (hAt : GxAt At) {a : Ordinal.{0}} (ha : GxCl Z At a) :
    gxTh Z At (ω ^ a) = ω ^ gxTh Z At a :=
  ggOtp_opow (GxCl.zero hZ.1) gx_set_add (gx_set_sub hZ hAt) (fun _ h => GxCl.opow hZ.1 h)
    (fun c hc => (gxDec hZ hAt c hc).2) a ha

/-- **THE φ-LAW**: `Θ(φ(a, b)) = φ(Θ a, Θ b)` for codes `a`, `b` (the proof of `Ph.phTh_phi`). -/
theorem gxTh_phi (hZ : SC Z) (hAt : GxAt At) :
    ∀ a, GxCl Z At a → ∀ b, GxCl Z At b → gxTh Z At (veblen a b) = veblen (gxTh Z At a) (gxTh Z At b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHa =>
  intro ha b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [gxTh_zero, veblen_zero_apply, veblen_zero_apply, gxTh_opow hZ hAt hb]
  have hx : GxCl Z At (veblen a b) := GxCl.phi ha hb
  have hfa0 : gxTh Z At a ≠ 0 := by
    have := gxTh_lt (GxCl.zero (At := At) hZ.1) (pos_iff_ne_zero.2 ha0)
    rw [gxTh_zero] at this; exact this.ne'
  have hfix : ∀ α < gxTh Z At a, veblen α (gxTh Z At (veblen a b)) = gxTh Z At (veblen a b) := by
    intro α hα
    obtain ⟨a', ha', ha'a, rfl⟩ := gxTh_onto hα
    rw [← IHa a' ha'a ha' (veblen a b) hx, veblen_veblen_of_lt ha'a]
  obtain ⟨β, hβ⟩ := (mem_range_veblen hfa0).2 hfix
  have hge : gxTh Z At b ≤ β := by
    refine le_of_forall_lt fun β' hβ' => ?_
    obtain ⟨b', hb', hb'b, rfl⟩ := gxTh_onto hβ'
    have h1 : gxTh Z At (veblen a b') < gxTh Z At (veblen a b) :=
      gxTh_lt (GxCl.phi ha hb') (veblen_lt_veblen_iff_right.2 hb'b)
    rw [IHb b' hb'b hb', ← hβ] at h1
    exact veblen_lt_veblen_iff_right.1 h1
  have hle : β ≤ gxTh Z At b := by
    by_contra hlt
    push Not at hlt
    have h1 : veblen (gxTh Z At a) (gxTh Z At b) < gxTh Z At (veblen a b) := by
      rw [← hβ]; exact veblen_lt_veblen_iff_right.2 hlt
    obtain ⟨w, hw, hwx, hwv⟩ := gxTh_onto h1
    have hwE : ω ^ w = w := by
      by_contra hne
      have hlt' : w < ω ^ w := lt_of_le_of_ne (right_le_opow w one_lt_omega0) (Ne.symm hne)
      have h2 := gxTh_lt hw hlt'
      rw [gxTh_opow hZ hAt hw, hwv, gg_veblen_eps hfa0] at h2
      exact lt_irrefl _ h2
    have hdec : veblen (invVeblen₁ w) (invVeblen₂ w) = w := by
      rw [veblen_invVeblen₁_invVeblen₂, hwE]
    have hb1 : invVeblen₂ w < w := by
      have := invVeblen₂_lt w; rwa [hwE] at this
    obtain ⟨ha1, hb1c⟩ := gxDecV hZ.1 hAt hw _ _ hdec hb1
    rcases lt_trichotomy (invVeblen₁ w) a with h | h | h
    · have e1 : gxTh Z At (veblen (invVeblen₁ w) w) = gxTh Z At w := by
        rw [IHa _ h ha1 w hw, hwv, veblen_veblen_of_lt (gxTh_lt ha1 h)]
      have hgt : w < veblen (invVeblen₁ w) w := by
        have := (veblen_lt_veblen_iff_right (o := invVeblen₁ w)).2 hb1
        rwa [hdec] at this
      have h3 := gxTh_lt hw hgt
      rw [e1] at h3
      exact lt_irrefl _ h3
    · rw [h] at hdec
      have hb1b : invVeblen₂ w < b := by
        rw [← hdec] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := IHb _ hb1b hb1c
      rw [hdec, hwv] at h3
      have h4 : veblen (gxTh Z At a) (gxTh Z At (invVeblen₂ w)) < veblen (gxTh Z At a) (gxTh Z At b) :=
        veblen_lt_veblen_iff_right.2 (gxTh_lt hb1c hb1b)
      rw [← h3] at h4
      exact lt_irrefl _ h4
    · have e1 : veblen a w = w := by
        have := veblen_veblen_of_lt h (invVeblen₂ w); rwa [hdec] at this
      have hwb : w < b := by
        rw [← e1] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := gxTh_lt hw hwb
      rw [hwv] at h3
      exact absurd (right_le_veblen _ _) (not_le.2 h3)
  rw [← hβ, le_antisymm hle hge]

/-- **The reading of a strongly critical code `s > 0` is strongly critical.** -/
theorem gxTh_SC (hZ : SC Z) (hAt : GxAt At) {s : Ordinal.{0}} (hs : SC s) (hZs : Z < s) :
    SC (gxTh Z At s) := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have := gxTh_lt (GxCl.zero (At := At) hZ.1) (hZ.1.trans hZs)
    rwa [gxTh_zero] at this
  · obtain ⟨ca, hca, hcas, rfl⟩ := gxTh_onto ha
    obtain ⟨cb, hcb, hcbs, rfl⟩ := gxTh_onto hb
    rw [← gxTh_phi hZ hAt ca hca cb hcb]
    exact gxTh_lt (GxCl.phi hca hcb) (hs.2 _ hcas _ hcbs)

end Googology.Trans.PoR.InaccPsi.R2.Mx
