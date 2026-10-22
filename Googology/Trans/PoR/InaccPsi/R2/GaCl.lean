import Googology.Trans.PoR.InaccPsi.R2.GaAt

/-!
# The codes with the atoms `Γ_{Ω₁+1+k}` (`k < ω`), below `Γ_{Ω₁+ω}`

The codes are `GxCl Z gaAt` of `R2.MxGx` (from the ordinals below `Z`, `Ω₁` and the atoms `gaG k` by `+` and `φ`),
the reading `gxTh y gaAt` (their order type); `R2.MxGx` already has the decomposition, additivity, `ω^·` and the
φ-law for any strongly critical atoms.  Here:

* generic (any atoms `At` with `GxAt At`): `gx_support` (finite support), `gx_mul_nat`, `gx_le_onto`, `gx_inj`,
  `gx_nat`, `gx_add_nat`, `gx_ne_zero`, `gx_Om1_one`, `gxTh_Om1_one`, `gxSplit` (a code is `a + n` with `ω ∣ a`),
  `gxTh_veblen_lvl`;
* the atoms `gaAt`: `gaCl_lt_W` (**a code over `Z ≤ Ω₁` is below `Γ_{Ω₁+ω}`**), `gaCl_mem_CSet` (**a code lies in every
  hull `Cl(a, b)` with `ω ≤ a`, `Z ≤ b`**), `gaCl_of_CSet` (**the hull below `Γ_{Ω₁+ω}` consists of codes**: a collapse
  `ψ_π(e) < Γ_{Ω₁+ω}` with `π ≠ Ω₁` is strongly critical and above `Ω₁`, hence an atom), `gaCl_of_lg`, `lg_of_gaCl`,
  `gaTh_eq_lgTh` (**below `Γ' = gaG 1` the codes and readings are those of `R2.LgCl`**), `gaTh_G0` (`Θ_y(Γ_{Ω₁+1}) =
  Γ(y)`), `gaTh_G` (**the reading of `gaG k` is strongly critical, above `y` and below `Ω₁`**), `gaTh_lt_Om1`;
* `GaPoly X E` (**terms for the codes below `E`**), `gaPoly_of_SC`, `gaPoly_of_lg` (`LgPoly X E` with `E ≤ Γ'` gives
  `GaPoly X E`).

No new axiom.  New definition: `GaPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}} {Z y : Ordinal.{0}} {At : Set Ordinal.{0}}

/-! ## Generic facts for strongly critical atoms -/

/-- **Finite support**: every code over a strongly critical `Z` is a code over some `Z' < Z`. -/
theorem gx_support (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z At x) : ∃ Z' < Z, GxCl Z' At x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | atom hs => exact ⟨0, hZ.1, GxCl.atom hs⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2,
      GxCl.add (g1.mono (le_max_left _ _) Subset.rfl) (g2.mono (le_max_right _ _) Subset.rfl)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2,
      GxCl.phi (g1.mono (le_max_left _ _) Subset.rfl) (g2.mono (le_max_right _ _) Subset.rfl)⟩

theorem gx_mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : GxCl Z At x) : ∀ n : ℕ, GxCl Z At (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact GxCl.add (gx_mul_nat hZ h n) h

theorem gx_le_onto {m v : Ordinal.{0}} (hm : GxCl y At m) (hv : v ≤ gxTh y At m) :
    ∃ c, GxCl y At c ∧ c ≤ m ∧ gxTh y At c = v := by
  rcases hv.lt_or_eq with h | h
  · obtain ⟨c, hc, hcm, e⟩ := gxTh_onto h
    exact ⟨c, hc, hcm.le, e⟩
  · exact ⟨m, hm, le_rfl, h.symm⟩

theorem gx_inj {u v : Ordinal.{0}} (hu : GxCl y At u) (hv : GxCl y At v) (h : gxTh y At u = gxTh y At v) :
    u = v := by
  rcases lt_trichotomy u v with h' | h' | h'
  · exact absurd h (gxTh_lt hu h').ne
  · exact h'
  · exact absurd h (gxTh_lt hv h').ne'

theorem gx_nat (hy : SC y) (n : ℕ) : gxTh y At (n : Ordinal.{0}) = n := gxTh_small (ph_nat_lt hy n).le

theorem gx_add_nat (hy : SC y) (hAt : GxAt At) {u : Ordinal.{0}} (hu : GxCl y At u) (n : ℕ) :
    gxTh y At (u + n) = gxTh y At u + n := by rw [gxTh_add hy hAt hu, gx_nat hy]

theorem gx_ne_zero (hy : SC y) {c : Ordinal.{0}} (h0 : c ≠ 0) : gxTh y At c ≠ 0 := by
  have := gxTh_lt (GxCl.zero (At := At) hy.1) (pos_iff_ne_zero.2 h0) (d := c)
  rw [gxTh_zero] at this; exact this.ne'

theorem gx_Om1_one (hZ : SC Z) : GxCl Z At (Om 1 + 1) := GxCl.add GxCl.om (GxCl.small (gg_one_lt_of_SC hZ))

theorem gxTh_Om1_one (hy : SC y) (hy1 : y < Om 1) (hAt : GxAt At) : gxTh y At (Om 1 + 1) = y + 1 := by
  rw [gxTh_add hy hAt GxCl.om, gxTh_Om1 hy hy1 hAt, gxTh_small (gg_one_lt_of_SC hy).le]

/-- `φ_a` with a constant level `a < y`: `Θ_y(φ_a(b)) = φ_a(Θ_y(b))`. -/
theorem gxTh_veblen_lvl (hy : SC y) (hAt : GxAt At) {a b : Ordinal.{0}} (ha : a < y) (hb : GxCl y At b) :
    gxTh y At (veblen a b) = veblen a (gxTh y At b) := by
  rw [gxTh_phi hy hAt a (GxCl.small ha) b hb, gxTh_small ha.le]

/-- **A code is `a + n`** with `a` a code, `ω ∣ a`, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical `y ≥ Z`. -/
theorem gxSplit (hZ : SC Z) (hAt : GxAt At) : ∀ b, GxCl Z At b → ∃ a : Ordinal.{0}, ∃ n : ℕ, GxCl Z At a ∧
    ω ∣ a ∧ b = a + n ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → ω ∣ gxTh y At a := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases lt_or_ge b ω with hbω | hbω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hbω
    exact ⟨0, n, GxCl.zero hZ.1, dvd_zero _, by rw [zero_add], fun y _ _ _ => by
      rw [gxTh_zero]; exact dvd_zero _⟩
  have hb0 : b ≠ 0 := (omega0_pos.trans_le hbω).ne'
  have hL : log ω b ≠ 0 := by
    intro h
    have := lt_opow_succ_log_self one_lt_omega0 b
    rw [h, Order.succ_eq_add_one, zero_add, opow_one] at this
    exact absurd hbω (not_le.2 this)
  obtain ⟨hsub, hlog⟩ := gxDec hZ hAt b hb
  have hw : GxCl Z At (ω ^ log ω b) := GxCl.opow hZ.1 hlog
  have hwb : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hr := hsub _ hw hwb
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwb
  rcases eq_or_ne (b - ω ^ log ω b) 0 with h0 | h0
  · rw [h0, add_zero] at hbr
    refine ⟨b, 0, hb, hbr ▸ ph_omega_dvd_opow hL, by rw [Nat.cast_zero, add_zero], fun y hy hy1 hZy => ?_⟩
    rw [← hbr, gxTh_opow hy hAt (hlog.mono hZy Subset.rfl)]
    exact ph_omega_dvd_opow (gx_ne_zero hy hL)
  · have hrb : b - ω ^ log ω b < b := by
      rcases (Ordinal.sub_le_self b (ω ^ log ω b)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : ω ^ log ω b + b = b := by conv_rhs => rw [← hbr]
                                            rw [h]
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [← opow_succ] at h2
        exact absurd (lt_opow_succ_log_self one_lt_omega0 b) (not_lt.2 h2)
    obtain ⟨a', n, ha', hd', he', hθ'⟩ := IH _ hrb hr
    refine ⟨ω ^ log ω b + a', n, GxCl.add hw ha', dvd_add (ph_omega_dvd_opow hL) hd', ?_,
      fun y hy hy1 hZy => ?_⟩
    · rw [add_assoc, ← he', hbr]
    · rw [gxTh_add hy hAt (hw.mono hZy Subset.rfl), gxTh_opow hy hAt (hlog.mono hZy Subset.rfl)]
      exact dvd_add (ph_omega_dvd_opow (gx_ne_zero hy hL)) (hθ' y hy hy1 hZy)

/-! ## The atoms `gaG k` -/

/-- **A code over `Z ≤ Ω₁` is below `Γ_{Ω₁+ω}`.** -/
theorem gaCl_lt_W (S : InaccSeq.{0}) (hZ : Z ≤ Om 1) {c : Ordinal.{0}} (hc : GxCl Z gaAt c) : c < gaW := by
  have hSC := gaW_SC S
  induction hc with
  | small h => exact (h.trans_le hZ).trans (ga_Om1_lt_W S)
  | om => exact ga_Om1_lt_W S
  | atom hs => exact gaAt_lt_W S hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

/-- **A code lies in every hull `Cl(a, b)` with `ω ≤ a` and `Z ≤ b`.** -/
theorem gaCl_mem_CSet {a b : Ordinal.{0}} (ha : ω ≤ a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z gaAt x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gaAt_mem ha hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `Γ_{Ω₁+ω}` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every
member of `Cl(a, Z)` below `Γ_{Ω₁+ω}` is a code over `Z`. -/
theorem gaCl_of_CSet {a : Ordinal.{0}} (hZ : 0 < Z) (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < gaW → GxCl Z gaAt x := by
  intro x hx
  have hx' := hx
  have hG2 := (gaW_lt_Om2 S).le
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | zero => exact fun _ => GxCl.zero hZ
  | inacc n =>
    intro h
    exact absurd ((h.trans_le hG2).trans (mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro h
    exact absurd ((h.trans_le hG2).trans mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le hG2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hZ
    · rw [h1]; exact GxCl.om
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact GxCl.small (hkey _ hx' hlt)
    · have hge : Om 1 ≤ S.psi e.1 π := not_lt.1 fun h' => hπ0 (Low.eq_Om_one_of_psi_lt hπ h')
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      obtain ⟨k, hk⟩ := gaSC_cases (SC_psi hπ _) (lt_of_le_of_ne hge hne) h
      rw [hk]; exact GxCl.atom ⟨k, rfl⟩

theorem gaCl_of_lg {x : Ordinal.{0}} (hx : LgCl Z x) : GxCl Z gaAt x := by
  induction hx with
  | small h => exact GxCl.small h
  | om => exact GxCl.om
  | gam => exact GxCl.atom ⟨0, rfl⟩
  | add _ _ ihx ihy => exact GxCl.add ihx ihy
  | phi _ _ ihx ihy => exact GxCl.phi ihx ihy

/-- **Below `Γ' = gaG 1` the codes are those of `R2.LgCl`.** -/
theorem lg_of_gaCl (S : InaccSeq.{0}) {x : Ordinal.{0}} (hx : GxCl Z gaAt x) : x < lgGam' → LgCl Z x := by
  induction hx with
  | small h => exact fun _ => LgCl.small h
  | om => exact fun _ => LgCl.om
  | @atom s hs =>
    intro h
    obtain ⟨k, rfl⟩ := hs
    have hk : k < 1 := (gaG_strictMono S).lt_iff_lt.1 (by rw [gaG_one]; exact h)
    obtain rfl : k = 0 := by omega
    exact LgCl.gam
  | @add x y _ _ ihx ihy =>
    exact fun h => LgCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => LgCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **`Θ_y(c) = Θ'_y(c)` for `c ≤ Γ'`.** -/
theorem gaTh_eq_lgTh (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c ≤ lgGam') : gxTh y gaAt c = lgTh y c :=
  ggOtp_congr c fun _ hx => ⟨fun h => lg_of_gaCl S h (hx.trans_le hc), fun h => gaCl_of_lg h⟩

/-- `Θ_y(Γ_{Ω₁+1}) = Γ(y)`. -/
theorem gaTh_G0 (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) : gxTh y gaAt (gaG 0) = lgG y := by
  rw [gaTh_eq_lgTh S (gaG_lt_succ S 0).le, gaG_zero, lgTh_Gam hy hy1]

/-- **The reading of `gaG k` is strongly critical, above `y`, below `Ω₁`.** -/
theorem gaTh_G (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) :
    ∀ k : ℕ, SC (gxTh y gaAt (gaG k)) ∧ y < gxTh y gaAt (gaG k) ∧ gxTh y gaAt (gaG k) < Om 1
  | 0 => by
    rw [gaTh_G0 S hy hy1]; exact ⟨Lp.lpG_SC hy hy1, (Lp.lpG_facts hy hy1).1, (Lp.lpG_facts hy hy1).2⟩
  | k + 1 => by
    obtain ⟨ihS, ihy, ih1⟩ := gaTh_G S hy hy1 k
    have hAt := gaAt_GxAt S
    have hXS := Lp.lpG_SC ihS ih1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts ihS ih1
    have hle : gxTh y gaAt (gaG (k + 1)) ≤ lgG (gxTh y gaAt (gaG k)) := by
      refine Ld.ldAtom_le hy hy1 hAt hXS (ihy.trans hX1) fun t ht htk => ?_
      obtain ⟨j, rfl⟩ := ht
      have hj : j ≤ k := Nat.lt_succ_iff.1 ((gaG_strictMono S).lt_iff_lt.1 htk)
      exact (gxTh_mono (gaG_le_of_le S hj)).trans_lt hX1
    have hlt : gxTh y gaAt (gaG k) < gxTh y gaAt (gaG (k + 1)) := gxTh_lt (GxCl.atom ⟨k, rfl⟩) (gaG_lt_succ S k)
    exact ⟨gxTh_SC hy hAt (gaG_SC S _) (hy1.trans (gaG_Om1_lt S _)), ihy.trans hlt, hle.trans_lt hX2⟩

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem gaTh_lt_Om1 (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y gaAt c) :
    gxTh y gaAt c < Om 1 := by
  have hAt := gaAt_GxAt S
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => obtain ⟨k, rfl⟩ := hs; exact (gaTh_G S hy hy1 k).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Terms for the codes -/

/-- **Terms for the codes below `E`**: for every code `c < E` over `Z` some term of `X` has the value `Θ_y(c)` at every
strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GaPoly (X : XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z gaAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y gaAt c

/-- **Reduction to strongly critical `Z`.** -/
theorem gaPoly_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → ∀ c, GxCl Z gaAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
      X.CB s y ∧ X.val s y = gxTh y gaAt c) : GaPoly X E := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 c (hc.mono h3 Subset.rfl) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

/-- **`LgPoly X E` with `E ≤ Γ'` gives `GaPoly X E`.** -/
theorem gaPoly_of_lg (S : InaccSeq.{0}) {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ lgGam') (h : LgPoly X E) :
    GaPoly X E := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := h Z c (lg_of_gaCl S hc (hcE.trans_le hE)) hcE
  refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
  rw [(hs y hy hy1 hZy).2, gaTh_eq_lgTh S (hcE.trans_le hE).le]

end Googology.Trans.PoR.InaccPsi.R2.Ga
