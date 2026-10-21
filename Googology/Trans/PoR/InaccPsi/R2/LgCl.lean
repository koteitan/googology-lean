import Googology.Trans.PoR.InaccPsi.R2.LgFr

/-!
# The codes past `Γ_{Ω₁+1}`: the atom `Γ_{Ω₁+1} = ψ_{Ω₂}(0)`, below the next strongly critical ordinal `Γ'`

`R2.GgCl` takes the codes below `ggGam = Γ_{Ω₁+1}` (generated from the ordinals below `Z` and `Ω₁` by `+` and `φ`).
Above `ggGam` the hull `Cl(A_η, ρ)` has the strongly critical atom `ψ_{Ω₂}(0) = ggGam` (`lg_Gam_psi`).  Here:

* `LgCl Z` (**the codes over `Z` with the atom `ggGam`**), `lgSet`, `lgTh y c` (the reading: order type of the codes
  over `y` below `c`), `lgGam'` (**`Γ'`, the least strongly critical ordinal above `Γ_{Ω₁+1}`**), `lgGam'_le_Om2`;
* `LgCl.mono`, `.zero`, `.opow`, `.mul_nat`, `.mem_CSet` (a code lies in every hull `Cl(a, b)` with `a > 0`, `Z ≤ b`),
  `.lt_of_lt_Om1`, `.support`; `lgCl_of_GgCl`, `lgCl_lt_Gam` (**below `ggGam` the codes are those of `GgCl`**),
  `lgTh_eq_ggTh` (`Θ'_y(c) = Θ_y(c)` for `c ≤ ggGam`);
* `lgCl_of_CSet` (**the hull below `Γ'` consists of codes**: a collapse `ψ_π(e) < Γ'` with `π ≠ Ω₁` is `ggGam`);
* `lgDec` (the codes are closed under `w ↦ w − x` and `w ↦ log_ω w`), `lgTh_add`, `lgTh_opow`, `lgTh_small`,
  `lgTh_Om1`, `lgTh_lt`, `lgTh_mono`, `lgTh_le_onto`, `lgTh_Gam` (**`Θ'_y(Γ_{Ω₁+1}) = Γ(y) = lgG y`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cp

/-- **The codes over `Z` with the atom `ggGam`**: generated from the ordinals below `Z`, `Ω₁` and `ggGam` by `+`
and `φ`. -/
inductive LgCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → LgCl Z x
  | om : LgCl Z (Om 1)
  | gam : LgCl Z ggGam
  | add {x y : Ordinal.{0}} : LgCl Z x → LgCl Z y → LgCl Z (x + y)
  | phi {x y : Ordinal.{0}} : LgCl Z x → LgCl Z y → LgCl Z (veblen x y)

/-- The set of codes over `Z`. -/
def lgSet (Z : Ordinal.{0}) : Set Ordinal.{0} := {x | LgCl Z x}

/-- **The reading over `y`**: the order type of the codes over `y` below `c`. -/
noncomputable def lgTh (y c : Ordinal.{0}) : Ordinal.{0} := cdOtp (lgSet y) c

/-- **`Γ'`**: the least strongly critical ordinal above `ggGam`. -/
noncomputable def lgGam' : Ordinal.{0} := sInf {b | SC b ∧ ggGam < b}

theorem lgGam'_spec (S : InaccSeq.{0}) : SC lgGam' ∧ ggGam < lgGam' :=
  csInf_mem (s := {b | SC b ∧ ggGam < b}) ⟨_, gg_SC_Om2, ggGam_lt_Om2 S⟩

theorem lgGam'_le {b : Ordinal.{0}} (hb : SC b) (h1 : ggGam < b) : lgGam' ≤ b :=
  csInf_le' (s := {b | SC b ∧ ggGam < b}) ⟨hb, h1⟩

theorem lgGam'_le_Om2 (S : InaccSeq.{0}) : lgGam' ≤ Om (1 + 1) := lgGam'_le gg_SC_Om2 (ggGam_lt_Om2 S)

variable {Z : Ordinal.{0}}

theorem LgCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : LgCl Z x) : LgCl Z' x := by
  induction hx with
  | small h' => exact LgCl.small (lt_of_lt_of_le h' h)
  | om => exact LgCl.om
  | gam => exact LgCl.gam
  | add _ _ ihx ihy => exact LgCl.add ihx ihy
  | phi _ _ ihx ihy => exact LgCl.phi ihx ihy

theorem LgCl.zero (hZ : 0 < Z) : LgCl Z 0 := LgCl.small hZ

theorem LgCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : LgCl Z c) : LgCl Z (ω ^ c) := by
  have := LgCl.phi (LgCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem LgCl.mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : LgCl Z x) : ∀ n : ℕ, LgCl Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact LgCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact LgCl.add (LgCl.mul_nat hZ h n) h

theorem lgCl_of_GgCl {x : Ordinal.{0}} (hx : GgCl Z x) : LgCl Z x := by
  induction hx with
  | small h => exact LgCl.small h
  | om => exact LgCl.om
  | add _ _ ihx ihy => exact LgCl.add ihx ihy
  | phi _ _ ihx ihy => exact LgCl.phi ihx ihy

/-- **Below `ggGam` the codes are those of `GgCl`.** -/
theorem lgCl_lt_Gam {x : Ordinal.{0}} (hx : LgCl Z x) : x < ggGam → GgCl Z x := by
  induction hx with
  | small h => exact fun _ => GgCl.small h
  | om => exact fun _ => GgCl.om
  | gam => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h => GgCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GgCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem lg_cl_iff {x : Ordinal.{0}} (hx : x < ggGam) : LgCl Z x ↔ GgCl Z x :=
  ⟨fun h => lgCl_lt_Gam h hx, lgCl_of_GgCl⟩

/-- **A code lies in every hull `Cl(a, b)` with `a > 0` and `Z ≤ b`.** -/
theorem LgCl.mem_CSet {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : LgCl Z x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | gam => exact lg_Gam_mem ha
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- A countable code over a strongly critical `Z` is below `Z`. -/
theorem LgCl.lt_of_lt_Om1 (hZ : SC Z) {x : Ordinal.{0}} (hx : LgCl Z x) : x < Om 1 → x < Z := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | gam => exact fun h => absurd (h.trans ggGam_spec.2) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1))
      (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))

/-- **Finite support**: every code over a strongly critical `Z` is a code over some `Z' < Z`. -/
theorem LgCl.support (hZ : SC Z) {x : Ordinal.{0}} (hx : LgCl Z x) : ∃ Z' < Z, LgCl Z' x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h =>
    exact ⟨x + 1, hZ.isPrincipal h h1, LgCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, LgCl.om⟩
  | gam => exact ⟨0, hZ.1, LgCl.gam⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2, LgCl.add (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2, LgCl.phi (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩

/-! ## The hull below `Γ'` -/

/-- **The hull below `Γ'` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every member of
`Cl(a, Z)` below `Γ'` is a code over `Z` (a collapse `ψ_π(e) < Γ'` with `π ≠ Ω₁` is strongly critical and `> Ω₁`,
hence `ggGam`). -/
theorem lgCl_of_CSet {S : InaccSeq.{0}} {a : Ordinal.{0}} (hZ : 0 < Z)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < lgGam' → LgCl Z x := by
  intro x hx
  have hx' := hx
  have hG2 := lgGam'_le_Om2 S
  induction hx with
  | small h => exact fun _ => LgCl.small h
  | zero => exact fun _ => LgCl.zero hZ
  | inacc n =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I n) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I n))
    rw [S.fix n] at h1
    exact absurd (h.trans_le hG2) (not_lt.2 h1.le)
  | inaccW =>
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) < Om (S.I 0) :=
      Om_lt_Om.2 (lg_two_lt_Om1.trans_le (Low.Om_one_le_I 0))
    rw [S.fix 0] at h1
    exact absurd (h.trans_le hG2) (not_lt.2 (h1.le.trans (S.I_le_Iw 0)))
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact LgCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact LgCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le hG2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact LgCl.zero hZ
    · rw [h1]; exact LgCl.om
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact LgCl.small (hkey _ hx' hlt)
    · have hge : Om 1 ≤ S.psi e.1 π := not_lt.1 fun h' => hπ0 (Low.eq_Om_one_of_psi_lt hπ h')
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      have hG : ggGam ≤ S.psi e.1 π := ggGam_le (SC_psi hπ _) (lt_of_le_of_ne hge hne)
      rcases hG.lt_or_eq with hlt | heq
      · exact absurd (lgGam'_le (SC_psi hπ _) hlt) (not_le.2 h)
      · rw [← heq]; exact LgCl.gam

/-! ## Decomposition -/

theorem lg_Gam_prin : IsPrincipal (· + ·) ggGam := by
  rw [← lg_Gam_eps]; exact isPrincipal_add_omega0_opow _

theorem lg_log_Gam : log ω ggGam = ggGam := by
  conv_lhs => rw [← lg_Gam_eps]
  exact log_opow one_lt_omega0 _

/-- **Decomposition**: for a strongly critical `Z`, a code `w` over `Z` has `w - x` (for every code `x ≤ w`) and
`log_ω w` codes over `Z`. -/
theorem lgDec (hZ : SC Z) : ∀ w, LgCl Z w →
    (∀ x, LgCl Z x → x ≤ w → LgCl Z (w - x)) ∧ LgCl Z (log ω w) := by
  have h0 : LgCl Z 0 := LgCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, LgCl Z v → v ≤ w →
      (∀ x, LgCl Z x → x ≤ v → LgCl Z (v - x)) ∧ LgCl Z (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => LgCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      LgCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
      rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact LgCl.om
      · exact h0
    · have : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
        conv_lhs => rw [← Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact LgCl.om
  | gam =>
    intro _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin lg_Gam_prin hx with e | e <;> rw [e]
      · exact LgCl.gam
      · exact h0
    · rw [lg_log_Gam]; exact LgCl.gam
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact LgCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : LgCl Z (x - u) := (IHo x hxw hx).1 u hu hux.le
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
        · exact LgCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact LgCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact LgCl.phi ha hb

/-! ## The reading over `y` -/

variable {y : Ordinal.{0}}

theorem lg_set_add (x z : Ordinal.{0}) (hx : x ∈ lgSet y) (hz : z ∈ lgSet y) : x + z ∈ lgSet y :=
  LgCl.add hx hz

theorem lg_set_sub (hy : SC y) (x w : Ordinal.{0}) (hx : x ∈ lgSet y) (hw : w ∈ lgSet y) (hxw : x ≤ w) :
    w - x ∈ lgSet y := (lgDec hy w hw).1 x hx hxw

/-- **`Θ'_y(c) = Θ_y(c)` for `c ≤ ggGam`.** -/
theorem lgTh_eq_ggTh {c : Ordinal.{0}} (hc : c ≤ ggGam) : lgTh y c = ggTh y c :=
  ggOtp_congr c fun _ hx => lg_cl_iff (hx.trans_le hc)

/-- `Θ'_y(c) = c` for `c ≤ y`. -/
theorem lgTh_small {c : Ordinal.{0}} (hc : c ≤ y) : lgTh y c = c :=
  cdOtp_of_Iio _ c fun _ hx => LgCl.small (lt_of_lt_of_le hx hc)

/-- **`Θ'_y(Ω₁) = y`** for a strongly critical `y < Ω₁`. -/
theorem lgTh_Om1 (hy : SC y) (hy1 : y < Om 1) : lgTh y (Om 1) = y := by
  rw [lgTh_eq_ggTh ggGam_spec.2.le, ggTh_Om1 hy hy1]

/-- **`Θ'_y(Γ_{Ω₁+1}) = Γ(y) = lgG y`** for a strongly critical `y < Ω₁`. -/
theorem lgTh_Gam (hy : SC y) (hy1 : y < Om 1) : lgTh y ggGam = lgG y := by
  rw [lgTh_eq_ggTh le_rfl, lg_ggTh_Gam hy hy1]

theorem lgTh_lt {c d : Ordinal.{0}} (hc : LgCl y c) (hcd : c < d) : lgTh y c < lgTh y d :=
  cdOtp_lt_of_mem hc hcd

theorem lgTh_mono {c d : Ordinal.{0}} (hcd : c ≤ d) : lgTh y c ≤ lgTh y d := cdOtp_mono _ hcd

theorem lgTh_onto {m v : Ordinal.{0}} (hv : v < lgTh y m) : ∃ c, LgCl y c ∧ c < m ∧ lgTh y c = v := by
  obtain ⟨c, hc, hcm, e⟩ := ggOtp_onto (lgSet y) m v hv
  exact ⟨c, hc, hcm, e⟩

theorem lgTh_le_onto {m v : Ordinal.{0}} (hm : LgCl y m) (hv : v ≤ lgTh y m) :
    ∃ c, LgCl y c ∧ c ≤ m ∧ lgTh y c = v := by
  rcases hv.lt_or_eq with h | h
  · obtain ⟨c, hc, hcm, e⟩ := lgTh_onto h
    exact ⟨c, hc, hcm.le, e⟩
  · exact ⟨m, hm, le_rfl, h.symm⟩

/-- **`Θ'_y(u + v) = Θ'_y(u) + Θ'_y(v)`** for a code `u` over a strongly critical `y`. -/
theorem lgTh_add (hy : SC y) {u : Ordinal.{0}} (hu : LgCl y u) (v : Ordinal.{0}) :
    lgTh y (u + v) = lgTh y u + lgTh y v :=
  ggOtp_add lg_set_add (lg_set_sub hy) hu v

/-- **`Θ'_y(ω^a) = ω^{Θ'_y(a)}`** for a code `a` over a strongly critical `y`. -/
theorem lgTh_opow (hy : SC y) {a : Ordinal.{0}} (ha : LgCl y a) : lgTh y (ω ^ a) = ω ^ lgTh y a :=
  ggOtp_opow (LgCl.zero hy.1) lg_set_add (lg_set_sub hy) (fun _ h => LgCl.opow hy.1 h)
    (fun c hc => (lgDec hy c hc).2) a ha

end Googology.Trans.PoR.InaccPsi.R2
