import Googology.Trans.PoR.InaccPsi.R2.NnPlat
import Googology.Trans.PoR.InaccPsi.R2.CdCodes
import Googology.Trans.PoR.InaccPsi.R2.CpRel
import Googology.Trans.PoR.InaccPsi.R2.CpName

/-!
# The codes below the least strongly critical ordinal above `Ω₁`

`GgCl Z` (**the codes over `Z`**): the least set containing the ordinals below `Z` and `Ω₁`, closed under `+` and
the binary Veblen function `φ`.  `ggTh y c` (**the reading over `y`**) is the order type of the codes over `y` below
`c`.  `ggGam` is the least strongly critical ordinal above `Ω₁`, `ggE` the least `ε`-number above `Ω₁`.

* `ggGam_spec`, `ggGam_le`, `ggE_spec`, `ggE_le`, `ggE_le_ggGam`, `ggGam_le_Om2`;
* `GgCl.mono`, `GgCl.zero`, `GgCl.opow`, `GgCl.mul_nat`, `GgCl.mem_CSet` (a code over `Z` lies in every hull
  `Cl(a, b)` with `Z ≤ b`), `GgCl.lt_of_lt_Om1` (a countable code over a strongly critical `Z` is below `Z`),
  `GgCl.support` (every code over a strongly critical `Z` is a code over some `Z' < Z`);
* `ggCl_of_CSet` (**the hull below `ggGam` consists of codes**): if every countable member of `Cl(a, Z)` is below
  `Z`, then every member of `Cl(a, Z)` below `ggGam` is a code over `Z` (the collapses `ψ_π(e)` with `π ≠ Ω₁`, the
  `I_n`, `I_ω` and the `Ω_x` with `x ≥ 2` are strongly critical above `Ω₁`);
* `ggExp_eps`, `ggExp_zero`, `ggExp_HCl` (**the last exponent of a member of the hull without countable
  collapses is in that hull**);
* `ggLog_add`, `ggDec` (**the codes are closed under `w ↦ w - x` and `w ↦ log_ω w`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp

/-- **The codes over `Z`**: generated from the ordinals below `Z` and `Ω₁` by `+` and `φ`. -/
inductive GgCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → GgCl Z x
  | om : GgCl Z (Om 1)
  | add {x y : Ordinal.{0}} : GgCl Z x → GgCl Z y → GgCl Z (x + y)
  | phi {x y : Ordinal.{0}} : GgCl Z x → GgCl Z y → GgCl Z (veblen x y)

/-- The set of codes over `Z`. -/
def ggSet (Z : Ordinal.{0}) : Set Ordinal.{0} := {x | GgCl Z x}

/-- **The reading over `y`**: the order type of the codes over `y` below `c`. -/
noncomputable def ggTh (y c : Ordinal.{0}) : Ordinal.{0} := cdOtp (ggSet y) c

/-- The least strongly critical ordinal above `Ω₁`. -/
noncomputable def ggGam : Ordinal.{0} := sInf {b | SC b ∧ Om 1 < b}

/-- The least `ε`-number above `Ω₁`. -/
noncomputable def ggE : Ordinal.{0} := sInf {b | ω ^ b = b ∧ Om 1 < b}

theorem gg_Om1_lt_Om2 : Om (1 : Ordinal.{0}) < Om (1 + 1) := Om_lt_Om.2 (lt_add_one 1)

theorem gg_SC_Om2 : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by rw [one_add_one_eq_two]; exact two_ne_zero)

theorem ggGam_spec : SC ggGam ∧ Om 1 < ggGam :=
  csInf_mem (s := {b | SC b ∧ Om 1 < b}) ⟨_, gg_SC_Om2, gg_Om1_lt_Om2⟩

theorem ggGam_le {b : Ordinal.{0}} (hb : SC b) (h1 : Om 1 < b) : ggGam ≤ b :=
  csInf_le' (s := {b | SC b ∧ Om 1 < b}) ⟨hb, h1⟩

theorem ggGam_le_Om2 : ggGam ≤ Om (1 + 1) := ggGam_le gg_SC_Om2 gg_Om1_lt_Om2

theorem ggE_spec : ω ^ ggE = ggE ∧ Om 1 < ggE :=
  csInf_mem (s := {b | ω ^ b = b ∧ Om 1 < b})
    ⟨_, Low.opow_eq_self_of_SC ggGam_spec.1, ggGam_spec.2⟩

theorem ggE_le {b : Ordinal.{0}} (hb : ω ^ b = b) (h1 : Om 1 < b) : ggE ≤ b :=
  csInf_le' (s := {b | ω ^ b = b ∧ Om 1 < b}) ⟨hb, h1⟩

theorem ggE_le_ggGam : ggE ≤ ggGam := ggE_le (Low.opow_eq_self_of_SC ggGam_spec.1) ggGam_spec.2

/-! ## Closure properties -/

variable {Z : Ordinal.{0}}

theorem GgCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : GgCl Z x) : GgCl Z' x := by
  induction hx with
  | small h' => exact GgCl.small (lt_of_lt_of_le h' h)
  | om => exact GgCl.om
  | add _ _ ihx ihy => exact GgCl.add ihx ihy
  | phi _ _ ihx ihy => exact GgCl.phi ihx ihy

theorem GgCl.zero (hZ : 0 < Z) : GgCl Z 0 := GgCl.small hZ

theorem GgCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : GgCl Z c) : GgCl Z (ω ^ c) := by
  have := GgCl.phi (GgCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem GgCl.mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : GgCl Z x) : ∀ n : ℕ, GgCl Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GgCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact GgCl.add (GgCl.mul_nat hZ h n) h

/-- A code over `Z` lies in every hull `Cl(a, b)` with `Z ≤ b`. -/
theorem GgCl.mem_CSet {S : InaccSeq.{0}} {a b : Ordinal.{0}} (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GgCl Z x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- A countable code over a strongly critical `Z` is below `Z`. -/
theorem GgCl.lt_of_lt_Om1 (hZ : SC Z) {x : Ordinal.{0}} (hx : GgCl Z x) : x < Om 1 → x < Z := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1))
      (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))

theorem gg_one_lt_of_SC (hZ : SC Z) : 1 < Z := by
  have := hZ.2 0 hZ.1 0 hZ.1
  rwa [veblen_zero_apply, opow_zero] at this

/-- **Finite support**: every code over a strongly critical `Z` is a code over some `Z' < Z`. -/
theorem GgCl.support (hZ : SC Z) {x : Ordinal.{0}} (hx : GgCl Z x) : ∃ Z' < Z, GgCl Z' x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h =>
    exact ⟨x + 1, hZ.isPrincipal h h1, GgCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GgCl.om⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2, GgCl.add (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1, g1⟩ := ihx
    obtain ⟨Z2, h2, g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1 h2, GgCl.phi (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩

/-! ## The hull below `ggGam` -/

theorem gg_Om1_lt_I (S : InaccSeq.{0}) (n : ℕ) : Om (1 : Ordinal.{0}) < S.I n := by
  have h : Om (1 : Ordinal.{0}) < Om (S.I n) :=
    Om_lt_Om.2 (one_lt_Om1.trans_le (Low.Om_one_le_I n))
  rwa [S.fix n] at h

theorem gg_Om1_lt_Iw (S : InaccSeq.{0}) : Om (1 : Ordinal.{0}) < S.Iw :=
  (gg_Om1_lt_I S 0).trans_le (S.I_le_Iw 0)

/-- **The hull below `ggGam` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every
member of `Cl(a, Z)` below `ggGam` is a code over `Z`. -/
theorem ggCl_of_CSet {S : InaccSeq.{0}} {a : Ordinal.{0}} (hZ : 0 < Z)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < ggGam → GgCl Z x := by
  intro x hx
  have hx' := hx
  induction hx with
  | small h => exact fun _ => GgCl.small h
  | zero => exact fun _ => GgCl.zero hZ
  | inacc n =>
    exact fun h => absurd (ggGam_le (SC_I (S := S) n) (gg_Om1_lt_I S n)) (not_le.2 h)
  | inaccW =>
    exact fun h => absurd (ggGam_le (SC_Iw (S := S)) (gg_Om1_lt_Iw S)) (not_le.2 h)
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact GgCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact GgCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le ggGam_le_Om2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GgCl.zero hZ
    · rw [h1]; exact GgCl.om
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact GgCl.small (hkey _ hx' hlt)
    · have hge : Om 1 ≤ S.psi e.1 π := not_lt.1 fun h' => hπ0 (Low.eq_Om_one_of_psi_lt hπ h')
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact absurd (ggGam_le (SC_psi hπ _) (lt_of_le_of_ne hge hne)) (not_le.2 h)

/-! ## The last exponent -/

/-- The last exponent of an `ε`-number is itself. -/
theorem ggExp_eps {x : Ordinal.{0}} (hx : ω ^ x = x) (h0 : x ≠ 0) : cdExp x = x := by
  refine cdExp_eq h0 (by rw [hx]) fun h => ?_
  have hle := le_of_dvd h0 h
  rw [← succ_eq_add_one, opow_succ, hx] at hle
  exact absurd hle (not_le.2 (lt_mul_of_one_lt_right (pos_iff_ne_zero.2 h0) one_lt_omega0))

theorem ggExp_zero : cdExp (0 : Ordinal.{0}) = 0 := by
  unfold cdExp
  have hs : {e : Ordinal.{0} | ω ^ e ∣ 0} = Set.univ := by ext e; simp
  rw [hs, csSup_of_not_bddAbove not_bddAbove_univ, csSup_empty]
  rfl

theorem ggExp_opow (c : Ordinal.{0}) : cdExp (ω ^ c) = c := by
  have := cpExp_mul_succ c 0
  rwa [zero_add, mul_one] at this

theorem gg_veblen_eps {x y : Ordinal.{0}} (hx : x ≠ 0) : ω ^ veblen x y = veblen x y := by
  rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx) y

theorem gg_SC_eps {b : Ordinal.{0}} (hb : SC b) : ω ^ b = b := Low.opow_eq_self_of_SC hb

/-- **The last exponent of a member of the hull without countable collapses is in that hull.** -/
theorem ggExp_HCl {S : InaccSeq.{0}} {a : Ordinal.{0}} {x : Ordinal.{0}} (hx : HCl S a Z x) :
    HCl S a Z (cdExp x) := by
  induction hx with
  | @small x h =>
    rcases eq_or_ne x 0 with rfl | h0
    · rw [ggExp_zero]; exact HCl.zero
    · exact HCl.small ((cpExp_le h0).trans_lt h)
  | zero => rw [ggExp_zero]; exact HCl.zero
  | inacc n =>
    rw [ggExp_eps (gg_SC_eps (SC_I (S := S) n)) (S.I_ne_zero n)]; exact HCl.inacc n
  | inaccW =>
    rw [ggExp_eps (gg_SC_eps (SC_Iw (S := S))) S.Iw_ne_zero]; exact HCl.inaccW
  | @add x y hx hy ihx ihy =>
    rcases eq_or_ne y 0 with rfl | h0
    · rw [add_zero]; exact ihx
    · rw [cpExp_add x h0]; exact ihy
  | @phi x y hx hy ihx ihy =>
    rcases eq_or_ne x 0 with rfl | h0
    · rw [veblen_zero_apply, ggExp_opow]; exact hy
    · rw [ggExp_eps (gg_veblen_eps h0) veblen_pos.ne']; exact HCl.phi hx hy
  | @om x hx ih =>
    rcases eq_or_ne x 0 with rfl | h0
    · rw [Om_zero, ggExp_zero]; exact HCl.zero
    · rw [ggExp_eps (gg_SC_eps (SC_Om h0)) (Om_pos h0).ne']; exact HCl.om hx
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    rw [ggExp_eps (gg_SC_eps (SC_psi hπ e)) (SC_psi hπ e).1.ne']
    exact HCl.coll hπ hπ1 hπC heC hea

/-! ## Decomposition: the codes are closed under `w ↦ w - x` and `w ↦ log_ω w` -/

/-- `log_ω (u + v)` is `log_ω u` or `log_ω v`. -/
theorem ggLog_add (u v : Ordinal.{0}) : log ω (u + v) = log ω u ∨ log ω (u + v) = log ω v := by
  rcases eq_or_ne v 0 with rfl | hv
  · left; rw [add_zero]
  rcases eq_or_ne u 0 with rfl | hu
  · right; rw [zero_add]
  have huv : u + v ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hv) le_add_self).ne'
  have hu1 := lt_opow_succ_log_self one_lt_omega0 u
  have hv1 := lt_opow_succ_log_self one_lt_omega0 v
  rcases le_or_gt (log ω u) (log ω v) with h | h
  · right
    refine (log_eq_iff one_lt_omega0 huv _).2 ⟨(opow_log_le_self ω hv).trans le_add_self, ?_⟩
    have hu2 : u < ω ^ (log ω v + 1) :=
      hu1.trans_le (opow_le_opow_right omega0_pos (by rw [succ_eq_add_one]; gcongr))
    rw [← succ_eq_add_one] at hu2 ⊢
    exact isPrincipal_add_omega0_opow _ hu2 hv1
  · left
    refine (log_eq_iff one_lt_omega0 huv _).2 ⟨(opow_log_le_self ω hu).trans le_self_add, ?_⟩
    have hv2 : v < ω ^ (log ω u + 1) :=
      hv1.trans_le (opow_le_opow_right omega0_pos (by rw [succ_eq_add_one]; exact Order.add_one_le_of_lt h |>.trans le_self_add))
    rw [← succ_eq_add_one] at hv2 ⊢
    exact isPrincipal_add_omega0_opow _ hu1 hv2

/-- `w - x = w` for an additive principal `w > x`, `0` for `x = w`. -/
theorem gg_sub_prin {w x : Ordinal.{0}} (hp : IsPrincipal (· + ·) w) (hx : x ≤ w) :
    w - x = w ∨ w - x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · left; exact Ordinal.sub_eq_of_add_eq (hp.add_eq_right h)
  · right; exact Ordinal.sub_self _

/-- **Decomposition**: for a strongly critical `Z`, a code `w` over `Z` has `w - x` (for every code `x ≤ w`) and
`log_ω w` codes over `Z`. -/
theorem ggDec (hZ : SC Z) : ∀ w, GgCl Z w →
    (∀ x, GgCl Z x → x ≤ w → GgCl Z (w - x)) ∧ GgCl Z (log ω w) := by
  have h0 : GgCl Z 0 := GgCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, GgCl Z v → v ≤ w →
      (∀ x, GgCl Z x → x ≤ v → GgCl Z (v - x)) ∧ GgCl Z (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => GgCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      GgCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
      rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact GgCl.om
      · exact h0
    · have : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
        conv_lhs => rw [← Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact GgCl.om
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact GgCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : GgCl Z (x - u) := (IHo x hxw hx).1 u hu hux.le
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
        · exact GgCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact GgCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact GgCl.phi ha hb

end Googology.Trans.PoR.InaccPsi.R2.Gg
