import Googology.Trans.PoR.InaccPsi.R2.FaName

/-!
# Fa: READINGS OF ORDINALS THAT ARE NOT CODES

`gxTh Z At c` is defined for every `c` (the order type of the codes below `c`).  Lemma IMG above `ι(Ω₂)` is stated for a code `c` of the
upper hull, which need not be a code of the lower hull, so the laws for `+` and `ω^` are needed for arbitrary ordinals:

* `fa_prefix`: a left part of a code (`a + c`, `ω^z ∣ a`, `c ≤ ω^z`) is a code;
* `fa_gx_add_le`: `Θ(a + c) ≤ Θ a + Θ c`;
* `fa_gx_opow`: `Θ(ω^a) = ω^{Θ a}`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}}

theorem fa_prefix_P {P : Ordinal.{0} → Prop} (hP : FaPC P) : ∀ x, P x → ∀ a c z : Ordinal.{0}, ω ^ z ∣ a → c ≤ ω ^ z →
    x = a + c → P a := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx a c z hd hc e
  rcases eq_or_ne a 0 with rfl | ha0
  · exact hP.zero
  have hx0 : x ≠ 0 := by
    rw [e]
    exact (lt_of_lt_of_le (pos_iff_ne_zero.2 ha0) le_self_add).ne'
  set g := Ordinal.log ω a with hg
  have hag : ω ^ g ≤ a := opow_log_le_self _ ha0
  have hzg : z ≤ g := by
    by_contra hcc
    push Not at hcc
    have hlt : a < ω ^ z := (lt_opow_succ_log_self one_lt_omega0 a).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hcc))
    exact absurd (Ordinal.le_of_dvd ha0 hd) (not_le.2 hlt)
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  have hdec : ω ^ g * (k : Ordinal.{0}) + a % ω ^ g = a := by
    have := Ordinal.div_add_mod a (ω ^ g); rwa [hk] at this
  have hr' : a % ω ^ g < ω ^ g := Ordinal.mod_lt _ (opow_pos g omega0_pos).ne'
  have hdr : ω ^ z ∣ a % ω ^ g := by
    have h1 : ω ^ z ∣ ω ^ g * (k : Ordinal.{0}) := (opow_dvd_opow ω hzg).trans (dvd_mul_right _ _)
    rw [← hdec] at hd
    exact (Ordinal.dvd_add_iff h1).1 hd
  rcases eq_or_ne (a % ω ^ g + c) (ω ^ g) with hs | hs
  · -- `a + c = ω^g (k + 1)`
    have hxe : x = ω ^ g * ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [e, ← hdec, add_assoc, hs, Nat.cast_succ, mul_add_one]
    have hlog : Ordinal.log ω x = g := by
      rw [hxe]
      have hk1 : ((k + 1 : ℕ) : Ordinal.{0}) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hkω : ((k + 1 : ℕ) : Ordinal.{0}) < ω := natCast_lt_omega0 _
      have hne : ω ^ g * ((k + 1 : ℕ) : Ordinal.{0}) ≠ 0 := by rw [← hxe]; exact hx0
      refine (Ordinal.log_eq_iff one_lt_omega0 hne g).2 ⟨?_, ?_⟩
      · exact Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hk1)
      · rw [opow_add, opow_one]
        exact (mul_lt_mul_iff_right₀ (opow_pos g omega0_pos)).2 hkω
    have hgP : P g := by have := hP.log hx; rwa [hlog] at this
    -- `a % ω^g + c = ω^g` with `c ≤ ω^z ≤ ω^g`: either the remainder is `0` or it is absorbed
    have hrP : P (a % ω ^ g) := by
      rcases eq_or_ne (a % ω ^ g) 0 with h0 | h0
      · rw [h0]; exact hP.zero
      · have hcg : c = ω ^ g := by
          by_contra hne
          have hclt : c < ω ^ g := lt_of_le_of_ne (hc.trans (opow_le_opow_right omega0_pos hzg)) hne
          have hsum := (Ordinal.isPrincipal_add_omega0_opow g) hr' hclt
          exact absurd hs hsum.ne
        -- then `x = a + ω^g` and `a % ω^g` is below `ω^z`-multiples
        have hzg' : z = g := by
          refine le_antisymm hzg ?_
          have : ω ^ g ≤ ω ^ z := by rw [← hcg]; exact hc
          exact (opow_le_opow_iff_right one_lt_omega0).1 this
        have hle := Ordinal.le_of_dvd h0 hdr
        rw [hzg'] at hle
        exact absurd hr' (not_lt.2 hle)
    rw [← hdec]
    exact hP.add (hP.mul_nat (hP.opow hgP) k) hrP
  · -- `a % ω^g + c < ω^g`
    have hclt : a % ω ^ g + c < ω ^ g := by
      refine lt_of_le_of_ne ?_ hs
      rcases eq_or_lt_of_le (hc.trans (opow_le_opow_right omega0_pos hzg)) with hcg | hcg
      · rw [hcg, Ordinal.add_of_omega0_opow_le hr' le_rfl]
      · exact ((Ordinal.isPrincipal_add_omega0_opow g) hr' hcg).le
    have hxdec : x = ω ^ g * (k : Ordinal.{0}) + (a % ω ^ g + c) := by
      calc x = a + c := e
        _ = (ω ^ g * (k : Ordinal.{0}) + a % ω ^ g) + c := by rw [hdec]
        _ = _ := add_assoc _ _ _
    have hk0 : (k : Ordinal.{0}) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_add] at hdec
      rw [← hdec] at hag
      exact absurd hr' (not_lt.2 hag)
    have hlog : Ordinal.log ω x = g := by
      refine (Ordinal.log_eq_iff one_lt_omega0 hx0 g).2 ⟨?_, ?_⟩
      · rw [hxdec]
        exact (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add
      · rw [hxdec, opow_add, opow_one]
        have h1 : ω ^ g * (k : Ordinal.{0}) + (a % ω ^ g + c) < ω ^ g * (k : Ordinal.{0}) + ω ^ g :=
          (add_lt_add_iff_left _).2 hclt
        refine h1.trans_le ?_
        rw [← mul_add_one]
        refine mul_le_mul_right ?_ _
        exact (isSuccLimit_omega0.add_one_lt (natCast_lt_omega0 k)).le
    obtain ⟨k', hdec', hgP, hrP, hrx⟩ := hP.split hx hx0
    rw [hlog] at hdec' hgP hrP hrx
    have hkk : x % ω ^ g = a % ω ^ g + c := by
      rw [hxdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hclt]
    rw [hkk] at hrP hrx
    have hraP : P (a % ω ^ g) := IH _ hrx hrP _ c z hdr hc rfl
    rw [← hdec]
    exact hP.add (hP.mul_nat (hP.opow hgP) k) hraP

/-- The codes form a closed set. -/
theorem fa_gxPC (hZ : SC Z) (hAt : GxAt At) : FaPC (GxCl Z At) where
  zero := GxCl.zero hZ.1
  add := GxCl.add
  phi := GxCl.phi
  sub := fun {w x} hw hx hle => (gxDec hZ hAt w hw).1 x hx hle
  log := fun {w} hw => (gxDec hZ hAt w hw).2

/-- **`Θ(a + c) ≤ Θ a + Θ c`** for `ω^z ∣ a`, `c ≤ ω^z` (for all ordinals). -/
theorem fa_gx_add_le (hZ : SC Z) (hAt : GxAt At) {a c z : Ordinal.{0}} (hd : ω ^ z ∣ a) (hc : c ≤ ω ^ z) :
    gxTh Z At (a + c) ≤ gxTh Z At a + gxTh Z At c := by
  by_cases ha : GxCl Z At a
  · exact (gxTh_add hZ hAt ha c).le
  refine Ge.gxTh_le_of fun d hdc hdlt => ?_
  rcases lt_or_ge d a with hda | had
  · exact (gxTh_lt hdc hda).trans_le le_self_add
  · exfalso
    obtain ⟨c', rfl⟩ := exists_add_of_le had
    have hc' : c' ≤ ω ^ z := (((add_lt_add_iff_left a).1 hdlt).le).trans hc
    exact ha (fa_prefix_P (fa_gxPC hZ hAt) _ hdc a c' z hd hc' rfl)

/-- **`Θ(ω^a) = ω^{Θ a}`** for every ordinal `a`. -/
theorem fa_gx_opow (hZ : SC Z) (hAt : GxAt At) (a : Ordinal.{0}) : gxTh Z At (ω ^ a) = ω ^ gxTh Z At a := by
  by_cases ha : GxCl Z At a
  · exact gxTh_opow hZ hAt ha
  have h1Z : (1 : Ordinal.{0}) < Z := Gg.gg_one_lt_of_SC hZ
  have h1c : GxCl Z At 1 := GxCl.small h1Z
  have hstep : ∀ b, GxCl Z At b → b < a → gxTh Z At b + 1 < gxTh Z At a := by
    intro b hb hba
    have hb1 : GxCl Z At (b + 1) := GxCl.add hb h1c
    have hne : b + 1 ≠ a := fun e => ha (e ▸ hb1)
    have hlt : b + 1 < a := lt_of_le_of_ne (Order.add_one_le_of_lt hba) hne
    have := gxTh_lt hb1 hlt
    rwa [gxTh_add hZ hAt hb, gxTh_small h1Z.le] at this
  refine le_antisymm ?_ ?_
  · refine Ge.gxTh_le_of fun d hd hdlt => ?_
    by_cases hd0 : d = 0
    · rw [hd0, gxTh_zero]; exact opow_pos _ omega0_pos
    have hlog := (gxDec hZ hAt d hd).2
    have hga : Ordinal.log ω d < a := (lt_opow_iff_log_lt one_lt_omega0 hd0).1 hdlt
    have hg1 : GxCl Z At (Ordinal.log ω d + 1) := GxCl.add hlog h1c
    have h2 := gxTh_lt hd (lt_opow_succ_log_self one_lt_omega0 d)
    rw [Order.succ_eq_add_one, gxTh_opow hZ hAt hg1, gxTh_add hZ hAt hlog, gxTh_small h1Z.le] at h2
    exact h2.trans_le (opow_le_opow_right omega0_pos (hstep _ hlog hga).le)
  · rcases eq_or_ne (gxTh Z At a) 0 with h0 | h0
    · rw [h0, opow_zero]
      have := gxTh_lt (GxCl.zero (At := At) hZ.1) (opow_pos a omega0_pos)
      rw [gxTh_zero] at this
      exact Order.one_le_iff_pos.2 this
    · have hlim : IsSuccLimit (gxTh Z At a) := by
        rcases zero_or_succ_or_isSuccLimit (gxTh Z At a) with h | ⟨s, hs⟩ | h
        · exact absurd h h0
        · exfalso
          have hsa : s < gxTh Z At a := by rw [← hs]; exact lt_succ s
          obtain ⟨b, hb, hba, rfl⟩ := gxTh_onto hsa
          have := hstep b hb hba
          rw [← succ_eq_add_one, hs] at this
          exact lt_irrefl _ this
        · exact h
      refine (Ordinal.opow_le_of_isSuccLimit (by norm_num) hlim).2 fun s hs => ?_
      obtain ⟨b, hb, hba, rfl⟩ := gxTh_onto hs
      rw [← gxTh_opow hZ hAt hb]
      exact (gxTh_lt (hb.opow hZ.1) ((opow_lt_opow_iff_right one_lt_omega0).2 hba)).le

end Googology.Trans.PoR.InaccPsi.R2.Fa
