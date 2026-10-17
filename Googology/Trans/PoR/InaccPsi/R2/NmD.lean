import Googology.Trans.PoR.InaccPsi.R2.NmO

/-!
# Which `η` are good, and the index `ι(η)` of Theorem GEN at the named points

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`; `η` is good when `η ∈ Cl(A_η + 1, P(η))` (`R2.Bt.Good`);
`ι` is the index of Theorem GEN (`υ_{ι(η)} = P(η)`, `R2.Bt.iota`).

* `good_iff`: for `η ≠ 0`, `η` is good iff `P(η) < P(η + 1)`;
* `good_V`, `bad_V`: for `1 ≤ γ < Λ_Γ`, `Ω₁^γ·α` is good for `1 ≤ α < V_{γ+1}(1)`, and every `η` with
  `Ω₁^γ·V_{γ+1}(1) ≤ η < Ω₁^{γ+1}` is bad;
* `bad_LamG`: every `η` with `Ω₁^{Λ_Γ} ≤ η < Ω₁^{Ω₁}` is bad;
* `good_GG`, `bad_PhiG`: `Ω₁^{Ω₁}·α` is good for `1 ≤ α < Φ_Γ`; every `η` with
  `Ω₁^{Ω₁}·Φ_Γ ≤ η < Ω₁^{Ω₁+1}` is bad;
* `iota_V`, `iota_LamG`, `iota_GG`, `iota_PhiG`: `ι(Ω₁^γ·α) = V_γ(α)`, `ι(Ω₁^{Ω₁}) = Λ_Γ`,
  `ι(Ω₁^{Ω₁}·α) = GG(α)`, `ι(Ω₁^{Ω₁+1}) = Φ_Γ`; `Orec_iota_V`, `Orec_iota_GG`: the recursive offset at
  the restart index `ι(η)` in terms of `η`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- For `η ≠ 0`: `η` is good iff `P(η) < P(η + 1)`. -/
theorem good_iff (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη0 : η ≠ 0) :
    Bt.Good S η ↔ Pv S η < Pv S (η + 1) := by
  refine ⟨Pv_lt_succ, fun h => ?_⟩
  by_contra hbad
  have := psi_succ_of_bad S hη0 hbad
  exact absurd this (ne_of_gt h)

/-- `η` with `P(η) = P(η + 1)` is bad. -/
theorem bad_of_eq {η : Ordinal.{0}} (h : Pv S η = Pv S (η + 1)) : ¬ Bt.Good S η := fun hg =>
  absurd h (ne_of_lt (Pv_lt_succ hg))

/-- The points between two arguments with the same value of `P` are bad. -/
theorem bad_between {a b η : Ordinal.{0}} (hab : Pv S a = Pv S b) (ha : a ≤ η) (hb : η < b) :
    ¬ Bt.Good S η := by
  refine bad_of_eq (le_antisymm (Pv_mono le_self_add) ?_)
  calc Pv S (η + 1) ≤ Pv S b := Pv_mono (Order.add_one_le_of_lt hb)
    _ = Pv S a := hab.symm
    _ ≤ Pv S η := Pv_mono ha

theorem lt_VG_of_lt_fix {γ α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < VG (γ + 1) 1) : α < VG γ α := by
  refine lt_of_le_of_ne (VG_id_le γ α) fun e => ?_
  obtain ⟨c, hc⟩ : α ∈ range (VG (γ + 1)) := mem_range_VG_succ.2 e.symm
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, VG_at_zero] at hc; exact (Order.one_le_iff_ne_zero.1 hα1) hc.symm
  have := (VG_strictMono (γ + 1)).monotone (Order.one_le_iff_ne_zero.2 hc0)
  rw [hc] at this
  exact absurd hα (not_lt.2 this)

/-- `Ω₁^γ·α` is good for `1 ≤ γ < Λ_Γ`, `1 ≤ α < V_{γ+1}(1)`. -/
theorem good_V (S : InaccSeq.{0}) {γ α : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG) (hα1 : 1 ≤ α)
    (hα : α < VG (γ + 1) 1) : Bt.Good S (Om 1 ^ γ * α) := by
  have hP : Pv S (Om 1 ^ γ * α) = VG γ α := (V_eq S hγ1 hγ hα1 hα.le).symm
  have hγP : γ < Pv S (Om 1 ^ γ * α) := by
    rw [hP]
    exact (lt_VG_one hγ1 hγ).trans_le ((VG_strictMono γ).monotone hα1)
  have hαP : α < Pv S (Om 1 ^ γ * α) := by rw [hP]; exact lt_VG_of_lt_fix hα1 hα
  exact mem_Om1_pow_mul hγP hαP

/-- Every `η` with `Ω₁^γ·V_{γ+1}(1) ≤ η < Ω₁^{γ+1}` is bad (`1 ≤ γ < Λ_Γ`). -/
theorem bad_V (S : InaccSeq.{0}) {γ η : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG)
    (h1 : Om 1 ^ γ * VG (γ + 1) 1 ≤ η) (h2 : η < Om 1 ^ (γ + 1)) : ¬ Bt.Good S η := by
  have hZ1 : 1 ≤ VG (γ + 1) 1 := (one_lt_VG_one _).le
  have ha : Pv S (Om 1 ^ γ * VG (γ + 1) 1) = VG (γ + 1) 1 := by
    have e : VG γ (VG (γ + 1) 1) = Pv S (Om 1 ^ γ * VG (γ + 1) 1) := V_eq S hγ1 hγ hZ1 le_rfl
    rw [← e]
    exact mem_range_VG_succ.1 ⟨1, rfl⟩
  have hb : Pv S (Om 1 ^ (γ + 1)) = VG (γ + 1) 1 :=
    Pv_Om1_pow S (hγ1.trans le_self_add) fun _ hδ hδ1 =>
      lt_VG_one hδ1 ((Order.lt_add_one_iff.1 hδ).trans_lt hγ)
  exact bad_between (ha.trans hb.symm) h1 h2

/-- Every `η` with `Ω₁^{Λ_Γ} ≤ η < Ω₁^{Ω₁}` is bad. -/
theorem bad_LamG (S : InaccSeq.{0}) {η : Ordinal.{0}} (h1 : Om 1 ^ LamG ≤ η)
    (h2 : η < Om 1 ^ Om (1 : Ordinal.{0})) : ¬ Bt.Good S η := by
  have ha := Pv_Om1_pow_LamG S
  have hb : Pv S (Om 1 ^ Om (1 : Ordinal.{0})) = LamG := (LamG_eq S).symm
  exact bad_between (ha.trans hb.symm) h1 h2

/-- `Ω₁^{Ω₁}·α` is good for `1 ≤ α < Φ_Γ`. -/
theorem good_GG (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < PhiG) :
    Bt.Good S (W * α) := by
  have hP : Pv S (W * α) = GG α := (GG_eq S hα1 hα.le).symm
  have hαP : α < Pv S (W * α) := by rw [hP]; exact lt_GG hα1 hα
  exact mem_W_mul hαP

/-- Every `η` with `Ω₁^{Ω₁}·Φ_Γ ≤ η < Ω₁^{Ω₁+1}` is bad. -/
theorem bad_PhiG (S : InaccSeq.{0}) {η : Ordinal.{0}} (h1 : W * PhiG ≤ η)
    (h2 : η < Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) : ¬ Bt.Good S η := by
  have ha : Pv S (W * PhiG) = PhiG := (PhiG_eq_mul S).symm
  have hb : Pv S (Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) = PhiG := (PhiG_eq S).symm
  exact bad_between (ha.trans hb.symm) h1 h2

/-! ## The index `ι` -/

theorem iota_of_fix {η x : Ordinal.{0}} (hP : Pv S η = x) (hx : upsilon x = x) : iota S η = x := by
  have h := ups_iota S η
  rw [show S.psi (ConjT.Aη S η) (Om 1) = Pv S η from rfl, hP, ← hx] at h
  exact upsilon_normal.strictMono.injective h

/-- `ι(Ω₁^γ·α) = V_γ(α)` for `1 ≤ γ < Λ_Γ`, `1 ≤ α ≤ V_{γ+1}(1)`. -/
theorem iota_V (S : InaccSeq.{0}) {γ α : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG) (hα1 : 1 ≤ α)
    (hα : α ≤ VG (γ + 1) 1) : iota S (Om 1 ^ γ * α) = VG γ α :=
  iota_of_fix (V_eq S hγ1 hγ hα1 hα).symm
    (ups_fix_of_VG (Order.one_le_iff_ne_zero.1 hγ1) ⟨α, rfl⟩)

/-- `ι(Ω₁^{Ω₁}) = Λ_Γ`. -/
theorem iota_LamG (S : InaccSeq.{0}) : iota S (Om 1 ^ Om (1 : Ordinal.{0})) = LamG :=
  iota_of_fix (LamG_eq S).symm LamG_ups

/-- `ι(Ω₁^{Ω₁}·α) = GG(α)` for `1 ≤ α ≤ Φ_Γ`. -/
theorem iota_GG (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α ≤ PhiG) :
    iota S (W * α) = GG α := by
  have hGP := isGP_of_GG (Order.one_le_iff_ne_zero.1 hα1)
  have hfix : upsilon (GG α) = GG α := by have := hGP.2 0 hGP.1; rwa [VG_zero] at this
  exact iota_of_fix (GG_eq S hα1 hα).symm hfix

/-- `ι(Ω₁^{Ω₁+1}) = Φ_Γ`. -/
theorem iota_PhiG (S : InaccSeq.{0}) : iota S (Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) = PhiG :=
  iota_of_fix (PhiG_eq S).symm PhiG_ups

/-- **The offset at the restart index `ι(Ω₁^γ·α)`**: `O(ι(Ω₁^γ·α)) = ι(Ω₁^γ·α)·γ + logend(α)`. -/
theorem Orec_iota_V (S : InaccSeq.{0}) {γ α : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG)
    (hα1 : 1 ≤ α) (hα : α < VG (γ + 1) 1) :
    Orec (iota S (Om 1 ^ γ * α)) = iota S (Om 1 ^ γ * α) * γ + lg α := by
  rw [iota_V S hγ1 hγ hα1 hα.le, V_eq S hγ1 hγ hα1 hα.le]
  exact Orec_V_eq S hγ1 hγ hα1 hα

/-- **The offset at the restart index `ι(Ω₁^{Ω₁}·α)`**: `O(ι(Ω₁^{Ω₁}·α)) = ι(Ω₁^{Ω₁}·α)² + logend(α)`. -/
theorem Orec_iota_GG (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < PhiG) :
    Orec (iota S (W * α)) = iota S (W * α) * iota S (W * α) + lg α := by
  rw [iota_GG S hα1 hα.le, GG_eq S hα1 hα.le]
  exact Orec_GG_eq S hα1 hα

end Googology.Trans.PoR.InaccPsi.R2.Nm
