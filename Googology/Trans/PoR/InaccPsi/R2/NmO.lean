import Googology.Trans.PoR.InaccPsi.R2.NmG
import Googology.Trans.PoR.InaccPsi.R2.OPhi

/-!
# The recursive offset at the named points: the link between `O` and the index `η`

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`, `O = R2.Orec` (the recursive offset), `logend = R2.lg`.
At the points named by Theorem V and Theorem GG, the offset is read off the exponent of `Ω₁` in `η`
(`Ω₁ ↦ ρ`, `ρ` the point itself):

* `Orec_V_eq`: `O(P(Ω₁^γ·α)) = P(Ω₁^γ·α)·γ + logend(α)` for `1 ≤ γ < Λ_Γ`, `1 ≤ α < V_{γ+1}(1)`;
* `Orec_GG_eq`: `O(P(Ω₁^{Ω₁}·α)) = P(Ω₁^{Ω₁}·α)² + logend(α)` for `1 ≤ α < Φ_Γ`
  (`α = 1` is `Λ_Γ`);
* `Orec_PhiG_eq`: `O(P(Ω₁^{Ω₁+1})) = P(Ω₁^{Ω₁+1})² + P(Ω₁^{Ω₁+1})`, with `P(Ω₁^{Ω₁+1}) = Φ_Γ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

theorem VG_succ_one_le_LamG {γ : Ordinal.{0}} (hγ : γ < LamG) : VG (γ + 1) 1 ≤ LamG := by
  have hl : IsSuccLimit LamG := ri_isSuccLimit LamG_ri
  have hγ1 : γ + 1 < LamG := hl.add_one_lt hγ
  have hmem : LamG ∈ range (VG (γ + 1)) := ⟨LamG, LamG_spec.2 _ hγ1⟩
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, VG_at_zero] at hc; exact absurd hc LamG_spec.1.ne
  calc VG (γ + 1) 1 ≤ VG (γ + 1) c := (VG_strictMono _).monotone (Order.one_le_iff_ne_zero.2 hc0)
    _ = LamG := hc

/-- **The offset at `V_γ(α)`**: `O(P(Ω₁^γ·α)) = P(Ω₁^γ·α)·γ + logend(α)` for `1 ≤ γ < Λ_Γ` and
`1 ≤ α < V_{γ+1}(1)`. -/
theorem Orec_V_eq (S : InaccSeq.{0}) {γ α : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG)
    (hα1 : 1 ≤ α) (hα : α < VG (γ + 1) 1) :
    Orec (S.psi (Om ω + ConjT.th S * (Om 1 ^ γ * α)) (Om 1)) =
      S.psi (Om ω + ConjT.th S * (Om 1 ^ γ * α)) (Om 1) * γ + lg α := by
  rw [← V_eq S hγ1 hγ hα1 hα.le]
  have hg : γ ≠ 0 := Order.one_le_iff_ne_zero.1 hγ1
  have hα0 : α ≠ 0 := Order.one_le_iff_ne_zero.1 hα1
  have hαV : α < VG γ α := by
    refine lt_of_le_of_ne (VG_id_le γ α) fun e => ?_
    have hmem : α ∈ range (VG (γ + 1)) := mem_range_VG_succ.2 e.symm
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := by intro h0; rw [h0, VG_at_zero] at hc; exact hα0 hc.symm
    have := (VG_strictMono (γ + 1)).monotone (Order.one_le_iff_ne_zero.2 hc0)
    rw [hc] at this
    exact absurd hα (not_lt.2 this)
  have hαL : α < LamG := hα.trans_le (VG_succ_one_le_LamG hγ)
  have hlL : VG γ α < LamG := by
    calc VG γ α < VG γ LamG := VG_strictMono γ hαL
      _ = LamG := LamG_spec.2 γ hγ
  have h0 : 0 < VG γ α := VG_pos (pos_iff_ne_zero.2 hα0)
  have hfix := ups_fix_of_VG hg ⟨α, rfl⟩
  have hG : ¬ IsGP (VG γ α) := fun hGP => absurd (LamG_le_GP hGP) (not_le.2 hlL)
  have h := lev_moved h0 hG
  have hlev : levG (VG γ α) = γ := by
    refine le_antisymm ?_ (levG_ge h hg ⟨α, rfl⟩)
    by_contra hlt
    have hf : VG γ (VG γ α) = VG γ α := (levG_spec h).1 γ (not_le.1 hlt)
    exact absurd hf (ne_of_gt (VG_strictMono γ hαV))
  rw [Orec_eq_offG2 _ (ri_of_fp h0 hfix) (hlL.trans LamG_lt_PhiG),
    offG2_pos hG (by rw [hlev]; exact hg), hlev, invG_VG, hfix]

/-- **The offset at a `Γ`-point**: `O(P(Ω₁^{Ω₁}·α)) = P(Ω₁^{Ω₁}·α)² + logend(α)` for `1 ≤ α < Φ_Γ`. -/
theorem Orec_GG_eq (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < PhiG) :
    Orec (S.psi (Om ω + ConjT.th S * (Om 1 ^ Om (1 : Ordinal.{0}) * α)) (Om 1)) =
      S.psi (Om ω + ConjT.th S * (Om 1 ^ Om (1 : Ordinal.{0}) * α)) (Om 1) *
        S.psi (Om ω + ConjT.th S * (Om 1 ^ Om (1 : Ordinal.{0}) * α)) (Om 1) + lg α := by
  rw [← GG_eq S hα1 hα.le]
  have hα0 : α ≠ 0 := Order.one_le_iff_ne_zero.1 hα1
  have hGP := isGP_of_GG hα0
  have hfix : upsilon (GG α) = GG α := by have := hGP.2 0 hGP.1; rwa [VG_zero] at this
  have hlt : GG α < PhiG := by
    calc GG α < GG PhiG := GG_strictMono hα
      _ = PhiG := PhiG_fp
  rw [Orec_eq_offG2 _ (ri_of_fp hGP.1 hfix) hlt, offG2_GP hGP, invGG_GG, hfix]

/-- **The offset at `Φ_Γ`**: `O(P(Ω₁^{Ω₁+1})) = P(Ω₁^{Ω₁+1})² + P(Ω₁^{Ω₁+1})`. -/
theorem Orec_PhiG_eq (S : InaccSeq.{0}) :
    Orec (S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1)) =
      S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1) *
        S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1) +
      S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1) := by
  rw [← PhiG_eq S]; exact Orec_PhiG

end Googology.Trans.PoR.InaccPsi.R2.Nm
