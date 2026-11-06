import Googology.Trans.PoR.InaccPsi.R2.ZrRead
import Googology.Trans.PoR.InaccPsi.R2.ZnWin

/-!
# Zs: the base `l₀ = ι(Ω₂)` of the (B-hi)/(C) induction is a fixed restart with a BIG reading

At `l₀ = Zo.zoBase S = ι(Ω₂)` (`Zr.zrBase_eq`) the name is `Ω₂`, `A = Ω_ω + Ω₂`, `ρ = ψ_{Ω₁}(A)`, the code is
`π_{Ω₂}` and `Θ_{l₀}(m_{l₀}) = otp(Cl(A, ρ) ∩ Ω₂)` (`Zr.zrBase_theta`).

* `zsFix` (**`υ_{l₀} = l₀`**: `e(Ω₂) = Ω₂`, so `l₀` is a (C) restart below `L(0)`, `Zo.zoC_fix`);
* `zsSucc` (`υ_{l₀+1} = ψ_{Ω₁}(A + θ)`, `Rg.rgUps_eq`);
* `zsBig` (**`υ_{l₀+1} < Θ_{l₀}(m_{l₀})`**: `θ = ψ_{Ω₂}(Ω_ω)` lies in the hull below `Ω₂` and reads
  `ψ_{Ω₁}(A + θ) = υ_{l₀+1}`, `Wl.wlThVal`);
* `zsBaseRs_lower` (**at `l₀` the RS inputs `Zc.ZcRsIn ∨ Zn.ZnRsVal` give only LOWER itself**,
  `Zn.znRsIn_big_lower`: the term branch fails at the `ε`-number `υ_{l₀+1} < O(l₀)`, the value branch asks values
  below `υ_{l₀+1}` only, and the successor branch needs `c(l₀) < 2`).

So LOWER at `l₀` is the big-reading case of the windows (skWinBig), not a short-term or value case.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo Googology.Trans.PoR.InaccPsi.R2.Zr

variable {S : InaccSeq.{0}}

/-- `Ω₂ ≤ e(Ω₂)`. -/
theorem zsExp : Om (1 + 1) ≤ cdExp (cdEta S (zoBase S)) := by
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := zrE2
  have h0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := (Om_pos (by
    rw [one_add_one_eq_two]; exact two_ne_zero)).ne'
  rw [zrBase_eta]
  exact cdExp_max h0 (by rw [hE2])

/-- `ρ_{l₀} < L(0)`. -/
theorem zsLt_L0 : upsilon (zoBase S) < Nc.ncL S 0 := by
  have hm : upsilon (zoBase S) < cdMstar S := by
    rw [← zoTop_ups (S := S)]; exact upsilon_normal.strictMono zoBase_lt_top
  exact hm.trans_le (cdMstar_le_L S 0)

/-- **`υ_{l₀} = l₀`.** -/
theorem zsFix : upsilon (zoBase S) = zoBase S :=
  zoC_fix zoBase_range zsExp zsLt_L0

/-- `υ_{l₀+1} = ψ_{Ω₁}(Ω_ω + Ω₂ + θ)`. -/
theorem zsSucc : upsilon (zoBase S + 1) = S.psi (Om ω + Om (1 + 1) + ConjT.th S) (Om 1) := by
  have hR : CdRange S (zoBase S) := zoBase_range
  have h1 : (1 : Ordinal.{0}) ≤ upsilon (zoBase S) := by
    rw [zsFix]
    exact Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 zoBase_spec.1.1)
  rw [Rg.rgUps_eq hR h1, zrBase_A, mul_one]

/-- **The base reads big: `υ_{l₀+1} < Θ_{l₀}(m_{l₀})`.** -/
theorem zsBig : upsilon (Order.succ (zoBase S)) < cdTheta S (zoBase S) (cdCode S (zoBase S)) := by
  have hri : IsRestartIdx (zoBase S) := zoBase_spec.1
  have hAη : ConjT.Aη S (cdEta S (zoBase S)) = Om ω + Om (1 + 1) := zrBase_A
  have hρ : S.psi (Om ω + Om (1 + 1)) (Om 1) = upsilon (zoBase S) := by
    rw [zrBase_rho]
    show S.psi (Om ω + Om (1 + 1)) (Om 1) = S.psi (ConjT.Aη S (Om (1 + 1))) (Om 1)
    rw [zrA_Om2]
  have hm : upsilon (zoBase S) < cdMstar S := by
    rw [← zoTop_ups (S := S)]; exact upsilon_normal.strictMono zoBase_lt_top
  have hω : upsilon (zoBase S) < Nc.ncL S ω := hm.trans_le (cdMstar_le_L S ω)
  obtain ⟨-, -, hown0⟩ := Rc.rcOwn hri hω
  rw [hAη] at hown0
  have hown' : Om ω + Om (1 + 1) ∈ S.CSet (Om ω + Om (1 + 1)) (S.psi (Om ω + Om (1 + 1)) (Om 1)) := hown0
  have hHull : cdHull S (zoBase S) = S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
    unfold cdHull; rw [hAη]
  have hθg := Wl.wlThVal hri hm hown' hρ
  have hat : Ld.ldAtR S (zoBase S) = Ls.lsAt S (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
    unfold Ld.ldAtR; rw [hAη]; ext s
    exact ⟨fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩, fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩⟩
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hθ : cdOtp (S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S))) (ConjT.th S) =
      S.psi (Om ω + Om (1 + 1) + ConjT.th S) (Om 1) := by
    rw [Ls.lsOtp_eq (m := ConjT.th S) hρ hθ2.le, ← hat]
    exact hθg
  have hAw : Om ω < Om ω + Om (1 + 1) :=
    lt_add_of_pos_right _ (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero))
  have hmem : ConjT.th S ∈ S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := ConjT.th_mem (S := S) hAw
  have hlt := cdOtp_lt_of_mem (C := S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S))) hmem hθ2
  rw [Order.succ_eq_add_one, zsSucc, zrBase_theta]
  unfold cdTheta
  rw [hHull, ← hθ]
  exact hlt

/-- **At the base the RS inputs give only LOWER itself** (the big-reading case, `Zn.znRsIn_big_lower`). -/
theorem zsBaseRs_lower (h : Zc.ZcRsIn (Ys.ysO S) (zoBase S) ∨ Zn.ZnRsVal (Ys.ysO S) (zoBase S)) :
    CdLower S (zoBase S) :=
  Zn.znRsIn_big_lower zoBase_spec.1 zsFix zsBig h

end Googology.Trans.PoR.InaccPsi.R2.Zs
