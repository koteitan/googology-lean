import Googology.Trans.PoR.InaccPsi.R2.TnGen
import Googology.Trans.PoR.InaccPsi.R2.TnSys

/-!
# The next prefix `P + Ω₂²` by the generic limit step

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_y(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `CL = Sn.SnCL`,
`G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`.

* `tnCodeHeadP` (**a code `z` with `P ≤ z ≤ P + Ω₂²`, `Ω₂² ∣ P`, gives the code `P`**), `tnLadDown` (**at a base,
  `CL (P + Ω₂²)` and `c < T_{P + Ω₂·c}` give `CL (P + Ω₂·c)`**, the collapse `St.stCollD`), `tnImgW2`;
* `tnO2_opow` (`ω^{Ω₁·2} = Ω₁·Ω₁`), `tnPDW2` (**THE NEXT PREFIX: if `P` with the image `P̂` is a prefix,
  `Ω₂² ∣ P` and `Ω₁² ∣ P̂`, then `P + Ω₂²` with the image `P̂ + Ω₁²` is a prefix**: `Tn.tnLevLimM` with the members
  `M(c) = P + Ω₂·c` of the ladder `St.stLad`, `M̂(ĉ) = P̂ + Ω₁·ĉ`);
* `tnGh_dvd2` (`Ω₁² ∣ Ĝ`), `tnPD_GW2` (**`G + Ω₂²` with the image `Ĝ + Ω₁²` is a prefix**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- **A code `z` with `P ≤ z ≤ P + Ω₂²`** (`Ω₂² ∣ P`) **gives the code `P`.** -/
theorem tnCodeHeadP {Q P z : Ordinal.{0}} (hQ : SC Q) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P) (h1 : P ≤ z)
    (h2 : z ≤ P + Om (1 + 1) * Om (1 + 1)) (hz : LeCl (Om (1 + 1)) Q z) : LeCl (Om (1 + 1)) Q P := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨x, rfl⟩ := exists_add_of_le h1
  have hxle : x ≤ Om (1 + 1) * Om (1 + 1) := (add_le_add_iff_left P).1 h2
  rcases hxle.lt_or_eq with hx | rfl
  · have hdW : x / Om (1 + 1) < Om (1 + 1) := (Ordinal.div_lt hW0).2 hx
    have hcW : x % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt x hW0
    have e : P + x = P + Om (1 + 1) * (x / Om (1 + 1)) + x % Om (1 + 1) := by
      rw [add_assoc, Ordinal.div_add_mod]
    rw [e] at hz
    have hdv : Om (1 + 1) ∣ P + Om (1 + 1) * (x / Om (1 + 1)) :=
      dvd_add ((dvd_mul_right _ _).trans hd2) (dvd_mul_right _ _)
    exact (stCodeHead2 hQ hd2 hdW (stCodeHead hQ hdv hcW hz).1).1
  · obtain ⟨q, rfl⟩ := hd2
    have e1 : (Om (1 + 1) * Om (1 + 1) * q + Om (1 + 1) * Om (1 + 1)) / Om (1 + 1) =
        Om (1 + 1) * q + Om (1 + 1) := by
      rw [mul_assoc, ← mul_add, Ordinal.mul_div_cancel _ hW0]
    have h1 := sjCl_div hQ ldOm2_SC _ hz
    rw [e1] at h1
    have h2 := stCodeHeadW hQ (dvd_mul_right _ _) h1
    rw [mul_assoc]; exact LeCl.mulK hQ ldOm2_SC _ h2

/-- **At a base, `CL (P + Ω₂²)` and `c < T_{P + Ω₂·c}` give `CL (P + Ω₂·c)`.** -/
theorem tnLadDown {l β X0 Xh0 P c : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + Om (1 + 1) * Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (P + Om (1 + 1) * Om (1 + 1))) 0 β) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P)
    (hcl : SnCL S (P + Om (1 + 1) * Om (1 + 1)) β X0)
    (hcT : c < S.psi (β + leWe (X0 + leWe (P + Om (1 + 1) * c))) (Om (1 + 1))) (hcW : c < Om (1 + 1)) :
    SnCL S (P + Om (1 + 1) * c) β X0 := by
  have hy : P + Om (1 + 1) * c ≤ P + Om (1 + 1) * Om (1 + 1) :=
    (add_le_add_iff_left P).2 (mul_le_mul_left' hcW.le _)
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
  intro Q hQ hQ'
  have hP := tnCodeHeadP hQ hd2 (le_self_add.trans hz1) hz2 (hz Q hQ hQ')
  exact LeCl.add hP (LeCl.mulK hQ ldOm2_SC _ (LeCl.small (hcT.trans_le hQ')))

theorem tnSC1 : SC (Om (1 : Ordinal.{0})) := Ph.ph_SC_Om1

theorem tnO2_opow : ω ^ (Om (1 : Ordinal.{0}) * (1 + 1)) = Om 1 * Om 1 := by
  rw [mul_add, mul_one, opow_add, gg_SC_eps tnSC1]

theorem tnO2_mem {a b : Ordinal.{0}} : Om (1 : Ordinal.{0}) * Om 1 ∈ S.CSet a b :=
  ldMulK_mem tnSC1 (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _))

theorem tnW2_mem {a b : Ordinal.{0}} : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∈ S.CSet a b :=
  ldMulK_mem ldOm2_SC (Mx.mxOm2_mem _ _) (Mx.mxOm2_mem _ _)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- The image condition of `P + Ω₂²`. -/
theorem tnImgW2 {P Ph : Ordinal.{0}} (himg : StImg S l P Ph) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P) :
    StImg S l (P + Om (1 + 1) * Om (1 + 1)) (Ph + Om 1 * Om 1) := by
  intro T hT hcl
  obtain ⟨h1, h2⟩ := himg T hT fun Q hQ hTQ => tnCodeHeadP hQ hd2 le_self_add le_rfl (hcl Q hQ hTQ)
  exact ⟨CSet.add_mem h1 tnO2_mem, fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (LeCl.mulK hQ tnSC1 _ LeCl.om)⟩

/-- **THE NEXT PREFIX `P + Ω₂²` with the image `P̂ + Ω₁²`.** -/
theorem tnPDW2 {P Ph : Ordinal.{0}} (hD : StPD S l P Ph) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P)
    (hdh2 : Om 1 * Om 1 ∣ Ph) : StPD S l (P + Om (1 + 1) * Om (1 + 1)) (Ph + Om 1 * Om 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hG3S := rwG3_SC (S := S)
  have himg := tnImgW2 hD.img hd2
  have hH : P + Om (1 + 1) * Om (1 + 1) ∈ cdHull S l := CSet.add_mem hD.hull tnW2_mem
  have h1 : 1 ≤ P + Om (1 + 1) * Om (1 + 1) := hD.one.trans le_self_add
  have hEG : P + Om (1 + 1) * Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    hG3S.isPrincipal hD.ltG3 (ldMul_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3)
  have hEhG : Ph + Om 1 * Om 1 < S.psi 0 (Om (1 + 1)) :=
    rwG_SC.isPrincipal hD.ltG (ldMul_lt_SC rwG_SC rwO_lt_G rwO_lt_G)
  refine ⟨dvd_add hD.dvd (dvd_mul_right _ _), hH, h1, hEG, hEhG, himg, ?_⟩
  refine tnLevLimM hl hX (M := fun d => P + Om (1 + 1) * d) (Mh := fun d => Ph + Om 1 * d)
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _))
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _))
    (stOwP_img himg hH h1) hEG hEhG ?_ ?_ ?_ ?_
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < Om (1 + 1) * Om (1 + 1) := (add_lt_add_iff_left P).1 hwE
    have hxc : LeCl (Om (1 + 1)) Q x := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (1 + 1)) hw
      obtain ⟨q, hq⟩ := hd2
      rwa [stW2_opow, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    have hd1 : LeCl (Om (1 + 1)) Q (x / Om (1 + 1)) := sjCl_div hQ ldOm2_SC _ hxc
    have hd1W : x / Om (1 + 1) < Om (1 + 1) := (Ordinal.div_lt hW0).2 hx
    have hd1Q : x / Om (1 + 1) < Q := LeCl.lt_of_lt hQ hd1 hd1W
    refine ⟨x / Om (1 + 1) + 1, hQ.isSuccLimit.add_one_lt hd1Q, (add_lt_add_iff_left P).2 ?_⟩
    have h := Ordinal.lt_mul_succ_div x hW0
    rwa [Order.succ_eq_add_one] at h
  · intro Q hQ w hw hwE
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < Om 1 * Om 1 := (add_lt_add_iff_left Ph).1 hwE
    have hxc : LeCl (Om 1) Q x := by
      have h := LeCl.mod hQ.1 tnSC1.isPrincipal (Om 1 * (1 + 1)) hw
      obtain ⟨q, hq⟩ := hdh2
      rwa [tnO2_opow, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    have hd1 : LeCl (Om 1) Q (x / Om 1) := sjCl_div hQ tnSC1 _ hxc
    have hd1W : x / Om 1 < Om 1 := (Ordinal.div_lt hΩ0).2 hx
    have hd1Q : x / Om 1 < Q := LeCl.lt_of_lt hQ hd1 hd1W
    refine ⟨x / Om 1 + 1, hQ.isSuccLimit.add_one_lt hd1Q, (add_lt_add_iff_left Ph).2 ?_⟩
    have h := Ordinal.lt_mul_succ_div x hΩ0
    rwa [Order.succ_eq_add_one] at h
  · intro c hc hc1 hcW
    have hDc := stLad hl hX hD hd2 c hc hcW
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    exact ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev,
      (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left hcW ldOm2_SC.1),
      (add_lt_add_iff_left Ph).2 (mul_lt_mul_of_pos_left hΘc (Om_pos one_ne_zero))⟩
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ _ hcW hcT
    exact tnLadDown hoff (le_self_add.trans_lt hG3) hb hd2 hOw hcT hcW

end Main

/-- `Ω₁² ∣ Ĝ`. -/
theorem tnGh_dvd2 : Om (1 : Ordinal.{0}) * Om 1 ∣ veblen (Om 1) 1 := by
  rw [← tnO2_opow]
  conv_rhs => rw [← gg_veblen_eps (y := 1) (Om_pos one_ne_zero).ne']
  refine opow_dvd_opow ω ?_
  have h : Om (1 : Ordinal.{0}) * (1 + 1) = Om 1 + Om 1 := by rw [mul_add, mul_one]
  rw [h]
  exact ((Ph.ph_veblen_prin _ _) ((lt_add_one _).trans tnOm1_lt_Gh) ((lt_add_one _).trans tnOm1_lt_Gh)).le

/-- **`G + Ω₂²` with the image `Ĝ + Ω₁²` is a prefix.** -/
theorem tnPD_GW2 {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    StPD S l (veblen (Om (1 + 1)) 1 + Om (1 + 1) * Om (1 + 1)) (veblen (Om 1) 1 + Om 1 * Om 1) :=
  tnPDW2 hl hX (tnPD_G hl hX) tnG_dvd2 tnGh_dvd2

end Googology.Trans.PoR.InaccPsi.R2.Tn
