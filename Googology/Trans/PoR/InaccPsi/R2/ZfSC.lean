import Googology.Trans.PoR.InaccPsi.R2.ZaWit
import Googology.Trans.PoR.InaccPsi.R2.ZaYvCl

/-!
# A `ϑᵗ`-value at an uncountable level is strongly critical

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

For a level `Ω₁ ≤ M` and `η < Ω₁` with `ξ = Ω₁·M + η ∈ Tᵗ ∩ Ω₂`, the value `v = ϑᵗ(ξ)` is strongly critical: for
`a, z < v`, `φ(0, z) = ω^z < v` (`v` is an `ε`-number, `R2.vt_E_iff`), and for `a ≥ 1`, `φ(a, z) ≤ ϑᵗ(Ω₁·a + z)`
(`Gl.glA_veb_le`) and `ϑᵗ(Ω₁·a + z) < v` by the cited comparison `R2.vdVt_lt` (the countable level `a ≤ M`, its datum
`a < v`).  This is the step that makes `Dl τ n` strongly critical once `Dl τ n` is read as a `ϑᵗ`-value at a level
`≥ Ω₁` (`R2.Zf.zfDlSC`).

* `zf_T_init` (`Tᵗ ∩ Ω₁` is an initial segment), `zf_lev_T` (the level of a countable-level argument is in `Tᵗ`),
  `zf_dat_in` (the data of a level `≥ Ω₁` are read in `Tᵗ`), `zf_vt_SC` (**the value is strongly critical**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **`Tᵗ ∩ Ω₁` is an initial segment of `Ω₁`.** -/
theorem zf_T_init {τ x y : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ∈ Tset τ) (hx1 : x < Om1)
    (hyx : y ≤ x) : y ∈ Tset τ :=
  vz_T_down hτ hτ1 hx hx1 hyx

/-- **The data of a level `Ω₁ ≤ M` with `Ω₁·M + η ∈ Tᵗ ∩ Ω₂` are read in `Tᵗ`.** -/
theorem zf_dat_in (S : InaccSeq.{0}) {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hη1 : η < Om1)
    (hξ : Om1 * M + η ∈ Tset τ) (hξ2 : Om1 * M + η < OmTwo) : Vd.VdDatIn (· ∈ Tset τ) M := by
  have hξθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτ hτ1 _ hξ hξ2
  have hM : M < ConjT.th S := ((Xe.xe_le_mul M).trans le_self_add).trans_lt hξθ
  have hA := vdArg_dat hτ hτ1 hM1 hη1 hξ
  rcases lt_or_ge M Uc.ucB with hB | hB
  · exact Vd.vdDatIn_uc hB (hA.1 hB)
  · exact Vd.vdDatIn_th hB hM (hA.2 S hB hM)

/-- **A `ϑᵗ`-value at an uncountable level is strongly critical**: `Ω₁ ≤ M`, `η < Ω₁`, `Ω₁·M + η ∈ Tᵗ ∩ Ω₂` ⇒
`SC (ϑᵗ(Ω₁·M + η))`. -/
theorem zf_vt_SC (S : InaccSeq.{0}) {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hη1 : η < Om1)
    (hξ : Om1 * M + η ∈ Tset τ) (hξ2 : Om1 * M + η < OmTwo) : SC (vt τ (Om1 * M + η)) := by
  set v := vt τ (Om1 * M + η) with hvdef
  obtain ⟨hvT, hτv, hv1, -, -⟩ := vt_memTwo hτ hτ1 hξ hξ2
  have hξ1 : Om1 ≤ Om1 * M + η := (le_mul_left Om1 (Rj.rj_Om1_pos.trans_le hM1)).trans le_self_add
  have hvE : InE v := ((vt_E_iff hτ hτ1 hξ hξ2).2 hξ1).2
  have hMT : Vd.VdDatIn (· ∈ Tset τ) M := zf_dat_in S hτ hτ1 hM1 hη1 hξ hξ2
  have hηT : η ∈ Tset τ := vzRem_T hτ hτ1 hξ hξ2 rfl (dvd_mul_right Om1 M) hη1
  have hOB : Om1 < Uc.ucB := (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B : Om1 < Uc.ucB)
  refine ⟨(omega0_pos.trans (omega0_lt_inE hτ)).trans_le hτv, fun a ha z hz => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero]
    calc ω ^ z < ω ^ v := (opow_lt_opow_iff_right one_lt_omega0).2 hz
      _ = v := hvE
  have h1a : 1 ≤ a := Order.one_le_iff_ne_zero.2 ha0
  have ha1 : a < Om1 := ha.trans hv1
  have hz1 : z < Om1 := hz.trans hv1
  have haT : a ∈ Tset τ := zf_T_init hτ hτ1 hvT hv1 ha.le
  have hzT : z ∈ Tset τ := zf_T_init hτ hτ1 hvT hv1 hz.le
  have hle : veblen a z ≤ Gl.glA a z τ := Gl.glA_veb_le hτ hτ1 h1a haT ha1 hzT hz1
  have harg : Om1 * a + z < Om1 * M + η := by
    calc Om1 * a + z < Om1 * a + Om1 := (add_lt_add_iff_left _).2 hz1
      _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
      _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt ha1) _
      _ ≤ Om1 * M := mul_le_mul_right hM1 _
      _ ≤ Om1 * M + η := le_self_add
  have haB : a < Uc.ucB := ha1.trans hOB
  have hM'T : Vd.VdDatIn (· ∈ Tset τ) a := Vd.vdDatIn_uc haB (by rw [Uc.ucDat_small ha1]; exact haT)
  have hd' : Vd.VdLtIn a v := Or.inl ⟨haB, by rw [Uc.ucDat_small ha1]; exact ha⟩
  have hlt : vt τ (Om1 * a + z) < v :=
    vdVt_lt hτ hτ1 hM1 (ha1.le.trans hM1) hM'T hzT hz1 hMT hηT hη1 harg hd' hz
  exact hle.trans_lt hlt

end Googology.Trans.PoR.InaccPsi.R2.Zf
