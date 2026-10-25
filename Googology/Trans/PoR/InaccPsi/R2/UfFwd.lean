import Googology.Trans.PoR.InaccPsi.R2.UfHull
import Googology.Trans.PoR.InaccPsi.R2.TwFwd

/-!
# FWD at every level `μ < B₂` of `Uc.ucP`, for the arguments that contain the level

`ψ_{Ω₁} = S.psi · Ω₁`, `Φ_μ = Uc.ucP μ` (data `Uc.ucDatL μ`), `u_μ = Ω₁^μ = Le.leOe μ`, `B₂ = Uc.ucB`.  The proof of
`Tw.twFwdAll` (levels `< X`) at the levels `< B₂`, with the codes `UcCl`, the hull converse `Uf.uf_mem_CSet` and the
top atom `Uf.uf_top`:

* `uf_datL_zero`, `uf_P_zero` (`Φ_0 = Tl.tlP 0`);
* `UfFWD S μ` (the statement name), `ufFwdAll` (**`ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` for every own `B ≠ 0` with
  `u_{μ+1} ∣ B`, `ucDatL μ < ψ_{Ω₁}(B)` and `Tw.TwArgs S B μ`, at every level `μ < B₂`**).

No new axiom.  New definition: the statement name `UfFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tw

theorem uf_datL_zero : ucDatL 0 = 0 := by unfold ucDatL; rw [add_zero, ucDat_Om1]

theorem uf_P_zero : ucP 0 = tlP 0 := ucP_eq_tlP 0 (lt_of_le_of_lt zero_le Tl.tlX_gt)

variable {S : InaccSeq.{0}}

/-- **FWD(μ)** for `tlP`: `ψ_{Ω₁}(B)` is a fixed point of `ucP μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B`,
`ucDatL μ < ψ_{Ω₁}(B)` and `TwArgs S B μ`. -/
def UfFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 →
    ucDatL μ < S.psi B (Om 1) → TwArgs S B μ → ucP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **FWD(μ) at every level `μ < X` of `tlP`**, for the own arguments `B` that bound the own arguments of the atoms
of `μ`. -/
theorem ufFwdAll (μ : Ordinal.{0}) : μ < ucB → UfFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx hargs
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [uf_P_zero, tlP_zero_eq, ← rhF_zero]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : ucDatL 0 = 0 := uf_datL_zero
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
      (hargs.mono le_rfl zero_le)
    rwa [uf_P_zero, tlP_zero_eq] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  have hx1' : x ≤ Om1 := by rw [uf_Om1]; exact hx1.le
  have hμc : UcCl x μ := uc_code_lvlL hxSC hx1' hμ hdx
  obtain ⟨A, hAB, hAargs, hAmem⟩ := uf_top hx1' hμc hargs (pos_iff_ne_zero.2 hB0)
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, ucP μ z < x := by
    intro z hz
    set a := ucDatL μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (ucDatL μ + z) e.symm
    have hdp : ucDatL μ < p := (le_self_add.trans_lt (lt_add_one (ucDatL μ + z))).trans hap
    have hz1p : z + 1 < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef, add_assoc]; exact le_add_self
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpx
    have hBpB : Bp < B := by
      have h := compare_psi Low.InR_Om_one hownp hown
      rw [hBp, compare_lt_iff_lt.2 hpx] at h
      exact compare_lt_iff_lt.1 h.symm
    set E := max Bp A with hEdef
    have hEB : E < B := max_lt hBpB hAB
    set e := u * (E / u) + u with hedef
    have hEe : E < e := by
      calc E = u * (E / u) + E % u := (Ordinal.div_add_mod E u).symm
        _ < e := (add_lt_add_iff_left _).2 (Ordinal.mod_lt E hu0)
    have hBpe : Bp ≤ e := (le_max_left _ _).trans hEe.le
    have hAe : A < e := (le_max_right _ _).trans_lt hEe
    have hpe : p ≤ S.psi e (Om 1) := by rw [← hBp]; exact (psi_mono Low.InR_Om_one hBpe).1
    have hde : ucDatL μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hψe1 : S.psi e (Om 1) ≤ Om1 := by rw [uf_Om1]; exact (psi_lt Low.InR_Om_one e).le
    have hψeS : SC (S.psi e (Om 1)) := SC_psi Low.InR_Om_one _
    have hμe : UcCl (S.psi e (Om 1)) μ := uc_code_lvlL hψeS hψe1 hμ hde
    have hμC : μ ∈ S.CSet e (S.psi e (Om 1)) :=
      (uf_mem_CSet hψeS hψe1 le_rfl μ hμe (hAargs e hAe)).1
    have hEmem : E ∈ S.CSet e (S.psi e (Om 1)) := by
      rcases le_total Bp A with h | h
      · rw [hEdef, max_eq_right h]; exact hAmem e _ hAe hψeS hψe1 hμe
      · rw [hEdef, max_eq_left h]; exact (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) E hEmem) (leOe_mem hμC)
    have hue : u ∣ e := ⟨E / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, ucP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hμC' : μ ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) := CSet_mono le_self_add hle hμC
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (leMulOe_mem hμC' (CSet.of_lt (hd.trans_le hle)))
      refine ⟨hownd, ucP_range (SC_psi Low.InR_Om_one _) (hde.trans_le hle) fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj ((hAargs e hAe).mono le_self_add hj.le)
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, ucP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : ucP μ w' < ucP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((ucP_lt_iff μ).1 h2) (not_lt.2 h1)
    have hz1e : z + 1 < S.psi e (Om 1) := hz1p.trans_le hpe
    obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
    have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
    have hlt : e + u * (z + 1) < B := by
      have hq : E / u < Om 1 * m := by
        rw [hm] at hEB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hEB
      have hc1 : 1 + (z + 1) < Om 1 :=
        rb_Om1_indec.add_lt (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero)))
          ((Om_isSuccLimit one_ne_zero).add_one_lt (hz.trans hx1))
      have e1 : e + u * (z + 1) = u * (E / u + (1 + (z + 1))) := by
        simp only [hedef, mul_add, mul_one, add_assoc]
      rw [e1, hm]
      exact (mul_lt_mul_iff_right₀ hupos).2 (rh_add_lt_Om1_mul hq hc1)
    have hψlt : S.psi (e + u * (z + 1)) (Om 1) < x :=
      psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono Low.InR_Om_one hlt.le).2 (hed (z + 1) hz1e).1)
    calc ucP μ z < ucP μ w := (ucP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((ucP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (ucP_le_self μ x)

end Googology.Trans.PoR.InaccPsi.R2.Uf
