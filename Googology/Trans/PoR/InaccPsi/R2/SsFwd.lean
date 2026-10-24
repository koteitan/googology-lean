import Googology.Trans.PoR.InaccPsi.R2.SsFn

/-!
# FWD at every level `μ < Γ_{Ω₁+1}` of the generic hierarchy `ssP`

`ψ = S.psi`, `ssP μ` the levels on the generic data `ssDatL μ = ssDat(Ω₁ + μ)` (`R2.SsFn`), `u_μ = Ω₁^μ = Le.leOe μ`,
`Γ_{Ω₁+1} = Gg.ggGam`.  An argument `B` is *own* when `B ∈ Cl(B, ψ_{Ω₁}(B))`.

* `ss_code_lvl` (**`ssDatL μ < b` makes `μ < Γ_{Ω₁+1}` a code over the strongly critical `b`**, by `ss_code` and
  `Gg.ggDec`);
* `SsFWD S μ` (the statement name), `ssFwdAll` (**`ψ_{Ω₁}(B)` is a fixed point of `ssP μ` for every own `B ≠ 0` with
  `u_{μ+1} ∣ B` and `ssDatL μ < ψ_{Ω₁}(B)`, at every level `μ < Γ_{Ω₁+1}`**: the proof of `Rk.rk_fwd`; it extends
  `Rk.rk_fwd` (levels `< ε_{Ω₁+1}`) and `Ss.ssFwd` (the level `ε_{Ω₁+1}`) to every Veblen code).

No new axiom.  New definition: the statement name `SsFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **`ssDatL μ < b` makes `μ < Γ_{Ω₁+1}` a code over a strongly critical `b`.** -/
theorem ss_code_lvl {μ b : Ordinal.{0}} (hb : SC b) (hμ : μ < ggGam) (hd : ssDatL μ < b) : GgCl b μ := by
  have hO : Om1 + μ < ggGam := (lq_SC_indec ggGam_spec.1).add_lt ss_Om1_lt_Gam hμ
  have h := ss_code hb.1 (Om1 + μ) hO hd
  have h2 := (ggDec hb _ h).1 (Om 1) GgCl.om (by rw [← Rj.rj_Om1]; exact le_self_add)
  rwa [← Rj.rj_Om1, Ordinal.add_sub_cancel] at h2

/-- **FWD(μ)** for `ssP`: `ψ_{Ω₁}(B)` is a fixed point of `ssP μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B` and
`ssDatL μ < ψ_{Ω₁}(B)`. -/
def SsFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 →
    ssDatL μ < S.psi B (Om 1) → ssP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **FWD(μ) at every level `μ < Γ_{Ω₁+1}` of `ssP`** (the proof of `Rk.rk_fwd`, codes read by `ss_cl_iff`). -/
theorem ssFwdAll (μ : Ordinal.{0}) : μ < ggGam → SsFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [ssP_eq_rkP 0 (InE.pos ggE_spec.1).le, rkP_zero, ← rhF_zero]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : ssDatL 0 = 0 := ssDatL_zero
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
    rwa [ssP_eq_rkP 0 (InE.pos ggE_spec.1).le, rkP_zero] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, ssP μ z < x := by
    intro z hz
    set a := ssDatL μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (ssDatL μ + z) e.symm
    have hdp : ssDatL μ < p := (le_self_add.trans_lt (lt_add_one (ssDatL μ + z))).trans hap
    have hz1p : z + 1 < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef, add_assoc]; exact le_add_self
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpx
    have hBpB : Bp < B := by
      have h := compare_psi Low.InR_Om_one hownp hown
      rw [hBp, compare_lt_iff_lt.2 hpx] at h
      exact compare_lt_iff_lt.1 h.symm
    set e := u * (Bp / u) + u with hedef
    have hBpe : Bp ≤ e := by
      calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
        _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
    have hpe : p ≤ S.psi e (Om 1) := by rw [← hBp]; exact (psi_mono Low.InR_Om_one hBpe).1
    have hde : ssDatL μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem)
        (rkU_mem (SC_psi Low.InR_Om_one _) (ss_code_lvl (SC_psi Low.InR_Om_one _) hμ hde))
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, ssP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (rkU_mul_mem (SC_psi Low.InR_Om_one _)
            (ss_code_lvl (SC_psi Low.InR_Om_one _) hμ (hde.trans_le hle)) (hd.trans_le hle))
      refine ⟨hownd, ssP_range (SC_psi Low.InR_Om_one _) (hde.trans_le hle)
        fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, ssP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : ssP μ w' < ssP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((ssP_lt_iff μ).1 h2) (not_lt.2 h1)
    have hz1e : z + 1 < S.psi e (Om 1) := hz1p.trans_le hpe
    obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
    have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
    have hlt : e + u * (z + 1) < B := by
      have hq : Bp / u < Om 1 * m := by
        rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
      have hc1 : 1 + (z + 1) < Om 1 :=
        rb_Om1_indec.add_lt (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero)))
          ((Om_isSuccLimit one_ne_zero).add_one_lt (hz.trans hx1))
      have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
        simp only [hedef, mul_add, mul_one, add_assoc]
      rw [e1, hm]
      exact (mul_lt_mul_iff_right₀ hupos).2 (rh_add_lt_Om1_mul hq hc1)
    have hψlt : S.psi (e + u * (z + 1)) (Om 1) < x :=
      psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono Low.InR_Om_one hlt.le).2 (hed (z + 1) hz1e).1)
    calc ssP μ z < ssP μ w := (ssP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((ssP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (ssP_le_self μ x)

end Googology.Trans.PoR.InaccPsi.R2.Ss
