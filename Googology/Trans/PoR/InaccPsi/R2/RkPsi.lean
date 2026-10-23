import Googology.Trans.PoR.InaccPsi.R2.RhPsi
import Googology.Trans.PoR.InaccPsi.R2.RkCL
import Googology.Trans.PoR.InaccPsi.R2.RiPsi

/-!
# `ψ_{Ω₁}(B + Ω₁^μ·D) = Φ_μ(c + D)` and the fixed points of `Φ_μ` among the collapses, at every level `μ < ε_{Ω₁+1}`

`ψ = S.psi`, `Φ_μ = Rk.rkP μ`, `u_μ = Ω₁^μ = Le.leOe μ`, `rkDat μ = rjDat (Ω₁ + μ)`.  An argument `B` is *own* when
`B ∈ Cl(B, ψ_{Ω₁}(B))`.  The proofs of `R2.RiPsi` with the generic levels (`R2.RkFn`, `R2.RkDig`, `R2.RkCL`).

* `rk_fwd` (by induction on `μ`): **`ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B`
  and `rkDat μ < ψ_{Ω₁}(B)`** (FWD; `μ = 0` is `Rh.rh_fwd`, `Φ_0 = Γ_`);
* `rk_conv` (**`u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`**, `μ < ε_{Ω₁+1}`);
* `rk_eq` (**`ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` and `D` is valid** when `d < Φ_μ(c+d)` for every `d ≤ D`, `B` own,
  `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `rkDat μ < ψ_{Ω₁}(B)`), `rk_valid`;
* `rk_dvd_eps`, `rk_dvd_A` (**`u_μ ∣ A_η`** for `μ ≤ ε_{Ω₁+1}`), `rk_fix_A` (**`ψ_{Ω₁}(A_η)` is a fixed point of
  every `Φ_μ`, `μ < ε_{Ω₁+1}`, `rkDat μ < ψ_{Ω₁}(A_η)`**).

No new axiom.  New definition: the statement name `RkFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- `u_μ ∈ Cl(a, b)` from `rkDat μ < b`, `b` strongly critical, `μ < ε_{Ω₁+1}`. -/
theorem rkU_mem' {μ a b : Ordinal.{0}} (hb : SC b) (hμE : μ < ggE) (h : rkDat μ < b) :
    Le.leOe μ ∈ S.CSet a b := rkU_mem hb ((rkDat_lt_iff hb hμE).1 h)

/-- `u_μ·D ∈ Cl(a, b)` from `rkDat μ < b`, `D < b`, `b` strongly critical, `μ < ε_{Ω₁+1}`. -/
theorem rkU_mul_mem' {μ a b D : Ordinal.{0}} (hb : SC b) (hμE : μ < ggE) (h : rkDat μ < b) (hD : D < b) :
    Le.leOe μ * D ∈ S.CSet a b := rkU_mul_mem hb ((rkDat_lt_iff hb hμE).1 h) hD

/-! ## The fixed-point lemmas -/

/-- **FWD(μ)**: `ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B` and
`rkDat μ < ψ_{Ω₁}(B)`. -/
def RkFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 → rkDat μ < S.psi B (Om 1) →
    rkP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **At every level `μ < Ω₁·Ω₁`: FWD(μ).** -/
theorem rk_fwd (μ : Ordinal.{0}) : μ < ggE → RkFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [rkP_zero, ← rhF_zero]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : rkDat 0 = 0 := rkDat_zero
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
    rwa [rkP_zero] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, rkP μ z < x := by
    intro z hz
    set a := rkDat μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (rkDat μ + z) e.symm
    have hdp : rkDat μ < p := (le_self_add.trans_lt (lt_add_one (rkDat μ + z))).trans hap
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
    have hde : rkDat μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem) (rkU_mem' (SC_psi Low.InR_Om_one _) hμ hde)
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, rkP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (rkU_mul_mem' (SC_psi Low.InR_Om_one _) hμ (hde.trans_le hle) (hd.trans_le hle))
      refine ⟨hownd, rkP_range (SC_psi Low.InR_Om_one _) (hde.trans_le hle)
        fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, rkP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : rkP μ w' < rkP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((rkP_lt_iff μ).1 h2) (not_lt.2 h1)
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
    calc rkP μ z < rkP μ w := (rkP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((rkP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (rkP_le_self μ x)

/-- **CONV(μ)**: `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`, `μ < Ω₁·Ω₁`. -/
theorem rk_conv {μ : Ordinal.{0}} (hμ : μ < ggE) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : rkP μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → RkLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := rk_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig (μ + 1) fun j hj => ?_
  have hjμ : j ≤ μ := Order.lt_add_one_iff.1 hj
  have hjΩ : j < ggE := hjμ.trans_lt hμ
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : rkDat j < p := hdl.2.1 j hjΩ hd0
  have hfj : rkP j p = p := rkP_fix_mono hjμ hfix hdj
  have huj : Le.leOe j ∣ B := ri_dvd_of_dig j fun i hi =>
    IHj i hi (hi.trans hj) (hi.le.trans hjμ) (hi.trans hjΩ)
  set u := Le.leOe j with hudef
  set u2 := Le.leOe (j + 1) with hu2def
  have hu2 : u2 = u * Om 1 := Le.leOe_succ j
  have hupos : 0 < u := rhU_pos j
  have h0 := rd_Om1_ne
  obtain ⟨m, hm⟩ := huj
  set D0 := m % Om 1 with hD0
  set B0 := u2 * (m / Om 1) with hB0
  have hBe : B0 + u * D0 = B := by
    rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
  have hD0lt : D0 < Om 1 := Ordinal.mod_lt m h0
  have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ (rhU_ne _)]
  have hD00 : D0 ≠ 0 := by rw [hD0, ← hmdiv]; exact hd0
  have hD0p : D0 < p := by have := hdl.1 j; rwa [← hudef, hmdiv] at this
  have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
  have hBdiv : B / u2 = m / Om 1 := by
    calc B / u2 = (u2 * (m / Om 1) + u * D0) / u2 := by rw [← hB0, hBe]
      _ = m / Om 1 := by
        rw [Ordinal.mul_add_div _ (rhU_ne (j + 1)), Ordinal.div_eq_zero_of_lt hlt', add_zero]
  have hB0m : B0 ∈ S.CSet B p := by
    have := rh_mod_mem (S := S) (m := j + 1) le_add_self B hown
    rwa [← hu2def, hBdiv] at this
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
  have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
  have hle := rk_UB (S := S) hjΩ.le B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (rkP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : rkP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (rkP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## The bridge at level `μ` -/

/-- **`ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)`, and `D < ψ_{Ω₁}(B + u_μ·D)`**, when `d < Φ_μ(c+d)` for every `d ≤ D`, for an
own `B` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)` and `rkDat μ < ψ_{Ω₁}(B)` (`μ < Ω₁·Ω₁`). -/
theorem rk_eq {μ : Ordinal.{0}} (hμ : μ < ggE)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe μ ∣ B)
    (hc : rkP μ c = S.psi B (Om 1)) (hdB : rkDat μ < S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < rkP μ (c + d)) →
      D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = rkP μ (c + D) := by
  set u := Le.leOe μ with hudef
  have hupos : 0 < u := rhU_pos μ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = rkP μ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = rkP μ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : rkDat μ < v := hdB.trans hBv
    have hlt : ∀ d, d < D → rkP μ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (rkU_mul_mem' (SC_psi Low.InR_Om_one _) hμ hdv hdv')
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact rk_UB hμ.le B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (rkU_mul_mem' (SC_psi Low.InR_Om_one _) hμ hdv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < μ, rkDat j < v → rkP j v = v := fun j hj hdj =>
          rk_fwd j (hj.trans hμ) _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
        obtain ⟨e, he⟩ := rkP_range hvSC hdv hfix
        rw [← he]
        refine (rkP_le_iff μ).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((rkP_le_iff μ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((rkP_normal μ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : rkP μ e < v := ((rkP_lt_iff μ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Φ_μ(c+d)` for every `d ≤ D`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `μ ≤ Ω₁·Ω₁`). -/
theorem rk_valid {μ B c D : Ordinal.{0}} (hμ : μ ≤ ggE) (hB : Le.leOe μ ∣ B)
    (hc : rkP μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < rkP μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (rkP_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < rkP μ (c + d) →
      S.psi (B + Le.leOe μ * d'') (Om 1) < rkP μ (c + d) := fun d'' hd'' hq =>
    (rk_UB hμ B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((rkP_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := rk_inv (S := S) hμ hB (rkP_SC μ (c + d)) (rk_clo_val2 μ _)
    (by rw [← hc]; exact (rkP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The points `ψ_{Ω₁}(A_η)` -/

/-- An `ε`-number above `Ω₁` is a multiple of every `u_μ`, `μ ≤ Ω₁·Ω₁`. -/
theorem rk_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ ggE) (hp : ω ^ p = p) (h : Om 1 < p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have hEp : ggE ≤ p := ggE_le hp h
  have hOE : Om 1 + ggE = ggE := Ordinal.add_of_omega0_opow_le (by rw [rk_E_inE]; exact rk_Om1_E) rk_E_inE.le
  have hk : Om 1 * μ ≤ p := by
    calc Om 1 * μ ≤ Om 1 * ggE := mul_le_mul_right hμ _
      _ = ggE := by
          conv_lhs => rw [← Bt.Om1_opow, ← rk_E_inE]
          rw [← opow_add, hOE, rk_E_inE]
      _ ≤ p := hEp
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

/-- **`u_μ ∣ A_η`** for `μ ≤ Ω₁·Ω₁`. -/
theorem rk_dvd_A {μ : Ordinal.{0}} (hμ : μ ≤ ggE) (η : Ordinal.{0}) : Le.leOe μ ∣ ConjT.Aη S η := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    rk_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  have h2 : Le.leOe μ ∣ ConjT.th S :=
    rk_dvd_eps hμ (Low.opow_eq_self_of_SC (ConjT.SC_th S)) Bt.Om1_lt_th
  exact dvd_add h1 (h2.mul_right η)

/-- **The `υ`-point `ψ_{Ω₁}(A_η)` is a fixed point of every `Φ_μ`, `μ < Ω₁·Ω₁`, `rkDat μ < ψ_{Ω₁}(A_η)`.** -/
theorem rk_fix_A {μ η : Ordinal.{0}} (hμ : μ < ggE)
    (hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)))
    (hd : rkDat μ < S.psi (ConjT.Aη S η) (Om 1)) :
    rkP μ (S.psi (ConjT.Aη S η) (Om 1)) = S.psi (ConjT.Aη S η) (Om 1) := by
  refine rk_fwd μ hμ _ hown (rk_dvd_A (Order.add_one_le_of_lt hμ) η) ?_ hd
  unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'

end Googology.Trans.PoR.InaccPsi.R2.Rk
