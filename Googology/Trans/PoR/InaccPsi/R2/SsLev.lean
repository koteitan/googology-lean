import Googology.Trans.PoR.InaccPsi.R2.SsDat

/-!
# The level `ε_{Ω₁+1}`: `Φ_{E₁} = Rk.rkP ε_{Ω₁+1}` enumerates the level-closed points; its `ψ_{Ω₁}`-side

`ψ = S.psi`, `Φ_μ = Rk.rkP μ`, `u_μ = Ω₁^μ = Le.leOe μ`, `E₁ = ε_{Ω₁+1} = Gg.ggE`, `B_n = Bc.bcB S n`, `c_{n+1} =
Bc.bcC S (n + 1)`, `SpLC` the level-closed ordinals (`R2.SpBase`).  `Rk.rkP μ` is defined for every `μ`; at `μ =
E₁` the data is `0` and **`Φ_{E₁}` enumerates exactly the level-closed points** (`ssLC_iff`).  The lemmas of
`R2.RkPsi` for the levels `μ < E₁` are proved here once more at `μ = E₁`, where `u_{E₁} = E₁`:

* `ssDatE` (`rkDat E₁ = 0`), `ssLC_iff` (**`SpLC v ↔ v ∈ range Φ_{E₁}`**), `ssU_mem`, `ssU_mul_mem`;
* `ssFwd` (**`ψ_{Ω₁}(B)` is a fixed point of `Φ_{E₁}` for every own `B ≠ 0` with `u_{E₁+1} ∣ B`**), `ssConv`
  (**the converse**), `ssEq` (**`ψ_{Ω₁}(B + E₁·D) = Φ_{E₁}(c + D)`** for an own `B` with `E₁ ∣ B`, `Φ_{E₁}(c) =
  ψ_{Ω₁}(B)`, when `d < Φ_{E₁}(c + d)` for every `d ≤ D`; the converse is `Rk.rk_valid`, stated for `μ ≤ E₁`);
* `ssDvd_eps`, `ssDvd_alpha`, `ssDvd_alphaW`, `ssDvd_A` (**`u_{E₁+1}` divides `α_j`, `α_ω`, `A_η`**), `ssB_dvd`
  (**`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `μ ∈ {E₁, E₁ + 1}` and `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`);
* `ssUps_fix` (**every `υ`-point `υ_ξ < c_{n+1}`, `ξ ≠ 0`, is a fixed point of `Φ_{E₁}`**), `ssB_E1` (`B_n(E₁ + 1) =
  E₁ + 1`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-! ## The level `E₁` -/

/-- `rkDat E₁ = 0`. -/
theorem ssDatE : rkDat ggE = 0 := by
  unfold rkDat
  rw [ss_Om1_add_E, Rj.rjDat, dif_neg (fun h => absurd h.2 (lt_irrefl _)),
    if_neg (not_lt.2 Rj.rj_Om1_lt_E.le)]

theorem ssE_pos : (0 : Ordinal.{0}) < ggE := InE.pos ggE_spec.1

/-- **`Φ_{E₁}` enumerates the level-closed points.** -/
theorem ssLC_iff {v : Ordinal.{0}} : SpLC v ↔ v ∈ range (rkP ggE) := by
  rw [(rkP_props ggE).2]
  refine ⟨fun h => ⟨h.1, by rw [ssDatE]; exact h.1.1, fun j hj hd => h.2 j hj hd⟩,
    fun h => ⟨h.1, fun j hj hd => h.2.2 j hj hd⟩⟩

/-- The values of `Φ_{E₁}` are level-closed. -/
theorem ssLC_val (o : Ordinal.{0}) : SpLC (rkP ggE o) := ssLC_iff.2 ⟨o, rfl⟩

theorem ssU_mem {a b : Ordinal.{0}} (hb : SC b) : Le.leOe ggE ∈ S.CSet a b :=
  rkU_mem hb (spE_cl (gg_one_lt_of_SC hb))

theorem ssU_mul_mem {a b D : Ordinal.{0}} (hb : SC b) (hD : D < b) : Le.leOe ggE * D ∈ S.CSet a b :=
  rkU_mul_mem hb (spE_cl (gg_one_lt_of_SC hb)) hD

/-! ## FWD, CONV and the bridge at `E₁` -/

/-- **FWD(E₁)**: `ψ_{Ω₁}(B)` is a fixed point of `Φ_{E₁}` for every own `B ≠ 0` with `u_{E₁+1} ∣ B` (the proof of
`Rk.rk_fwd` at `μ = E₁`). -/
theorem ssFwd {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe (ggE + 1) ∣ B)
    (hB0 : B ≠ 0) : rkP ggE (S.psi B (Om 1)) = S.psi B (Om 1) := by
  have h0 := rd_Om1_ne
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμ0 : ggE ≠ 0 := ssE_pos.ne'
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ ggE + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := rk_fwd 0 ssE_pos B hown h1 hB0 (by rw [rkDat_zero]; exact hxSC.1)
    rwa [rkP_zero] at this
  set u := Le.leOe ggE with hudef
  have hu0 : u ≠ 0 := rhU_ne ggE
  have hupos : 0 < u := rhU_pos ggE
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, rkP ggE z < x := by
    intro z hz
    set a := rkDat ggE + z + 1 with hadef
    have hdx : rkDat ggE < x := by rw [ssDatE]; exact hxSC.1
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (rkDat ggE + z) e.symm
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
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem) (ssU_mem (SC_psi Low.InR_Om_one _))
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, rkP ggE w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (ssU_mul_mem (SC_psi Low.InR_Om_one _) (hd.trans_le hle))
      refine ⟨hownd, rkP_range (SC_psi Low.InR_Om_one _) (by rw [ssDatE]; exact (SC_psi Low.InR_Om_one _).1)
        fun j hj hdj => ?_⟩
      exact rk_fwd j hj _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, rkP ggE w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : rkP ggE w' < rkP ggE w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((rkP_lt_iff ggE).1 h2) (not_lt.2 h1)
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
    calc rkP ggE z < rkP ggE w := (rkP_lt_iff ggE).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((rkP_normal ggE).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (rkP_le_self ggE x)

/-- **CONV(E₁)**: `u_{E₁+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_{E₁}` (the proof of
`Rk.rk_conv` at `μ = E₁`; at the digit `j = E₁` the data is `0`). -/
theorem ssConv {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : rkP ggE (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (ggE + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → RkLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := rk_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig (ggE + 1) fun j hj => ?_
  have hjμ : j ≤ ggE := Order.lt_add_one_iff.1 hj
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : rkDat j < p := by
    rcases lt_or_eq_of_le hjμ with hjE | rfl
    · exact hdl.2.1 j hjE hd0
    · rw [ssDatE]; exact hpSC.1
  have hfj : rkP j p = p := rkP_fix_mono hjμ hfix hdj
  have huj : Le.leOe j ∣ B := ri_dvd_of_dig j fun i hi =>
    IHj i hi (hi.trans hj) (hi.le.trans hjμ)
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
  have hle := rk_UB (S := S) hjμ B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (rkP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : rkP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (rkP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **`ψ_{Ω₁}(B + E₁·D) = Φ_{E₁}(c + D)`, and `D < ψ_{Ω₁}(B + E₁·D)`**, when `d < Φ_{E₁}(c+d)` for every `d ≤ D`,
for an own `B` with `u_{E₁} ∣ B` and `Φ_{E₁}(c) = ψ_{Ω₁}(B)` (the proof of `Rk.rk_eq` at `μ = E₁`). -/
theorem ssEq {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe ggE ∣ B)
    (hc : rkP ggE c = S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < rkP ggE (c + d)) →
      D < S.psi (B + Le.leOe ggE * D) (Om 1) ∧ S.psi (B + Le.leOe ggE * D) (Om 1) = rkP ggE (c + D) := by
  set u := Le.leOe ggE with hudef
  have hupos : 0 < u := rhU_pos ggE
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = rkP ggE (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = rkP ggE (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : rkDat ggE < v := by rw [ssDatE]; exact hvSC.1
    have hlt : ∀ d, d < D → rkP ggE (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (ssU_mul_mem (SC_psi Low.InR_Om_one _) hdv')
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact rk_UB le_rfl B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (ssU_mul_mem (SC_psi Low.InR_Om_one _) hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < ggE, rkDat j < v → rkP j v = v := fun j hj hdj =>
          rk_fwd j hj _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
        obtain ⟨e, he⟩ := rkP_range hvSC hdv hfix
        rw [← he]
        refine (rkP_le_iff ggE).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((rkP_le_iff ggE).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((rkP_normal ggE).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : rkP ggE e < v := ((rkP_lt_iff ggE).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-! ## Divisibility by `u_{E₁+1}` -/

/-- `u_μ ∣ p` for an `ε`-number `p` with `Ω₁·μ ≤ p`. -/
theorem ssDvd_eps {μ p : Ordinal.{0}} (hp : ω ^ p = p) (hk : Om 1 * μ ≤ p) : Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

/-- `Ω₁·(E₁ + 1) = E₁ + Ω₁ < p` for a strongly critical `p > Ω₁`. -/
theorem ss_mulE1_lt {p : Ordinal.{0}} (hp : SC p) (h1 : Om 1 < p) : Om 1 * (ggE + 1) < p := by
  have e : Om 1 * (ggE + 1) = ggE + Om 1 := by
    rw [mul_add_one, ← Rj.rj_Om1, ss_Om1_mul_E]
  rw [e]
  exact (lq_SC_indec hp).add_lt (sp_E_lt_SC hp h1) h1

/-- `u_{E₁+1} ∣ p` for a strongly critical `p > Ω₁`. -/
theorem ssDvd_SC {p : Ordinal.{0}} (hp : SC p) (h1 : Om 1 < p) : Le.leOe (ggE + 1) ∣ p :=
  ssDvd_eps (Low.opow_eq_self_of_SC hp) (ss_mulE1_lt hp h1).le

theorem ss_Om1_lt_Omw : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0

/-- **`u_{E₁+1} ∣ α_j`.** -/
theorem ssDvd_alpha (j : ℕ) : Le.leOe (ggE + 1) ∣ bcAlpha S j := by
  have h1 : Le.leOe (ggE + 1) ∣ Om (ω : Ordinal.{0}) := ssDvd_SC (SC_Om omega0_pos.ne') ss_Om1_lt_Omw
  have h2 : Le.leOe (ggE + 1) ∣ Nc.ncPp S := ssDvd_SC (Nc.ncPp_SC S) rb_Om1_lt_Pp
  exact dvd_add (dvd_add h1 h1) (dvd_mul_of_dvd_left h2 _)

/-- **`u_{E₁+1} ∣ α_ω`.** -/
theorem ssDvd_alphaW : Le.leOe (ggE + 1) ∣ bcAlphaW S := by
  have h1 : Le.leOe (ggE + 1) ∣ Om (ω : Ordinal.{0}) := ssDvd_SC (SC_Om omega0_pos.ne') ss_Om1_lt_Omw
  refine dvd_add (dvd_add h1 h1) ?_
  have hE : ω ^ Nc.ncPp S = Nc.ncPp S := Low.opow_eq_self_of_SC (Nc.ncPp_SC S)
  have h2 : Le.leOe (ggE + 1) ∣ Nc.ncPp S := ssDvd_SC (Nc.ncPp_SC S) rb_Om1_lt_Pp
  have hI : Indec (ω ^ (Nc.ncPp S + 1)) :=
    indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  refine rh_dvd_of_indec (ggE + 1) hI ((Ordinal.le_of_dvd (inE_indec hE).ne_zero h2).trans ?_)
  conv_lhs => rw [← hE]
  exact opow_le_opow_right omega0_pos le_self_add

/-- **`u_{E₁+1} ∣ A_η`.** -/
theorem ssDvd_A (η : Ordinal.{0}) : Le.leOe (ggE + 1) ∣ ConjT.Aη S η := by
  have h1 : Le.leOe (ggE + 1) ∣ Om (ω : Ordinal.{0}) := ssDvd_SC (SC_Om omega0_pos.ne') ss_Om1_lt_Omw
  have h2 : Le.leOe (ggE + 1) ∣ ConjT.th S := ssDvd_SC (ConjT.SC_th S) Bt.Om1_lt_th
  exact dvd_add h1 (h2.mul_right η)

/-- **`u_μ ∣ B` gives `u_{B_n μ} ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`, a code `μ` over `c_{n+1}`
with `u_μ ∣ α_{n+1}` and `u_{B_n μ} ∣ α_ω` (the proof of `Rk.rkB_dvd`). -/
theorem ssB_dvd {n : ℕ} {μ : Ordinal.{0}} (hμ : GgCl (Bc.bcC S (n + 1)) μ)
    (hα : Le.leOe μ ∣ bcAlpha S (n + 1)) (hαW : Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S)
    {B : Ordinal.{0}} {r : Term} (hr : bcD S r)
    (hB : B = bcAlpha S (n + 1) + val S r) (h : Le.leOe μ ∣ B) :
    Le.leOe (Bc.bcB S n μ) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rd_dvd_add_left hα] at h
  rw [rd_dvd_add_left hαW]
  exact rk_dvd_sig hμ hr h

/-- `B_n E₁ = E₁` and `B_n(E₁ + 1) = E₁ + 1`, with `E₁`, `E₁ + 1` in the domain of `B_n`. -/
theorem ssB_E1 {n : ℕ} : Mv.MvD S ggE ∧ Bc.bcB S n ggE = ggE ∧ Bc.bcB S n (ggE + 1) = ggE + 1 := by
  obtain ⟨hD, hB⟩ := rkB_E (S := S) (n := n)
  exact ⟨hD, hB, by rw [rkB_succ hD, hB]⟩

/-- `E₁ + 1` is a code over every `Z > 1`. -/
theorem ssE1_cl {Z : Ordinal.{0}} (hZ : 1 < Z) : GgCl Z (ggE + 1) := GgCl.add (spE_cl hZ) (GgCl.small hZ)

/-- **`u_{E₁+1} ∣ B` gives `u_{E₁+1} ∣ B'`** under `B_n`. -/
theorem ssB_dvd1 {n : ℕ} {B : Ordinal.{0}} {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r)
    (h : Le.leOe (ggE + 1) ∣ B) :
    Le.leOe (ggE + 1) ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hc1 : (1 : Ordinal.{0}) < Bc.bcC S (n + 1) := gg_one_lt_of_SC (Lw.lw_L_SC S _)
  have e := (ssB_E1 (S := S) (n := n)).2.2
  have := ssB_dvd (n := n) (ssE1_cl hc1) (ssDvd_alpha (n + 1)) (by rw [e]; exact ssDvd_alphaW) hr hB h
  rwa [e] at this

/-- **`u_{E₁} ∣ B` gives `u_{E₁} ∣ B'`** under `B_n`. -/
theorem ssB_dvd0 {n : ℕ} {B : Ordinal.{0}} {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r)
    (h : Le.leOe ggE ∣ B) :
    Le.leOe ggE ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  have hc1 : (1 : Ordinal.{0}) < Bc.bcC S (n + 1) := gg_one_lt_of_SC (Lw.lw_L_SC S _)
  have e := (ssB_E1 (S := S) (n := n)).2.1
  have := ssB_dvd (n := n) (spE_cl hc1) (rk_dvd_alpha le_rfl (n + 1)) (by rw [e]; exact rk_dvd_alphaW le_rfl)
    hr hB h
  rwa [e] at this

/-! ## The `υ`-points -/

/-- **Every `υ`-point `υ_ξ < c_{n+1}`, `ξ ≠ 0`, is a fixed point of `Φ_{E₁}`**: `υ_ξ = ψ_{Ω₁}(A_η)` with
`u_{E₁+1} ∣ A_η`. -/
theorem ssUps_fix {n : ℕ} {ξ : Ordinal.{0}} (hξ0 : ξ ≠ 0) (hτc : upsilon ξ < Bc.bcC S (n + 1)) :
    rkP ggE (upsilon ξ) = upsilon ξ := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτc.trans hLw
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτc)).2
  have hown := Sf.sfOwn hg0 hAL
  have hA0 : ConjT.Aη S (Cd.cdEta S ξ) ≠ 0 := by
    unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'
  rw [← hpvA]
  exact ssFwd hown (ssDvd_A _) hA0

end Googology.Trans.PoR.InaccPsi.R2.Ss
