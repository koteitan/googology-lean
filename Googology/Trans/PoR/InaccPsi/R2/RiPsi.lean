import Googology.Trans.PoR.InaccPsi.R2.RhPsi
import Googology.Trans.PoR.InaccPsi.R2.RiCL

/-!
# `ψ_{Ω₁}(B + Ω₁^μ·D) = Φ_μ(c + D)` and the fixed points of `Φ_μ` among the collapses, at every level `μ < Ω₁·Ω₁`

`ψ = S.psi`, `Φ_μ = Ri.riP μ`, `u_μ = Ω₁^μ = Le.leOe μ`, `riDat μ = max(μ/Ω₁, μ mod Ω₁)`.  An argument `B` is *own*
when `B ∈ Cl(B, ψ_{Ω₁}(B))`.

* `ri_dvd_of_dig` (**`u_l ∣ B` once every digit of `B` below `l` vanishes**);
* `ri_fwd` (by induction on `μ`): **`ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B`
  and `riDat μ < ψ_{Ω₁}(B)`** (FWD; as `Rh.rh_fwd`, with the base point `Γ(riDat μ + z + 1)`);
* `ri_conv` (**`u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`**, `μ < Ω₁·Ω₁`: the digits
  of `B` at the levels `j ≤ μ` with `riDat j ≥ ψ_{Ω₁}(B)` vanish by `Ri.ri_diglev`, the others by UB(j));
* `ri_eq` (**`ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` and `D` is valid** when `d < Φ_μ(c+d)` for every `d ≤ D`, `B` own, `u_μ ∣
  B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `riDat μ < ψ_{Ω₁}(B)`), `ri_valid`;
* `ri_dvd_eps`, `ri_dvd_A` (**`u_μ ∣ A_η`** for `μ ≤ Ω₁·Ω₁`), `ri_fix_A` (**`ψ_{Ω₁}(A_η)` is a fixed point of every
  `Φ_μ`, `μ < Ω₁·Ω₁`, `riDat μ < ψ_{Ω₁}(A_η)`**).

No new axiom.  New definition: the statement name `RiFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-- **`u_l ∣ B` once every digit of `B` below `l` vanishes.** -/
theorem ri_dvd_of_dig {B : Ordinal.{0}} :
    ∀ l : Ordinal.{0}, (∀ j < l, B / Le.leOe j % Om 1 = 0) → Le.leOe l ∣ B := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro h
  rcases zero_or_succ_or_isSuccLimit l with h0 | ⟨j, rfl⟩ | hl
  · rw [h0, Le.leOe_zero]; exact one_dvd B
  · rw [Order.succ_eq_add_one] at h IH ⊢
    obtain ⟨m, hm⟩ := IH j (lt_add_one j) fun i hi => h i (hi.trans (lt_add_one j))
    have hd := h j (lt_add_one j)
    rw [hm, Ordinal.mul_div_cancel _ (rhU_ne j)] at hd
    have hm' : m = Om 1 * (m / Om 1) := by
      conv_lhs => rw [← Ordinal.div_add_mod m (Om 1), hd, add_zero]
    refine ⟨m / Om 1, ?_⟩
    rw [hm, Le.leOe_succ, mul_assoc, ← hm']
  · exact rhU_dvd_lim hl fun j hj => IH j hj fun i hi => h i (hi.trans hj)

/-- `u_{j+1} ∣ B` kills the digit of `B` at `j`. -/
theorem ri_dig_zero_of_dvd {j B : Ordinal.{0}} (h : Le.leOe (j + 1) ∣ B) : B / Le.leOe j % Om 1 = 0 := by
  obtain ⟨m, rfl⟩ := h
  rw [Le.leOe_succ, mul_assoc, Ordinal.mul_div_cancel _ (rhU_ne j), Ordinal.mul_mod]

/-! ## The fixed-point lemmas -/

/-- **FWD(μ)**: `ψ_{Ω₁}(B)` is a fixed point of `Φ_μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B` and
`riDat μ < ψ_{Ω₁}(B)`. -/
def RiFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 → riDat μ < S.psi B (Om 1) →
    riP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **At every level `μ < Ω₁·Ω₁`: FWD(μ).** -/
theorem ri_fwd (μ : Ordinal.{0}) : μ < Om 1 * Om 1 → RiFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [riP_lt (rb_Om1_indec.pos)]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : riDat 0 = 0 := by unfold riDat; rw [Ordinal.zero_div, Ordinal.zero_mod, max_self]
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
    rwa [riP_lt rb_Om1_indec.pos, rhF_zero] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, riP μ z < x := by
    intro z hz
    set a := riDat μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (riDat μ + z) e.symm
    have hdp : riDat μ < p := (le_self_add.trans_lt (lt_add_one (riDat μ + z))).trans hap
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
    have hde : riDat μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem) (riU_mem hde)
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, riP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (riU_mul_mem (hde.trans_le hle) (hd.trans_le hle))
      refine ⟨hownd, riP_range (SC_psi Low.InR_Om_one _) (psi_lt Low.InR_Om_one _) (hde.trans_le hle)
        fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, riP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : riP μ w' < riP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((riP_lt_iff μ).1 h2) (not_lt.2 h1)
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
    calc riP μ z < riP μ w := (riP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((riP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (riP_le_self μ x)

/-- **CONV(μ)**: `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`, `μ < Ω₁·Ω₁`. -/
theorem ri_conv {μ : Ordinal.{0}} (hμ : μ < Om 1 * Om 1) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : riP μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → RiLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := ri_diglev (S := S) hpSC hcoll B hown
  refine ri_dvd_of_dig (μ + 1) fun j hj => ?_
  have hjμ : j ≤ μ := Order.lt_add_one_iff.1 hj
  have hjΩ : j < Om 1 * Om 1 := hjμ.trans_lt hμ
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : riDat j < p := hdl.2 j hjΩ hd0
  have hfj : riP j p = p := riP_fix_mono hjμ hfix hdj
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
  have hle := ri_UB (S := S) hjΩ.le B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (riP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : riP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (riP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## The bridge at level `μ` -/

/-- **`ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)`, and `D < ψ_{Ω₁}(B + u_μ·D)`**, when `d < Φ_μ(c+d)` for every `d ≤ D`, for an
own `B` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)` and `riDat μ < ψ_{Ω₁}(B)` (`μ < Ω₁·Ω₁`). -/
theorem ri_eq {μ : Ordinal.{0}} (hμ : μ < Om 1 * Om 1)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe μ ∣ B)
    (hc : riP μ c = S.psi B (Om 1)) (hdB : riDat μ < S.psi B (Om 1)) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < riP μ (c + d)) →
      D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = riP μ (c + D) := by
  set u := Le.leOe μ with hudef
  have hupos : 0 < u := rhU_pos μ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = riP μ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = riP μ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : riDat μ < v := hdB.trans hBv
    have hlt : ∀ d, d < D → riP μ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (riU_mul_mem hdv hdv')
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact ri_UB hμ.le B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (riU_mul_mem hdv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < μ, riDat j < v → riP j v = v := fun j hj hdj =>
          ri_fwd j (hj.trans hμ) _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
        obtain ⟨e, he⟩ := riP_range hvSC (psi_lt Low.InR_Om_one _) hdv hfix
        rw [← he]
        refine (riP_le_iff μ).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((riP_le_iff μ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((riP_normal μ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : riP μ e < v := ((riP_lt_iff μ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Φ_μ(c+d)` for every `d ≤ D`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `μ ≤ Ω₁·Ω₁`). -/
theorem ri_valid {μ B c D : Ordinal.{0}} (hμ : μ ≤ Om 1 * Om 1) (hB : Le.leOe μ ∣ B)
    (hc : riP μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < riP μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (riP_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < riP μ (c + d) →
      S.psi (B + Le.leOe μ * d'') (Om 1) < riP μ (c + d) := fun d'' hd'' hq =>
    (ri_UB hμ B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((riP_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := ri_inv (S := S) hμ hB (riP_SC μ (c + d)) (ri_clo_val μ _)
    (by rw [← hc]; exact (riP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-! ## The points `ψ_{Ω₁}(A_η)` -/

/-- An `ε`-number above `Ω₁` is a multiple of every `u_μ`, `μ ≤ Ω₁·Ω₁`. -/
theorem ri_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ Om 1 * Om 1) (hp : ω ^ p = p) (h : Om 1 < p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have h3 : Om 1 + Om 1 + Om 1 < p := hI.add_lt (hI.add_lt h h) h
  have hk : Om 1 * μ < p := by
    calc Om 1 * μ ≤ Om 1 * (Om 1 * Om 1) := mul_le_mul_right hμ _
      _ = ω ^ (Om 1 + Om 1 + Om 1) := by rw [opow_add, opow_add, Bt.Om1_opow, mul_assoc]
      _ < ω ^ p := (opow_lt_opow_iff_right one_lt_omega0).2 h3
      _ = p := hp
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk.le

/-- **`u_μ ∣ A_η`** for `μ ≤ Ω₁·Ω₁`. -/
theorem ri_dvd_A {μ : Ordinal.{0}} (hμ : μ ≤ Om 1 * Om 1) (η : Ordinal.{0}) : Le.leOe μ ∣ ConjT.Aη S η := by
  have h1 : Le.leOe μ ∣ Om (ω : Ordinal.{0}) :=
    ri_dvd_eps hμ (Low.opow_eq_self_of_SC (SC_Om omega0_pos.ne')) (Om_lt_Om.2 one_lt_omega0)
  have h2 : Le.leOe μ ∣ ConjT.th S :=
    ri_dvd_eps hμ (Low.opow_eq_self_of_SC (ConjT.SC_th S)) Bt.Om1_lt_th
  exact dvd_add h1 (h2.mul_right η)

/-- **The `υ`-point `ψ_{Ω₁}(A_η)` is a fixed point of every `Φ_μ`, `μ < Ω₁·Ω₁`, `riDat μ < ψ_{Ω₁}(A_η)`.** -/
theorem ri_fix_A {μ η : Ordinal.{0}} (hμ : μ < Om 1 * Om 1)
    (hown : ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)))
    (hd : riDat μ < S.psi (ConjT.Aη S η) (Om 1)) :
    riP μ (S.psi (ConjT.Aη S η) (Om 1)) = S.psi (ConjT.Aη S η) (Om 1) := by
  refine ri_fwd μ hμ _ hown (ri_dvd_A (Order.add_one_le_of_lt hμ) η) ?_ hd
  unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'

end Googology.Trans.PoR.InaccPsi.R2.Ri
