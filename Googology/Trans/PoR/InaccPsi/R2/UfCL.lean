import Googology.Trans.PoR.InaccPsi.R2.UfDL
import Googology.Trans.PoR.InaccPsi.R2.UfFwd
import Googology.Trans.PoR.InaccPsi.R2.TzCL

/-!
# CL, UB, INV, CONV and EQ at every level `μ ≤ B₂` of the hierarchy `Uc.ucP`

`ψ = S.psi`, `Φ_μ = Uc.ucP μ` (data `ucDatL μ = Uc.ucDat (Ω₁ + μ)`), `u_μ = Ω₁^μ = Le.leOe μ`, `B₂ = Uc.ucB`,
`RiDg q e` (all `Ω₁`-digits of `e` below `q`), `UfLev q e` (all levels `j < B₂` of `e` with `ucDatL j < q`),
`Tw.TwArgs S a μ` (the own arguments of the atoms of `μ` are below `a`).  An argument `B` is *own* when
`B ∈ Cl(B, ψ_{Ω₁}(B))`.  The proofs of `R2.TzCL` (levels `≤ X`) at the levels `≤ B₂`, with the codes `UcCl` and the
direct hull lemma `Uf.uf_diglev`:

* `uf_clo_val`, `UfClo`, `UfCL`, `UfUB`, `uf_CL_UB` (**CL(μ) and UB(μ) at every level `μ ≤ B₂`**:
  `ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)` for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`), `uf_UB`, `uf_inv` (INV(μ)),
  `uf_validP`;
* `uf_U_mem`, `uf_U_mul_mem` (`u_μ·D ∈ Cl(a, b)` under `TwArgs S a μ`);
* `uf_conv` (**CONV(μ): `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`**, `μ < B₂`),
  `uf_conv_iff` (with `TwArgs S B μ`), `uf_eqP` (**EQ(μ): `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)` and
  `D < ψ_{Ω₁}(B + u_μ·D)`** when `d < Φ_μ(c+d)` for every `d ≤ D`, `B` own, `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`,
  `ucDatL μ < ψ_{Ω₁}(B)`, `TwArgs S B μ`, `μ < B₂`), `uf_dvd_eps`.

No new axiom.  New definitions: the statement names `UfClo`, `UfCL`, `UfUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tw

/-- The values of `Φ_μ` are closed under the lower levels. -/
theorem uf_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, ucDatL j < ucP μ o → ∀ z < ucP μ o, ucP j z < ucP μ o := fun j hj hd z hz => by
  have h := (ucP_lt_iff j).2 hz
  rwa [ucP_fix_lower hj ⟨o, rfl⟩ hd] at h

variable {S : InaccSeq.{0}}

/-- `q` is closed under every `Φ_j`, `j < μ`, with `ucDatL j < q`. -/
def UfClo (μ q : Ordinal.{0}) : Prop := ∀ j < μ, ucDatL j < q → ∀ z < q, ucP j z < q

/-- **CL(μ)** for `tfP`. -/
def UfCL (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Le.leOe μ ∣ B → SC q → UfClo μ q → S.psi B (Om 1) < q → e < Le.leOe μ →
    RiDg q e → UfLev q e → S.psi (B + e) (Om 1) < q

/-- **UB(μ)** for `tfP`: `ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)` for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`. -/
def UfUB (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Le.leOe μ ∣ B → S.psi B (Om 1) ≤ ucP μ c → D ≤ Om 1 →
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ ucP μ (c + D)

theorem uf_CL_zero : UfCL S 0 := by
  intro B e q _ _ _ hBq he _ _
  rw [Le.leOe_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- The digits and levels of `e % u_μ` from those of `e`, when `u_{j+1} ∣ e - e % u_μ` below `μ`. -/
theorem uf_rem_dl {μ q a t : Ordinal.{0}} (hq : SC q) (hdvd : Le.leOe μ ∣ a) (hdg : RiDg q (a + t))
    (hlv : UfLev q (a + t)) (ht : t < Le.leOe μ) : RiDg q t ∧ UfLev q t := by
  have hdig : ∀ j : Ordinal.{0}, j < μ → (a + t) / Le.leOe j % Om 1 = t / Le.leOe j % Om 1 := fun j hj =>
    rhk_dig_add_dvd j ((rhU_dvd_succ hj).trans hdvd)
  have hzero : ∀ j : Ordinal.{0}, μ ≤ j → t / Le.leOe j % Om 1 = 0 := fun j hj => by
    rw [Ordinal.div_eq_zero_of_lt (ht.trans_le (rhU_le hj)), Ordinal.zero_mod]
  refine ⟨fun j => ?_, fun j hj h => ?_⟩
  · rcases lt_or_ge j μ with hjk | hjk
    · rw [← hdig j hjk]; exact hdg j
    · rw [hzero j hjk]; exact hq.1
  · rcases lt_or_ge j μ with hjk | hjk
    · exact hlv j hj (by rw [hdig j hjk]; exact h)
    · exact absurd (hzero j hjk) h

/-- **INV(μ)** from CL(μ). -/
theorem uf_INV {μ : Ordinal.{0}} (hCL : UfCL S μ) {B D q : Ordinal.{0}} (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : UfClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → RiDg q e → UfLev q e →
      S.psi e (Om 1) < q := by
    intro e he _ hdg hlv
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 hBq
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < Om 1 := hdD.trans_le hD
    have her : u * (e1 / u) + e1 % u = e1 := Ordinal.div_add_mod e1 u
    have hrlt : e1 % u < u := Ordinal.mod_lt _ hu0
    obtain ⟨m, hm⟩ := hB
    have he_eq : e = u * (m + e1 / u) + e1 % u := by
      rw [← hee]
      conv_lhs => rw [← her, hm]
      rw [← add_assoc, ← mul_add]
    have hdiv : e / u = m + e1 / u := by
      rw [he_eq, Ordinal.mul_add_div _ hu0, Ordinal.div_eq_zero_of_lt hrlt, add_zero]
    have hdq : e1 / u < q := by
      refine lt_of_le_of_lt ?_ (hdg μ)
      rw [← hudef, hdiv]; exact rd_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    rw [← hee2] at hdg hlv
    obtain ⟨hdg2, hlv2⟩ := uf_rem_dl hq hdvd' hdg hlv hrlt
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdg2 hlv2
    rwa [hee2] at this
  have hinv := uf_diglev (S := S) hq h1.le hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := (hinv x hx).1 0
  rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(μ)** from CL(μ). -/
theorem uf_UB_of {μ : Ordinal.{0}} (hCL : UfCL S μ) : UfUB S μ := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hprev : ∀ d, d < D → d < ucP μ (c + D) →
      S.psi (B + Le.leOe μ * d) (Om 1) < ucP μ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((ucP_lt_iff μ).2 ((add_lt_add_iff_left c).2 hd))
  exact uf_INV hCL hB (ucP_SC μ _) (uf_clo_val μ _)
    (hc.trans_lt ((ucP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(μ+1)** from CL(μ) and UB(μ), `μ < X`. -/
theorem uf_CL_succ {μ : Ordinal.{0}} (hμ : μ < ucB) (hCL : UfCL S μ) (hUB : UfUB S μ) :
    UfCL S (μ + 1) := by
  intro B e q hB hq hcl hBq he hdg hlv
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hqI : Indec q := lq_SC_indec hq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om 1 := by
    rw [Le.leOe_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hdig : e / u % Om 1 = e / u := Ordinal.mod_eq_of_lt hdΩ
  have hdq : e / u < q := by have := hdg μ; rwa [← hudef, hdig] at this
  have hBk : u ∣ B := (rhU_dvd le_self_add).trans hB
  have hP : S.psi (B + u * (e / u)) (Om 1) < q := by
    rcases eq_or_ne (e / u) 0 with h0 | h0
    · rw [h0, mul_zero, add_zero]; exact hBq
    have hdat : ucDatL μ < q := hlv μ hμ (by rw [← hudef, hdig]; exact h0)
    have hle := hUB B (S.psi B (Om 1)) (e / u) hBk (ucP_le_self μ _) hdΩ.le
    exact hle.trans_lt (hcl μ (lt_add_one μ) hdat _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdg' : RiDg q (u * (e / u) + e % u) := by rw [her]; exact hdg
  have hlv' : UfLev q (u * (e / u) + e % u) := by rw [her]; exact hlv
  obtain ⟨hdg2, hlv2⟩ := uf_rem_dl hq (dvd_mul_right u (e / u)) hdg' hlv' hrlt
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (lt_add_one μ))) hP hrlt hdg2 hlv2
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem uf_CL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, UfCL S j) : UfCL S l := by
  intro B e q hB hq hcl hBq he hdg hlv
  obtain ⟨j, hj, hej⟩ := rhU_lt_lim hl he
  exact h j hj B e q ((rhU_dvd hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hdg hlv

/-- **CL(μ) and UB(μ) at every level `μ ≤ X` of `tfP`.** -/
theorem uf_CL_UB (μ : Ordinal.{0}) : μ ≤ ucB → UfCL S μ ∧ UfUB S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have hCL : UfCL S μ := by
    rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact uf_CL_zero
    · rw [Order.succ_eq_add_one] at IH hμ ⊢
      have hj : j < ucB := (lt_add_one j).trans_le hμ
      have h := IH j (lt_add_one j) hj.le
      exact uf_CL_succ hj h.1 h.2
    · exact uf_CL_lim hl fun j hj => (IH j hj (hj.le.trans hμ)).1
  exact ⟨hCL, uf_UB_of hCL⟩

/-- **`ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)`** for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`, at every level
`μ ≤ X` of `tfP`. -/
theorem uf_UB {μ : Ordinal.{0}} (hμ : μ ≤ ucB) : UfUB S μ := (uf_CL_UB μ hμ).2

/-- **INV(μ)** at every level `μ ≤ X` of `tfP`. -/
theorem uf_inv {μ B D q : Ordinal.{0}} (hμ : μ ≤ ucB) (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : UfClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q :=
  uf_INV (uf_CL_UB μ hμ).1 hB hq hcl hBq hD hprev



/-- `u_μ ∈ Cl(a, b)` for a code `μ < X` over a countable strongly critical `b` whose atoms have their own arguments
below `a`. -/
theorem uf_U_mem {μ a b : Ordinal.{0}} (hb : SC b) (hb1 : b ≤ Om 1) (hμ : μ < ucB) (h : ucDatL μ < b)
    (hargs : TwArgs S a μ) : Le.leOe μ ∈ S.CSet a b := by
  have hb1' : b ≤ Om1 := by rw [uf_Om1]; exact hb1
  exact leOe_mem (uf_mem_CSet hb hb1' le_rfl μ (uc_code_lvlL hb hb1' hμ h) hargs).1

/-- `u_μ·D ∈ Cl(a, b)` for a code `μ < X` over a countable strongly critical `b` whose atoms have their own
arguments below `a`, `D < b`. -/
theorem uf_U_mul_mem {μ a b D : Ordinal.{0}} (hb : SC b) (hb1 : b ≤ Om 1) (hμ : μ < ucB) (h : ucDatL μ < b)
    (hD : D < b) (hargs : TwArgs S a μ) : Le.leOe μ * D ∈ S.CSet a b := by
  have hb1' : b ≤ Om1 := by rw [uf_Om1]; exact hb1
  exact leMulOe_mem (uf_mem_CSet hb hb1' le_rfl μ (uc_code_lvlL hb hb1' hμ h) hargs).1 (CSet.of_lt hD)

/-- **CONV(μ)**: `u_{μ+1} ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Φ_μ`, `μ < X`. -/
theorem uf_conv {μ : Ordinal.{0}} (hμ : μ < ucB) {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ucP μ (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe (μ + 1) ∣ B := by
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  have hcoll : ∀ e, e < B → e ∈ S.CSet B p → RiDg p e → UfLev p e → S.psi e (Om 1) < p :=
    fun e he heC _ _ => lt_psi_of_mem Low.InR_Om_one
      (CSet.psi_mem he Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) heC) (psi_lt Low.InR_Om_one _)
  have hdl := uf_diglev (S := S) hpSC (psi_lt Low.InR_Om_one B).le hcoll B hown
  refine ri_dvd_of_dig (μ + 1) fun j hj => ?_
  have hjμ : j ≤ μ := Order.lt_add_one_iff.1 hj
  have hjX : j < ucB := hjμ.trans_lt hμ
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  by_contra hd0
  have hdj : ucDatL j < p := hdl.2.1 j hjX hd0
  have hfj : ucP j p = p := ucP_fix_mono hjμ hfix hdj
  have huj : Le.leOe j ∣ B := ri_dvd_of_dig j fun i hi =>
    IHj i hi (hi.trans hj) (hi.le.trans hjμ) (hi.trans hjX)
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
  have hle := uf_UB (S := S) hjX.le B0 (S.psi B0 (Om 1)) D0
    (by rw [hB0]; exact (rhU_dvd le_self_add).trans (dvd_mul_right _ _)) (ucP_le_self _ _) hD0lt.le
  rw [hBe] at hle
  have hlt : S.psi B0 (Om 1) + D0 < p := (lq_SC_indec hpSC).add_lt hB0p hD0p
  have h2 : ucP j (S.psi B0 (Om 1) + D0) < p := by
    conv_rhs => rw [← hfj]
    exact (ucP_lt_iff j).2 hlt
  exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-- **FWD and CONV together**: for an own `B ≠ 0` with `ucDatL μ < ψ_{Ω₁}(B)`, `μ < X`: `ψ_{Ω₁}(B)` is a
fixed point of `Φ_μ` iff `u_{μ+1} ∣ B`. -/
theorem uf_conv_iff {μ B : Ordinal.{0}} (hμ : μ < ucB) (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB0 : B ≠ 0)
    (hd : ucDatL μ < S.psi B (Om 1)) (hargs : TwArgs S B μ) :
    ucP μ (S.psi B (Om 1)) = S.psi B (Om 1) ↔ Le.leOe (μ + 1) ∣ B :=
  ⟨uf_conv hμ hown, fun h => ufFwdAll μ hμ B hown h hB0 hd hargs⟩

/-- **EQ(μ)**: `ψ_{Ω₁}(B + u_μ·D) = Φ_μ(c + D)`, and `D < ψ_{Ω₁}(B + u_μ·D)`, when `d < Φ_μ(c+d)` for every `d ≤ D`,
for an own `B` with `u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)` and `ucDatL μ < ψ_{Ω₁}(B)` (`μ < X`). -/
theorem uf_eqP {μ : Ordinal.{0}} (hμ : μ < ucB)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hB : Le.leOe μ ∣ B)
    (hc : ucP μ c = S.psi B (Om 1)) (hdB : ucDatL μ < S.psi B (Om 1)) (hargs : TwArgs S B μ) :
    ∀ D, D < Om 1 → (∀ d, d ≤ D → d < ucP μ (c + d)) →
      D < S.psi (B + Le.leOe μ * D) (Om 1) ∧ S.psi (B + Le.leOe μ * D) (Om 1) = ucP μ (c + D) := by
  set u := Le.leOe μ with hudef
  have hupos : 0 < u := rhU_pos μ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om 1) = ucP μ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om 1) = ucP μ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om 1) with hv
    have hvSC : SC v := SC_psi Low.InR_Om_one _
    have hBv : S.psi B (Om 1) < v :=
      rh_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hdv : ucDatL μ < v := hdB.trans hBv
    have hlt : ∀ d, d < D → ucP μ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om 1) ≤ v :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv' : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * D)).2 hown)
          (uf_U_mul_mem (SC_psi Low.InR_Om_one _) (psi_lt Low.InR_Om_one _).le hμ hdv
            hdv' (hargs.mono le_self_add le_rfl))
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem Low.InR_Om_one
        ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact uf_UB hμ.le B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (uf_U_mul_mem (SC_psi Low.InR_Om_one _) (psi_lt Low.InR_Om_one _).le hμ hdv
              hDv (hargs.mono le_self_add le_rfl))
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < μ, ucDatL j < v → ucP j v = v := fun j hj hdj =>
          ufFwdAll j (hj.trans hμ) _ hown1 ((rhU_dvd_succ hj).trans (dvd_add hB (dvd_mul_right _ _))) hne hdj
            (hargs.mono le_self_add hj.le)
        obtain ⟨e, he⟩ := ucP_range hvSC hdv hfix
        rw [← he]
        refine (ucP_le_iff μ).2 (not_lt.1 fun hlt' => ?_)
        have hle : e ≤ c + d0 := by
          rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
        have := ((ucP_le_iff μ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
        rw [he] at this
        exact lt_irrefl _ this
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((ucP_normal μ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : ucP μ e < v := ((ucP_lt_iff μ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Φ_μ(c+d)` for every `d ≤ D`** (`u_μ ∣ B`, `Φ_μ(c) = ψ_{Ω₁}(B)`, `μ ≤ X`). -/
theorem uf_validP {μ B c D : Ordinal.{0}} (hμ : μ ≤ ucB) (hB : Le.leOe μ ∣ B)
    (hc : ucP μ c = S.psi B (Om 1))
    (hv : D < S.psi (B + Le.leOe μ * D) (Om 1)) : ∀ d, d ≤ D → d < ucP μ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (ucP_SC _ _).1)
  have hDΩ : D ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have hprev : ∀ d'', d'' < D → d'' < ucP μ (c + d) →
      S.psi (B + Le.leOe μ * d'') (Om 1) < ucP μ (c + d) := fun d'' hd'' hq =>
    (uf_UB hμ B c d'' hB hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((ucP_lt_iff μ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := uf_inv (S := S) hμ hB (ucP_SC μ (c + d)) (uf_clo_val μ _)
    (by rw [← hc]; exact (ucP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- An `ε`-number `p ≥ X` is a multiple of every `u_μ`, `μ ≤ X`. -/
theorem uf_dvd_eps {μ p : Ordinal.{0}} (hμ : μ ≤ ucB) (hp : ω ^ p = p) (hG : ucB ≤ p) :
    Le.leOe μ ∣ p := by
  have hI : Indec p := inE_indec hp
  have hk : Om 1 * μ ≤ p := by
    have hGG : Om 1 * ucB = ucB := by
      conv_lhs => rw [← Bt.Om1_opow, ← uf_B_inE]
      rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [uf_B_inE]; exact uf_Om1_lt_B) uf_B_inE.le,
        uf_B_inE]
    calc Om 1 * μ ≤ Om 1 * ucB := mul_le_mul_right hμ _
      _ = ucB := hGG
      _ ≤ p := hG
  refine rh_dvd_of_indec μ hI ?_
  unfold Le.leOe
  rw [← hp]
  exact opow_le_opow_right omega0_pos hk

end Googology.Trans.PoR.InaccPsi.R2.Uf
