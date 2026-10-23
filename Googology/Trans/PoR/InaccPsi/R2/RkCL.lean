import Googology.Trans.PoR.InaccPsi.R2.RkDig

/-!
# `ψ_{Ω₁}(B + Ω₁^μ·D) ≤ Φ_μ(c + D)` at every level `μ ≤ ε_{Ω₁+1}`

`ψ = S.psi`, `u_μ = Ω₁^μ = Le.leOe μ`, `Φ_μ = Rk.rkP μ`, `rkDat μ = rjDat (Ω₁ + μ)`, `RiDg q e` (all digits of `e`
below `q`), `RkLev q e` (every level `j < ε_{Ω₁+1}` of `e` has `rkDat j < q`).  The proofs of `R2.RiCL` with the
generic levels of `R2.RkFn` and the levels of `R2.RkDig`.

* `RkClo μ q` (`q` closed under every `Φ_j`, `j < μ`, with `rkDat j < q`);
* `rk_CL_UB` (by induction on `μ ≤ ε_{Ω₁+1}`): **CL(μ)** (`ψ_{Ω₁}(B' + e) < q` for `u_μ ∣ B'`, `ψ_{Ω₁}(B') < q`,
  `e < u_μ` with digits and levels below `q`, `q` strongly critical with `RkClo μ q`) and **UB(μ)**
  (**`ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)`** for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`); `rk_inv` (INV(μ)).

No new axiom.  New definitions: the statement names `RkClo`, `RkCL`, `RkUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- `q` is closed under every `Φ_j`, `j < μ`, with `rkDat j < q`. -/
def RkClo (μ q : Ordinal.{0}) : Prop := ∀ j < μ, rkDat j < q → ∀ z < q, rkP j z < q

/-- **CL(μ)**. -/
def RkCL (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Le.leOe μ ∣ B → SC q → RkClo μ q → S.psi B (Om 1) < q → e < Le.leOe μ →
    RiDg q e → RkLev q e → S.psi (B + e) (Om 1) < q

/-- **UB(μ)**: `ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)` for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`. -/
def RkUB (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Le.leOe μ ∣ B → S.psi B (Om 1) ≤ rkP μ c → D ≤ Om 1 →
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ rkP μ (c + D)

theorem rk_CL_zero : RkCL S 0 := by
  intro B e q _ _ _ hBq he _ _
  rw [Le.leOe_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem rk_clo_val2 (μ o : Ordinal.{0}) : RkClo μ (rkP μ o) := fun j hj hd z hz => by
  have h := (rkP_lt_iff j).2 hz
  rwa [rkP_fix_lower hj ⟨o, rfl⟩ hd] at h

/-- The digits and levels of `e % u_μ` from those of `e`, when `u_{j+1} ∣ e - e % u_μ` below `μ`. -/
theorem rk_rem_dl {μ q a t : Ordinal.{0}} (hq : SC q) (hdvd : Le.leOe μ ∣ a) (hdg : RiDg q (a + t))
    (hlv : RkLev q (a + t)) (ht : t < Le.leOe μ) : RiDg q t ∧ RkLev q t := by
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
theorem rk_INV {μ : Ordinal.{0}} (hCL : RkCL S μ) {B D q : Ordinal.{0}} (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : RkClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → RiDg q e → RkLev q e →
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
    obtain ⟨hdg2, hlv2⟩ := rk_rem_dl hq hdvd' hdg hlv hrlt
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdg2 hlv2
    rwa [hee2] at this
  have hinv := rk_diglev (S := S) hq hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := (hinv x hx).1 0
  rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(μ)** from CL(μ). -/
theorem rk_UB_of {μ : Ordinal.{0}} (hCL : RkCL S μ) : RkUB S μ := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hprev : ∀ d, d < D → d < rkP μ (c + D) →
      S.psi (B + Le.leOe μ * d) (Om 1) < rkP μ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((rkP_lt_iff μ).2 ((add_lt_add_iff_left c).2 hd))
  exact rk_INV hCL hB (rkP_SC μ _) (rk_clo_val2 μ _)
    (hc.trans_lt ((rkP_lt_iff μ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(μ+1)** from CL(μ) and UB(μ), `μ < Ω₁·Ω₁`. -/
theorem rk_CL_succ {μ : Ordinal.{0}} (hμ : μ < ggE) (hCL : RkCL S μ) (hUB : RkUB S μ) :
    RkCL S (μ + 1) := by
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
    have hdat : rkDat μ < q := hlv μ hμ (by rw [← hudef, hdig]; exact h0)
    have hle := hUB B (S.psi B (Om 1)) (e / u) hBk (rkP_le_self μ _) hdΩ.le
    exact hle.trans_lt (hcl μ (lt_add_one μ) hdat _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdg' : RiDg q (u * (e / u) + e % u) := by rw [her]; exact hdg
  have hlv' : RkLev q (u * (e / u) + e % u) := by rw [her]; exact hlv
  obtain ⟨hdg2, hlv2⟩ := rk_rem_dl hq (dvd_mul_right u (e / u)) hdg' hlv' hrlt
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (lt_add_one μ))) hP hrlt hdg2 hlv2
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem rk_CL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, RkCL S j) : RkCL S l := by
  intro B e q hB hq hcl hBq he hdg hlv
  obtain ⟨j, hj, hej⟩ := rhU_lt_lim hl he
  exact h j hj B e q ((rhU_dvd hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hdg hlv

/-- **CL(μ) and UB(μ) at every level `μ ≤ Ω₁·Ω₁`.** -/
theorem rk_CL_UB (μ : Ordinal.{0}) : μ ≤ ggE → RkCL S μ ∧ RkUB S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have hCL : RkCL S μ := by
    rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact rk_CL_zero
    · rw [Order.succ_eq_add_one] at IH hμ ⊢
      have hj : j < ggE := (lt_add_one j).trans_le hμ
      have h := IH j (lt_add_one j) hj.le
      exact rk_CL_succ hj h.1 h.2
    · exact rk_CL_lim hl fun j hj => (IH j hj (hj.le.trans hμ)).1
  exact ⟨hCL, rk_UB_of hCL⟩

/-- **`ψ_{Ω₁}(B + u_μ·D) ≤ Φ_μ(c + D)`** for `u_μ ∣ B`, `ψ_{Ω₁}(B) ≤ Φ_μ(c)`, `D ≤ Ω₁`, at every level `μ ≤ Ω₁·Ω₁`. -/
theorem rk_UB {μ : Ordinal.{0}} (hμ : μ ≤ ggE) : RkUB S μ := (rk_CL_UB μ hμ).2

/-- **INV(μ)** at every level `μ ≤ Ω₁·Ω₁`. -/
theorem rk_inv {μ B D q : Ordinal.{0}} (hμ : μ ≤ ggE) (hB : Le.leOe μ ∣ B)
    (hq : SC q) (hcl : RkClo μ q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe μ * d) (Om 1) < q) :
    S.psi (B + Le.leOe μ * D) (Om 1) ≤ q :=
  rk_INV (rk_CL_UB μ hμ).1 hB hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Rk
