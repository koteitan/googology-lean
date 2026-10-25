import Googology.Trans.PoR.InaccPsi.R2.UcCa
import Googology.Trans.PoR.InaccPsi.R2.UcFn
import Googology.Trans.PoR.InaccPsi.R2.TsFn

/-!
# `ψ_{Ω₂}(B + Ω₂^γ·D) ≤ H_γ(c + D)` at every level `γ < ε_{Ω₂+1}`: the hull lemma, CL, UB, INV

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `W^γ = Ω₂^γ`, `E₂ = ucE = ε_{Ω₂+1}`, `H_γ = Uc.ucH γ`, `ucC γ` the largest component,
`UcLt q x` (every component of `x` below `q`, `R2.UcCa`).  This is `R2.TsFn` (levels `β < Ω₂` with `F_β`) for every
level `γ < E₂` with `H_γ`: the digits of `R2.TsFn` become the components, and the closure under the lower levels is
asked only for the levels `j` with `ucC j < q`.

* `uc_W_lt_E` (`Ω₂^x < E₂` for `x < E₂`), `uc_E_SC`, `uc_E_le_SC` (**a strongly critical `v > Ω₂` is `≥ E₂`**);
* `uc_hull` (**every member of `Cl(a, q)` has all its components below `q`**, for `Ω₁ < q < Ω₂` strongly critical,
  `a ≤ E₂`, once the collapses `ψ(e)`, `e < a`, of members with small components are below `q`);
* `UcCL`, `UcUB`, `ucINV` (**INV(γ)**: `ψ(B + W^γ·D) ≤ q`), `ucUB_of`, `ucCL_succ`, `ucCL_lim`, `ucCL_UB`
  (**CL(γ) and UB(γ) at every level `γ < E₂`**), `ucUB` (**`ψ(B + Ω₂^γ·D) ≤ H_γ(c + D)` for `Ω₂^γ ∣ B < E₂`,
  `ψ(B) ≤ H_γ(c)`, `D ≤ Ω₂`**), `ucInv`.

No new axiom.  New definitions: the statement names `UcCL`, `UcUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## `E₂` -/

theorem uc_E_mulPrin : IsPrincipal (· * ·) ucE := by
  have h := isPrincipal_mul_omega0_opow_opow ucE
  rwa [ucE_fix, ucE_fix] at h

theorem uc_E_indec : IsPrincipal (· + ·) ucE := by
  rw [← ucE_fix]; exact isPrincipal_add_omega0_opow _

theorem uc_W_lt_E {x : Ordinal.{0}} (hx : x < ucE) : OmTwo ^ x < ucE := by
  rw [uc_W_eq, ← ucE_fix]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (uc_E_mulPrin (ucE_gt) hx)

/-- **A strongly critical `v > Ω₂` is `≥ E₂`.** -/
theorem uc_E_le_SC {v : Ordinal.{0}} (hv : SC v) (h : OmTwo < v) : ucE ≤ v :=
  ucE_le (Low.opow_eq_self_of_SC hv) h

theorem uc_one_lt_SC {q : Ordinal.{0}} (hq : SC q) : (1 : Ordinal.{0}) < q := by
  have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this

/-! ## The hull lemma -/

/-- **Every member of `Cl(a, q)` has all its components below `q`.** -/
theorem uc_hull {a q : Ordinal.{0}} (hq : SC q) (hq1 : Om 1 < q) (hq2 : q < OmTwo) (ha : a ≤ ucE)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → UcLt q e → S.psi e (Om (1 + 1)) < q) :
    ∀ x, x ∈ S.CSet a q → UcLt q x := by
  have h1q := uc_one_lt_SC hq
  have hO : (OmTwo : Ordinal.{0}) = Om (1 + 1) := uc_Om2_eq
  have hbig : ∀ v, SC v → OmTwo ≤ v → UcLt q v := fun v hv h => by
    rcases eq_or_lt_of_le h with e | h'
    · rw [← e]; exact ucLt_Om2 h1q
    · exact ucLt_out (uc_E_le_SC hv h')
  intro x hx
  induction hx with
  | @small x hxb => exact (ucLt_small (hxb.trans hq2)).2 hxb
  | zero => exact ucLt_zero hq.1
  | inacc n => exact hbig _ (SC_I n) (by rw [hO]; exact (Mx.mxOm2_lt_I n).le)
  | inaccW => exact hbig _ SC_Iw (by rw [hO]; exact Mx.mxOm2_lt_Iw.le)
  | @add x y _ _ ihx ihy =>
    by_cases hE : x + y < ucE
    · exact ucLt_add hq hE ihx ihy
    · exact ucLt_out (not_lt.1 hE)
  | @phi x y _ _ ihx ihy =>
    by_cases hE : veblen x y < ucE
    · rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply] at hE ⊢; exact ucLt_opow hq hE ihy
      have hfix : ω ^ veblen x y = veblen x y := Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)
      rcases lt_trichotomy (veblen x y) OmTwo with hv | hv | hv
      · have hx2 : x < OmTwo := (left_le_veblen x y).trans_lt hv
        have hy2 : y < OmTwo := (right_le_veblen x y).trans_lt hv
        exact (ucLt_small hv).2 (hq.2 x ((ucLt_small hx2).1 ihx) y ((ucLt_small hy2).1 ihy))
      · rw [hv]; exact ucLt_Om2 h1q
      · exact absurd (ucE_le hfix hv) (not_le.2 hE)
    · exact ucLt_out (not_lt.1 hE)
  | @om x _ _ =>
    rcases lt_or_ge (Om x) OmTwo with hv | hv
    · have hx2 : x < 1 + 1 := by rw [hO] at hv; exact Om_lt_Om.1 hv
      have hx1 : Om x ≤ Om 1 := Om_le_Om.2 (Order.lt_add_one_iff.1 hx2)
      exact (ucLt_small hv).2 (hx1.trans_lt hq1)
    · have hx0 : x ≠ 0 := by
        rintro rfl
        rw [Om_zero] at hv
        exact absurd hv (not_le.2 uc_SC_Om2.1)
      exact hbig _ (SC_Om hx0) hv
  | @coll π e hπ _ heC _ ihe =>
    show UcLt q (S.psi e.1 π)
    by_cases hπ1 : π = Om 1
    · subst hπ1
      have h := (psi_lt (S := S) Low.InR_Om_one e.1).trans hq1
      exact (ucLt_small (h.trans hq2)).2 h
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      have h := hcoll e.1 e.2 heC ihe
      exact (ucLt_small (h.trans hq2)).2 h
    · exact hbig _ (SC_psi hπ e.1) (by rw [hO]; exact Ts.ts_Om2_le_psi hπ hπ1 hπ2)

/-! ## The closure and the upper bound at level `γ` -/

/-- **CL(γ)**: `ψ(B + e) < q` for `Ω₂^γ ∣ B < E₂`, `ψ(B) < q`, `e < Ω₂^γ` with all components below `q`, when `q` is
strongly critical and closed under every `H_j`, `j < γ`, with `ucC j < q`. -/
def UcCL (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, OmTwo ^ γ ∣ B → B < ucE → SC q → (∀ j < γ, ucC j < q → ∀ z < q, ucH j z < q) →
    S.psi B (Om (1 + 1)) < q → e < OmTwo ^ γ → UcLt q e → S.psi (B + e) (Om (1 + 1)) < q

/-- **UB(γ)**: `ψ(B + Ω₂^γ·D) ≤ H_γ(c + D)` for `Ω₂^γ ∣ B < E₂`, `ψ(B) ≤ H_γ(c)`, `D ≤ Ω₂`. -/
def UcUB (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, OmTwo ^ γ ∣ B → B < ucE → S.psi B (Om (1 + 1)) ≤ ucH γ c → D ≤ OmTwo →
    S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ≤ ucH γ (c + D)

theorem ucCL_zero : UcCL S 0 := by
  intro B e q _ _ _ _ hBq he _
  rw [opow_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

theorem uc_lt_E_add {γ B D : Ordinal.{0}} (hγ : γ < ucE) (hB : B < ucE) (hD : D ≤ OmTwo) :
    B + OmTwo ^ γ * D < ucE := by
  have h1 : γ + 1 < ucE := uc_E_indec hγ (uc_one_lt_Om2.trans ucE_gt)
  have h2 : OmTwo ^ γ * D ≤ OmTwo ^ (γ + 1) := by rw [uc_W_succ]; exact mul_le_mul_left' hD _
  exact uc_E_indec hB (h2.trans_lt (uc_W_lt_E h1))

/-- **INV(γ)** from CL(γ). -/
theorem ucINV {γ : Ordinal.{0}} (hγ : γ < ucE) (hCL : UcCL S γ) {B D q : Ordinal.{0}} (hB : OmTwo ^ γ ∣ B)
    (hBE : B < ucE) (hq : SC q) (hcl : ∀ j < γ, ucC j < q → ∀ z < q, ucH j z < q)
    (hBq : S.psi B (Om (1 + 1)) < q) (hD : D ≤ OmTwo)
    (hprev : ∀ d, d < D → d < q → S.psi (B + OmTwo ^ γ * d) (Om (1 + 1)) < q) :
    S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ≤ q := by
  have hO : (OmTwo : Ordinal.{0}) = Om (1 + 1) := uc_Om2_eq
  rcases le_or_gt OmTwo q with h1 | h1
  · rw [hO] at h1; exact (Ts.ts_psi_lt _).le.trans h1
  have hq1 : Om 1 < q := (Ts.ts_Om1_lt_psi B).trans hBq
  set u := OmTwo ^ γ with hudef
  have hu0 : u ≠ 0 := (uc_W_pos γ).ne'
  have haE : B + u * D < ucE := uc_lt_E_add hγ hBE hD
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → UcLt q e → S.psi e (Om (1 + 1)) < q := by
    intro e he _ hcomp
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono (InR_Om_succ 1) heB.le).1 hBq
    have heE : e < ucE := he.trans haE
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < OmTwo := hdD.trans_le hD
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
      refine lt_of_le_of_lt ?_ (uc_dig_lt hq.1 heE hcomp γ)
      rw [← hudef, hdiv]
      have := Ts.ts_le_mod_add m (by rw [← hO]; exact hdΩ)
      rwa [← hO] at this
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hB'E : B + u * (e1 / u) < ucE := le_self_add.trans_lt (by rw [hee2]; exact heE)
    have hcomp2 : UcLt q (e1 % u) := by
      have hc := ucLt_concat hq.1 _ _ γ hdvd' hrlt (by rw [hee2]; exact heE)
      rw [hee2] at hc
      exact (hc.1 hcomp).2
    have := hCL _ _ q hdvd' hB'E hq hcl hPd hrlt hcomp2
    rwa [hee2] at this
  have hinv := uc_hull (S := S) hq hq1 h1 haE.le hcoll
  refine psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx1 => ?_
  rw [← hO] at hx1
  exact (ucLt_small hx1).1 (hinv x hx)

/-- **UB(γ)** from CL(γ). -/
theorem ucUB_of {γ : Ordinal.{0}} (hγ : γ < ucE) (hCL : UcCL S γ) : UcUB S γ := by
  intro B c D hB hBE hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hcl : ∀ j < γ, ucC j < ucH γ (c + D) → ∀ z < ucH γ (c + D), ucH j z < ucH γ (c + D) :=
    fun j hj hcj z hz => by
      have hf : ucH j (ucH γ (c + D)) = ucH γ (c + D) := ucG_fix_lower hj ⟨c + D, rfl⟩ hcj
      have := (ucH_lt_iff j).2 hz
      rwa [hf] at this
  have hprev : ∀ d, d < D → d < ucH γ (c + D) →
      S.psi (B + OmTwo ^ γ * d) (Om (1 + 1)) < ucH γ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((ucH_lt_iff γ).2 ((add_lt_add_iff_left c).2 hd))
  exact ucINV hγ hCL hB hBE (ucH_SC γ _) hcl
    (hc.trans_lt ((ucH_lt_iff γ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(γ+1)** from CL(γ) and UB(γ) (`γ + 1 < E₂`). -/
theorem ucCL_succ {γ : Ordinal.{0}} (hγ1 : γ + 1 < ucE) (hCL : UcCL S γ) (hUB : UcUB S γ) :
    UcCL S (γ + 1) := by
  intro B e q hB hBE hq hcl hBq he hcomp
  set u := OmTwo ^ γ with hudef
  have hu0 : u ≠ 0 := (uc_W_pos γ).ne'
  have hqI : IsPrincipal (· + ·) q := hq.isPrincipal
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < OmTwo := by
    rw [uc_W_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hBk : u ∣ B := (opow_dvd_opow _ le_self_add).trans hB
  have hEe : B + e < ucE := uc_E_indec hBE (he.trans (uc_W_lt_E hγ1))
  have heE : e < ucE := le_add_self.trans_lt hEe
  rcases eq_or_ne (e / u) 0 with h0 | h0
  · have hee : e = e % u := by
      conv_lhs => rw [← her, h0, mul_zero, zero_add]
    rw [hee]
    exact hCL B _ q hBk hBE hq (fun j hj => hcl j (hj.trans (lt_add_one γ))) hBq hrlt
      (by rw [← hee]; exact hcomp)
  -- the digit at `γ` and the components of `γ`
  have hγc : UcLt q γ ∧ e / u < q ∧ UcLt q (e % u) := by
    rcases eq_or_ne γ 0 with hγ0 | hγ0
    · have hu1 : u = 1 := by rw [hudef, hγ0, opow_zero]
      have he2 : e < OmTwo := by rw [hγ0, zero_add, opow_one] at he; exact he
      refine ⟨by rw [hγ0]; exact ucLt_zero hq.1, ?_, ?_⟩
      · rw [hu1, Ordinal.div_one]; exact (ucLt_small he2).1 hcomp
      · rw [hu1, Ordinal.mod_one]; exact ucLt_zero hq.1
    · have hcn := ucLt_cnf (q := q) (one_le_iff_ne_zero.2 hγ0) h0 hdΩ hrlt (by rw [her]; exact heE)
      rw [her] at hcn
      exact hcn.1 hcomp
  obtain ⟨hγq, hdq, hrq⟩ := hγc
  have hCγ : ucC γ < q := (ucC_lt_iff hq.1 γ).2 hγq
  have hle := hUB B (S.psi B (Om (1 + 1))) (e / u) hBk hBE (ucH_le_self γ _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om (1 + 1)) < q :=
    hle.trans_lt (hcl γ (lt_add_one γ) hCγ _ (hqI hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hB'E : B + u * (e / u) < ucE := by
    refine lt_of_le_of_lt ?_ hEe
    conv_rhs => rw [← her, ← add_assoc]
    exact le_self_add
  have := hCL _ _ q hdvd' hB'E hq (fun j hj => hcl j (hj.trans (lt_add_one γ))) hP hrlt hrq
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem ucCL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, UcCL S j) : UcCL S l := by
  intro B e q hB hBE hq hcl hBq he hcomp
  obtain ⟨j, hj, hej⟩ := ((isNormal_opow uc_one_lt_Om2).lt_iff_exists_lt hl).1 he
  exact h j hj B e q ((opow_dvd_opow _ hj.le).trans hB) hBE hq (fun i hi => hcl i (hi.trans hj)) hBq hej hcomp

/-- **CL(γ) and UB(γ) at every level `γ < E₂`.** -/
theorem ucCL_UB : ∀ γ : Ordinal.{0}, γ < ucE → UcCL S γ ∧ UcUB S γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  have hCL : UcCL S γ := by
    rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact ucCL_zero
    · rw [Order.succ_eq_add_one] at IH hγ ⊢
      have h := IH j (lt_add_one j) ((lt_add_one j).trans hγ)
      exact ucCL_succ hγ h.1 h.2
    · exact ucCL_lim hl fun j hj => (IH j hj (hj.trans hγ)).1
  exact ⟨hCL, ucUB_of hγ hCL⟩

/-- **`ψ_{Ω₂}(B + Ω₂^γ·D) ≤ H_γ(c + D)`** for `γ < E₂`, `Ω₂^γ ∣ B < E₂`, `ψ_{Ω₂}(B) ≤ H_γ(c)`, `D ≤ Ω₂`. -/
theorem ucUB {γ : Ordinal.{0}} (hγ : γ < ucE) : UcUB S γ := (ucCL_UB γ hγ).2

/-- **`ψ_{Ω₂}(B + Ω₂^γ·D) ≤ q`** (INV(γ)) at every level `γ < E₂`. -/
theorem ucInv {γ B D q : Ordinal.{0}} (hγ : γ < ucE) (hB : OmTwo ^ γ ∣ B) (hBE : B < ucE) (hq : SC q)
    (hcl : ∀ j < γ, ucC j < q → ∀ z < q, ucH j z < q) (hBq : S.psi B (Om (1 + 1)) < q) (hD : D ≤ OmTwo)
    (hprev : ∀ d, d < D → d < q → S.psi (B + OmTwo ^ γ * d) (Om (1 + 1)) < q) :
    S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ≤ q :=
  ucINV hγ (ucCL_UB γ hγ).1 hB hBE hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Uc
