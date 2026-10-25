import Googology.Trans.PoR.InaccPsi.R2.UiPsi

/-!
# `ψ_{Ω_{s+1}}(B + Ω_{s+1}^γ·D) ≤ H^s_γ(c + D)` at every level `γ < ε_{Ω_{s+1}+1}`: hull lemma, CL, UB, INV

`ψ = S.psi · W`, `W = Ω_{s+1}`, `L = Ω_s`, `E = uiE s`, `H_γ = uiH s γ`, `uiC s γ` the largest component, `UiLt s q x`
(every component of `x` below `q`).  This is `R2.UcUB` (`s = 1`) for every finite `s`:

* `ui_E_mulPrin`, `ui_E_indec`, `ui_W_lt_E`, `ui_E_le_SC` (**a strongly critical `v > W` is `≥ E`**), `ui_one_lt_SC`;
* `ui_hull` (**every member of `Cl(a, q)` has all its components below `q`**, for `L < q < W` strongly critical,
  `a ≤ E`, once the collapses `ψ(e)`, `e < a`, of members with small components are below `q`);
* `UiCL`, `UiUB`, `uiINV` (**INV(γ)**: `ψ(B + W^γ·D) ≤ q`), `uiUB_of`, `uiCL_succ`, `uiCL_lim`, `uiCL_UB` (**CL(γ)
  and UB(γ) at every level `γ < E`**), `uiUB` (**`ψ(B + W^γ·D) ≤ H_γ(c + D)` for `W^γ ∣ B < E`, `ψ(B) ≤ H_γ(c)`,
  `D ≤ W`**), `uiInv`.

No new axiom.  New definitions: the statement names `UiCL`, `UiUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## `E = ε_{W+1}` -/

theorem ui_E_mulPrin (s : Ordinal.{0}) : IsPrincipal (· * ·) (uiE s) := by
  have h := isPrincipal_mul_omega0_opow_opow (uiE s)
  rwa [(uiE_fix s), (uiE_fix s)] at h

theorem ui_E_indec (s : Ordinal.{0}) : IsPrincipal (· + ·) (uiE s) := by
  rw [← (uiE_fix s)]; exact isPrincipal_add_omega0_opow _

theorem ui_W_lt_E {x : Ordinal.{0}} (hx : x < uiE s) : Om (s + 1) ^ x < uiE s := by
  rw [(ui_W_eq s), ← (uiE_fix s)]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 ((ui_E_mulPrin s) ((uiE_gt s)) hx)

/-- **A strongly critical `v > W` is `≥ E`.** -/
theorem ui_E_le_SC {v : Ordinal.{0}} (hv : SC v) (h : (Om (s + 1)) < v) : uiE s ≤ v :=
  uiE_le (Low.opow_eq_self_of_SC hv) h

theorem ui_one_lt_SC {q : Ordinal.{0}} (hq : SC q) : (1 : Ordinal.{0}) < q := by
  have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this

/-! ## The hull lemma -/

/-- **Every member of `Cl(a, q)` has all its components below `q`.** -/
theorem ui_hull (hs : s < ω) {a q : Ordinal.{0}} (hq : SC q) (hq1 : (Om s) < q) (hq2 : q < Om (s + 1)) (ha : a ≤ uiE s)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → UiLt s q e → S.psi e (Om (s + 1)) < q) :
    ∀ x, x ∈ S.CSet a q → UiLt s q x := by
  have h1q := ui_one_lt_SC hq
  have hbig : ∀ v, SC v → (Om (s + 1)) ≤ v → UiLt s q v := fun v hv h => by
    rcases eq_or_lt_of_le h with e | h'
    · rw [← e]; exact uiLt_W h1q
    · exact uiLt_out (ui_E_le_SC hv h')
  intro x hx
  induction hx with
  | @small x hxb => exact (uiLt_small (hxb.trans hq2)).2 hxb
  | zero => exact uiLt_zero hq.1
  | inacc n => exact hbig _ (SC_I n) (ui_W_lt_I hs n).le
  | inaccW => exact hbig _ SC_Iw (ui_W_lt_Iw hs).le
  | @add x y _ _ ihx ihy =>
    by_cases hE : x + y < uiE s
    · exact uiLt_add hq hE ihx ihy
    · exact uiLt_out (not_lt.1 hE)
  | @phi x y _ _ ihx ihy =>
    by_cases hE : veblen x y < uiE s
    · rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply] at hE ⊢; exact uiLt_opow hq hE ihy
      have hfix : ω ^ veblen x y = veblen x y := Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)
      rcases lt_trichotomy (veblen x y) (Om (s + 1)) with hv | hv | hv
      · have hx2 : x < Om (s + 1) := (left_le_veblen x y).trans_lt hv
        have hy2 : y < Om (s + 1) := (right_le_veblen x y).trans_lt hv
        exact (uiLt_small hv).2 (hq.2 x ((uiLt_small hx2).1 ihx) y ((uiLt_small hy2).1 ihy))
      · rw [hv]; exact uiLt_W h1q
      · exact absurd (uiE_le hfix hv) (not_le.2 hE)
    · exact uiLt_out (not_lt.1 hE)
  | @om x _ _ =>
    rcases lt_or_ge (Om x) (Om (s + 1)) with hv | hv
    · have hx2 : x < s + 1 := Om_lt_Om.1 hv
      have hx1 : Om x ≤ Om s := Om_le_Om.2 (Order.lt_add_one_iff.1 hx2)
      exact (uiLt_small hv).2 (hx1.trans_lt hq1)
    · have hx0 : x ≠ 0 := by
        rintro rfl
        rw [Om_zero] at hv
        exact absurd hv (not_le.2 (ui_SC_W s).1)
      exact hbig _ (SC_Om hx0) hv
  | @coll π e hπ _ heC _ ihe =>
    show (UiLt s) q (S.psi e.1 π)
    by_cases hπ2 : π = Om (s + 1)
    · subst hπ2
      have h := hcoll e.1 e.2 heC ihe
      exact (uiLt_small (h.trans hq2)).2 h
    · rcases ui_psi_cases (S := S) (e := e.1) hs hπ hπ2 with h | h
      · have h' := h.trans hq1
        exact (uiLt_small (h'.trans hq2)).2 h'
      · exact hbig _ (SC_psi hπ e.1) h

/-! ## The closure and the upper bound at level `γ` -/

/-- **CL(γ)**: `ψ(B + e) < q` for `W^γ ∣ B < E`, `ψ(B) < q`, `e < W^γ` with all components below `q`, when `q` is
strongly critical and closed under every `H_j`, `j < γ`, with `uiC s j < q`. -/
def UiCL (s : Ordinal.{0}) (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Om (s + 1) ^ γ ∣ B → B < uiE s → SC q → (∀ j < γ, uiC s j < q → ∀ z < q, uiH s j z < q) →
    S.psi B (Om (s + 1)) < q → e < Om (s + 1) ^ γ → UiLt s q e → S.psi (B + e) (Om (s + 1)) < q

/-- **UB(γ)**: `ψ(B + W^γ·D) ≤ H_γ(c + D)` for `W^γ ∣ B < E`, `ψ(B) ≤ H_γ(c)`, `D ≤ W`. -/
def UiUB (s : Ordinal.{0}) (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Om (s + 1) ^ γ ∣ B → B < uiE s → S.psi B (Om (s + 1)) ≤ uiH s γ c → D ≤ Om (s + 1) →
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ uiH s γ (c + D)

theorem uiCL_zero (s : Ordinal.{0}) : UiCL s S 0 := by
  intro B e q _ _ _ _ hBq he _
  rw [opow_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

theorem ui_lt_E_add {γ B D : Ordinal.{0}} (hγ : γ < uiE s) (hB : B < uiE s) (hD : D ≤ Om (s + 1)) :
    B + Om (s + 1) ^ γ * D < uiE s := by
  have h1 : γ + 1 < uiE s := (ui_E_indec s) hγ ((ui_one_lt_W s).trans (uiE_gt s))
  have h2 : Om (s + 1) ^ γ * D ≤ Om (s + 1) ^ (γ + 1) := by rw [(ui_W_succ s)]; exact mul_le_mul_left' hD _
  exact (ui_E_indec s) hB (h2.trans_lt (ui_W_lt_E h1))

/-- **INV(γ)** from CL(γ). -/
theorem uiINV (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < uiE s) (hCL : UiCL s S γ) {B D q : Ordinal.{0}}
    (hB : Om (s + 1) ^ γ ∣ B)
    (hBE : B < uiE s) (hq : SC q) (hcl : ∀ j < γ, uiC s j < q → ∀ z < q, uiH s j z < q)
    (hBq : S.psi B (Om (s + 1)) < q) (hD : D ≤ Om (s + 1))
    (hprev : ∀ d, d < D → d < q → S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < q) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ q := by
  rcases le_or_gt (Om (s + 1)) q with h1 | h1
  · exact (ui_psi_lt _).le.trans h1
  have hq1 : (Om s) < q := (ui_L_lt_psi B).trans hBq
  set u := Om (s + 1) ^ γ with hudef
  have hu0 : u ≠ 0 := ((ui_W_pos s) γ).ne'
  have haE : B + u * D < uiE s := ui_lt_E_add hγ hBE hD
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → UiLt s q e → S.psi e (Om (s + 1)) < q := by
    intro e he _ hcomp
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono (InR_Om_succ s) heB.le).1 hBq
    have heE : e < uiE s := he.trans haE
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < Om (s + 1) := hdD.trans_le hD
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
      refine lt_of_le_of_lt ?_ (ui_dig_lt hq.1 heE hcomp γ)
      rw [← hudef, hdiv]
      exact ui_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hB'E : B + u * (e1 / u) < uiE s := le_self_add.trans_lt (by rw [hee2]; exact heE)
    have hcomp2 : UiLt s q (e1 % u) := by
      have hc := uiLt_concat hq.1 _ _ γ hdvd' hrlt (by rw [hee2]; exact heE)
      rw [hee2] at hc
      exact (hc.1 hcomp).2
    have := hCL _ _ q hdvd' hB'E hq hcl hPd hrlt hcomp2
    rwa [hee2] at this
  have hinv := ui_hull (S := S) hs hq hq1 h1 haE.le hcoll
  refine psi_le_of_good (ui_W_mem hs _ _) fun x hx hx1 => ?_
  exact (uiLt_small hx1).1 (hinv x hx)

/-- **UB(γ)** from CL(γ). -/
theorem uiUB_of (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < uiE s) (hCL : UiCL s S γ) : UiUB s S γ := by
  intro B c D hB hBE hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hcl : ∀ j < γ, uiC s j < uiH s γ (c + D) → ∀ z < uiH s γ (c + D), uiH s j z < uiH s γ (c + D) :=
    fun j hj hcj z hz => by
      have hf : uiH s j (uiH s γ (c + D)) = uiH s γ (c + D) := ucG_fix_lower hj ⟨c + D, rfl⟩ hcj
      have := (uiH_lt_iff (s := s) j).2 hz
      rwa [hf] at this
  have hprev : ∀ d, d < D → d < uiH s γ (c + D) →
      S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < uiH s γ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((uiH_lt_iff (s := s) γ).2 ((add_lt_add_iff_left c).2 hd))
  exact uiINV hs hγ hCL hB hBE (uiH_SC (s := s) γ _) hcl
    (hc.trans_lt ((uiH_lt_iff (s := s) γ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(γ+1)** from CL(γ) and UB(γ) (`γ + 1 < E`). -/
theorem uiCL_succ {γ : Ordinal.{0}} (hγ1 : γ + 1 < uiE s) (hCL : UiCL s S γ) (hUB : UiUB s S γ) :
    UiCL s S (γ + 1) := by
  intro B e q hB hBE hq hcl hBq he hcomp
  set u := Om (s + 1) ^ γ with hudef
  have hu0 : u ≠ 0 := ((ui_W_pos s) γ).ne'
  have hqI : IsPrincipal (· + ·) q := hq.isPrincipal
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om (s + 1) := by
    rw [(ui_W_succ s)] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hBk : u ∣ B := (opow_dvd_opow _ le_self_add).trans hB
  have hEe : B + e < uiE s := (ui_E_indec s) hBE (he.trans (ui_W_lt_E hγ1))
  have heE : e < uiE s := le_add_self.trans_lt hEe
  rcases eq_or_ne (e / u) 0 with h0 | h0
  · have hee : e = e % u := by
      conv_lhs => rw [← her, h0, mul_zero, zero_add]
    rw [hee]
    exact hCL B _ q hBk hBE hq (fun j hj => hcl j (hj.trans (lt_add_one γ))) hBq hrlt
      (by rw [← hee]; exact hcomp)
  -- the digit at `γ` and the components of `γ`
  have hγc : UiLt s q γ ∧ e / u < q ∧ UiLt s q (e % u) := by
    rcases eq_or_ne γ 0 with hγ0 | hγ0
    · have hu1 : u = 1 := by rw [hudef, hγ0, opow_zero]
      have he2 : e < Om (s + 1) := by rw [hγ0, zero_add, opow_one] at he; exact he
      refine ⟨by rw [hγ0]; exact uiLt_zero hq.1, ?_, ?_⟩
      · rw [hu1, Ordinal.div_one]; exact (uiLt_small he2).1 hcomp
      · rw [hu1, Ordinal.mod_one]; exact uiLt_zero hq.1
    · have hcn := uiLt_cnf (q := q) (one_le_iff_ne_zero.2 hγ0) h0 hdΩ hrlt (by rw [her]; exact heE)
      rw [her] at hcn
      exact hcn.1 hcomp
  obtain ⟨hγq, hdq, hrq⟩ := hγc
  have hCγ : uiC s γ < q := (uiC_lt_iff hq.1 γ).2 hγq
  have hle := hUB B (S.psi B (Om (s + 1))) (e / u) hBk hBE (uiH_le_self (s := s) γ _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om (s + 1)) < q :=
    hle.trans_lt (hcl γ (lt_add_one γ) hCγ _ (hqI hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hB'E : B + u * (e / u) < uiE s := by
    refine lt_of_le_of_lt ?_ hEe
    conv_rhs => rw [← her, ← add_assoc]
    exact le_self_add
  have := hCL _ _ q hdvd' hB'E hq (fun j hj => hcl j (hj.trans (lt_add_one γ))) hP hrlt hrq
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem uiCL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, UiCL s S j) : UiCL s S l := by
  intro B e q hB hBE hq hcl hBq he hcomp
  obtain ⟨j, hj, hej⟩ := ((isNormal_opow (ui_one_lt_W s)).lt_iff_exists_lt hl).1 he
  exact h j hj B e q ((opow_dvd_opow _ hj.le).trans hB) hBE hq (fun i hi => hcl i (hi.trans hj)) hBq hej hcomp

/-- **CL(γ) and UB(γ) at every level `γ < E`.** -/
theorem uiCL_UB (hs : s < ω) : ∀ γ : Ordinal.{0}, γ < uiE s → UiCL s S γ ∧ UiUB s S γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  have hCL : UiCL s S γ := by
    rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact (uiCL_zero s)
    · rw [Order.succ_eq_add_one] at IH hγ ⊢
      have h := IH j (lt_add_one j) ((lt_add_one j).trans hγ)
      exact uiCL_succ hγ h.1 h.2
    · exact uiCL_lim hl fun j hj => (IH j hj (hj.trans hγ)).1
  exact ⟨hCL, uiUB_of hs hγ hCL⟩

/-- **`ψ_{W}(B + W^γ·D) ≤ H_γ(c + D)`** for `γ < E`, `W^γ ∣ B < E`, `ψ_{W}(B) ≤ H_γ(c)`, `D ≤ W`. -/
theorem uiUB (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < uiE s) : UiUB s S γ := (uiCL_UB hs γ hγ).2

/-- **`ψ_{W}(B + W^γ·D) ≤ q`** (INV(γ)) at every level `γ < E`. -/
theorem uiInv (hs : s < ω) {γ B D q : Ordinal.{0}} (hγ : γ < uiE s) (hB : Om (s + 1) ^ γ ∣ B) (hBE : B < uiE s) (hq :
    SC q)
    (hcl : ∀ j < γ, uiC s j < q → ∀ z < q, uiH s j z < q) (hBq : S.psi B (Om (s + 1)) < q) (hD : D ≤ Om (s + 1))
    (hprev : ∀ d, d < D → d < q → S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < q) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ q :=
  uiINV hs hγ (uiCL_UB hs γ hγ).1 hB hBE hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Ui
