import Googology.Trans.PoR.InaccPsi.R2.UlK

/-!
# The lifted hierarchy `Hˡ_γ` at every level `γ`, `Hˡ = H^s` below `ε_{Ω_{s+1}+1}`, and the upper bound
# `ψ_{Ω_{s+1}}(B + Ω_{s+1}^γ·D) ≤ Hˡ_γ(c + D)` at every level and every `B`

`ψ = S.psi · W`, `W = Ω_{s+1}`, `L = Ω_s`, `E = Ui.uiE s = ε_{W+1}`, `K_q = UlK S s q` and `ulD` the visibility
datum (`R2.UlK`), `Uc.ucG d L μ` the generic hierarchy (`R2.UcH`).

* `ulH S s γ := ucG (ulD S s) L γ` (**the lifted hierarchy**: a level `γ` is any ordinal, visible at `v` when `γ ∈
  K_v`; the levels `γ ≥ E` have components `≥ W`, atoms `ψ_{Ω_{s+2}}(e)`), `ulH_SC`, `ulH_gt`, `ulH_D_lt`,
  `ulH_lt_iff`, `ulH_le_iff`, `ulH_le_self`, `ulH_normal`;
* `ul_ucG_congr` (two data with the same tests `d j < v` at the strongly critical `v > L` give the same hierarchy),
  `ul_lt_iff_K` (**below `E`: all components of `γ` below `v` iff `γ ∈ K_v`**, `v > L` strongly critical),
  `ulH_eq_uiH` (**`Hˡ_γ = H^s_γ` for every `γ < E`**: the lifted hierarchy extends `R2.UiH`);
* `UlCL`, `UlUB` (the statements with no bound on `γ` or `B`), `ulINV`, `ulUB_of`, `ulCL_succ`, `ulCL_lim`,
  `ulCL_UB` (**CL(γ) and UB(γ) at every level `γ`**), `ulUB` (**`ψ(B + W^γ·D) ≤ Hˡ_γ(c + D)` for every `γ`, every `B`
  with `W^γ ∣ B` and `ψ(B) ≤ Hˡ_γ(c)`, `D ≤ W`**), `ulInv`.

No new axiom.  New definitions: `ulH` and the statement names `UlCL`, `UlUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## The lifted hierarchy -/

/-- **The lifted hierarchy**: the generic hierarchy on the visibility datum `ulD`, floor `Ω_s`, every level `γ`. -/
noncomputable def ulH (S : InaccSeq.{0}) (s γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  ucG (ulD S s) (Om s) γ

theorem ulH_SC (γ o : Ordinal.{0}) : SC (ulH S s γ o) := ucG_SC γ o

theorem ulH_gt (γ o : Ordinal.{0}) : Om s < ulH S s γ o := ucG_L_lt γ o

theorem ulH_D_lt (γ o : Ordinal.{0}) : ulD S s γ < ulH S s γ o := ucG_d_lt γ o

theorem ulH_lt_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : ulH S s γ a < ulH S s γ b ↔ a < b := ucG_lt_iff γ

theorem ulH_le_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : ulH S s γ a ≤ ulH S s γ b ↔ a ≤ b := ucG_le_iff γ

theorem ulH_le_self (γ o : Ordinal.{0}) : o ≤ ulH S s γ o := ucG_le_self γ o

theorem ulH_normal (γ : Ordinal.{0}) : Order.IsNormal (ulH S s γ) := ucG_normal γ

/-- **Two data with the same tests give the same hierarchy.** -/
theorem ul_ucG_congr {d1 d2 : Ordinal.{0} → Ordinal.{0}} {L : Ordinal.{0}} :
    ∀ μ : Ordinal.{0}, (∀ j ≤ μ, ∀ v, SC v → L < v → (d1 j < v ↔ d2 j < v)) → ucG d1 L μ = ucG d2 L μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro h
  rw [ucG_eq, ucG_eq]
  congr 1
  ext v
  simp only [ucGC, mem_setOf_eq]
  constructor
  · rintro ⟨hSC, hL, hμ, hf⟩
    refine ⟨hSC, hL, (h μ le_rfl v hSC hL).1 hμ, fun j hj hj2 => ?_⟩
    rw [← IH j hj fun i hi => h i (hi.trans hj.le)]
    exact hf j hj ((h j hj.le v hSC hL).2 hj2)
  · rintro ⟨hSC, hL, hμ, hf⟩
    refine ⟨hSC, hL, (h μ le_rfl v hSC hL).2 hμ, fun j hj hj1 => ?_⟩
    rw [IH j hj fun i hi => h i (hi.trans hj.le)]
    exact hf j hj ((h j hj.le v hSC hL).1 hj1)

/-- **Below `E`: every component of `γ` is below `v` iff `γ ∈ K_v`** (`v > L` strongly critical). -/
theorem ul_lt_iff_K (hs : s < ω) {v : Ordinal.{0}} (hv : SC v) (hLv : Om s < v) :
    ∀ γ, γ < Ui.uiE s → (Ui.UiLt s v γ ↔ UlK S s v γ) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE
  by_cases h1 : γ < Om (s + 1)
  · rw [Ui.uiLt_small h1]
    exact ⟨UlK.small, fun h => ulK_lt_W hs hv hLv h h1⟩
  have h1' := not_lt.1 h1
  set e := log (Om (s + 1)) γ with hedef
  set u := Om (s + 1) ^ e with hudef
  have he1 : 1 ≤ e := by
    rw [hedef]; exact (Order.one_le_iff_pos).2 (log_pos (Ui.ui_one_lt_W s) (Ui.ui_ne_zero h1') h1')
  have hd0 : γ / u ≠ 0 := (Ui.ui_div_pos h1').ne'
  have hdW : γ / u < Om (s + 1) := Ui.ui_div_lt s γ
  have hrlt : γ % u < u := Ordinal.mod_lt _ (Ui.ui_W_pos s e).ne'
  have hcnf : u * (γ / u) + γ % u = γ := Ordinal.div_add_mod _ _
  have hcn := Ui.uiLt_cnf (q := v) he1 hd0 hdW hrlt (by rw [hcnf]; exact hγE)
  rw [hcnf] at hcn
  have helt : e < γ := Ui.ui_log_lt h1' hγE
  have hrγ : γ % u < γ := Ui.ui_mod_lt h1'
  have heE : e < Ui.uiE s := helt.trans hγE
  have hrE : γ % u < Ui.uiE s := hrγ.trans hγE
  rw [hcn]
  constructor
  · rintro ⟨hce, hcd, hcr⟩
    have hK1 := (IH e helt heE).1 hce
    have hK2 := (IH _ hrγ hrE).1 hcr
    have hWe : UlK S s v (Om (s + 1) * e) := by
      have := ulK_opow_mul hv (ulK_W (S := S) (q := v) hs) e hK1; rwa [Ui.ui_W_opow s] at this
    have hu : UlK S s v (u * (γ / u)) := by
      have e2 : u = ω ^ (Om (s + 1) * e) := Ui.ui_W_eq s e
      have := ulK_opow_mul hv hWe _ (UlK.small hcd)
      rwa [← e2] at this
    rw [← hcnf]; exact UlK.add hu hK2
  · intro hK
    have hdig := ulK_dig hs hv hK e
    rw [← hudef, Ordinal.mod_eq_of_lt hdW] at hdig
    exact ⟨(IH e helt heE).2 (hdig.2 hd0), ulK_lt_W hs hv hLv hdig.1 hdW,
      (IH _ hrγ hrE).2 (ulK_modW hv hK e)⟩

/-- **`Hˡ_γ = H^s_γ` for every `γ < E`**: the lifted hierarchy extends `R2.UiH`. -/
theorem ulH_eq_uiH (hs : s < ω) {γ : Ordinal.{0}} (hγ : γ < Ui.uiE s) : ulH S s γ = Ui.uiH s γ := by
  unfold ulH Ui.uiH
  refine ul_ucG_congr γ fun j hj v hv hLv => ?_
  have hjE : j < Ui.uiE s := hj.trans_lt hγ
  rcases le_or_gt v (Om (s + 1)) with hvW | hvW
  · rw [ul_vis hv, Ui.uiC_lt_iff hv.1]
    exact (ul_lt_iff_K hs hv hLv j hjE).symm
  · have hEv : Ui.uiE s ≤ v := Ui.ui_E_le_SC hv hvW
    exact ⟨fun _ => (Ui.uiC_lt_W s j).trans hvW, fun _ => (ulD_le_self j).trans_lt (hjE.trans_le hEv)⟩

/-! ## CL, UB, INV at every level -/

/-- **CL(γ)**: `ψ(B + e) < q` for `W^γ ∣ B`, `ψ(B) < q`, `e < W^γ` with `e ∈ K_q`, when `q` is strongly critical and
closed under every `Hˡ_j`, `j < γ`, visible at `q`. -/
def UlCL (S : InaccSeq.{0}) (s γ : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Om (s + 1) ^ γ ∣ B → SC q → (∀ j < γ, ulD S s j < q → ∀ z < q, ulH S s j z < q) →
    S.psi B (Om (s + 1)) < q → e < Om (s + 1) ^ γ → UlK S s q e → S.psi (B + e) (Om (s + 1)) < q

/-- **UB(γ)**: `ψ(B + W^γ·D) ≤ Hˡ_γ(c + D)` for `W^γ ∣ B`, `ψ(B) ≤ Hˡ_γ(c)`, `D ≤ W`. -/
def UlUB (S : InaccSeq.{0}) (s γ : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Om (s + 1) ^ γ ∣ B → S.psi B (Om (s + 1)) ≤ ulH S s γ c → D ≤ Om (s + 1) →
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ ulH S s γ (c + D)

theorem ulCL_zero : UlCL S s 0 := by
  intro B e q _ _ _ hBq he _
  rw [opow_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- **INV(γ)** from CL(γ). -/
theorem ulINV (hs : s < ω) {γ : Ordinal.{0}} (hCL : UlCL S s γ) {B D q : Ordinal.{0}}
    (hB : Om (s + 1) ^ γ ∣ B) (hq : SC q) (hcl : ∀ j < γ, ulD S s j < q → ∀ z < q, ulH S s j z < q)
    (hBq : S.psi B (Om (s + 1)) < q) (hD : D ≤ Om (s + 1))
    (hprev : ∀ d, d < D → d < q → S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < q) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ q := by
  rcases le_or_gt (Om (s + 1)) q with h1 | h1
  · exact (Ui.ui_psi_lt _).le.trans h1
  have hq1 : Om s < q := (Ui.ui_L_lt_psi B).trans hBq
  set u := Om (s + 1) ^ γ with hudef
  have hu0 : u ≠ 0 := (Ui.ui_W_pos s γ).ne'
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q → UlK S s q e →
      S.psi e (Om (s + 1)) < q := by
    intro e he _ hK
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono (InR_Om_succ s) heB.le).1 hBq
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
    have hdig := (ulK_dig hs hq hK γ).1
    have hdq : e1 / u < q := by
      refine lt_of_le_of_lt ?_ (ulK_lt_W hs hq hq1 hdig (Ordinal.mod_lt _ (Ui.ui_SC_W s).1.ne'))
      rw [← hudef, hdiv]
      exact Ui.ui_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hcomp2 : UlK S s q (e1 % u) := by
      have hmod : e % u = e1 % u := by
        rw [he_eq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrlt]
      rw [← hmod]; exact ulK_modW hq hK γ
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hcomp2
    rwa [hee2] at this
  have hinv := ulK_hull (S := S) (s := s) hcoll
  refine psi_le_of_good (Ui.ui_W_mem hs _ _) fun x hx hx1 => ?_
  exact ulK_lt_W hs hq hq1 (hinv x hx) hx1

/-- **UB(γ)** from CL(γ). -/
theorem ulUB_of (hs : s < ω) {γ : Ordinal.{0}} (hCL : UlCL S s γ) : UlUB S s γ := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hcl : ∀ j < γ, ulD S s j < ulH S s γ (c + D) → ∀ z < ulH S s γ (c + D),
      ulH S s j z < ulH S s γ (c + D) := fun j hj hcj z hz => by
    have hf : ulH S s j (ulH S s γ (c + D)) = ulH S s γ (c + D) := ucG_fix_lower hj ⟨c + D, rfl⟩ hcj
    have := (ulH_lt_iff (S := S) (s := s) j).2 hz
    rwa [hf] at this
  have hprev : ∀ d, d < D → d < ulH S s γ (c + D) →
      S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < ulH S s γ (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((ulH_lt_iff (S := S) (s := s) γ).2 ((add_lt_add_iff_left c).2 hd))
  exact ulINV hs hCL hB (ulH_SC (S := S) (s := s) γ _) hcl
    (hc.trans_lt ((ulH_lt_iff (S := S) (s := s) γ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(γ+1)** from CL(γ) and UB(γ). -/
theorem ulCL_succ (hs : s < ω) {γ : Ordinal.{0}} (hCL : UlCL S s γ) (hUB : UlUB S s γ) : UlCL S s (γ + 1) := by
  intro B e q hB hq hcl hBq he hK
  set u := Om (s + 1) ^ γ with hudef
  have hu0 : u ≠ 0 := (Ui.ui_W_pos s γ).ne'
  have hqI : IsPrincipal (· + ·) q := hq.isPrincipal
  have hq1 : Om s < q := (Ui.ui_L_lt_psi B).trans hBq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om (s + 1) := by
    rw [Ui.ui_W_succ s] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hBk : u ∣ B := (opow_dvd_opow _ le_self_add).trans hB
  have hrq : UlK S s q (e % u) := ulK_modW hq hK γ
  have hcl' : ∀ j < γ, ulD S s j < q → ∀ z < q, ulH S s j z < q := fun j hj => hcl j (hj.trans (lt_add_one γ))
  rcases eq_or_ne (e / u) 0 with h0 | h0
  · have hee : e = e % u := by
      conv_lhs => rw [← her, h0, mul_zero, zero_add]
    rw [hee]
    exact hCL B _ q hBk hq hcl' hBq hrlt hrq
  have hdig := ulK_dig hs hq hK γ
  rw [← hudef, Ordinal.mod_eq_of_lt hdΩ] at hdig
  have hγq : UlK S s q γ := hdig.2 h0
  have hdq : e / u < q := ulK_lt_W hs hq hq1 hdig.1 hdΩ
  have hCγ : ulD S s γ < q := (ul_vis hq).2 hγq
  have hle := hUB B (S.psi B (Om (s + 1))) (e / u) hBk (ulH_le_self (S := S) (s := s) γ _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om (s + 1)) < q :=
    hle.trans_lt (hcl γ (lt_add_one γ) hCγ _ (hqI hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have := hCL _ _ q hdvd' hq hcl' hP hrlt hrq
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem ulCL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, UlCL S s j) : UlCL S s l := by
  intro B e q hB hq hcl hBq he hK
  obtain ⟨j, hj, hej⟩ := ((isNormal_opow (Ui.ui_one_lt_W s)).lt_iff_exists_lt hl).1 he
  exact h j hj B e q ((opow_dvd_opow _ hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hK

/-- **CL(γ) and UB(γ) at every level `γ`** (no bound on `γ`). -/
theorem ulCL_UB (hs : s < ω) : ∀ γ : Ordinal.{0}, UlCL S s γ ∧ UlUB S s γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  have hCL : UlCL S s γ := by
    rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact ulCL_zero
    · rw [Order.succ_eq_add_one] at IH ⊢
      have h := IH j (lt_add_one j)
      exact ulCL_succ hs h.1 h.2
    · exact ulCL_lim hl fun j hj => (IH j hj).1
  exact ⟨hCL, ulUB_of hs hCL⟩

/-- **`ψ_W(B + W^γ·D) ≤ Hˡ_γ(c + D)`** for every level `γ` and every `B` with `W^γ ∣ B`, `ψ_W(B) ≤ Hˡ_γ(c)`,
`D ≤ W`. -/
theorem ulUB (hs : s < ω) (γ : Ordinal.{0}) : UlUB S s γ := (ulCL_UB hs γ).2

/-- **`ψ_W(B + W^γ·D) ≤ q`** (INV(γ)) at every level `γ`. -/
theorem ulInv (hs : s < ω) {γ B D q : Ordinal.{0}} (hB : Om (s + 1) ^ γ ∣ B) (hq : SC q)
    (hcl : ∀ j < γ, ulD S s j < q → ∀ z < q, ulH S s j z < q) (hBq : S.psi B (Om (s + 1)) < q)
    (hD : D ≤ Om (s + 1)) (hprev : ∀ d, d < D → d < q → S.psi (B + Om (s + 1) ^ γ * d) (Om (s + 1)) < q) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ≤ q :=
  ulINV hs (ulCL_UB hs γ).1 hB hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Ul
