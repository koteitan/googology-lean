import Googology.Trans.PoR.InaccPsi.R2.RnG

/-!
# `Lj.LjAtMove` below `T₁ = ψ_{Ω₂}(Ω₂^{Ω₂+1})`, and the road with the atoms in `[T₁, θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `μ = Ω₂^{Ω₂}`, `O = Ω₁^{Ω₁}`, `T₁ = ψ_{Ω₂}(μ·Ω₂)` (`Rn.rnT1`), `θ = ψ_{Ω₂}(Ω_ω)`.

* `rnB_W2`, `rnB_O2`, `rnB_muG` (**`B_n(μ·γ) = μ·B_n γ`** on the codes below an atom whose codes move), `rnB_Ox`
  (**`B_n(O·x) = O·B_n x`** for `x < c_{n+1}`), `rnB_T1` (`B_n T₁ = T₁`);
* `rnAtMove_g` (**every atom `s` with `ψ_{Ω₂}(μ·g) ≤ s ≤ ψ_{Ω₂}(μ·(g+1))`, `g < T₁` a code, moves** once the codes
  below `s` move: `Rn.rnAtMove_base` at the bases `μ·g` and `μ·B_n g`, readings by `Rn.rnThG` at `λ` and `λ'`);
* `rnCls_g` (**every atom `s < T₁` lies in `[ψ_{Ω₂}(μ·g), ψ_{Ω₂}(μ·(g+1))]` for a code `g < T₁`**);
* `RnAtMove1 S` (a hypothesis name): **`Lj.LjAtMove` for the atoms `T₁ ≤ s ≤ θ`**; `rnLjAtMove1` (**`RnAtMove1`
  gives `LjAtMove`**), `rnAtMove1_of` (the converse), `rnRoadC` (**the road** with `RnAtMove1`, `Rn.RnThMoveM`,
  `Rn.RnEQhi2`).

No new axiom.  New definition: the hypothesis name `RnAtMove1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

theorem rnB_W2 {n : ℕ} : MvD S (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) ∧
    Bc.bcB S n (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [ldOm2sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB2]⟩

theorem rnB_O2 {n : ℕ} : MvD S (Om (1 : Ordinal.{0}) * Om 1) ∧
    Bc.bcB S n (Om (1 : Ordinal.{0}) * Om 1) = Om 1 * Om 1 := by
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD1 hD1
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [rnOm1sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB1]⟩

/-- **`B_n(μ·γ) = μ·B_n γ`** for `γ` in a class of `MvD` below `Ω₂` closed under `log` and the tail. -/
theorem rnB_muG {n : ℕ} (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {γ : Ordinal.{0}} (hγ : P γ) :
    MvD S (leWe (Om (1 + 1)) * γ) ∧ Bc.bcB S n (leWe (Om (1 + 1)) * γ) = leWe (Om (1 + 1)) * Bc.bcB S n γ := by
  obtain ⟨hDK, hBK⟩ := rnB_W2 (S := S) (n := n)
  have hWW : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1) * Om (1 + 1) := by
    have := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
    rwa [mul_one] at this
  obtain ⟨hD, hB⟩ := leB_mulOp2 (n := n) hDK P hPD hPdec (fun x hx => (hPW x hx).trans hWW) γ hγ
  rw [hBK] at hB
  exact ⟨hD, hB⟩

/-- **`B_n(O·x) = O·B_n x`** for `x < c_{n+1}`. -/
theorem rnB_Ox {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S (n + 1)) :
    MvD S (leOe (Om 1) * x) ∧ Bc.bcB S n (leOe (Om 1) * x) = leOe (Om 1) * Bc.bcB S n x := by
  obtain ⟨hDK, hBK⟩ := rnB_O2 (S := S) (n := n)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hOO : Om (1 : Ordinal.{0}) ≤ Om 1 * Om 1 := le_mul_right (Om 1) (Om_pos one_ne_zero)
  obtain ⟨hD, hB⟩ := leB_mulOp2 (n := n) hDK (fun y => y < Bc.bcC S (n + 1))
    (fun y hy => mvD_of_lt (hy.trans hLw))
    (fun y hy _ => ⟨(log_le_self ω y).trans_lt hy, (Ordinal.sub_le_self _ _).trans_lt hy⟩)
    (fun y hy => (hy.trans hc1).trans_le hOO) x hx
  rw [hBK] at hB
  exact ⟨hD, hB⟩

/-- `B_n T₁ = T₁`. -/
theorem rnB_T1 {n : ℕ} : MvD S (rnT1 S) ∧ Bc.bcB S n (rnT1 S) = rnT1 S := by
  obtain ⟨hD1, hB1⟩ := rnB_W2 (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD1 hD2
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [hBs, hB1, hB2, ← rnMuW_eq] at hBo
  rw [← rnMuW_eq] at hDo
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDo (leMulWe_mem (mxOm2_mem _ _) (mxOm2_mem _ _))
  refine ⟨hDT, ?_⟩
  unfold rnT1; rw [hBT, hBo]

/-- **The atoms `ψ_{Ω₂}(μ·g) ≤ s ≤ ψ_{Ω₂}(μ·(g+1))` move** once the codes below them move. -/
theorem rnAtMove_g {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl' : IsRestartIdx l') (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1))
    {g : Ordinal.{0}} (hgc : GxCl (upsilon l) (ldAtR S l) g) (hgT : g < rnT1 S) :
    ∀ s ∈ ldAtR S l, S.psi (leWe (Om (1 + 1)) * g) (Om (1 + 1)) ≤ s →
      s ≤ S.psi (leWe (Om (1 + 1)) * (g + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < rnT1 S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro s hs h1 h2 IH
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hgW : g < Om (1 + 1) := hgT.trans rnT1_lt_Om2
  have hgH : g ∈ cdHull S l := (ldHull_iff hl hX hgW).2 hgc
  have hgs : g < s := (rnT1_gt hgT).trans_le h1
  obtain ⟨hDg, hBgc, hΘgX, hΘg⟩ := IH g hgc hgs
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < s ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  obtain ⟨hDβ, hBβ⟩ := rnB_muG (n := n) P hPD hPdec (fun x hx => hx.2.2) ⟨hgc, hgs, hgW⟩
  obtain ⟨hDT, hBT⟩ := rnB_T1 (S := S) (n := n)
  have hBgT : Bc.bcB S n g < rnT1 S := by
    have := (mvB_lt_iff (k := n) hDg hDT).2 hgT; rwa [hBT] at this
  have hBgW : Bc.bcB S n g < Om (1 + 1) := hBgT.trans rnT1_lt_Om2
  have hBgH : Bc.bcB S n g ∈ cdHull S l' := (ldHull_iff hl' hX' hBgW).2 hBgc
  obtain ⟨e0, own0⟩ := rnThG hl hX hA hρ g hgc hgT
  obtain ⟨e0', own0'⟩ := rnThG hl' hX' hA' hρ' (Bc.bcB S n g) hBgc hBgT
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hΘg1 : gxTh (upsilon l) (ldAtR S l) g < Om 1 := hΘgX.trans hc1
  obtain ⟨hDOx, hBOx⟩ := rnB_Ox (S := S) (n := n) hΘgX
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hD1 hDOx
  rw [mwB_one, hBOx, ← hΘg] at hBD
  have hG : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hDG : 1 + leOe (Om 1) * gxTh (upsilon l) (ldAtR S l) g < S.psi 0 (Om (1 + 1)) :=
    hG.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG)) (ldMul_lt_SC hG rnOO_lt_G (hΘg1.trans hΩG))
  rw [add_assoc] at e0 own0 e0' own0'
  rw [← hBD] at e0' own0'
  have hsT : s ≤ rnTW S (leWe (Om (1 + 1)) * g) := by
    unfold rnTW; rw [← mul_add_one]; exact h2
  rw [← hBβ] at e0'
  obtain ⟨hDs, hBs, hBle, hth, hEq⟩ := rnAtMove_base hl hl' hX hX' hbX hBψ (rnBg_base l hgH hgT)
    (rnBg_base l' hBgH hBgT) hDβ hBβ hDD hDG own0 own0' e0 (by rw [← hBβ]; exact e0') s hs h1 hsT IH
  refine ⟨hDs, hBs, ?_, hth, hEq⟩
  have hBg1T : Bc.bcB S n g + 1 < rnT1 S := rnT1_SC.isSuccLimit.succ_lt hBgT
  have hBg1W : Bc.bcB S n g + 1 < Om (1 + 1) := hBg1T.trans rnT1_lt_Om2
  refine hBle.trans_lt ?_
  unfold rnTW; rw [← mul_add_one]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (leMulWe_lt hBg1W) (leMulWe_mem (mxOm2_mem _ _) (CSet.of_lt hBg1T))

/-- **Every atom `s < T₁` lies in `[ψ_{Ω₂}(μ·g), ψ_{Ω₂}(μ·(g+1))]` for a code `g < T₁`.** -/
theorem rnCls_g {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ s ∈ ldAtR S l, s < rnT1 S → ∃ g, GxCl (upsilon l) (ldAtR S l) g ∧ g < rnT1 S ∧
      S.psi (leWe (Om (1 + 1)) * g) (Om (1 + 1)) ≤ s ∧ s ≤ S.psi (leWe (Om (1 + 1)) * (g + 1)) (Om (1 + 1)) := by
  intro s hs hsT
  obtain ⟨a, haH, -, rfl⟩ := hs
  have hμ0 : leWe (Om (1 + 1)) ≠ 0 := (leWe_pos _).ne'
  have haW : a < leWe (Om (1 + 1)) * Om (1 + 1) := by
    by_contra h
    push Not at h
    exact absurd hsT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 (dvd_zero _) zero_le (by rw [zero_add]; exact haW)
  rw [zero_add] at hlo hhi
  have hgH : a % (leWe (Om (1 + 1)) * Om (1 + 1)) / leWe (Om (1 + 1)) ∈ cdHull S l := by
    have h1 : a % (leWe (Om (1 + 1)) * Om (1 + 1)) ∈ cdHull S l := by
      rw [← leWe_succ]; exact leModP_mem _ haH
    have h2 : a % (leWe (Om (1 + 1)) * Om (1 + 1)) < ω ^ (Om (1 + 1) * Om (1 + 1) + Om (1 + 1)) := by
      rw [← rnMuW_eq]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
    exact leDivOp_mem (dvd_mul_right _ _) h1 h2
  have hgc := (ldHull_iff hl hX hgW).1 hgH
  have hlo' := (psi_mono (S := S) (InR_Om_succ 1) hlo).1
  refine ⟨_, hgc, ?_, hlo', (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1⟩
  by_contra h
  push Not at h
  exact absurd ((rnT1_ge h).trans hlo') (not_le.2 hsT)

/-- **`LjAtMove` for the atoms `T₁ ≤ s ≤ θ`.** -/
def RnAtMove1 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, rnT1 S ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RnAtMove1` gives `LjAtMove`.** -/
theorem rnLjAtMove1 (h : RnAtMove1 S) : LjAtMove S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  by_cases hs1 : rnT1 S ≤ s
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH
  push Not at hs1
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  obtain ⟨g, hgc, hgT, hg1, hg2⟩ := rnCls_g hR.1 hX s hs hs1
  obtain ⟨hDs, hBs, hBT, hth, hEq⟩ := rnAtMove_g (n := n) hR.1 hl' hX hX' hA hA' hρ hρ' hbX hBψ hgc hgT s hs
    hg1 hg2 (fun x hx hxs => by
      obtain ⟨a1, a2, -, a4, a5⟩ := IH x hx hxs
      exact ⟨a1, a2, a4, a5⟩)
  exact ⟨hDs, hBs, hBT.trans (rnT1_lt_th.trans ljTh_lt_ThP), hth, hEq⟩

theorem rnFWW_le_T1 : leFWW S ≤ rnT1 S := by
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  have := (mul_le_mul_iff_right₀ (leWe_pos (Om (1 + 1)))).2
    (Order.one_le_iff_pos.2 ldOm2_SC.1)
  rwa [mul_one] at this

/-- **`LjAtMove` gives `RnAtMove1`.** -/
theorem rnAtMove1_of (h : LjAtMove S) : RnAtMove1 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (rnFWW_le_T1.trans hs1) hsθ IH

/-- **The road with `RnAtMove1`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rnRoadC (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove1 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ljRoadA hU hO hL hV hN hlh (fun hν => rnLjAtMove1 (hat hν)) (fun hν => rnLjEQhi_of hν (hM hν) (hhi hν))

end Googology.Trans.PoR.InaccPsi.R2.Rn
