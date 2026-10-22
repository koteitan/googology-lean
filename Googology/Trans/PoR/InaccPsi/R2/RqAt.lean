import Googology.Trans.PoR.InaccPsi.R2.RqFam

/-!
# The atoms below every `EM_j` move, and the road with the atoms in `[sup_j EM_j, θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`F_ξ = ψ_{Ω₂}(W^{Ω₂·ξ})`, `EM_0 = Ω₁`, `EM_{j+1} = F_{EM_j}` (`Rq.rqEM`).

* `rqShC_B` (**the code shifts move**: `B_n(Ω₂·(Ω₂·ξ)) = Ω₂·(Ω₂·B_n ξ)`, `B_n(Ω₁·(Ω₁·Θ ξ)) = Ω₁·(Ω₁·Θ'(B_n ξ))`,
  and `(Ω₂·B_n ξ, Ω₁·Θ'(B_n ξ))` is a code shift at `λ'`, once the codes below `F_ξ` move), `rqBase0`;
* `rqAtMoveC` (**every atom `ψ_{Ω₂}(0) < s ≤ F_ξ` moves**, `ξ` a code shift);
* `RqAtMove5 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `s ≤ θ` above every `EM_j`;
  `rqAtMove4_of5` (**`RqAtMove5` gives `Ro.RoAtMove4`**), `rqAtMove5_of` (the converse), `rqRoadG` (**the road**),
  `rqRoadG_hyps` (its hypotheses follow from those of `Rn.rnRoadD`).

No new axiom.  New definition: the hypothesis name `RqAtMove5`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

/-- **The code shifts move** once the codes below `F_ξ` move. -/
theorem rqShC_B {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ X Xh, rqShC S l X Xh →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, rqShC S l' XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  rintro X Xh ⟨ξ, hξ, h1, ⟨j, hj⟩, hΘ1, rfl, rfl⟩ IH
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hξW : ξ < Om (1 + 1) := hj.trans (rqEM_lt_Om2 j)
  have hown := rqEM_gt j ξ hj
  obtain ⟨hDξ, hBξc, hΘξc, hΘξB⟩ := IH ξ hξ hown
  obtain ⟨hDE, hBE⟩ := rqEM_B (S := S) (n := n) j
  have hΘ1le : (1 : Ordinal.{0}) ≤ gxTh (upsilon l) (ldAtR S l) ξ := by
    have := gxTh_mono (Z := upsilon l) (At := ldAtR S l) h1
    rwa [gxTh_small (gg_one_lt_of_SC hρSC).le] at this
  have hXh0 : Om 1 * gxTh (upsilon l) (ldAtR S l) ξ ≠ 0 :=
    mul_ne_zero (Om_pos one_ne_zero).ne' (Order.one_le_iff_ne_zero.1 hΘ1le)
  -- the image code
  have hB1 : 1 ≤ Bc.bcB S n ξ := by
    have := leB_le (n := n) hD1 hDξ h1; rwa [mwB_one] at this
  have hBj : Bc.bcB S n ξ < rqEM S j := by
    have := (mvB_lt_iff (k := n) hDξ hDE).2 hj; rwa [hBE] at this
  have hBΘ : gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ξ) < Om 1 := by
    rw [hΘξB]; exact (Bc.bcB_bound' S n _ hΘξc).trans (psi_lt Low.InR_Om_one _)
  -- `B_n(Ω₂·(Ω₂·ξ)) = Ω₂·(Ω₂·B_n ξ)`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hBK
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (leWe (Om (1 + 1) * ξ)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hWW := leB_mulOp2 (n := n) hDK P hPD hPdec (fun z hz => hz.2.2.trans_le le_self_add) ξ ⟨hξ, hown, hξW⟩
  rw [hBK] at hWW
  have e2 : ∀ y, Om (1 + 1) * (Om (1 + 1) * y) = ω ^ (Om (1 + 1) + Om (1 + 1)) * y := fun y => by
    rw [← mul_assoc, opow_add, gg_SC_eps ldOm2_SC]
  -- `B_n(Ω₁·(Ω₁·Θ ξ)) = Ω₁·(Ω₁·B_n(Θ ξ))`
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDOK, hBOK⟩ := mvB_add (k := n) hDO hDO
  rw [hBO] at hBOK
  have hOO := leB_mulOp2 (n := n) hDOK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le le_self_add) _ ⟨hΘ1, hΘξc⟩
  rw [hBOK, ← hΘξB] at hOO
  have e1 : ∀ y, Om 1 * (Om 1 * y) = ω ^ (Om 1 + Om 1) * y := fun y => by
    rw [← mul_assoc, opow_add, gg_SC_eps Ph.ph_SC_Om1]
  refine ⟨hXh0, Om (1 + 1) * Bc.bcB S n ξ, Om 1 * gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ξ),
    ⟨_, hBξc, hB1, ⟨j, hBj⟩, hBΘ, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [e2]; exact hWW.1
  · rw [e2, e2]; exact hWW.2
  · rw [e1]; exact hOO.1
  · rw [e1, e1]; exact hOO.2

/-- A base of shift `X` (`0` or base-relative) and exponent `e < T_{X+W}(0)` at `0`. -/
theorem rqBase0 {l X e : Ordinal.{0}} (hXs : X = 0 ∨ ∃ Xh, RqSh S l X Xh) (hXW : X + Om (1 + 1) < Om ω)
    (he : e < leTe S (X + Om (1 + 1)) 0) : RoBaseE S l X e 0 := by
  have hb0 : RoBaseE S l (X + Om (1 + 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hXW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  exact rqBase_lower hXs hb0 le_rfl he

theorem rqShC_X {l X Xh : Ordinal.{0}} (h : rqShC S l X Xh) : X + Om (1 + 1) < Om ω := by
  obtain ⟨ξ, -, -, ⟨j, hj⟩, -, rfl, -⟩ := h
  rw [← mul_add_one]
  exact rqMulW_lt_OmW (ldOm2_SC.isSuccLimit.succ_lt (hj.trans (rqEM_lt_Om2 j)))

theorem rqX_W {l X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh, rqShC S l X Xh) : X + Om (1 + 1) < Om ω := by
  rcases h with rfl | ⟨Xh, h⟩
  · rw [zero_add]; exact ldOm2_lt_OmW
  · exact rqShC_X h

/-- **Every atom `ψ_{Ω₂}(0) < s ≤ F_ξ` moves** once the codes below it move (`ξ` a code shift). -/
theorem rqAtMoveC {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {ξ : Ordinal.{0}} {j : ℕ} (hξ : GxCl (upsilon l) (ldAtR S l) ξ) (hξ1 : 1 ≤ ξ) (hj : ξ < rqEM S j)
    (hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hs0 : S.psi 0 (Om (1 + 1)) < s) (hsξ : s ≤ S.psi (leWe (Om (1 + 1) * ξ)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  rcases rqRepC hl hX hξ hξ1 hj hΘ1 s hs hsξ with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, hv⟩ := rqReadC hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, XB, hDX, hBX, hown'⟩ := rqDigMove (n := n) (l' := l') hl hX (rqShC_sh hl hX)
    (rqShC_B hl hX) hown hb hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  -- the shifts at `λ` and `λ'`
  have hXs' : X = 0 ∨ ∃ Xh, RqSh S l X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (rqShC_sh hl hX _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, rqShC S l' XB Xh := roOwn_sh hown'
  have hXBs' : XB = 0 ∨ ∃ Xh, RqSh S l' XB Xh := by
    rcases hXBs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (rqShC_sh hl' hX' _ _ h).1⟩
  have hec := roOwn_code hl hX hown
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) 0 := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left 0).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDX hBX
  obtain ⟨hD0W, hB0W⟩ := mvB_add (k := n) hD0 hDWW
  rw [Bc.bcB_zero, hBWW] at hB0W
  have hXC : X ∈ S.CSet (0 + leWe (X + Om (1 + 1))) (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) := by
    rcases hXs' with rfl | ⟨Xh, hs'⟩
    · exact CSet.zero_mem _ _
    · exact rqMem hs' (rqWX_le X 0 _) le_rfl
  have hTown : 0 + leWe (X + Om (1 + 1)) ∈ S.CSet (0 + leWe (X + Om (1 + 1)))
      (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (CSet.zero_mem _ _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hD0W hTown
  rw [hB0W] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) 0 := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) 0 := rqBase0 hXBs' (rqX_W hXBs) hBeT
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  obtain ⟨e1', -, -, -⟩ := rqOwnRead hl' hX' (rqShC_sh hl' hX') hown' (A' + 1) hb' hA'1 (ldBlk_zero hA' hρ')
  rw [zero_add] at e1'
  -- the move of the atom
  have hcown := rqOwn_own hl hX (rqShC_sh hl hX) hown hb
  rw [zero_add] at hcown
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hcown
  obtain ⟨hBH, hBA⟩ := rqOwn_mem hl' hX' (rqShC_sh hl' hX') hown' hb'
  rw [zero_add] at hBH hBA
  obtain ⟨hDE, hBE⟩ := rqEM_B (S := S) (n := n) (j + 1)
  have hFE : S.psi (leWe (Om (1 + 1) * ξ)) (Om (1 + 1)) ≤ rqEM S (j + 1) :=
    (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (mul_le_mul_right hj.le _))).1
  have hvθ : 1 + v ≤ ConjT.th S :=
    (hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) hv).le.trans rnG_le_th
  have hownd : A + (1 + v) ∈ S.CSet (A + (1 + v)) (S.psi (A + (1 + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  obtain ⟨hD1v, hB1v⟩ := mvB_add (k := n) hD1 hDv
  rw [mwB_one] at hB1v
  refine ⟨hDs, by rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩, ?_, by rw [e1, add_assoc]; exact hbX _ hvθ, ?_⟩
  · have h := leB_le (n := n) hDs hDE (hsξ.trans hFE)
    rw [hBE] at h
    exact (h.trans_lt (rqEM_lt_th _)).trans ljTh_lt_ThP
  · rw [hBs, e1', e1, add_assoc A, hBψ _ hD1v hownd hvθ, hB1v, add_assoc]

/-- **`LjAtMove` for the atoms `s ≤ θ` above every `EM_j`.** -/
def RqAtMove5 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, (∀ j : ℕ, rqEM S j < s) → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem rqOO_lt_EM1 {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1)) < rqEM S 1 := by
  have hαΩ : α < Om 1 := hα.trans roOO_lt_Om1
  have hαE : α < rqEM S 1 := hαΩ.trans (rqEM_lt_succ 0)
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_lt ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hαΩ))
    (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hαE)))

/-- **`RqAtMove5` gives `RoAtMove4`.** -/
theorem rqAtMove4_of5 (h : RqAtMove5 S) : RoAtMove4 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsα hsθ IH
  have hF1 : S.psi (leWe (Om (1 + 1) * (1 : Ordinal.{0}))) (Om (1 + 1)) < s :=
    hsα 1 le_rfl (one_lt_omega0.trans_le (by
      have := opow_le_opow_right (a := ω) omega0_pos (one_lt_omega0 : (1 : Ordinal.{0}) < ω).le
      rwa [opow_one] at this))
  have hs0 : S.psi 0 (Om (1 + 1)) < s :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) zero_le).1 hF1
  have hΩs : Om (1 : Ordinal.{0}) < s := (psiS_bounds (S := S) 0 1).1.trans hs0
  by_cases hex : ∃ j, s ≤ rqEM S j
  · classical
    set j0 := Nat.find hex with hj0_def
    have hj0 : s ≤ rqEM S j0 := Nat.find_spec hex
    rcases j0.eq_zero_or_eq_succ_pred with h0 | hsucc
    · rw [h0] at hj0; exact absurd hj0 (not_le.2 hΩs)
    · set i := j0.pred with hi
      have hmin : ¬ s ≤ rqEM S i := Nat.find_min hex (by omega)
      have hEs : rqEM S i < s := lt_of_not_ge hmin
      have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
      have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
      obtain ⟨hX, -⟩ := ldOwnA hR.1 h2
      have hEc := rqEM_code (S := S) hR.1 hX i
      obtain ⟨-, -, -, hΘE, -⟩ := IH _ hEc hEs
      have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
      have hΘE1 : gxTh (upsilon l) (ldAtR S l) (rqEM S i) < Om 1 :=
        hΘE.trans (hLw.trans (psi_lt Low.InR_Om_one _))
      have hsξ : s ≤ S.psi (leWe (Om (1 + 1) * rqEM S i)) (Om (1 + 1)) := by
        rw [hsucc] at hj0; exact hj0
      exact rqAtMoveC hR h1 hr hl' hB hEc ((Order.one_le_iff_pos.2 (Om_pos one_ne_zero)).trans (rqOm1_le_EM i))
        (rqEM_lt_succ i) hΘE1 s hs hs0 hsξ IH
  · push Not at hex
    exact h n l l' hR h1 hr hl' hB hm hF hK s hs hex hsθ IH

/-- **`RoAtMove4` gives `RqAtMove5`.** -/
theorem rqAtMove5_of (h : RoAtMove4 S) : RqAtMove5 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsj hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (fun _ _ hα => (rqOO_lt_EM1 hα).trans (hsj 1)) hsθ IH

/-- **The road with `RqAtMove5`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rqRoadG (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RqAtMove5 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  roRoadF hU hO hL hV hN hlh (fun hν => rqAtMove4_of5 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `rqRoadG` follows from that of `Rn.rnRoadD`. -/
theorem rqRoadG_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RqAtMove5 S :=
  fun hν => rqAtMove5_of (roAtMove4_of (hat hν))

end Googology.Trans.PoR.InaccPsi.R2.Rq
