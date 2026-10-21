import Googology.Trans.PoR.InaccPsi.R2.MxAtom

/-!
# `B_n` on the atoms `ψ_{Ω₂}(α)` and on their readings `ψ_{Ω₁}(A + 1 + α)`: the reading moves below `ψ_{Ω₂}(Ω₁)`

`B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW` (`B_n = val ∘ σ ∘ nf`), `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`,
`K = ψ_{Ω₂}(Ω₁)`, `GxCl ρ (mxAt S ρ)` the codes over `ρ` with the atoms `ψ_{Ω₂}(α)`, `α < ρ` (`R2.MxAtom`).

* `mxB_psi_add` (**`B_n(P(η)) = ψ_{Ω₁}(A')` and `B_n(ψ_{Ω₁}(A_η + d)) = ψ_{Ω₁}(A' + B_n d)`** for every
  `d < ψ_{Ω₁}(A_η + d)`, `A'` own, at a good `η` in the window: the normal form of `ψ_{Ω₁}(A_η + d)` is
  `ψ^S_0(a₁)` whose rest is the rest of `A_η` followed by the normal form of `d`; `Mx.mxB_psi1` is `d = 1`);
* `mxNf_psi2` (the normal form of `ψ_{Ω₂}(α)`, `α` own for `ψ_{Ω₂}`, is `ψ^S_1(a)` with `|a| = α`), `mxB_atom`
  (**`B_n(ψ_{Ω₂}(α)) = ψ_{Ω₂}(B_n α)`** for `α ∈ MvD` own for `ψ_{Ω₂}`);
* `mxAt_move` (**the hull transport below `K`**, by induction on the code): for own `A`, `A'` with `ψ_{Ω₁}(A) = ρ`,
  `ψ_{Ω₁}(A') = ρ' = B_n ρ`, a strongly critical `X` with `ρ < X < L(ω)` above every `ψ_{Ω₁}(A + 1 + α)`, `α < ρ`,
  and `B_n(ψ_{Ω₁}(A + d)) = ψ_{Ω₁}(A' + B_n d)` for `d < ρ`: a code `x < K` over `ρ` has `B_n x` a code `< K` over
  `ρ'`, and **`Θ_{ρ'}(B_n x) = B_n(Θ_ρ(x))`** (the new case is the atom `x = ψ_{Ω₂}(α)`: `Θ_ρ(x) = ψ_{Ω₁}(A + 1 + α)`,
  `Mx.mxTh_atom`);
* `mxThMove_K` (**`MxThMove` at every long code `m_λ < ψ_{Ω₂}(Ω₁)`**, no hypothesis);
* `MxThMoveK S` (a hypothesis name): `MxThMove` at the codes `ψ_{Ω₂}(Ω₁) ≤ m_λ ≤ θ`; `mxThMove_of_K`
  (**`MxThMoveK` gives `MxThMove`**), `mxThMoveK_of` (`MxThMove` gives `MxThMoveK`), `mxRoad4`.

No new axiom.  New definition: the hypothesis name `MxThMoveK`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-! ## `B_n` on `ψ_{Ω₁}(A_η + d)` -/

/-- **`B_n(P(η)) = ψ_{Ω₁}(A')`, `B_n(ψ_{Ω₁}(A_η + d)) = ψ_{Ω₁}(A' + B_n d)`**, `A'` own, `d < ψ_{Ω₁}(A_η + d)`. -/
theorem mxB_psi_add {n : ℕ} {η d : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hd : d < S.psi (ConjT.Aη S η + d) (Om 1)) (hhi : S.psi (ConjT.Aη S η + d) (Om 1) < Bc.bcC S (n + 1)) :
    ∃ A', A' ∈ S.CSet A' (S.psi A' (Om 1)) ∧ Bc.bcB S n (Pv S η) = S.psi A' (Om 1) ∧
      Bc.bcB S n (S.psi (ConjT.Aη S η + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
  have hP1 : Pv S η ≤ S.psi (ConjT.Aη S η + d) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + d)).1
  have hAL : ConjT.Aη S η < S.Lam := (sfA_lt (hP1.trans_lt hhi)).2
  have hown := sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := sfArg_le (sfOwn_alpha S n) hown hlo
  have hown1 : ConjT.Aη S η + d ∈ S.CSet (ConjT.Aη S η + d) (S.psi (ConjT.Aη S η + d) (Om 1)) := by
    have h1 := (psi_mono (S := S) Low.InR_Om_one
      (le_self_add : ConjT.Aη S η ≤ ConjT.Aη S η + d)).2 hown
    exact CSet.add_mem h1 (CSet.of_lt hd)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : S.psi (ConjT.Aη S η + d) (Om 1) < Nc.ncL S ω := hhi.trans hLw
  have hdL : d < Nc.ncL S ω := hd.trans hx1
  have hDe : bcD S (bcNf S d) := bcD_nf S hdL
  have hve : val S (bcNf S d) = d := val_nf S hdL
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  obtain ⟨a1, ha1, hva1⟩ := sfNf_psi hown1 (bcD_nf S hx1).1 (val_nf S hx1)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hD1 : bcD S (psiS Term.zero a1) := ha1 ▸ bcD_nf S hx1
  have hN := hD.1
  have hN1 := hD1.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hA1W : val S a1 < bcAlphaW S := hD1.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hlo1 : bcAlpha S (n + 1) ≤ val S a1 := by rw [hva1]; exact hαA.trans le_self_add
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  have hB1 := sfB_psi (n := n) hN1 hlo1 hA1W
  rw [hva] at hB0
  rw [hva1] at hB1
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hpre1 := (bc_pre_iff S hN1.2.1 hA1W).2 hlo1
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hvρ1 : val S a1 = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) := by
    have := val_of_pre S hN1.2.1 hpre1; rwa [sfPre_len] at this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have hDρ : bcD S (bcDrop (n + 3) a) := bcD_drop hDa (n + 3)
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + d := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + d) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 hDe.1
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) (bcNf S d) :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, hve, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + Bc.bcB S n d := by
    rw [hρ1, bcSig_addNF (k := n) hDρ hDe,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) (bc_NF (k := n) hDe)).2.1]
    rfl
  refine ⟨bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)), ?_, hB0, ?_⟩
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rw [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW
        (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)))) := sem_of_NF hσN
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW] at h2
    exact h2
  · rw [hB1, hσ1, add_assoc]

/-! ## `B_n` on the atoms -/

theorem mxPsi2_mem {α : Ordinal.{0}} (hα : α ∈ ⋃ a, S.CSet a 0) :
    S.psi α (Om (1 + 1)) ∈ ⋃ a, S.CSet a 0 := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hα
  refine Set.mem_iUnion.2 ⟨max c (α + 1), ?_⟩
  exact CSet.psi_mem ((lt_add_one α).trans_le (le_max_right _ _)) (InR_Om_succ 1) (mxOm2_mem _ _)
    (CSet_mono (le_max_left _ _) le_rfl hc)

/-- The normal form of `ψ_{Ω₂}(α)`, `α ∈ Cl(α, ψ_{Ω₂}(α))`, is `ψ^S_1(a)` with `|a| = α`. -/
theorem mxNf_psi2 {α : Ordinal.{0}} (hown : α ∈ S.CSet α (S.psi α (Om (1 + 1)))) {t : Term} (ht : NF t)
    (hv : val S t = S.psi α (Om (1 + 1))) : ∃ a, t = psiS Bc.tOne a ∧ val S a = α := by
  have hSC : SC (val S t) := hv ▸ SC_psi (InR_Om_succ 1) α
  have hb := psiS_bounds (S := S) α 1
  have hsc := isSC_of_SC (S := S) ht hSC
  have h22 : Om (2 : Ordinal.{0}) = Om (1 + 1) := by rw [one_add_one_eq_two]
  cases t with
  | psiS s a =>
    have hbs := val_psiS_bounds S s a
    rw [hv] at hbs
    have hs2 : val S s < 1 + 1 := Om_lt_Om.1 (hbs.1.trans hb.2)
    have hs1 : 1 < val S s + 1 := Om_lt_Om.1 (hb.1.trans hbs.2)
    have hvs : val S s = 1 :=
      le_antisymm (Order.lt_add_one_iff.1 hs2) (Order.lt_add_one_iff.1 hs1)
    have hst : s = Bc.tOne := eq_of_val_eq S ht.1 NF_tOne (by rw [hvs, val_tOne])
    subst hst
    refine ⟨a, rfl, ?_⟩
    have h : Sem S (psiS Bc.tOne a) := sem_of_NF ht
    have hsem := h.2.2
    rw [val_tOne] at hsem
    have hc := compare_psi (InR_Om_succ 1) hsem hown
    have hv' : S.psi (val S a) (Om (1 + 1)) = S.psi α (Om (1 + 1)) := by
      have := hv; simp only [val, val_tOne] at this; exact this
    rw [hv', compare_eq_iff_eq.2 rfl] at hc
    exact compare_eq_iff_eq.1 hc.symm
  | om a =>
    exfalso
    have h1 : Om 1 < Om (val S a) := by
      have := hb.1; rw [← hv] at this; exact this
    have h2 : Om (val S a) < Om (1 + 1) := by
      have := hb.2; rw [← hv] at this; exact this
    have e1 := Om_lt_Om.1 h1
    have e2 := Order.lt_add_one_iff.1 (Om_lt_Om.1 h2)
    exact absurd e1 (not_lt.2 e2)
  | psiI n a =>
    exfalso
    have h2 := Om_two_le_psiI (S := S) n a
    rw [h22, hv] at h2
    exact absurd hb.2 (not_lt.2 h2)
  | inacc n =>
    exfalso
    have h2 := mxOm2_lt_I (S := S) n
    have : val S (inacc n) = S.I n := rfl
    rw [← this, hv] at h2
    exact absurd hb.2 (not_lt.2 h2.le)
  | inaccW =>
    exfalso
    have h2 := mxOm2_lt_Iw (S := S)
    have : val S inaccW = S.Iw := rfl
    rw [← this, hv] at h2
    exact absurd hb.2 (not_lt.2 h2.le)
  | zero => exact absurd hsc (by simp [isSC])
  | add _ _ => exact absurd hsc (by simp [isSC])
  | phi _ _ => exact absurd hsc (by simp [isSC])

/-- **`B_n(ψ_{Ω₂}(α)) = ψ_{Ω₂}(B_n α)`** for `α ∈ MvD` with `α ∈ Cl(α, ψ_{Ω₂}(α))`, and `ψ_{Ω₂}(α) ∈ MvD`. -/
theorem mxB_atom {n : ℕ} {α : Ordinal.{0}} (hDα' : MvD S α) (hown : α ∈ S.CSet α (S.psi α (Om (1 + 1)))) :
    MvD S (S.psi α (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi α (Om (1 + 1))) = S.psi (Bc.bcB S n α) (Om (1 + 1)) := by
  have hmem := mxPsi2_mem hDα'.1
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hmem
  obtain ⟨a, ht, hva⟩ := mxNf_psi2 hown hN hv
  have hNa : NF a := by rw [ht] at hN; exact hN.2.1
  have ha : Bc.bcNf S α = a := by rw [← hva]; exact Bc.bcNf_val S hNa
  have hDα := hDα'.2
  refine ⟨⟨hmem, ?_⟩, ?_⟩
  · rw [ht]
    refine ⟨ht ▸ hN, bcArgsLt_of_free bcFree_tOne, ha ▸ hDα.2, fun h => absurd h tOne_ne_zero⟩
  · unfold Bc.bcB
    rw [ht, bcSig_psiS_ne tOne_ne_zero, bcSig_free bcFree_tOne, ← ha]
    show S.psi _ (Om (val S Bc.tOne + 1)) = _
    rw [val_tOne]

/-! ## The hull transport below `K` -/

/-- **The hull transport below `K = ψ_{Ω₂}(Ω₁)`.** -/
theorem mxAt_move {n : ℕ} {ρ ρ' A A' X : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ : S.psi A (Om 1) = ρ) (hρ' : S.psi A' (Om 1) = ρ')
    (hB : Bc.bcB S n ρ = ρ') (hX : SC X) (hρX : ρ < X) (hXL : X < Nc.ncL S ω)
    (hbX : ∀ α, α < ρ → S.psi (A + 1 + α) (Om 1) < X)
    (hBψ : ∀ d, d < ρ → Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ x, GxCl ρ (mxAt S ρ) x → x < mxK S → MvD S x ∧ GxCl ρ' (mxAt S ρ') (Bc.bcB S n x) ∧
      Bc.bcB S n x < mxK S ∧ gxTh ρ (mxAt S ρ) x < X ∧
      gxTh ρ' (mxAt S ρ') (Bc.bcB S n x) = Bc.bcB S n (gxTh ρ (mxAt S ρ) x) := by
  have hρSC : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC ρ' := hρ' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : ρ' < Om 1 := hρ' ▸ psi_lt Low.InR_Om_one A'
  have hAt : GxAt (mxAt S ρ) := mxAt_GxAt ρ
  have hAt' : GxAt (mxAt S ρ') := mxAt_GxAt ρ'
  have hρL : ρ < Nc.ncL S ω := hρX.trans hXL
  have hXp : IsPrincipal (· + ·) X := hX.isPrincipal
  have hKp : IsPrincipal (· + ·) (mxK S) := mxK_SC.isPrincipal
  have hKo : ∀ a < mxK S, ω ^ a < mxK S := fun a ha => by
    have := (mxK_SC (S := S)).2 0 (mxK_SC (S := S)).1 a ha; rwa [veblen_zero_apply] at this
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := hX.2 0 hX.1 a ha; rwa [veblen_zero_apply] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxK
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · -- a countable code: below `ρ`
    have hxρ : x < ρ := GxCl.lt_of_lt_Om1 hρSC hAt hx hx1
    have hxL : x < Nc.ncL S ω := hxρ.trans hρL
    have hBx : Bc.bcB S n x < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hxL hρL).2 hxρ
    refine ⟨mvD_of_lt hxL, GxCl.small hBx, hBx.trans (hρ'1.trans mxOm1_lt_K), ?_, ?_⟩
    · rw [gxTh_small hxρ.le]; exact hxρ.trans hρX
    · rw [gxTh_small hxρ.le, gxTh_small hBx.le]
  · -- `Ω₁`
    subst hx1
    obtain ⟨hD, hBO⟩ := mvB_Om1 (S := S) (k := n)
    refine ⟨hD, by rw [hBO]; exact GxCl.om, by rw [hBO]; exact mxOm1_lt_K, ?_, ?_⟩
    · rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρX
    · rw [hBO, gxTh_Om1 hρSC hρ1 hAt, gxTh_Om1 hρ'SC hρ'1 hAt', hB]
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    by_cases hSCx : SC x
    · -- an atom `ψ_{Ω₂}(α)`
      obtain ⟨α, hαρ, rfl⟩ := gxSC_atom hρ1 hx hSCx hx1
      have hα1 : α < Om 1 := hαρ.trans hρ1
      have hαL : α < Nc.ncL S ω := hαρ.trans hρL
      obtain ⟨hD, hBa⟩ := mxB_atom (n := n) (mvD_of_lt hαL)
        (CSet.of_lt (hα1.trans (psiS_bounds (S := S) α 1).1))
      have hBα : Bc.bcB S n α < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hαL hρL).2 hαρ
      have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
      have h1α : 1 + α < ρ := hρSC.isPrincipal (gg_one_lt_of_SC hρSC) hαρ
      refine ⟨hD, by rw [hBa]; exact GxCl.atom ⟨_, hBα, rfl⟩, by rw [hBa]; exact mxAt_lt_K (hBα.trans hρ'1),
        ?_, ?_⟩
      · rw [mxTh_atom hA hρ α hαρ]; exact hbX α hαρ
      · rw [hBa, mxTh_atom hA' hρ' _ hBα, mxTh_atom hA hρ α hαρ,
          show A + 1 + α = A + (1 + α) from add_assoc _ _ _, hBψ _ h1α, Bc.bcB_add h1L hαL, mwB_one,
          add_assoc]
    by_cases hE : ω ^ x = x
    · -- `x = φ(a, b)` with `a, b < x`
      obtain ⟨hdec, hax, hbx, -⟩ := mxDec hE (pos_iff_ne_zero.2 hx0) hSCx
      generalize invVeblen₁ x = a at hdec hax
      generalize invVeblen₂ x = b at hdec hbx
      obtain ⟨hga, hgb⟩ := gxDecV hρSC.1 hAt hx a b hdec hbx
      obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
      obtain ⟨hDb, hgb', hbK, htb, heb⟩ := IH b hbx hgb (hbx.trans hxK)
      have hax' : a < veblen a b := by rw [hdec]; exact hax
      have hbx' : b < veblen a b := by rw [hdec]; exact hbx
      obtain ⟨hDx, hBx⟩ := mwB_phi (k := n) hDa hDb hax' hbx'
      have hth : gxTh ρ (mxAt S ρ) (veblen a b) =
          veblen (gxTh ρ (mxAt S ρ) a) (gxTh ρ (mxAt S ρ) b) := gxTh_phi hρSC hAt a hga b hgb
      have hta' : gxTh ρ (mxAt S ρ) a < veblen (gxTh ρ (mxAt S ρ) a) (gxTh ρ (mxAt S ρ) b) := by
        rw [← hth]; exact gxTh_lt hga hax'
      have htb' : gxTh ρ (mxAt S ρ) b < veblen (gxTh ρ (mxAt S ρ) a) (gxTh ρ (mxAt S ρ) b) := by
        rw [← hth]; exact gxTh_lt hgb hbx'
      obtain ⟨-, hBt⟩ := mwB_phi (k := n) (mvD_of_lt (hta.trans hXL)) (mvD_of_lt (htb.trans hXL)) hta' htb'
      rw [← hdec]
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GxCl.phi hga' hgb'
      · rw [hBx]; exact (mxK_SC (S := S)).2 _ haK _ hbK
      · rw [hth]; exact hX.2 _ hta _ htb
      · rw [hBx, gxTh_phi hρ'SC hAt' _ hga' _ hgb', hea, heb, hth, hBt]
    · -- `x` is not an `ε`-number: `x = ω^a` or `x = ω^a + r`
      obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
      have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
      have hxlt : x < ω ^ a * ω := by
        rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hga : GxCl ρ (mxAt S ρ) a := by rw [ha]; exact (gxDec hρSC hAt x hx).2
      have hgl : GxCl ρ (mxAt S ρ) (ω ^ a) := GxCl.opow hρSC.1 hga
      have hgr : GxCl ρ (mxAt S ρ) (x - ω ^ a) := (gxDec hρSC hAt x hx).1 _ hgl hlead
      have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
      by_cases hr : x - ω ^ a = 0
      · have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
        have hax : a < x := by
          rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
          · rwa [hxa] at h
          · exfalso; apply hE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
        obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
        have hne : ω ^ a ≠ a := fun h => hax.ne (h.symm.trans hxa)
        obtain ⟨hDx, hBx⟩ := mvB_opow (k := n) hDa hne
        subst hxa
        have hta' : ω ^ gxTh ρ (mxAt S ρ) a < X := hXo _ hta
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.opow hρ'SC.1 hga'
        · rw [hBx]; exact hKo _ haK
        · rw [gxTh_opow hρSC hAt hga]; exact hta'
        · rw [hBx, gxTh_opow hρ'SC hAt' hga', hea, gxTh_opow hρSC hAt hga, Tp.tpOpowB (hta'.trans hXL)]
      · obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
        rw [← hr'] at hgr hdec hr
        have hlx : ω ^ a < x := by
          rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
        have hrx : r < x := by
          refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
          have h' : ω ^ a + x = x := by
            calc ω ^ a + x = ω ^ a + r := by rw [e]
              _ = x := hdec
          have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
          exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
        obtain ⟨hDl, hgl', hlK, htl, hel⟩ := IH _ hlx hgl (hlx.trans hxK)
        obtain ⟨hDr, hgr', hrK, htr, her⟩ := IH r hrx hgr (hrx.trans hxK)
        obtain ⟨hDx, hBx⟩ := mvB_add (k := n) hDl hDr
        have hts : gxTh ρ (mxAt S ρ) (ω ^ a + r) = gxTh ρ (mxAt S ρ) (ω ^ a) + gxTh ρ (mxAt S ρ) r :=
          gxTh_add hρSC hAt hgl r
        rw [← hdec]
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.add hgl' hgr'
        · rw [hBx]; exact hKp hlK hrK
        · rw [hts]; exact hXp htl htr
        · rw [hBx, gxTh_add hρ'SC hAt' hgl', hel, her, hts, Bc.bcB_add (htl.trans hXL) (htr.trans hXL)]

/-! ## `MxThMove` below `K` -/

/-- `υ_{λ+1} = ψ_{Ω₁}(A_{η_λ} + θ)` at a named restart. -/
theorem mxUps_succ {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    upsilon (l + 1) = S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) := by
  obtain ⟨hg, hιl, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have e := Bt.ups_iota S (cdEta S l + 1)
  rw [Bt.iota_good hg, hιl, ← ConjT.A_succ] at e
  exact e

/-- **`MxThMove` at every long code `m_λ < ψ_{Ω₂}(Ω₁)`.** -/
theorem mxThMove_K {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < mxK S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  -- the code is `e`, below `K`
  have hWA : Om ω ≤ A := le_self_add
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : mxK S ≤ cdPi S η :=
      (psi_mono (S := S) (InR_Om_succ 1) (mxOm1_lt_OmW.le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heK : e < mxK S := hcode ▸ hK
  -- `e` is in the hull, a code with atoms
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (mxAt S (upsilon l)) e := (mxHull_iff hl hX heK).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  -- the image name
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heK.trans mxK_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the bounds `ψ_{Ω₁}(A + d) < L(n+2)` for `d < θ`
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hθ1 : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1
  have hdθ : ∀ d, d < Om 1 → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 (hd.trans hθ1).le)).1
    exact (h3.trans_lt hu1).trans hδr
  -- `A'`
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, d < upsilon l → Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hd
    have hdA : d < S.psi (A + d) (Om 1) :=
      (hpv ▸ hd : d < Pv S η).trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1
    obtain ⟨A'', hA'', hBP'', hBd⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) hdA (hdθ d (hd.trans hρ1))
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hbX : ∀ α, α < upsilon l → S.psi (A + 1 + α) (Om 1) < Bc.bcC S (n + 1) := by
    intro α hα
    rw [add_assoc]
    exact hdθ _ (Ph.ph_SC_Om1.isPrincipal one_lt_Om1 (hα.trans hρ1))
  obtain ⟨hDe, -, hBeK, -, hEq⟩ := mxAt_move (n := n) hown hA' hρA hρA' hB (Lw.lw_L_SC S _) h2 hLw hbX hBψ
    e hge heK
  -- the image code is `B_n e`
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeK.trans mxK_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', mxTheta_K hl hX heK.le, mxTheta_K hl' hX' hBeK.le, hEq]

/-- `MxThMove` at the long codes with `ψ_{Ω₂}(Ω₁) ≤ m_λ ≤ θ`. -/
def MxThMoveK (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l ≤ ConjT.th S → mxK S ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`MxThMoveK` gives `MxThMove`.** -/
theorem mxThMove_of_K (h : MxThMoveK S) : MxThMove S := by
  intro n l l' hR h1 hr hl' hB hm he hθ
  by_cases hK : cdCode S l < mxK S
  · exact mxThMove_K hR h1 hr hl' hB he hK
  · exact h n l l' hR h1 hr hl' hB hm he hθ (not_lt.1 hK)

/-- `MxThMove` gives `MxThMoveK` (so `MxThMoveK` is the weaker hypothesis). -/
theorem mxThMoveK_of (h : MxThMove S) : MxThMoveK S :=
  fun n l l' hR h1 hr hl' hB hm he hθ _ => h n l l' hR h1 hr hl' hB hm he hθ

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → MxThMoveK` and `L(ω+1) ≤ ν_C → MxEQth`.** -/
theorem mxRoad4 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveK S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad3 hU hO hL hV hN hlh (fun hν => mxThMove_of_K (hth hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Mx
