import Googology.Trans.PoR.InaccPsi.R2.LeEMove
import Googology.Trans.PoR.InaccPsi.R2.LjExp

/-!
# The reading moves on `[ψ_{Ω₂}(Ω₂^{Ω₂}), θ⁺)` from the moves of the atoms in `[ψ_{Ω₂}(Ω₂^{Ω₂}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = ψ_{Ω₂}(Ω_ω + 1)` (`ljThP`), `F_W = ψ_{Ω₂}(Ω₂^{Ω₂})`,
`A = A_{η_λ}`, `ρ_λ = ψ_{Ω₁}(A)`, `δ_λ = υ_{λ+ω+1}`, `Θ_λ` the reading, `At_λ` the atoms of the hull.

* `ljAt_le_th` (**every atom below `θ⁺` is at most `θ`**), `ljTheta_ThP` (**`Θ_λ(θ⁺) ≤ ψ_{Ω₁}(A + θ + 1)`**),
  `ljTheta_lt_delta` (**`Θ_λ(m) < δ_λ` for every `m ≤ θ⁺`**, so the codes in `(θ·ω, θ⁺)` need no closed point past
  `δ_λ`);
* `LjAtMove S` (a hypothesis name): **the atoms `s ∈ At_λ` with `F_W ≤ s ≤ θ` move** once the codes below `s` move;
* `ljThMove_P` (**the reading move `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at every code `F_W ≤ m_λ < θ⁺`** from
  `LjAtMove`; the code of `λ'` is `B_n m_λ` by `Lj.ljExp_move`).

No new axiom.  New definitions: `ljThP`, the hypothesis name `LjAtMove`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-! ## `θ⁺` and the atoms below it -/

/-- `θ⁺ = ψ_{Ω₂}(Ω_ω + 1)`, the atom after `θ`. -/
noncomputable def ljThP (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om ω + 1) (Om (1 + 1))

theorem ljThP_SC : SC (ljThP S) := SC_psi (InR_Om_succ 1) _

theorem ljThP_lt_Om2 : ljThP S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem ljOm1_lt_ThP : Om (1 : Ordinal.{0}) < ljThP S := (psiS_bounds (S := S) _ 1).1

theorem ljTh_lt_ThP : ConjT.th S < ljThP S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_one _) (ConjT.OmW_mem S _ _)

theorem ljThW_lt_ThP : ConjT.th S * ω < ljThP S := by
  have h1 : ConjT.th S + 1 < ljThP S := ljThP_SC.isSuccLimit.succ_lt ljTh_lt_ThP
  have := ljThP_SC.2 0 ljThP_SC.1 _ h1
  rwa [veblen_zero_apply, ← ljThW_eq S] at this

theorem ljFWW_lt_ThP : leFWW S < ljThP S := leFWW_lt_th.trans ljTh_lt_ThP

/-- **Every atom below `θ⁺` is at most `θ`.** -/
theorem ljAt_le_th {l s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hsP : s < ljThP S) : s ≤ ConjT.th S := by
  obtain ⟨a, -, -, rfl⟩ := hs
  rcases le_or_gt a (Om ω) with ha | ha
  · exact (psi_mono (S := S) (InR_Om_succ 1) ha).1
  · exact absurd hsP (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (Order.add_one_le_of_lt ha)).1)

/-! ## `Θ_λ < δ_λ` below `θ⁺` -/

section Bound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))

include hl hX hown

/-- **`Θ_λ(θ⁺) ≤ ψ_{Ω₁}(A + θ + 1)`.** -/
theorem ljTheta_ThP :
    gxTh (upsilon l) (ldAtR S l) (ljThP S) ≤ S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + 1) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hWA : Om ω ≤ A := le_self_add
  have hAθ : A + ConjT.th S ∈ S.CSet (A + ConjT.th S + 1) (S.psi (A + ConjT.th S + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown)
      (ConjT.th_mem S (hWA.trans_lt ((lt_add_of_pos_right A (sfTh_pos S)).trans (lt_add_one _))))
  have hlt : S.psi (A + ConjT.th S) (Om 1) < S.psi (A + ConjT.th S + 1) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_one _) hAθ
  have hρX : upsilon l < S.psi (A + ConjT.th S + 1) (Om 1) := by
    rw [← hρ]
    refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one le_self_add).1 hlt
  refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) hρX fun t ht htP => ?_
  have htθ := ljAt_le_th ht htP
  rw [← ldTheta hl hX ((htθ.trans_lt (psi_lt (InR_Om_succ 1) _)).le)]
  refine ((ldTheta_le_psi hl hX hown t).trans ?_).trans_lt hlt
  exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 htθ)).1

/-- **`Θ_λ(m) < δ_λ` for every `m ≤ θ⁺`.** -/
theorem ljTheta_lt_delta {m : Ordinal.{0}} (hm : m ≤ ljThP S) : cdTheta S l m < cdDelta l := by
  obtain ⟨-, hιl, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have h1 : cdTheta S l m ≤ S.psi (A + ConjT.th S + 1) (Om 1) := by
    refine (cdTheta_mono S l hm).trans ?_
    rw [ldTheta hl hX ljThP_lt_Om2.le]
    exact ljTheta_ThP hl hX hown
  have h2 : S.psi (A + ConjT.th S + 1) (Om 1) ≤ upsilon (l + 2) := by
    have hι : Bt.iota S (cdEta S l + 2) ≤ l + 2 := by
      have := ldIota_add_le (S := S) (cdEta S l) 2
      rwa [hιl] at this
    calc S.psi (A + ConjT.th S + 1) (Om 1) ≤ S.psi (ConjT.Aη S (cdEta S l + 2)) (Om 1) := by
          rw [Bt.A_add, add_assoc]
          refine (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 ?_)).1
          rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
          exact (add_le_add_iff_left _).2 (Order.one_le_iff_pos.2 (sfTh_pos S))
      _ = upsilon (Bt.iota S (cdEta S l + 2)) := (Bt.ups_iota S _).symm
      _ ≤ upsilon (l + 2) := upsilon_normal.monotone hι
  refine (h1.trans h2).trans_lt (upsilon_normal.strictMono ?_)
  calc l + 2 < l + ω := (add_lt_add_iff_left l).2 (by exact_mod_cast natCast_lt_omega0 2)
    _ < l + ω + 1 := lt_add_one _

end Bound

/-! ## The atoms in `[F_W, θ]` and the reading moves below `θ⁺` -/

/-- **The atoms `F_W ≤ s ≤ θ` move** (at the restarts `λ` of the range with `F_W ≤ m_λ < θ⁺`) once the codes below
`s` move. -/
def LjAtMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, leFWW S ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem ljExp_zero : cdExp (0 : Ordinal.{0}) = 0 := by
  unfold cdExp
  have hu : {e : Ordinal.{0} | ω ^ e ∣ (0 : Ordinal.{0})} = Set.univ := by
    ext e; simp
  rw [hu]; exact csSup_of_not_bddAbove not_bddAbove_univ |>.trans (by simp)

/-- **The reading move at every code `F_W ≤ m_λ < θ⁺`**, given `LjAtMove`. -/
theorem ljThMove_P (hat : LjAtMove S) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hm : upsilon l < cdCode S l) (hF : leFWW S ≤ cdCode S l)
    (hK : cdCode S l < ljThP S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  have he : ggGam < cdExp (cdEta S l) :=
    ldGam_lt_Fw.trans_le (ldFw_le_G2.trans (leG2_le_Fw.trans (leFw_le_FWW.trans
      (hF.trans (cdCodeOf_le_exp S _)))))
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hη0 : η ≠ 0 := by
      intro h0
      have : e = 0 := by rw [he_def, h0, ljExp_zero]
      rw [this] at h
      exact h (Om_pos (by simp))
    have hle : ljThP S ≤ cdPi S η := by
      refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
      show Om ω + 1 ≤ Om ω + ConjT.th S * η
      refine (add_le_add_iff_left _).2 ?_
      calc (1 : Ordinal.{0}) ≤ ConjT.th S := Order.one_le_iff_pos.2 (sfTh_pos S)
        _ = ConjT.th S * 1 := (mul_one _).symm
        _ ≤ ConjT.th S * η := mul_le_mul_right (Order.one_le_iff_ne_zero.2 hη0) _
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heP : e < ljThP S := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨η', -, hBη', hη', hexp'⟩ := ljExp_move hl.1 h1 h2 hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDF, hBF⟩ := leB_FWW (S := S) (n := n)
  -- every atom below `θ⁺` moves
  have hatom : ∀ s ∈ ldAtR S l, s < ljThP S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
    intro s hs hsP IHx
    rcases lt_or_ge s (leFWW S) with hsF | hsF
    · obtain ⟨hDs, hBs, hBsF, hth, hEq⟩ := leAtMove_FWW hl hl' hX hX' hown hA' hρA hρA' hbX hBψ s hs hsF
        (fun x hx hxs => by
          obtain ⟨hD, hc, -, h4, h5⟩ := IHx x hx hxs
          refine ⟨hD, hc, ?_, h4, h5⟩
          have := (mvB_lt_iff (k := n) hD hDF).2 (hxs.trans hsF)
          rwa [hBF] at this)
      exact ⟨hDs, hBs, hBsF.trans ljFWW_lt_ThP, hth, hEq⟩
    · exact hat n l l' hR h1 hr hl' hB hm hF hK s hs hsF (ljAt_le_th hs hsP) IHx
  obtain ⟨hDe, -, hBeP, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw ljThP_SC ljOm1_lt_ThP.le hatom e hge heP
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeP.trans ljThP_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeP.trans ljThP_lt_Om2).le]
  exact hEq.symm

end Googology.Trans.PoR.InaccPsi.R2.Lj
