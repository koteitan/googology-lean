import Googology.Trans.PoR.InaccPsi.R2.WlLow
import Googology.Trans.PoR.InaccPsi.R2.WdSplit
import Googology.Trans.PoR.InaccPsi.R2.GaEnd

/-!
# The reading move at the codes `θ⁺ ≤ m_λ ≤ M_W` (`Rn.RnThMoveM`) from a code-free wall

`B_n = Bc.bcB S n`, `Θ_λ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = Lj.ljThP`, `M_W = Rn.rnMW = ψ_{Ω₂}(Ω_ω + Ω₂)`,
`A = A_{η_λ}`, `A' = A_{η_{λ'}}`, "window" = `CdRange λ`, `L(n+1) < ρ_λ`, `r(λ) < L(n+2)`, `λ'` a restart,
`B_n ρ_λ = ρ_{λ'}`.

`Wd.WdAtWall` is stated only at windows with `F_W ≤ m_λ < θ⁺`; `Rn.RnThMoveM` asks windows with `m_λ ≥ θ⁺`, so the
wall cannot be applied there.  `WrWallCF` is the wall with no code hypothesis.

* `WrWallCF`, `WrWallLowCF` (statement names), `wrWall_of_cf` (`WrWallCF ⇒ Wd.WdAtWall`), `wrWallCF_of_low`;
* `wrAtTh` (**the atom `θ` moves at every window**), `wrAtLow` (**every atom `s < θ⁺` moves**, given `WrWallCF`:
  `Le.leAtMove_FWW` below `F_W`, `Ux.uxAtMoveTop` below `ψ_{Ω₂}(Y₃)`);
* `wrA_big` (`Ω_ω + Ω₂ < A` above `P(Ω₂)`), `wrWin` (the window data);
* `wrAtBlk` (**the atoms `ψ_{Ω₂}(Ω_ω + c)`, `c < M_W`, move**: block law `Ro.roThW_A` with `Wl.wlThVal` at `λ`
  and `λ'`, `Ld.ldB_psi_add`);
* `wrThMW` (**`Θ_λ(M_W) = ψ_{Ω₁}(A + θ + Ω₁)`**);
* `wrMid` (**`WrWallCF ⇒ Rn.RnThMoveM`**: `Ld.ldGxStepRec` with the bound `M_W`, and the code `M_W` by `wrThMW`);
* `wrImgMove_iff` (the move of own top-law images is the atom move itself).

No new axiom.  New definitions: the statement names `WrWallCF`, `WrWallLowCF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sf Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-- `Ω_ω ∈ MvD` and `B_n Ω_ω = Ω_ω`. -/
theorem wrB_OmW {n : ℕ} : MvD S (Om ω) ∧ Bc.bcB S n (Om ω) = Om ω := by
  have h : Bc.bcD S Bc.tW := Bc.bcD_free Bc.NF_tW Bc.bcFree_tW
  rw [← Bc.val_tW (S := S)]
  exact ⟨mvD_of_term h, by rw [mvB_term h, Bc.bcSig_free Bc.bcFree_tW]⟩

/-- **The code-free wall**: `Wd.WdAtWall` without the code hypotheses `ρ_λ < m_λ`, `F_W ≤ m_λ < θ⁺`. -/
def WrWallCF (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **The code-free wall below `θ`** (the atoms `ψ_{Ω₂}(Y₃) ≤ s < θ`). -/
def WrWallLowCF (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s < ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- The code-free wall gives `Wd.WdAtWall`. -/
theorem wrWall_of_cf (h : WrWallCF S) : Wd.WdAtWall S :=
  fun n l l' hR h1 hr hl' hB _ _ _ s hs hsY hsθ IH => h n l l' hR h1 hr hl' hB s hs hsY hsθ IH

/-- `P(Ω₂) < L(n+1)`. -/
theorem wrP2_lt (n : ℕ) : Pv S (Om (1 + 1)) < Bc.bcC S n := by
  have h0 : Nc.ncL S ((0 : ℕ) : Ordinal.{0}) ≤ Bc.bcC S n := Qq.qqL_mono (S := S) (Nat.zero_le (n + 1))
  rw [Nat.cast_zero] at h0
  exact (Ga.gaEnd_Om2 (S := S) le_rfl).2.2.2.trans_le h0

/-- **`Ω_ω + Ω₂ < A`** whenever `P(Ω₂) < ψ_{Ω₁}(A)`. -/
theorem wrA_big {A : Ordinal.{0}} (h : Pv S (Om (1 + 1)) < S.psi A (Om 1)) : Om ω + Om (1 + 1) < A := by
  by_contra hc
  push Not at hc
  have h2 : Om ω + Om (1 + 1) ≤ ConjT.Aη S (Om (1 + 1)) := by
    unfold ConjT.Aη
    exact (add_le_add_iff_left _).2 (le_mul_right _ (sfTh_pos S))
  have h3 : S.psi A (Om 1) ≤ Pv S (Om (1 + 1)) := (psi_mono (S := S) Low.InR_Om_one (hc.trans h2)).1
  exact absurd (h.trans_le h3) (lt_irrefl _)

/-- The window data: `P(Ω₂) < ρ_λ, ρ_{λ'}`. -/
theorem wrP2_win {n : ℕ} {l l' : Ordinal.{0}} (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    Pv S (Om (1 + 1)) < upsilon l ∧ Pv S (Om (1 + 1)) < upsilon l' := by
  have hP2 := wrP2_lt (S := S) n
  have hPρ := hP2.trans h1
  refine ⟨hPρ, ?_⟩
  rw [← hB, ← Bc.bcB_fix' (S := S) n _ hP2]
  exact Bc.bcB_mono' (S := S) n (show Pv S (Om (1 + 1)) ∈ Set.Iio (Bc.bcC S (n + 1)) from hPρ.trans h2)
    (show upsilon l ∈ Set.Iio (Bc.bcC S (n + 1)) from h2) hPρ

/-- `window λ → λ' ⇒ θ ∈ At_{λ'}`. -/
theorem wrThAtom {n : ℕ} {l l' : Ordinal.{0}} (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    ConjT.th S ∈ ldAtR S l' := by
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  have hpv' := cdEta_pv (S := S) hl'.1 hX'
  have hbig := wrA_big (S := S) (A := ConjT.Aη S (cdEta S l')) (by
    show Pv S (Om (1 + 1)) < Pv S (cdEta S l')
    rw [hpv']; exact (wrP2_win h1 h2 hB).2)
  refine ⟨Om ω, ConjT.OmW_mem (S := S) _ _, ?_, rfl⟩
  exact (lt_add_of_pos_right _ (Om_pos (by simp))).trans hbig

/-- **The atom `θ` moves at every window** (code-free). -/
theorem wrAtTh {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    MvD S (ConjT.th S) ∧ Bc.bcB S n (ConjT.th S) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (ConjT.th S)) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (ConjT.th S)) := by
  obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
  refine ⟨hDθ, by rw [hBθ]; exact wrThAtom h1 hr hl' hB, ?_⟩
  rw [hBθ]
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hΘ := Wl.wlThVal hl hX hown hρA
  have hθ0 : 0 < ConjT.th S := Sf.sfTh_pos S
  have hWA : Om ω < A + ConjT.th S := by
    rw [hA_def]; unfold ConjT.Aη
    exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
  have hownθ : A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (ConjT.th_mem (S := S) hWA)
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hbX : S.psi (A + ConjT.th S) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← mxUps_succ hl hX]; exact hu1.trans hδr
  obtain ⟨A', hA', hBP, hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDθ hownθ hbX
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  have hΘ' := Wl.wlThVal hl' hX' hA' hρA'
  rw [hΘ', hΘ, hBd, hBθ]

/-- **The code-free wall from its part below `θ`.** -/
theorem wrWallCF_of_low (h : WrWallLowCF S) : WrWallCF S := by
  intro n l l' hR h1 hr hl' hB s hs hsY hsθ IH
  rcases hsθ.lt_or_eq with hlt | rfl
  · exact h n l l' hR h1 hr hl' hB s hs hsY hlt IH
  · exact wrAtTh hR h1 hr hl' hB

/-- **Every atom `s < θ⁺` moves at every window** (code-free), given `WrWallCF`. -/
theorem wrAtLow (hW : WrWallCF S) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    ∀ s ∈ ldAtR S l, s < ljThP S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro s hs hsP IHx
  have hsθ := ljAt_le_th hs hsP
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := Rn.rnSetup hR h1 hr hB
  obtain ⟨hDF, hBF⟩ := leB_FWW (S := S) (n := n)
  rcases lt_or_ge s (leFWW S) with hsF | hsF
  · obtain ⟨hDs, hBs, hBsF, hth, hEq⟩ := leAtMove_FWW hR.1 hl' hX hX' hA hA' hρ hρ' hbX hBψ s hs hsF
      (fun x hx hxs => by
        obtain ⟨hD, hc, -, h4, h5⟩ := IHx x hx hxs
        refine ⟨hD, hc, ?_, h4, h5⟩
        have := (mvB_lt_iff (k := n) hD hDF).2 (hxs.trans hsF)
        rwa [hBF] at this)
    exact ⟨hDs, hBs, hBsF.trans ljFWW_lt_ThP, hth, hEq⟩
  have hs0 : S.psi 0 (Om (1 + 1)) < s :=
    (psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_pos _) (CSet.zero_mem _ _)).trans_le hsF
  rcases lt_or_ge s (S.psi (Ug.ugY S) (Om (1 + 1))) with hsY | hsY
  · exact Ux.uxAtMoveTop hR h1 hr hl' hB s hs hs0 hsY IHx
  obtain ⟨hD, hmem, heq⟩ := hW n l l' hR h1 hr hl' hB s hs hsY hsθ IHx
  refine ⟨hD, hmem, ?_, ?_, heq⟩
  · obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
    rcases hsθ.lt_or_eq with hlt | he
    · exact (((mvB_lt_iff hD hDθ).2 hlt).trans_eq hBθ).trans Lj.ljTh_lt_ThP
    · rw [he, hBθ]; exact Lj.ljTh_lt_ThP
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
    obtain ⟨hX2, hown⟩ := ldOwnA hR.1 h2
    have hθM : ConjT.th S ≤ Rn.rnMW S := Lj.ljTh_lt_ThP.le.trans Rn.rnThP_le_MW
    have hs2 : s ≤ Om (1 + 1) := hsθ.trans (Lj.ljTh_lt_ThP.trans Lj.ljThP_lt_Om2).le
    rw [← ldTheta hR.1 hX2 hs2]
    exact (Rn.rnTheta_lt_delta hR.1 hX2 hown (hsθ.trans hθM)).trans hδr

/-- The window data at `λ` and `λ'`: own names, `Θ(θ)` at both, and the move of `ψ_{Ω₁}(A + d)`. -/
theorem wrWin {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    upsilon l < Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) ∧
    upsilon l' < Pv S (Om ω + Nc.ncPp S * (ω + 1)) ∧
    ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
    ConjT.Aη S (cdEta S l') ∈ S.CSet (ConjT.Aη S (cdEta S l')) (S.psi (ConjT.Aη S (cdEta S l')) (Om 1)) ∧
    S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l ∧ S.psi (ConjT.Aη S (cdEta S l')) (Om 1) = upsilon l' ∧
    Om ω + Om (1 + 1) < ConjT.Aη S (cdEta S l) ∧ Om ω + Om (1 + 1) < ConjT.Aη S (cdEta S l') ∧
    (∀ d, MvD S d →
      ConjT.Aη S (cdEta S l) + d ∈ S.CSet (ConjT.Aη S (cdEta S l) + d)
        (S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1)) →
      S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1) < Bc.bcC S (n + 1) →
      Bc.bcB S n (S.psi (ConjT.Aη S (cdEta S l) + d) (Om 1)) =
        S.psi (ConjT.Aη S (cdEta S l') + Bc.bcB S n d) (Om 1)) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  have hX' : upsilon l' < Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hpv' := cdEta_pv (S := S) hl'.1 hX'
  have hρ0 : (0 : Ordinal.{0}) < Pv S (cdEta S l) := hpv ▸ mvUps_pos hl
  obtain ⟨A1, hA1, hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S (cdEta S l) < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA1 : S.psi A1 (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  obtain ⟨hown', hA1e⟩ := Wg.wgOwnEta hl' hX' hA1 hρA1
  obtain ⟨hP, hP'⟩ := wrP2_win h1 h2 hB
  refine ⟨hX, hX', hown, hown', hpv, hpv', wrA_big (by
    show Pv S (Om (1 + 1)) < Pv S (cdEta S l); rw [hpv]; exact hP), wrA_big (by
    show Pv S (Om (1 + 1)) < Pv S (cdEta S l'); rw [hpv']; exact hP'), ?_⟩
  intro d hDd hownd hbd
  obtain ⟨A2, hA2, hBP2, hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd hbd
  have : A2 = A1 := mxPsi_inj hA2 hA1 (by rw [← hBP2, hBP])
  rw [hBd, this, ← hA1e]

/-- **The atoms `ψ_{Ω₂}(Ω_ω + c)`, `c < M_W`, move** at every window once the codes below them move. -/
theorem wrAtBlk {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c) (hcM : c < rnMW S)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om ω + c) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < rnMW S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (Om ω + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om ω + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (Om ω + c) (Om (1 + 1))) < rnMW S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om ω + c) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1)))) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', hpv, hpv', hAb, hAb', hBψ⟩ := wrWin hR h1 hr hl' hB
  set A := ConjT.Aη S (cdEta S l) with hA_def
  set A' := ConjT.Aη S (cdEta S l') with hA'_def
  set s := S.psi (Om ω + c) (Om (1 + 1)) with hs_def
  have hM2 : rnMW S < Om (1 + 1) := ldTop_lt_Om2 _
  have hcs : c < s := ldTop_gt rnOmW_own rnOm2_dvd_OmW hcM
  obtain ⟨hDc, hc', hBcM, hΘc, hEc⟩ := IH c hc hcs
  have hcA : Om ω + c < A := ((add_lt_add_iff_left _).2 (hcM.trans hM2)).trans hAb
  have hBcA : Om ω + Bc.bcB S n c < A' := ((add_lt_add_iff_left _).2 (hBcM.trans hM2)).trans hAb'
  have hownc := ldOwn rnOmW_own rnOm2_dvd_OmW hcM
  obtain ⟨hDW, hBW⟩ := wrB_OmW (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDc
  rw [hBW] at hBa
  obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psi2 (n := n) hDa hownc
  rw [hBa] at hBs
  -- the readings
  have hθ := Wl.wlThVal hl hX hown hpv
  have hθ' := Wl.wlThVal hl' hX' hown' hpv'
  have hΘs : gxTh (upsilon l) (ldAtR S l) s =
      S.psi (A + ConjT.th S + gxTh (upsilon l) (ldAtR S l) c) (Om 1) :=
    Ro.roThW_A hl hX hown rfl hθ c hc hcM hcA
  have hΘs' : gxTh (upsilon l') (ldAtR S l') (S.psi (Om ω + Bc.bcB S n c) (Om (1 + 1))) =
      S.psi (A' + ConjT.th S + gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n c)) (Om 1) :=
    Ro.roThW_A hl' hX' hown' rfl hθ' _ hc' hBcM hBcA
  have hsM : s < rnMW S := ldTop_lt rnOmW_own hcM
  have hΘlt : gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) := by
    rw [← ldTheta hl hX (hsM.trans hM2).le]
    exact (Rn.rnTheta_lt_delta hl hX hown hsM.le).trans hδr
  refine ⟨hDs, ?_, ?_, hΘlt, ?_⟩
  · rw [hBs]
    refine ⟨Om ω + Bc.bcB S n c, CSet.add_mem (ConjT.OmW_mem (S := S) _ _) ?_, hBcA, rfl⟩
    exact (ldHull_iff hl' hX' (hBcM.trans hM2)).2 hc'
  · rw [hBs]; exact ldTop_lt rnOmW_own hBcM
  · -- the move of `ψ_{Ω₁}(A + θ + Θ c)`
    have hθ0 : 0 < ConjT.th S := Sf.sfTh_pos S
    have hWA : Om ω < A + ConjT.th S := by
      rw [hA_def]; unfold ConjT.Aη
      exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
    set t := gxTh (upsilon l) (ldAtR S l) c with ht_def
    have htlt : t < S.psi (A + ConjT.th S + t) (Om 1) := by
      rw [← hΘs]; exact gxTh_lt hc hcs
    have hownd : A + (ConjT.th S + t) ∈ S.CSet (A + (ConjT.th S + t))
        (S.psi (A + (ConjT.th S + t)) (Om 1)) := by
      rw [← add_assoc]
      exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one
        (le_self_add.trans le_self_add)).2 hown) (ConjT.th_mem (S := S) (hWA.trans_le le_self_add)))
        (CSet.of_lt htlt)
    obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
    have hDt : MvD S t := mvD_of_lt (hΘc.trans (Bc.bcC_lt S (n + 1)))
    obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDt
    have hbd : S.psi (A + (ConjT.th S + t)) (Om 1) < Bc.bcC S (n + 1) := by
      rw [← add_assoc, ← hΘs]; exact hΘlt
    have hmv := hBψ _ hDd hownd hbd
    rw [hBs, hΘs', hΘs, hEc, add_assoc A, hmv, hBd, hBθ, add_assoc]

/-- **`Θ_λ(M_W) = ψ_{Ω₁}(A + θ + Ω₁)`** at every restart with `Ω_ω + Ω₂ < A` (`M_W = ψ_{Ω₂}(Ω_ω + Ω₂)`). -/
theorem wrThMW {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (hAb : Om ω + Om (1 + 1) < ConjT.Aη S (cdEta S l)) :
    gxTh (upsilon l) (ldAtR S l) (rnMW S) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) := by
  obtain ⟨hZ, hZ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  set Θ := gxTh (upsilon l) (ldAtR S l) with hΘ_def
  set K := ldKb S (Om ω) with hK_def
  have hM2 : rnMW S < Om (1 + 1) := ldTop_lt_Om2 _
  have hθ := Wl.wlThVal hl hX hown hρ
  -- the layers `K_j` are codes below `M_W`
  have hKc : ∀ j, GxCl (upsilon l) (ldAtR S l) (K j) ∧ K j < rnMW S := by
    intro j
    induction j with
    | zero => exact ⟨GxCl.om, ldOm1_lt_Top _⟩
    | succ j IH =>
      refine ⟨GxCl.atom ⟨Om ω + K j, CSet.add_mem (ConjT.OmW_mem (S := S) _ _)
        ((ldHull_iff hl hX (IH.2.trans hM2)).2 IH.1),
        ((add_lt_add_iff_left _).2 (IH.2.trans hM2)).trans hAb, rfl⟩, ?_⟩
      exact ldTop_lt rnOmW_own IH.2
  have hKs : ∀ j, Θ (K (j + 1)) = S.psi (A + ConjT.th S + Θ (K j)) (Om 1) := fun j =>
    Ro.roThW_A hl hX hown rfl hθ (K j) (hKc j).1 (hKc j).2
      (((add_lt_add_iff_left _).2 ((hKc j).2.trans hM2)).trans hAb)
  have hcof : ∀ v, v < Θ (rnMW S) → ∃ j, v < Θ (K j) := by
    intro v hv
    obtain ⟨c, hc, hcM, rfl⟩ := gxTh_onto hv
    obtain ⟨j, hj⟩ := ldKb_sup rnOmW_own rnOm2_dvd_OmW hcM
    exact ⟨j, gxTh_lt hc hj⟩
  refine le_antisymm (Rn.rnTheta_MW hl hX hown) ?_
  have hZS : SC (Θ (rnMW S)) :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hθSC := ConjT.SC_th S
  have hθM : ConjT.th S < rnMW S := Lj.ljTh_lt_ThP.trans_le Rn.rnThP_le_MW
  have hθat : GxCl (upsilon l) (ldAtR S l) (ConjT.th S) :=
    GxCl.atom ⟨Om ω, ConjT.OmW_mem (S := S) _ _,
      (lt_add_of_pos_right _ (Om_pos (by simp))).trans hAb, rfl⟩
  have hdvd : ConjT.th S ∣ A + ConjT.th S := by
    have := Rx.rxDvdTh (S := S) (cdEta S l) 0
    rw [mul_zero, add_zero] at this
    exact dvd_add this (dvd_refl _)
  refine Bt.psi_le_of_key hZS fun e he heA => ?_
  rcases lt_or_ge e (A + ConjT.th S) with h1 | h1
  · calc S.psi e (Om 1) ≤ S.psi (A + ConjT.th S) (Om 1) := (psi_mono (S := S) Low.InR_Om_one h1.le).1
      _ = Θ (ConjT.th S) := hθ.symm
      _ < Θ (rnMW S) := gxTh_lt hθat hθM
  · obtain ⟨ζ, rfl⟩ := exists_add_of_le h1
    have hζ1 : ζ < Om 1 := (add_lt_add_iff_left _).1 heA
    have hζθ : ζ < ConjT.th S := hζ1.trans (psiS_bounds (S := S) _ 1).1
    have hm : (A + ConjT.th S + ζ) % ConjT.th S = ζ := by
      rw [ldModK_add_lt hθSC _ hζθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hζH : Bt.HCl S (A + ConjT.th S + Om 1) (Θ (rnMW S)) ζ := by
      rw [← hm]; exact Ru.ruHCl_modK hθSC he
    obtain ⟨j, hj⟩ := hcof ζ (Bt.HCl_lt hZS hζH hζ1)
    calc S.psi (A + ConjT.th S + ζ) (Om 1) ≤ S.psi (A + ConjT.th S + Θ (K j)) (Om 1) :=
          (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 hj.le)).1
      _ = Θ (K (j + 1)) := (hKs j).symm
      _ < Θ (rnMW S) := gxTh_lt (hKc (j + 1)).1 (hKc (j + 1)).2

/-- `M_W ∈ MvD` and `B_n M_W = M_W`. -/
theorem wrB_MW {n : ℕ} : MvD S (rnMW S) ∧ Bc.bcB S n (rnMW S) = rnMW S := by
  obtain ⟨hDW, hBW⟩ := wrB_OmW (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hD2
  have hown : Om ω + Om (1 + 1) ∈ S.CSet (Om ω + Om (1 + 1)) (S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) :=
    CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (mxOm2_mem _ _)
  obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psi2 (n := n) hDa hown
  refine ⟨hDs, ?_⟩
  show Bc.bcB S n (S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) = S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))
  rw [hBs, hBa, hBW, hB2]

/-- **THE READING MOVE AT THE CODES `θ⁺ ≤ m_λ ≤ M_W`** (`Rn.RnThMoveM`) from the code-free wall. -/
theorem wrMid (hW : WrWallCF S) : Rn.RnThMoveM S := by
  intro n l l' hR h1 hr hl' hB hm hP hK
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hX, hX', hown, hown', hpv, hpv', hAb, hAb', hBψ⟩ := wrWin hR h1 hr hl' hB
  obtain ⟨hg, -, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  set e := cdExp η with he_def
  have hM2 : rnMW S < Om (1 + 1) := ldTop_lt_Om2 _
  have hΩP : Om (1 : Ordinal.{0}) < ljThP S := ljOm1_lt_ThP
  -- the code is the last exponent
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hlt : rnMW S < cdPi S η :=
      psi_lt_psi_of_mem (InR_Om_succ 1) hAb (CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (mxOm2_mem _ _))
    exact absurd (hc ▸ hK) (not_le.2 hlt)
  have hωe : (ω : Ordinal.{0}) ≤ e := by
    by_contra h
    push Not at h
    have hc : cdCode S l = e - 1 := by
      show cdCodeOf S η = _; rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_pos h]
    have h3 : cdCode S l < ω := hc ▸ (Ordinal.sub_le_self _ _).trans_lt h
    exact absurd (h3.trans ((Lw.lw_omega_lt_SC Ph.ph_SC_Om1).trans hΩP)) (not_lt.2 hP)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heM : e ≤ rnMW S := hcode ▸ hK
  have hΩe : Om (1 : Ordinal.{0}) < e := hΩP.trans_le (hcode ▸ hP)
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hpv] at this
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨η', -, hBη', hη', hexp'⟩ := ljExp_move hl.1 h1 h2 hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hρ'SC : SC (upsilon l') := hpv' ▸ SC_psi Low.InR_Om_one _
  have hρ'1 : upsilon l' < Om 1 := hpv' ▸ psi_lt Low.InR_Om_one _
  -- the move of `e` and of its reading
  have key : MvD S e ∧ Bc.bcB S n e ≤ rnMW S ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n e) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) e) := by
    rcases heM.lt_or_eq with heM | heM
    · have hatom : ∀ s ∈ ldAtR S l, s < rnMW S →
          (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
            GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < rnMW S ∧
            gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
            gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
          MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < rnMW S ∧
            gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
            gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
        intro s hs hsM IHx
        rcases lt_or_ge s (ljThP S) with hsP | hsP
        · have hsθ := ljAt_le_th hs hsP
          obtain ⟨a1, a2, a3, a4, a5⟩ := wrAtLow hW hR h1 hr hl' hB s hs hsP (fun x hx hxs => by
            obtain ⟨b1, b2, -, b4, b5⟩ := IHx x hx hxs
            refine ⟨b1, b2, ?_, b4, b5⟩
            obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
            exact (((mvB_lt_iff b1 hDθ).2 (hxs.trans_le hsθ)).trans_eq hBθ).trans Lj.ljTh_lt_ThP)
          exact ⟨a1, a2, a3.trans_le Rn.rnThP_le_MW, a4, a5⟩
        · rcases ldBlk_cls hl hX rnOmW_own rnOm2_dvd_OmW hs hsM with hsθ | ⟨c, hc, hcM, rfl⟩
          · exact absurd (hsθ.trans_lt Lj.ljTh_lt_ThP) (not_lt.2 hsP)
          · exact wrAtBlk hR h1 hr hl' hB hc hcM IHx
      obtain ⟨hDe, -, hBeM, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
        (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw (SC_psi (InR_Om_succ 1) _) (ldOm1_lt_Top _).le
        hatom e hge heM
      exact ⟨hDe, hBeM.le, hEq⟩
    · rw [heM]
      obtain ⟨hDM, hBM⟩ := wrB_MW (S := S) (n := n)
      refine ⟨hDM, hBM.le, ?_⟩
      rw [hBM, wrThMW hl hX hown hAb, wrThMW hl' hX' hown' hAb']
      have hθ0 : 0 < ConjT.th S := Sf.sfTh_pos S
      have hWA : Om ω < A + ConjT.th S := by
        rw [hA_def]; unfold ConjT.Aη
        exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
      have hownd : A + (ConjT.th S + Om 1) ∈ S.CSet (A + (ConjT.th S + Om 1))
          (S.psi (A + (ConjT.th S + Om 1)) (Om 1)) := by
        rw [← add_assoc]
        exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one
          (le_self_add.trans le_self_add)).2 hown) (ConjT.th_mem (S := S) (hWA.trans_le le_self_add)))
          (CSet.Om_mem (CSet.one_mem _ _))
      obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
      obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
      obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDO
      have hbd : S.psi (A + (ConjT.th S + Om 1)) (Om 1) < Bc.bcC S (n + 1) := by
        rw [← add_assoc, ← wrThMW hl hX hown hAb, ← ldTheta hl hX hM2.le]
        exact (Rn.rnTheta_lt_delta hl hX hown le_rfl).trans hδr
      rw [add_assoc A, hBψ _ hDd hownd hbd, hBd, hBθ, hBO, add_assoc]
  obtain ⟨hDe, hBeM, hEq⟩ := key
  have hΩBe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 hΩe
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩBe.le
  have hBe2 : Bc.bcB S n e < Om (1 + 1) := hBeM.trans_lt hM2
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBe2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' hBe2.le]
  exact hEq.symm

/-- **The image move is the atom move** (REFUTE-FIRST record for the wall steps): if the reading of an atom at `λ'`
is `ψ_{Ω₁}(Â' + Ω₁^{Z'})` and `B_n` sends the reading at `λ` to `ψ_{Ω₁}(Â' + Ω₁^{Z_B})`, both arguments own, then the
atom move `Θ_{λ'} = B_n Θ_λ` holds iff `Z' = Z_B`.  So the hypothesis `B_n X̂^λ_e(β) = X̂^{λ'}_{B_n e}(B_n β)` (for own
images) is the atom move itself at the atoms `T_{X+e}(β)`, not a weaker tool for it. -/
theorem wrImgMove_iff {Â' Z' ZB a b : Ordinal.{0}}
    (h1 : Â' + leOe Z' ∈ S.CSet (Â' + leOe Z') (S.psi (Â' + leOe Z') (Om 1)))
    (h2 : Â' + leOe ZB ∈ S.CSet (Â' + leOe ZB) (S.psi (Â' + leOe ZB) (Om 1)))
    (ha : a = S.psi (Â' + leOe ZB) (Om 1)) (hb : b = S.psi (Â' + leOe Z') (Om 1)) :
    b = a ↔ Z' = ZB := by
  constructor
  · intro h
    rw [ha, hb] at h
    have e1 := add_left_cancel (mxPsi_inj h1 h2 h)
    rcases lt_trichotomy Z' ZB with hl | he | hg
    · exact absurd e1 (leOe_lt hl).ne
    · exact he
    · exact absurd e1.symm (leOe_lt hg).ne
  · intro h; rw [ha, hb, h]

end Googology.Trans.PoR.InaccPsi.R2.Wr

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrB_OmW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrWall_of_cf
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrP2_lt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrA_big
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrP2_win
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrThAtom
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrAtTh
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrWallCF_of_low
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrAtLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrWin
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrAtBlk
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrThMW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrB_MW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrMid
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wr.wrImgMove_iff
