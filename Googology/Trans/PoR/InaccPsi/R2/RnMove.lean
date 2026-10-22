import Googology.Trans.PoR.InaccPsi.R2.RnBlk

/-!
# The atoms of a base `β` move, up to and including `T_W(β)`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^e = Ω₂^e`, `Ω^x = Ω₁^x`, `T_W(β) = ψ_{Ω₂}(β + W^W)`
(`Rn.rnTW`), `G = ψ_{Ω₂}(0)`.

* `rnB_WW` (`B_n(Ω₂^{Ω₂}) = Ω₂^{Ω₂}`), `rnB_OO` (`B_n(Ω₁^{Ω₁}) = Ω₁^{Ω₁}`), `rnB_TW` (`B_n(T_W(β)) = T_W(B_n β)`);
* `rnAtMove_base` (**every atom `s` with `ψ_{Ω₂}(β) ≤ s ≤ T_W(β)` moves** once the codes below `s` move: given bases
  `β` at `λ` and `β' = B_n β` at `λ'` with `Θ_λ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(A + D)`, `Θ_{λ'}(ψ_{Ω₂}(β')) = ψ_{Ω₁}(A' + B_n D)`,
  `D < G`: `B_n s` is an atom at `λ'`, `B_n s ≤ T_W(β')`, `Θ_λ(s) < c_{n+1}` and `Θ_{λ'}(B_n s) = B_n Θ_λ(s)`; the
  digits move by `Le.leDigMoveE`, the readings by `Rn.rnTh_base` and `Rn.rnTopW`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `B_n(Ω₂^{Ω₂}) = Ω₂^{Ω₂}`. -/
theorem rnB_WW {n : ℕ} : MvD S (leWe (Om (1 + 1))) ∧ Bc.bcB S n (leWe (Om (1 + 1))) = leWe (Om (1 + 1)) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  have hWW : MvD S (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) ∧
      Bc.bcB S n (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
    rw [ldOm2sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB2]⟩
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hWW.1
  rw [hWW.2] at hBW
  exact ⟨hDW, hBW⟩

theorem rnOm1sq_eq : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by
  rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]

/-- `B_n(Ω₁^{Ω₁}) = Ω₁^{Ω₁}`. -/
theorem rnB_OO {n : ℕ} : MvD S (leOe (Om 1)) ∧ Bc.bcB S n (leOe (Om 1)) = leOe (Om 1) := by
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD1 hD1
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  have hOO : MvD S (Om (1 : Ordinal.{0}) * Om 1) ∧
      Bc.bcB S n (Om (1 : Ordinal.{0}) * Om 1) = Om 1 * Om 1 := by
    rw [rnOm1sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB1]⟩
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hOO.1
  rw [hOO.2] at hBW
  exact ⟨hDW, hBW⟩

/-- `B_n(T_W(β)) = T_W(B_n β)`. -/
theorem rnB_TW {n : ℕ} {l β : Ordinal.{0}} (hb : RnBase S l β) (hDβ : MvD S β) :
    MvD S (rnTW S β) ∧ Bc.bcB S n (rnTW S β) = rnTW S (Bc.bcB S n β) := by
  obtain ⟨-, -, -, hβown⟩ := hb
  obtain ⟨hDW, hBW⟩ := rnB_WW (S := S) (n := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDW
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDs (CSet.add_mem (hβown _ le_rfl) (leWe_mem (mxOm2_mem _ _)))
  refine ⟨hDT, ?_⟩
  unfold rnTW; rw [hBT, hBs, hBW]

theorem rnG_le_th : S.psi 0 (Om (1 + 1)) ≤ ConjT.th S := (psi_mono (S := S) (InR_Om_succ 1) zero_le).1

theorem rnOO_lt_G : leOe (Om 1) < S.psi 0 (Om (1 + 1)) :=
  (leOe_lt_SC (SC_psi (InR_Om_succ 1) 0) (psiS_bounds (S := S) 0 1).1 (psiS_bounds (S := S) 0 1).1).1

/-- **The atoms `ψ_{Ω₂}(β) ≤ s ≤ T_W(β)` of a base move** once the codes below them move. -/
theorem rnAtMove_base {n : ℕ} {l l' A A' ηx ηx' β β' D : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl' : IsRestartIdx l') (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1))
    (hb : RnBase S l β) (hb' : RnBase S l' β') (hDβ : MvD S β) (hBβ : Bc.bcB S n β = β')
    (hDD : MvD S D) (hDG : D < S.psi 0 (Om (1 + 1)))
    (hAD : A + D ∈ S.CSet (A + D) (S.psi (A + D) (Om 1)))
    (hA'D : A' + Bc.bcB S n D ∈ S.CSet (A' + Bc.bcB S n D) (S.psi (A' + Bc.bcB S n D) (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi (A + D) (Om 1))
    (hbase' : gxTh (upsilon l') (ldAtR S l') (S.psi β' (Om (1 + 1))) =
      S.psi (A' + Bc.bcB S n D) (Om 1)) :
    ∀ s ∈ ldAtR S l, S.psi β (Om (1 + 1)) ≤ s → s ≤ rnTW S β →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s ≤ rnTW S β' ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro s hs hsβ hsT IHx
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hDθ : D ≤ ConjT.th S := hDG.le.trans rnG_le_th
  obtain ⟨hDT, hBT⟩ := rnB_TW (n := n) hb hDβ
  rw [hBβ] at hBT
  rcases hsT.lt_or_eq with hlt | rfl
  · rcases rnTh_base hl hX hb hAD hbase s hs hlt with h | ⟨e, c, v, heT, hown, rfl, hth, hownv, hv, -⟩
    · obtain rfl : s = S.psi β (Om (1 + 1)) := le_antisymm h hsβ
      obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDβ (rnBase_own hb)
      rw [hBβ] at hBs
      refine ⟨hDs, by rw [hBs]; exact rnBase_atom hb', by rw [hBs]; exact (rnBase_lt hb').le,
        by rw [hbase]; exact hbX D hDθ, ?_⟩
      rw [hBs, hbase', hbase, hBψ D hDD hAD hDθ]
    obtain ⟨hDe, hDc, hDs, hBs, hDv, hBown⟩ := leDigMoveE (n := n) (l' := l') hl hX hown (rnBaseE hb heT)
      hDβ (fun x hx hxs => IHx x hx hxs)
    rw [hBβ] at hBown hBs
    have hownc := leOwnH_own hl hX hown (rnBaseE hb heT)
    obtain ⟨hDsψ, hBsψ⟩ := mxB_atom (n := n) hDs hownc
    have hBlt : Bc.bcB S n (S.psi (β + c) (Om (1 + 1))) < rnTW S β' := by
      have := (mvB_lt_iff (k := n) hDsψ hDT).2 hlt; rwa [hBT] at this
    have hBeT : Bc.bcB S n e < rnTW S β' := by
      have := (mvB_lt_iff (k := n) hDe hDT).2 heT; rwa [hBT] at this
    have hb'e := rnBaseE hb' hBeT
    obtain ⟨hBH, hBA⟩ := leOwnH_mem hl' hX' hBown hb'e
    obtain ⟨hth', -, -, -⟩ := leOwnRead hl' hX' hBown (A' + Bc.bcB S n D) hb'e hA'D hbase'
    have hΘe1 := rnTheta_exp hl hX hb hAD hbase heT hown
    have hvG : v < S.psi 0 (Om (1 + 1)) := hv.trans (leOe_lt_SC hG1 hΩG1 (hΘe1.trans hΩG1)).1
    have hdθ : D + v ≤ ConjT.th S := (hG1.isPrincipal hDG hvG).le.trans rnG_le_th
    obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDD hDv
    have hownd : A + (D + v) ∈ S.CSet (A + (D + v)) (S.psi (A + (D + v)) (Om 1)) := by
      rw [← add_assoc]; exact hownv
    refine ⟨hDsψ, ?_, hBlt.le, ?_, ?_⟩
    · rw [hBsψ, hBs]; exact ⟨_, hBH, hBA, rfl⟩
    · rw [hth, add_assoc]; exact hbX _ hdθ
    · rw [hBsψ, hBs, hth', hth, add_assoc A, hBψ _ hDd hownd hdθ, hBd, add_assoc]
  · have e1 := rnTopW hl hX hb hAD hbase
    have e1' := rnTopW hl' hX' hb' hA'D hbase'
    obtain ⟨hDO, hBO⟩ := rnB_OO (S := S) (n := n)
    have hdθ : D + leOe (Om 1) ≤ ConjT.th S := (hG1.isPrincipal hDG rnOO_lt_G).le.trans rnG_le_th
    have hownd : A + (D + leOe (Om 1)) ∈
        S.CSet (A + (D + leOe (Om 1))) (S.psi (A + (D + leOe (Om 1))) (Om 1)) := by
      rw [← add_assoc]
      refine CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) Low.InR_Om_one le_self_add).1 hAD) ?_
      exact leOe_mem (CSet.Om_mem (CSet.one_mem _ _))
    obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDD hDO
    refine ⟨hDT, by rw [hBT]; exact rnTW_atom hb', by rw [hBT], by rw [e1, add_assoc]; exact hbX _ hdθ, ?_⟩
    rw [hBT, e1', e1, add_assoc A, hBψ _ hDd hownd hdθ, hBd, hBO, add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Rn
