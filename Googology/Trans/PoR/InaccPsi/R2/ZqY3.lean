import Googology.Trans.PoR.InaccPsi.R2.ZqUx
import Googology.Trans.PoR.InaccPsi.R2.VnRead

/-!
# The atom `ψ_{Ω₂}(Ω_ω + Y₃)`: its reading and its move (REFUTE-FIRST record for the band above `Y₃`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`,
`y_n = ψ_{Ω₃}^n(0)`, `z_n = ψ_{Ω₂}^n(0)`, `F₂^ω = ψ_{Ω₂}(Ω_ω + W^{W^{Ω₂}})`.

* `zqF2_read` (**`Θ(F₂^ω) = ψ_{Ω₁}(A + θ + Ω^{Ω^{Ω₁}})`**: `Rw.rwTopWW` at the base `Ω_ω`);
* `zqThTh_read` (**`Θ(ψ_{Ω₂}(Ω_ω + θ)) = ψ_{Ω₁}(A + θ + ψ_{Ω₁}(A + θ))`**);
* `zqTopY_it` (**`Θ(ψ_{Ω₂}(Ω_ω + W^{W^{y_{n+1}}})) = ψ_{Ω₁}(A + θ + Ω^{Ω^{z_{n+1}}})`**: the level statements of
  `Uu.uuLSY` are base-relative tops `Rv.RvTop λ 0`, read at the base `Ω_ω`);
* `zqRead_Y3` (**`Θ(ψ_{Ω₂}(Ω_ω + Y₃)) = ψ_{Ω₁}(A + θ + Y₂)`**, `Ug.ugReadLim` at the base `Ω_ω`);
* `zqY3_atom`, `zqY3_move` (**in every window `B_n Θ_λ(ψ_{Ω₂}(Ω_ω + Y₃)) = Θ_{λ'}(ψ_{Ω₂}(Ω_ω + Y₃))`**, no wall).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ux
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Zj

variable {S : InaccSeq.{0}}

/-- `Y₂ = ψ_{Ω₂}(Ω₂) < θ`. -/
theorem zqY2_lt_th : S.psi (Om (1 + 1)) (Om (1 + 1)) < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ldOm2_lt_OmW (mxOm2_mem _ _)

/-- `B_n Y₂ = Y₂`. -/
theorem zqB_Y2 {n : ℕ} : MvD S (S.psi (Om (1 + 1)) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om (1 + 1)) (Om (1 + 1))) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hD2 (mxOm2_mem _ _)
  exact ⟨hDs, by rw [hBs, hB2]⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAW

/-- **REFUTE-FIRST record: `Θ(F₂^ω) = ψ_{Ω₁}(A + θ + Ω^{Ω^{Ω₁}})`** (`F₂^ω = ψ_{Ω₂}(Ω_ω + W^{W^{Ω₂}})`). -/
theorem zqF2_read :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + leOe (leOe (Om 1))) (Om 1) := by
  have h := rwTopWW hl hX (Om ω) _ (zjBaseX hAW (roWe_lt_OmW ldOm2_lt_OmW)) (zjHat hl hX hown hAW)
    (zjBase0 hl hX hown hAW)
  rw [add_zero, gxTh_zero, add_zero] at h
  exact h

/-- **REFUTE-FIRST record: `Θ(ψ_{Ω₂}(Ω_ω + θ)) = ψ_{Ω₁}(A + θ + ψ_{Ω₁}(A + θ))`.** -/
theorem zqThTh_read :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + ConjT.th S) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1)) (Om 1) := by
  have hat : ConjT.th S ∈ ldAtR S l :=
    ⟨Om ω, ConjT.OmW_mem (S := S) _ _, (lt_add_of_pos_right _ (Om_pos omega0_ne_zero)).trans_le hAW, rfl⟩
  have hθT : ConjT.th S < ldTop S (Om ω) := by
    rw [← leTe_one]
    unfold leTe ConjT.th
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (leWe_pos _)) (zjOmW_own _)
  have hown1 : LeOwnH S l 1 (Om ω) (ConjT.th S) (gxTh (upsilon l) (ldAtR S l) (ConjT.th S)) :=
    LeOwnH.one (GxCl.atom hat) hθT
  have h1T : (1 : Ordinal.{0}) < rnTW S (Om ω) :=
    one_lt_omega0.trans (Lw.lw_omega_lt_SC (rnTW_SC _))
  obtain ⟨e1, -, -, -⟩ := zjOwn_read hl hX hown hAW hown1 h1T
  rw [e1]
  congr 2
  exact zjBase0 hl hX hown hAW

/-- **`Θ(ψ_{Ω₂}(Ω_ω + W^{W^{y_{n+1}}})) = ψ_{Ω₁}(A + θ + Ω^{Ω^{z_{n+1}}})`.** -/
theorem zqTopY_it (n : ℕ) :
    gxTh (upsilon l) (ldAtR S l)
        (S.psi (Om ω + leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0))) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)))
        (Om 1) := by
  have hay : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 < ugY S := vnIt_lt (s := 1 + 1) vnOm3C (n + 1)
  have haA := uuLtA (l := l) hay
  have haH : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 ∈ cdHull S l :=
    vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ haA.le
  have hΩa : Om (1 + 1) < (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']; exact ugOm2_lt_psi3 _
  have h1 : 1 ≤ (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 :=
    (gg_one_lt_of_SC ldOm2_SC).le.trans hΩa.le
  have hT := vnT_it (S := S) l (n + 1)
  have hTY : ugTh S l ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) < ujY S 0 := by
    rw [ujY_zero]; exact uuTh_lt_Y2 hl hX haH hay
  have hlev := (uuLSY hl hX).lev _ haH h1 hay
  have h3 : 0 + leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) + Om (1 + 1) < ugY S := by
    rw [zero_add]; exact uqY_SC.isPrincipal (leWe_lt_SC uqY_SC uqW_lt_Y hay).1 uqW_lt_Y
  have h2 : 0 + leOe (ugTh S l ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) + Om 1 < ujY S 0 := by
    rw [zero_add]; exact uuY2_SC.isPrincipal (leOe_lt_SC uuY2_SC uuOm1_lt_Y2 hTY).1 uuOm1_lt_Y2
  have hle : (fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0 ≤
      0 + leWe (0 + leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) := by
    rw [zero_add, zero_add]; exact (ujLe_We _).trans (ujLe_We _)
  have hown3 : uuOw S ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) 0 0 :=
    Or.inr ⟨hΩa.le, fun Q hQ hQ' => uqC_mem hQ hQ' (vnIt_mem (s := 1 + 1) vnOm3C (n + 1) _ _ hle) hay⟩
  have hT3 := hlev 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) h3 h2 hown3
  rw [zero_add, zero_add] at hT3
  have hWω : leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0) < Om ω :=
    ((leWe_lt_SC uqY_SC uqW_lt_Y hay).1.trans ugY_lt_Om3).trans Ry.ryOm3_lt
  have h := hT3 (Om ω) _ (zjBaseX hAW hWω) zero_le (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [hT] at h
  exact h

/-- **`Θ(ψ_{Ω₂}(Ω_ω + Y₃)) = ψ_{Ω₁}(A + θ + Y₂)`.** -/
theorem zqRead_Y3 :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + ugY S) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have hκC2 : ∀ a b, Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => mxOm2_mem a b
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hΩ1Y2 : Om 1 < S.psi (Om (1 + 1)) (Om (1 + 1)) := (psiS_bounds (S := S) _ 1).1
  have hEX : ∀ n : ℕ, leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) ≤ ugY S := fun n =>
    (leWe_lt_SC uqY_SC uqW_lt_Y (leWe_lt_SC uqY_SC uqW_lt_Y (vnIt_lt (s := 1 + 1) vnOm3C (n + 1))).1).1.le
  have hEcof : ∀ e, e < ugY S → ∃ n : ℕ, e < leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)) := by
    intro e he
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) (1 + 1))).1 (he.trans_le (uuY_le_sup (S := S) uuThree_lt))
    exact ⟨m, hm.trans ((uuIt_lt (S := S) (1 + 1) m).trans_le ((ujLe_We _).trans (ujLe_We _)))⟩
  have hyY : ∀ n : ℕ, leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)) ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    fun n => (leOe_lt_SC hY2SC hΩ1Y2 (leOe_lt_SC hY2SC hΩ1Y2 (vnIt_lt (s := 1) hκC2 (n + 1))).1).1.le
  have hycof : ∀ z, z < S.psi (Om (1 + 1)) (Om (1 + 1)) →
      ∃ n : ℕ, z ≤ leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)) := by
    intro z hz
    obtain ⟨m, hm⟩ := (lt_ciSup_iff (uuIt_bdd (S := S) 1)).1 (hz.trans_le (uuY_le_sup (S := S) uuTwo_lt))
    exact ⟨m, (hm.trans (uuIt_lt (S := S) 1 m)).le.trans ((ujLe_Oe _).trans (ujLe_Oe _))⟩
  exact ugReadLim (S := S) (l := l) (β := Om ω) (Â := ConjT.Aη S (cdEta S l) + ConjT.th S)
    (fun n => leWe (leWe ((fun x => S.psi x (Om (1 + 1 + 1)))^[n + 1] 0)))
    (fun n => leOe (leOe ((fun x => S.psi x (Om (1 + 1)))^[n + 1] 0)))
    uqY_SC.isSuccLimit hY2SC.isSuccLimit hEX hEcof hyY hycof (zqTopY_it hl hX hown hAW)

omit hl hX hown in
/-- `ψ_{Ω₂}(Ω_ω + Y₃)` is an atom of `λ`. -/
theorem zqY3_atom : S.psi (Om ω + ugY S) (Om (1 + 1)) ∈ ldAtR S l := by
  have h3 : Om (1 + 1 + 1 : Ordinal.{0}) < ConjT.Aη S (cdEta S l) :=
    Ry.ryOm3_lt.trans_le (le_self_add.trans hAW)
  exact ⟨Om ω + ugY S, CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (Vq.vqY3_mem h3),
    ((add_lt_add_iff_left _).2 zqY_lt_OmW).trans_le hAW, rfl⟩

end Main

/-- **The reading at `ψ_{Ω₂}(Ω_ω + Y₃)` is below `δ_λ`**, `ψ_{Ω₁}(A + θ + Y₂)` own. -/
theorem zqY3_bd {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l)) :
    ConjT.Aη S (cdEta S l) + (ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1))) ∈
      S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1))))
        (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1)))) (Om 1)) ∧
      S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1)))) (Om 1) < cdDelta l := by
  have hÂ := zjHat hl hX hown hAW
  refine ⟨?_, Xs.xsLt_delta hl hX (zjTh_add_le zqY2_lt_th)⟩
  rw [← add_assoc]
  have h2 : Om (1 + 1 : Ordinal.{0}) < ConjT.Aη S (cdEta S l) + ConjT.th S + S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    (ldOm2_lt_OmW.trans_le (le_self_add.trans hAW)).trans_le (le_self_add.trans le_self_add)
  exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
    (CSet.psi_mem h2 (InR_Om_succ 1) (mxOm2_mem _ _) (mxOm2_mem _ _))

/-- **The move at `ψ_{Ω₂}(Ω_ω + Y₃)`**: in every window `B_n Θ_λ(ψ_{Ω₂}(Ω_ω + Y₃)) = Θ_{λ'}(ψ_{Ω₂}(Ω_ω + Y₃))`. -/
theorem zqY3_move {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + ugY S) (Om (1 + 1)))) =
      gxTh (upsilon l') (ldAtR S l') (S.psi (Om ω + ugY S) (Om (1 + 1))) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  rw [zqRead_Y3 hl hX hown hAW, zqRead_Y3 hl' hX' hown' hAW']
  obtain ⟨hownd, hbd⟩ := zqY3_bd hl hX hown hAW
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  obtain ⟨hDY, hBY⟩ := zqB_Y2 (S := S) (n := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDY
  rw [add_assoc, hBψ _ hDd hownd (hbd.trans hδr), hBd, hBθ, hBY, ← add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Zq
