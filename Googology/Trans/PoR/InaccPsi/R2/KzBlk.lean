import Googology.Trans.PoR.InaccPsi.R2.KzMove
import Googology.Trans.PoR.InaccPsi.R2.ZqBd

/-!
# Kz: THE BLOCK MOVE ABOVE A BAND BASE WITH A LAW AT BOTH ENDS (`Yj.yjBlkMove` for bases in `[Ω_ω, Ω_ω·2)`)

`B_n = Bc.bcB S n`, "window" as in `Yj.yjBlkMove`, `A = A_{η_λ}`, `A'` own with `ψ₁(A') = ρ_{λ'}`, `F^a = ψ₂(a + Ω₂)`.
In a window `Ω_ω·2 ≤ A` and `Ω_ω·2 ≤ A'` (`Zj.zjWin_A`), so a base `a` with `a + Ω₂ < Ω_ω·2` has `a + Ω₂ < A`.

* `KzBase` (**a band base with a law at both ends**: `Yj.YjBase` with `D_K` in place of `D`, and
  `a + Ω₂ < Ω_ω·2`, `B_n a + Ω₂ < Ω_ω·2` in place of `a < Ω_ω`);
* `kzBlkMove` (**EVERY ATOM OF THE BLOCK MOVES** above a band base, under the moves of the codes below it with the band
  bound `B_n x < P′`).

No new axiom.  New definition: `KzBase`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **A band base with a law at both ends** (data at `λ` and at `λ'`). -/
structure KzBase (S : InaccSeq.{0}) (n : ℕ) (l l' A' K a D : Ordinal.{0}) : Prop where
  D_a : VbDK S l K a
  aW : a + Om (1 + 1) < Om ω + Om ω
  dvd : Om (1 + 1) ∣ a
  own : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))
  mv_a : MvD S a
  mv_D : MvD S D
  hat : ConjT.Aη S (cdEta S l) + D ∈
    S.CSet (ConjT.Aη S (cdEta S l) + D) (S.psi (ConjT.Aη S (cdEta S l) + D) (Om 1))
  law : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi (ConjT.Aη S (cdEta S l) + D) (Om 1)
  D_a' : VbDK S l' K (Bc.bcB S n a)
  aW' : Bc.bcB S n a + Om (1 + 1) < Om ω + Om ω
  dvd' : Om (1 + 1) ∣ Bc.bcB S n a
  own' : ∀ d, d ≤ Om (1 + 1) → Bc.bcB S n a ∈
    S.CSet (Bc.bcB S n a + d) (S.psi (Bc.bcB S n a + d) (Om (1 + 1)))
  hat' : A' + Bc.bcB S n D ∈ S.CSet (A' + Bc.bcB S n D) (S.psi (A' + Bc.bcB S n D) (Om 1))
  law' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n a) (Om (1 + 1))) =
    S.psi (A' + Bc.bcB S n D) (Om 1)

section Win

variable {n : ℕ} {l l' A' K : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY ATOM OF THE BLOCK MOVES** above a band base with a law at both ends. -/
theorem kzBlkMove {a D : Ordinal.{0}} (hb : KzBase S n l l' A' K a D) {c : Ordinal.{0}}
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (a + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (a + c) (Om (1 + 1))) = S.psi (Bc.bcB S n a + Bc.bcB S n c) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (a + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (a + c) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (a + c) (Om (1 + 1)))) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  obtain ⟨hAW, hAW'⟩ := Zj.zjWin_A hR h1 hr hl' hB
  have hbA : a + Om (1 + 1) < ConjT.Aη S (cdEta S l) := hb.aW.trans_le hAW
  have hbA' : Bc.bcB S n a + Om (1 + 1) < ConjT.Aη S (cdEta S l') := hb.aW'.trans_le hAW'
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hc2 : c < Om (1 + 1) := hcF.trans (ldTop_lt_Om2 a)
  have hcs : c < S.psi (a + c) (Om (1 + 1)) := ldTop_gt hb.own hb.dvd hcF
  obtain ⟨hDc, hBc, -, hΘc, hmvc⟩ := IH c hc hcs
  -- the reading at `λ`
  have hstep := ldBlk_step hl hX hb.own hb.dvd hb.D_a.1 hbA hb.hat hb.law c hc hcF
  have hΘlt : gxTh (upsilon l) (ldAtR S l) c < S.psi (A + D + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
    rw [← hstep]; exact gxTh_lt hc hcs
  have hown : A + (D + gxTh (upsilon l) (ldAtR S l) c) ∈ S.CSet (A + (D + gxTh (upsilon l) (ldAtR S l) c))
      (S.psi (A + (D + gxTh (upsilon l) (ldAtR S l) c)) (Om 1)) := by
    rw [← add_assoc]
    exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat) (CSet.of_lt hΘlt)
  -- `B_n` on the atom
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDac, hBac⟩ := mvB_add (k := n) hb.mv_a hDc
  obtain ⟨hDs, hBs, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDac (ldOwn hb.own hb.dvd hcF)
  rw [hB1, hBac] at hBs
  -- `B_n c < F^{B_n a}`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDa2, hBa2⟩ := mvB_add (k := n) hb.mv_a hD2
  obtain ⟨hDF, hBF, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDa2
    (CSet.add_mem (hb.own _ le_rfl) (mxOm2_mem _ _))
  rw [hB1, hBa2, hB2] at hBF
  have hBcF : Bc.bcB S n c < ldTop S (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDc hDF).2 hcF
    rw [hBF] at h; exact h
  -- the reading at `λ'`
  have hstep' := ldBlk_step hl' hX' hb.own' hb.dvd' hb.D_a'.1 hbA' hb.hat' hb.law' _ hBc hBcF
  have hat' := ldBlk_atom hl' hX' hb.D_a'.1 hbA' hBc hBcF
  -- `B_n` on the reading
  have hDΘ : MvD S (gxTh (upsilon l) (ldAtR S l) c) := mvD_of_lt (hΘc.trans (Bc.bcC_lt S (n + 1)))
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hb.mv_D hDΘ
  have hac2 : a + c < Om ω + Om ω := ((add_lt_add_iff_left a).2 hc2).trans hb.aW
  have hsP : S.psi (a + c) (Om (1 + 1)) < Nc.ncPp S :=
    psi_lt_psi_of_mem hκ2 hac2 (CSet_mono hac2.le (psi_mono hκ2 hac2.le).1 (ldOwn hb.own hb.dvd hcF))
  have hsH : S.psi (a + c) (Om (1 + 1)) ∈ cdHull S l :=
    (ldHull_iff hl hX (psi_lt hκ2 _)).2 (GxCl.atom (ldBlk_atom hl hX hb.D_a.1 hbA hc hcF))
  have hhi : S.psi (A + (D + gxTh (upsilon l) (ldAtR S l) c)) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← add_assoc, ← hstep]; exact Zq.zqTh_lt_c hR hr hsH hsP
  have hψ := Yj.yjPsi1 hR h1 hr hl' hB hA' hρ' hDd hown hhi
  refine ⟨hDs, hBs, hBs ▸ hat', ?_⟩
  rw [hBs, hstep', hmvc, hstep, add_assoc (ConjT.Aη S (cdEta S l)), hψ, hBd, ← add_assoc]

end Win

end Googology.Trans.PoR.InaccPsi.R2.Kz
