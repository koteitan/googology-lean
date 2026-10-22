import Googology.Trans.PoR.InaccPsi.R2.RnMove

/-!
# The bases `Ω₂^{Ω₂}·k`: the readings `Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂}·k)) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁}·k)` and the atom moves below them

`β_k = Ω₂^{Ω₂}·k` (`rnBk`), `D_k = 1 + Ω₁^{Ω₁}·k` (`rnDk`), `T_W(β_k) = ψ_{Ω₂}(β_{k+1})`, `F_W = ψ_{Ω₂}(β_1)`.

* `rnBk_base` (**every `β_k` is a base** (`Rn.RnBase`) at every restart), `rnBk_D`, `rnDk_D` (`B_n` fixes `β_k`, `D_k`),
  `rnDk_lt_G` (`D_k < ψ_{Ω₂}(0)`), `rnDk_own`;
* `rnTh_k` (**`Θ_λ(ψ_{Ω₂}(β_k)) = ψ_{Ω₁}(A + D_k)`** for every `k`, `A` own with `ψ_{Ω₁}(A) = ρ_λ`: `k = 0` is
  `Ld.ldBlk_zero`, the step is the pull-back `Rn.rnTopW`; at `k = 1`: **`Θ_λ(F_W) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁})`**);
* `rnAtMove_k` (**every atom `s` with `ψ_{Ω₂}(β_k) ≤ s ≤ ψ_{Ω₂}(β_{k+1})` moves** once the codes below `s` move).

No new axiom.  New definitions: `rnBk`, `rnDk`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `β_k = Ω₂^{Ω₂}·k`. -/
noncomputable def rnBk (k : ℕ) : Ordinal.{0} := leWe (Om (1 + 1)) * (k : Ordinal.{0})

/-- `D_k = 1 + Ω₁^{Ω₁}·k`. -/
noncomputable def rnDk (k : ℕ) : Ordinal.{0} := 1 + leOe (Om 1) * (k : Ordinal.{0})

theorem rnBk_zero : rnBk 0 = 0 := by unfold rnBk; rw [Nat.cast_zero, mul_zero]
theorem rnDk_zero : rnDk 0 = 1 := by unfold rnDk; rw [Nat.cast_zero, mul_zero, add_zero]
theorem rnBk_succ (k : ℕ) : rnBk (k + 1) = rnBk k + leWe (Om (1 + 1)) := by
  unfold rnBk; rw [Nat.cast_succ, mul_add_one]
theorem rnDk_succ (k : ℕ) : rnDk (k + 1) = rnDk k + leOe (Om 1) := by
  unfold rnDk; rw [Nat.cast_succ, mul_add_one, add_assoc]
theorem rnBk_one : rnBk 1 = leWe (Om (1 + 1)) := by unfold rnBk; rw [Nat.cast_one, mul_one]

theorem rnTW_Bk (k : ℕ) : rnTW S (rnBk k) = S.psi (rnBk (k + 1)) (Om (1 + 1)) := by
  unfold rnTW; rw [rnBk_succ]

theorem rnFWW_eq : S.psi (rnBk 1) (Om (1 + 1)) = leFWW S := by rw [rnBk_one]; rfl

theorem rnNat_mem (k : ℕ) (a b : Ordinal.{0}) : (k : Ordinal.{0}) ∈ S.CSet a b := by
  induction k with
  | zero => simpa using CSet.zero_mem (S := S) a b
  | succ k ih => rw [Nat.cast_succ]; exact CSet.succ_mem ih

theorem rnMulNat_mem {x a b : Ordinal.{0}} (hx : x ∈ S.CSet a b) (k : ℕ) :
    x * (k : Ordinal.{0}) ∈ S.CSet a b := by
  induction k with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem a b
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hx

theorem rnBk_mem (k : ℕ) (a b : Ordinal.{0}) : rnBk k ∈ S.CSet a b :=
  rnMulNat_mem (leWe_mem (mxOm2_mem _ _)) k

theorem rnBk_lt_OmW (k : ℕ) : rnBk k < Om ω := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have h1 : rnBk k < leWe (Om (1 + 1)) * ω :=
    (mul_lt_mul_iff_right₀ (leWe_pos _)).2 (natCast_lt_omega0 k)
  have h2 : leWe (Om (1 + 1)) * ω = ω ^ (Om (1 + 1) * Om (1 + 1) + 1) := by
    unfold leWe; rw [opow_add, opow_one]
  rw [h2] at h1
  exact h1.trans (ldOpow_lt_SC hSC (hSC.isSuccLimit.succ_lt ldOm2sq_lt_OmW))

theorem rnBk_lt_th (k : ℕ) : S.psi (rnBk k) (Om (1 + 1)) < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (rnBk_lt_OmW k) (rnBk_mem k _ _)

/-- **Every `β_k` is a base.** -/
theorem rnBk_base (l : Ordinal.{0}) (k : ℕ) : RnBase S l (rnBk k) := by
  refine ⟨dvd_mul_right _ _, rnBk_mem k _ _, ?_, fun d _ => rnBk_mem k _ _⟩
  rw [← rnBk_succ]
  exact (rnBk_lt_OmW (k + 1)).trans_le le_self_add

theorem rnD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1

theorem rnBk_D {n : ℕ} : ∀ k : ℕ, MvD S (rnBk k) ∧ Bc.bcB S n (rnBk k) = rnBk k
  | 0 => by rw [rnBk_zero]; exact ⟨rnD0, by rw [Bc.bcB_zero]⟩
  | k + 1 => by
    obtain ⟨hD, hB⟩ := rnBk_D (n := n) k
    obtain ⟨hDW, hBW⟩ := rnB_WW (S := S) (n := n)
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD hDW
    rw [rnBk_succ]; exact ⟨hDs, by rw [hBs, hB, hBW]⟩

theorem rnOk_D {n : ℕ} : ∀ k : ℕ, MvD S (leOe (Om 1) * (k : Ordinal.{0})) ∧
    Bc.bcB S n (leOe (Om 1) * (k : Ordinal.{0})) = leOe (Om 1) * (k : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact ⟨rnD0, by rw [Bc.bcB_zero]⟩
  | k + 1 => by
    obtain ⟨hD, hB⟩ := rnOk_D (n := n) k
    obtain ⟨hDO, hBO⟩ := rnB_OO (S := S) (n := n)
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD hDO
    rw [Nat.cast_succ, mul_add_one]; exact ⟨hDs, by rw [hBs, hB, hBO]⟩

theorem rnDk_D {n : ℕ} (k : ℕ) : MvD S (rnDk k) ∧ Bc.bcB S n (rnDk k) = rnDk k := by
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hD, hB⟩ := rnOk_D (S := S) (n := n) k
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD1 hD
  unfold rnDk; exact ⟨hDs, by rw [hBs, hB, mwB_one]⟩

theorem rnDk_lt_G (k : ℕ) : rnDk k < S.psi 0 (Om (1 + 1)) := by
  have hG : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hO : ∀ j : ℕ, leOe (Om 1) * (j : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, mul_zero]; exact hG.1
    | succ j ih => rw [Nat.cast_succ, mul_add_one]; exact hG.isPrincipal ih rnOO_lt_G
  exact hG.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG)) (hO k)

theorem rnDk_own {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (k : ℕ) :
    A + rnDk k ∈ S.CSet (A + rnDk k) (S.psi (A + rnDk k) (Om 1)) := by
  refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) ?_
  exact CSet.add_mem (CSet.one_mem _ _) (rnMulNat_mem (leOe_mem (CSet.Om_mem (CSet.one_mem _ _))) k)

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂}·k)) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁}·k)`.** -/
theorem rnTh_k {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ k : ℕ, gxTh (upsilon l) (ldAtR S l) (S.psi (rnBk k) (Om (1 + 1))) = S.psi (A + rnDk k) (Om 1)
  | 0 => by rw [rnBk_zero, rnDk_zero]; exact ldBlk_zero hA hρ
  | k + 1 => by
    rw [← rnTW_Bk, rnTopW hl hX (rnBk_base l k) (rnDk_own hA k) (rnTh_k hl hX hA hρ k), rnDk_succ,
      add_assoc]

/-- **`Θ_λ(ψ_{Ω₂}(Ω₂^{Ω₂})) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁})`.** -/
theorem rnTh_FWW {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (leFWW S) = S.psi (A + 1 + leOe (Om 1)) (Om 1) := by
  rw [← rnFWW_eq, rnTh_k hl hX hA hρ 1, rnDk, Nat.cast_one, mul_one, add_assoc]

/-- **The atoms `ψ_{Ω₂}(β_k) ≤ s ≤ ψ_{Ω₂}(β_{k+1})` move** once the codes below them move. -/
theorem rnAtMove_k {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl' : IsRestartIdx l') (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) (k : ℕ) :
    ∀ s ∈ ldAtR S l, S.psi (rnBk k) (Om (1 + 1)) ≤ s → s ≤ S.psi (rnBk (k + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s ≤ S.psi (rnBk (k + 1)) (Om (1 + 1)) ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro s hs h1 h2 IH
  obtain ⟨hDβ, hBβ⟩ := rnBk_D (S := S) (n := n) k
  obtain ⟨hDD, hBD⟩ := rnDk_D (S := S) (n := n) k
  have hbase' := rnTh_k hl' hX' hA' hρ' k
  rw [← hBD] at hbase'
  have hA'D := rnDk_own hA' k
  rw [← hBD] at hA'D
  rw [← rnTW_Bk] at h2 ⊢
  exact rnAtMove_base hl hl' hX hX' hbX hBψ (rnBk_base l k) (rnBk_base l' k) hDβ hBβ hDD (rnDk_lt_G k)
    (rnDk_own hA k) hA'D (rnTh_k hl hX hA hρ k) hbase' s hs h1 h2 IH

end Googology.Trans.PoR.InaccPsi.R2.Rn
