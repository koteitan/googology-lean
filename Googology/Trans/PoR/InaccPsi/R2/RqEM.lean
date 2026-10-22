import Googology.Trans.PoR.InaccPsi.R2.RqMove

/-!
# The sequence `EM_0 = Ω₁`, `EM_{j+1} = ψ_{Ω₂}(Ω₂^{Ω₂·EM_j})`: own shift codes, atoms, fixed by `B_n`

`W^E = Ω₂^E = ω^{Ω₂·E}` (`Le.leWe`), `B_n = Bc.bcB S n`, `θ = ψ_{Ω₂}(Ω_ω)`.  (`sup_j EM_j = ψ_{Ω₂}(Ω₂^{Ω₂²})` is
not used.)

* `rqMulK_mem` (`κ·x ∈ Cl(a, b)` for a strongly critical `κ ∈ Cl(a, b)` and `x ∈ Cl(a, b)`);
* `rqEM`, `rqEM_lt_Om2`, `rqEM_SC`, `rqEM_gt` (**every `ξ < EM_j` is own at the shift `Ω₂·ξ`:
  `ξ < ψ_{Ω₂}(W^{Ω₂·ξ})`**), `rqEM_lt_succ`, `rqEM_mono`, `rqOm1_le_EM`, `rqEM_lt_th` (`EM_j < θ`);
* `rqEM_code` (**every `EM_j` is a code at every named restart**), `rqEM_B` (**`B_n(EM_j) = EM_j`**).

No new axiom.  New definition: `rqEM`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

theorem rqMulK_mem {κ a b x : Ordinal.{0}} (hκ : SC κ) (hκC : κ ∈ S.CSet a b) (hx : x ∈ S.CSet a b) :
    κ * x ∈ S.CSet a b := by
  have e : κ * x = ω ^ κ * x := by rw [gg_SC_eps hκ]
  rw [e]; exact leMulOp_mem hκC x hx

/-- `EM_0 = Ω₁`, `EM_{j+1} = ψ_{Ω₂}(W^{Ω₂·EM_j})`. -/
noncomputable def rqEM (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (leWe (Om (1 + 1) * rqEM S j)) (Om (1 + 1))

theorem rqEM_lt_Om2 : ∀ j, rqEM S j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem rqEM_SC : ∀ j, SC (rqEM S j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

/-- **Every `ξ < EM_j` is own at the shift `Ω₂·ξ`.** -/
theorem rqEM_gt : ∀ j x, x < rqEM S j → x < S.psi (leWe (Om (1 + 1) * x)) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (rqEM S j) with h' | h'
    · exact rqEM_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (mul_le_mul_right h' _))).1

theorem rqEM_lt_succ : ∀ j, rqEM S j < rqEM S (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rqEM_lt_succ j
    have hle : rqEM S (j + 1) ≤ rqEM S (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (mul_le_mul_right IH.le _))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_lt ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 IH)) ?_
    exact leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (IH.trans_le hle)))

theorem rqEM_mono {j j' : ℕ} (h : j ≤ j') : rqEM S j ≤ rqEM S j' :=
  (strictMono_nat_of_lt_succ (fun i => rqEM_lt_succ (S := S) i)).monotone h

theorem rqOm1_le_EM (j : ℕ) : Om (1 : Ordinal.{0}) ≤ rqEM S j := rqEM_mono (S := S) (Nat.zero_le j)

theorem rqMulW_lt_OmW {x : Ordinal.{0}} (hx : x < Om (1 + 1)) : Om (1 + 1) * x < Om ω :=
  ldMul_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW (hx.trans ldOm2_lt_OmW)

/-- `EM_j < θ`. -/
theorem rqEM_lt_th : ∀ j, rqEM S j < ConjT.th S
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rqEM_lt_th j
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (roWe_lt_OmW (rqMulW_lt_OmW (rqEM_lt_Om2 j)))
      (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt IH)))

/-- **Every `EM_j` is a code** at a named restart. -/
theorem rqEM_code {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rqEM S j)
  | 0 => GxCl.om
  | j + 1 => by
    have IH := rqEM_code hl hX j
    refine GxCl.atom ⟨leWe (Om (1 + 1) * rqEM S j), ?_, ?_, rfl⟩
    · exact leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) ((ldHull_iff hl hX (rqEM_lt_Om2 j)).2 IH))
    · exact (roWe_lt_OmW (rqMulW_lt_OmW (rqEM_lt_Om2 j))).trans_le le_self_add

/-- `B_n(Ω₂·(Ω₂·x)) = Ω₂·(Ω₂·x)` for a strongly critical `x ∈ MvD` fixed by `B_n`. -/
theorem rqB_WWx {n : ℕ} {x : Ordinal.{0}} (hx : SC x) (hDx : MvD S x) (hBx : Bc.bcB S n x = x) :
    MvD S (Om (1 + 1) * (Om (1 + 1) * x)) ∧
      Bc.bcB S n (Om (1 + 1) * (Om (1 + 1) * x)) = Om (1 + 1) * (Om (1 + 1) * x) := by
  have e : Om (1 + 1) * (Om (1 + 1) * x) = ω ^ (Om (1 + 1) + (Om (1 + 1) + x)) := by
    rw [opow_add, opow_add, gg_SC_eps ldOm2_SC, gg_SC_eps hx]
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD1, hB1⟩ := mvB_add (k := n) hD2 hDx
  rw [hB2, hBx] at hB1
  obtain ⟨hD3, hB3⟩ := mvB_add (k := n) hD2 hD1
  rw [hB2, hB1] at hB3
  obtain ⟨hD4, hB4⟩ := ldB_opow (n := n) hD3
  rw [hB3] at hB4
  rw [e]; exact ⟨hD4, hB4⟩

/-- **`B_n(EM_j) = EM_j`.** -/
theorem rqEM_B {n : ℕ} : ∀ j, MvD S (rqEM S j) ∧ Bc.bcB S n (rqEM S j) = rqEM S j
  | 0 => mvB_Om1
  | j + 1 => by
    obtain ⟨hD, hB⟩ := rqEM_B (n := n) j
    obtain ⟨hDK, hBK⟩ := rqB_WWx (n := n) (rqEM_SC j) hD hB
    obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDK
    rw [hBK] at hBW
    have hown : leWe (Om (1 + 1) * rqEM S j) ∈ S.CSet (leWe (Om (1 + 1) * rqEM S j))
        (S.psi (leWe (Om (1 + 1) * rqEM S j)) (Om (1 + 1))) :=
      leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (rqEM_lt_succ j)))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDW hown
    refine ⟨hDT, ?_⟩
    change Bc.bcB S n (S.psi (leWe (Om (1 + 1) * rqEM S j)) (Om (1 + 1))) =
      S.psi (leWe (Om (1 + 1) * rqEM S j)) (Om (1 + 1))
    unfold leWe
    rw [hBT, hBW]

end Googology.Trans.PoR.InaccPsi.R2.Rq
