import Googology.Trans.PoR.InaccPsi.R2.SjAt

/-!
# The atoms `ψ_{Ω₂}(Ω₂^{Ω₂^E})`, `1 ≤ E < ε_{Ω₂+1}`, move under `B_n` (base `0`)

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Θ̂ = Sg.sgThH S λ`, `θ⁺ = Lj.ljThP`.

* `sjEps_lt_OmW` (`ε_{Ω₂+1} < Ω_ω`), `sjBase0` (`0` is a base of `W^E` at every restart for `E < ε_{Ω₂+1}`);
* `sjAtMove00` (**THE ATOM `s = ψ_{Ω₂}(W^{W^E})` MOVES**: for `E ∈ H_λ`, `1 ≤ E < ε_{Ω₂+1}`, `E` a code over
  every strongly critical `Q ≥ s`, `Ω^{Θ̂ E} + Ω₁ < ψ_{Ω₂}(0)` and `s ≤ θ`: if the codes below `s` move, then the
  conclusion of `Rw.RwAtMove10` holds at `s`, with `B_n s = ψ_{Ω₂}(W^{W^{B_n E}})`; the base move of
  `Sj.sjAtMove0` is supplied by `Rn.rnSetup` and `Ld.ldBlk_zero`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Lj
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- `ε_{Ω₂+1} < Ω_ω`. -/
theorem sjEps_lt_OmW : veblen 1 (Om (1 + 1) + 1) < Om (ω : Ordinal.{0}) := by
  have h30 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om h30
  have hW3 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have h1 : (1 : Ordinal.{0}) < Om (1 + 1 + 1) := (gg_one_lt_of_SC ldOm2_SC).trans hW3
  have h3ω : (1 + 1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 3
  exact (h3.2 1 h1 _ (h3.isPrincipal hW3 h1)).trans (Om_lt_Om.2 h3ω)

/-- `0` is a base of `W^E` at every restart, for `E < ε_{Ω₂+1}`. -/
theorem sjBase0 {l E : Ordinal.{0}} (hE : E < veblen 1 (Om (1 + 1) + 1)) : RoBaseE S l (leWe E) 0 0 := by
  have hEW : E < Om (ω : Ordinal.{0}) := hE.trans sjEps_lt_OmW
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]; exact (roWe_lt_OmW (roWe_lt_OmW hEW)).trans_le le_self_add
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **THE ATOM `ψ_{Ω₂}(W^{W^E})` MOVES** (`1 ≤ E < ε_{Ω₂+1}`, `E` own at the atom). -/
theorem sjAtMove00 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hG : leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (leWe (leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hsθ : S.psi (leWe (leWe E)) (Om (1 + 1)) ≤ ConjT.th S)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (leWe (leWe E)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (leWe (leWe E)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (leWe E)) (Om (1 + 1))) = S.psi (leWe (leWe (Bc.bcB S n E))) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (leWe (leWe E)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (leWe (leWe E)) (Om (1 + 1))) < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe E)) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (leWe (leWe E)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe E)) (Om (1 + 1)))) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have h1G1 : (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)
  -- `B_n E < ε` from the exponent move
  have hsSC : SC (S.psi (leWe (leWe E)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨-, -, -, hBEε, -⟩ := sjB_thH hl hX hl' hX' hsSC (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx hxs
      exact ⟨a, b, d, e⟩) E hEH hE (hEcl _ hsSC le_rfl)
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hA1' : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  have hb' : RoBaseE S l' (leWe (Bc.bcB S n E)) 0 (Bc.bcB S n 0) := by
    rw [Bc.bcB_zero]; exact sjBase0 hBEε
  have hbase' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n 0) (Om (1 + 1))) = S.psi (A' + 1) (Om 1) := by
    rw [Bc.bcB_zero]; exact ldBlk_zero hA' hρ'
  have hBÂ : ∀ y, MvD S y → y < S.psi 0 (Om (1 + 1)) →
      A + 1 + y ∈ S.CSet (A + 1 + y) (S.psi (A + 1 + y) (Om 1)) →
      Bc.bcB S n (S.psi (A + 1 + y) (Om 1)) = S.psi (A' + 1 + Bc.bcB S n y) (Om 1) := by
    intro y hDy hyG hown
    obtain ⟨hD1y, hB1y⟩ := mvB_add (k := n) hD1 hDy
    rw [mwB_one] at hB1y
    have h1y : 1 + y ≤ ConjT.th S := (hG1.isPrincipal h1G1 hyG).le.trans rnG_le_th
    rw [add_assoc A] at hown ⊢
    rw [hBψ _ hD1y hown h1y, hB1y, add_assoc]
  have hÂc : ∀ y, y < S.psi 0 (Om (1 + 1)) → S.psi (A + 1 + y) (Om 1) < Bc.bcC S (n + 1) := by
    intro y hyG
    rw [add_assoc]; exact hbX _ ((hG1.isPrincipal h1G1 hyG).le.trans rnG_le_th)
  have h := sjAtMove0 (β := 0) (Â := A + 1) (Â' := A' + 1) hR h1 hr hl' hB hEH hE1 hE hG (sjBase0 hE)
    (mvD_of_lt (Lw.lw_L_SC S ω).1) (fun Q hQ hQ' => hEcl Q hQ (by rwa [zero_add] at hQ')) hA1
    (ldBlk_zero hA hρ) hb' hA1' hbase' hBÂ hÂc (by rwa [zero_add])
    (fun x hx hxs => IH x hx (by rwa [zero_add] at hxs))
  simp only [zero_add, Bc.bcB_zero] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Sj
