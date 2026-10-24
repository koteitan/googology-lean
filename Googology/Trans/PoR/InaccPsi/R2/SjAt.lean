import Googology.Trans.PoR.InaccPsi.R2.SjMove

/-!
# The atoms `ψ_{Ω₂}(β + Ω₂^{Ω₂^E})`, `1 ≤ E < ε_{Ω₂+1}`, move under `B_n` once their base moves

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `Θ̂ = Sg.sgThH S λ`, `Θ̂' = Sg.sgThH S λ'`, `G₃ = ψ_{Ω₃}(0)`, `θ⁺ = Lj.ljThP`.

* `sjG3` (`W^E + Ω₂ < G₃` for `E < ε_{Ω₂+1}`), `sjB_G1` (`B_n ψ_{Ω₂}(0) = ψ_{Ω₂}(0)`), `sjB_OO`
  (`B_n(Ω^y) = Ω^{B_n y}`, `B_n(Ω₁·Ω^y) = Ω₁·Ω^{B_n y}`, `B_n(Ω^{Ω^y}) = Ω^{Ω^{B_n y}}` when
  `B_n(Ω₁·y) = Ω₁·B_n y`);
* `sjAtMove0` (**THE MOVE OF THE ATOM `s = ψ_{Ω₂}(β + W^{W^E})`**: given the closure condition of `E` at `β`, a base
  `β` of `Ro.RoBaseE (W^E) 0` with reading `Θ(ψ_{Ω₂} β) = ψ_{Ω₁} Â`, and the BASE MOVE (`B_n β` a base of
  `W^{B_n E}` at `λ'` with reading `ψ_{Ω₁} Â'`, `B_n ψ_{Ω₁}(Â + y) = ψ_{Ω₁}(Â' + B_n y)` for own `Â + y`,
  `y < ψ_{Ω₂}(0)`, and `ψ_{Ω₁}(Â + y) < c_{n+1}`), if the codes below `s` move then `s ∈ MvD`,
  `B_n s = ψ_{Ω₂}(B_n β + W^{W^{B_n E}})` is an atom at `λ'`, `B_n s < θ⁺`, `Θ s < c_{n+1}` and
  **`Θ'(B_n s) = B_n(Θ s)`**: the conclusion of `Rw.RwAtMove10` at `s`).

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

/-- `W^E + Ω₂ < ψ_{Ω₃}(0)` for `E < ε_{Ω₂+1}`. -/
theorem sjG3 {E : Ordinal.{0}} (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have h1 : (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (gg_one_lt_of_SC ldOm2_SC).trans hWG3
  have hεG3 : veblen 1 (Om (1 + 1) + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    hG3.2 1 h1 _ (hG3.isPrincipal hWG3 h1)
  exact hG3.isPrincipal (leWe_lt_SC hG3 hWG3 (hE.trans hεG3)).1 hWG3

/-- `B_n ψ_{Ω₂}(0) = ψ_{Ω₂}(0)`, `ψ_{Ω₂}(0) ∈ MvD`. -/
theorem sjB_G1 {n : ℕ} : MvD S (S.psi 0 (Om (1 + 1))) ∧ Bc.bcB S n (S.psi 0 (Om (1 + 1))) = S.psi 0 (Om (1 + 1)) := by
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hD, hB⟩ := mxB_atom (n := n) hD0 (CSet.zero_mem (S := S) 0 (S.psi 0 (Om (1 + 1))))
  rw [Bc.bcB_zero] at hB
  exact ⟨hD, hB⟩

/-- `B_n(Ω^y) = Ω^{B_n y}` and `B_n(Ω^{Ω^y}) = Ω^{Ω^{B_n y}}` when `B_n(Ω₁·y) = Ω₁·B_n y`. -/
theorem sjB_OO {n : ℕ} {y : Ordinal.{0}} (hDOy : MvD S (Om 1 * y))
    (hBOy : Bc.bcB S n (Om 1 * y) = Om 1 * Bc.bcB S n y) :
    MvD S (leOe y) ∧ Bc.bcB S n (leOe y) = leOe (Bc.bcB S n y) ∧
      MvD S (leOe (leOe y)) ∧ Bc.bcB S n (leOe (leOe y)) = leOe (leOe (Bc.bcB S n y)) ∧
      MvD S (Om 1 * leOe y) ∧ Bc.bcB S n (Om 1 * leOe y) = Om 1 * leOe (Bc.bcB S n y) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have eK : ∀ z, Om 1 * leOe z = ω ^ (Om 1 + Om 1 * z) := fun z => by
    unfold leOe; rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  obtain ⟨hD1, hB1⟩ := ldB_opow (n := n) hDOy
  rw [hBOy] at hB1
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDO hDOy
  rw [hBO, hBOy] at hBK
  obtain ⟨hDK2, hBK2⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBK2
  have hDOO : MvD S (Om 1 * leOe y) := by rw [eK]; exact hDK2
  have hBOO : Bc.bcB S n (Om 1 * leOe y) = Om 1 * leOe (Bc.bcB S n y) := by rw [eK, hBK2, eK]
  obtain ⟨hD2, hB2⟩ := ldB_opow (n := n) hDOO
  rw [hBOO] at hB2
  exact ⟨hD1, hB1, hD2, hB2, hDOO, hBOO⟩

/-- **THE MOVE OF THE ATOM `ψ_{Ω₂}(β + W^{W^E})`** once its base moves and the codes below it move. -/
theorem sjAtMove0 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {E β Â Â' : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hG : leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hb : RoBaseE S l (leWe E) 0 β) (hDβ : MvD S β)
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    (hb' : RoBaseE S l' (leWe (Bc.bcB S n E)) 0 (Bc.bcB S n β))
    (hÂ' : Â' ∈ S.CSet Â' (S.psi Â' (Om 1)))
    (hbase' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n β) (Om (1 + 1))) = S.psi Â' (Om 1))
    (hBÂ : ∀ y, MvD S y → y < S.psi 0 (Om (1 + 1)) → Â + y ∈ S.CSet (Â + y) (S.psi (Â + y) (Om 1)) →
      Bc.bcB S n (S.psi (Â + y) (Om 1)) = S.psi (Â' + Bc.bcB S n y) (Om 1))
    (hÂc : ∀ y, y < S.psi 0 (Om (1 + 1)) → S.psi (Â + y) (Om 1) < Bc.bcC S (n + 1))
    (hsθ : S.psi (β + leWe (leWe E)) (Om (1 + 1)) ≤ ConjT.th S)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (leWe E)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (leWe E)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (leWe E)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (leWe (Bc.bcB S n E))) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (leWe E)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (β + leWe (leWe E)) (Om (1 + 1))) < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (leWe E)) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (β + leWe (leWe E)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (leWe E)) (Om (1 + 1)))) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', -, -, -, -, -, -⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  set s := S.psi (β + leWe (leWe E)) (Om (1 + 1)) with hs_def
  have hsSC : SC s := SC_psi (InR_Om_succ 1) _
  have hEs : LeCl (Om (1 + 1)) s E := hEcl s hsSC le_rfl
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have IHm : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x) :=
    fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx hxs
      exact ⟨a, b, d, e⟩
  obtain ⟨hDE, hDWE, hBWE, hBEε, hBEH, hcl', hDΘ, hDOΘ, hBOΘ, hΘ'⟩ :=
    sjB_thH hl hX hl' hX' hsSC IHm E hEH hE hEs
  -- `B_n(W^{W^E}) = W^{W^{B_n E}}`
  obtain ⟨hDW0, hBW⟩ := ldB_opow (n := n) hDWE
  rw [hBWE] at hBW
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have eK : ∀ z, Om (1 + 1) * leWe z = ω ^ (Om (1 + 1) + Om (1 + 1) * z) := fun z => by
    unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDWE
  rw [hB2, hBWE] at hBK
  obtain ⟨hDK2, hBK2⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBK2
  have hDΩW : MvD S (Om (1 + 1) * leWe E) := by rw [eK]; exact hDK2
  have hBΩW : Bc.bcB S n (Om (1 + 1) * leWe E) = Om (1 + 1) * leWe (Bc.bcB S n E) := by rw [eK, hBK2, eK]
  obtain ⟨hDWW0, hBWW⟩ := ldB_opow (n := n) hDΩW
  rw [hBΩW] at hBWW
  have hDWW : MvD S (leWe (leWe E)) := hDWW0
  have hBWW' : Bc.bcB S n (leWe (leWe E)) = leWe (leWe (Bc.bcB S n E)) := hBWW
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDWW
  rw [hBWW'] at hBa
  -- the atom
  have hb0 := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb0
  rw [add_zero] at hβd hβA hβown
  have hown : β + leWe (leWe E) ∈ S.CSet (β + leWe (leWe E)) s :=
    CSet.add_mem (hβown _ le_rfl) (leWe_mem (leWe_mem (sjCl_mem hEs)))
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
  rw [hBa] at hBs
  -- the reading at `λ`
  have e1 := sjTop0 hl hX hEH hE1 hE (sjG3 hE) hG hb hÂ hbase hEcl
  -- the reading at `λ'`
  have hBE1 : 1 ≤ Bc.bcB S n E := by
    have := leB_le (n := n) hD1 hDE hE1; rwa [mwB_one] at this
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  obtain ⟨hDO1, hBO1, hDO2, hBO2, -, -⟩ := sjB_OO (n := n) hDOΘ hBOΘ
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDG1, hBG1⟩ := sjB_G1 (S := S) (n := n)
  have hG' : leOe (sgThH S l' (Bc.bcB S n E)) + Om 1 < S.psi 0 (Om (1 + 1)) := by
    obtain ⟨hDs1, hBs1⟩ := mvB_add (k := n) hDO1 hDO
    have h := (mvB_lt_iff (k := n) hDs1 hDG1).2 hG
    rwa [hBs1, hBO1, hBO, hBG1, ← hΘ'] at h
  have hEcl' : ∀ Q, SC Q → S.psi (Bc.bcB S n β + leWe (leWe (Bc.bcB S n E))) (Om (1 + 1)) ≤ Q →
      LeCl (Om (1 + 1)) Q (Bc.bcB S n E) := fun Q hQ hQ' => hcl' hDs Q hQ (by rw [hBs]; exact hQ')
  have e1' := sjTop0 hl' hX' hBEH hBE1 hBEε (sjG3 hBEε) hG' hb' hÂ' hbase' hEcl'
  -- the own condition of `Â + Ω^{Ω^{Θ̂ E}}`
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  have hOw : SgOwn S β 0 (fun y => y) (sgTmH E) := by
    refine sjOwn hl hX (X0 := 0) (by rwa [zero_add]) (fun d hd => hβown d (by rwa [zero_add] at hd))
      (fun Q hQ _ => LeCl.zero hQ.1) (by rw [zero_add]; exact le_self_add.trans_lt (sjG3 hE))
      (fun Q hQ hQ' => hEcl Q hQ (by rwa [zero_add] at hQ')) hEH hE (CSet.zero_mem _ _)
  obtain ⟨-, hdat2, -, -⟩ := sgDat (S := S) (l := l) (b := β) (X0 := 0) (sgTmH E) (fun y => y)
    (fun _ _ h => h) hw hOw
  have hΘmem : sgThH S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) s) := by
    refine hdat2 _ ?_
    rw [hv, zero_add]
  have hyG : leOe (leOe (sgThH S l E)) < S.psi 0 (Om (1 + 1)) :=
    (leOe_lt_SC hG1 hΩG1 (le_self_add.trans_lt hG)).1
  have hownÂ : Â + leOe (leOe (sgThH S l E)) ∈ S.CSet (Â + leOe (leOe (sgThH S l E)))
      (S.psi (Â + leOe (leOe (sgThH S l E))) (Om 1)) := by
    refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leOe_mem (leOe_mem ?_))
    rw [← e1]
    exact CSet_mono zero_le le_rfl hΘmem
  -- the conclusion
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  refine ⟨hDs, hBs, ?_, ?_, ?_, ?_⟩
  · rw [hBs]
    obtain ⟨-, hβH', hβA', -, -⟩ := hb'
    rw [add_zero] at hβA'
    exact ⟨_, CSet.add_mem hβH' (leWe_mem (leWe_mem hBEH)), hβA', rfl⟩
  · exact (leB_le (n := n) hDs hDθ hsθ).trans_lt (by rw [hBθ]; exact ljTh_lt_ThP)
  · rw [e1]; exact hÂc _ hyG
  · rw [hBs, e1', e1, hBÂ _ hDO2 hyG hownÂ, hBO2, hΘ']

end Googology.Trans.PoR.InaccPsi.R2.Sj
