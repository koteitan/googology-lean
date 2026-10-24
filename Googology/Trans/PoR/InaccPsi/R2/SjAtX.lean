import Googology.Trans.PoR.InaccPsi.R2.SjAt0

/-!
# The atoms `ψ_{Ω₂}(β + Ω₂^{X₀ + Ω₂^E})` over an offset move under `B_n` once the offset and the base move

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `Θ̂ = Sg.sgThH S λ`, `Θ̂' = Sg.sgThH S λ'`, `θ⁺ = Lj.ljThP`.

* `sjAtMoveX` (**THE MOVE OF THE ATOM `s = ψ_{Ω₂}(β + W^{X₀ + W^E})`, `1 ≤ E < ε_{Ω₂+1}`**: given the closure
  condition of `E` at `β`, an offset `Rv.RvOff β X₀ X̂₀` with `W^E ∣ X₀` and the size bounds, a base `β` of
  `Ro.RoBaseE (X₀ + W^E) 0` with reading `ψ_{Ω₁} Â`; THE OFFSET MOVE (`B_n(Ω₂·X₀) = Ω₂·X₀_B`,
  `B_n(Ω₁·X̂₀) = Ω₁·X̂₀_B`, `Rv.RvOff (B_n β) X₀_B X̂₀_B` at `λ'`, `W^{B_n E} ∣ X₀_B`, the size bounds at `λ'`) and
  THE BASE MOVE (as in `Sj.sjAtMove0`); if the codes below `s` move, the conclusion of `Rw.RwAtMove10` holds at
  `s`, with `B_n s = ψ_{Ω₂}(B_n β + W^{X₀_B + W^{B_n E}})`).

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

/-- **THE MOVE OF THE ATOM `ψ_{Ω₂}(β + W^{X₀ + W^E})`** once its offset and its base move. -/
theorem sjAtMoveX {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {E β X0 Xh0 X0B Xh0B Â Â' : Ordinal.{0}}
    (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hoff : RvOff S l β X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hb : RoBaseE S l (X0 + leWe E) 0 β) (hDβ : MvD S β)
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    -- the offset move
    (hDX0 : MvD S (Om (1 + 1) * X0)) (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B)
    (hDXh0 : MvD S (Om 1 * Xh0)) (hBXh0 : Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B)
    (hoff' : RvOff S l' (Bc.bcB S n β) X0B Xh0B) (hd' : leWe (Bc.bcB S n E) ∣ X0B)
    (hG3' : X0B + leWe (Bc.bcB S n E) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG' : Xh0B + leOe (sgThH S l' (Bc.bcB S n E)) + Om 1 < S.psi 0 (Om (1 + 1)))
    -- the base move
    (hb' : RoBaseE S l' (X0B + leWe (Bc.bcB S n E)) 0 (Bc.bcB S n β))
    (hÂ' : Â' ∈ S.CSet Â' (S.psi Â' (Om 1)))
    (hbase' : gxTh (upsilon l') (ldAtR S l') (S.psi (Bc.bcB S n β) (Om (1 + 1))) = S.psi Â' (Om 1))
    (hBÂ : ∀ y, MvD S y → y < S.psi 0 (Om (1 + 1)) → Â + y ∈ S.CSet (Â + y) (S.psi (Â + y) (Om 1)) →
      Bc.bcB S n (S.psi (Â + y) (Om 1)) = S.psi (Â' + Bc.bcB S n y) (Om 1))
    (hÂc : ∀ y, y < S.psi 0 (Om (1 + 1)) → S.psi (Â + y) (Om 1) < Bc.bcC S (n + 1))
    (hsθ : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ ConjT.th S)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (X0B + leWe (Bc.bcB S n E))) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)))) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', -, -, -, -, -, -⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  set s := S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) with hs_def
  have hsSC : SC s := SC_psi (InR_Om_succ 1) _
  have hEs : LeCl (Om (1 + 1)) s E := hEcl s hsSC le_rfl
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDE, hDWE, hBWE, hBEε, hBEH, hcl', hDΘ, hDOΘ, hBOΘ, hΘ'⟩ :=
    sjB_thH hl hX hl' hX' hsSC (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx hxs
      exact ⟨a, b, d, e⟩) E hEH hE hEs
  -- `B_n(W^{X₀ + W^E}) = W^{X₀_B + W^{B_n E}}`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have eK : ∀ z, Om (1 + 1) * leWe z = ω ^ (Om (1 + 1) + Om (1 + 1) * z) := fun z => by
    unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDWE
  rw [hB2, hBWE] at hBK
  obtain ⟨hDK2, hBK2⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBK2
  have hDΩW : MvD S (Om (1 + 1) * leWe E) := by rw [eK]; exact hDK2
  have hBΩW : Bc.bcB S n (Om (1 + 1) * leWe E) = Om (1 + 1) * leWe (Bc.bcB S n E) := by rw [eK, hBK2, eK]
  obtain ⟨hDX, hBX⟩ := mvB_add (k := n) hDX0 hDΩW
  rw [hBX0, hBΩW, ← mul_add, ← mul_add] at hBX
  rw [← mul_add] at hDX
  obtain ⟨hDWX0, hBWX⟩ := ldB_opow (n := n) hDX
  rw [hBX] at hBWX
  have hDWX : MvD S (leWe (X0 + leWe E)) := hDWX0
  have hBWX' : Bc.bcB S n (leWe (X0 + leWe E)) = leWe (X0B + leWe (Bc.bcB S n E)) := hBWX
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDWX
  rw [hBWX'] at hBa
  -- the atom
  obtain ⟨-, -, hX0m, hXh0m, hX0cl, -⟩ := rvOff_data hoff
  have hb0 := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb0
  rw [add_zero] at hβd hβown
  have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ s :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hown : β + leWe (X0 + leWe E) ∈ S.CSet (β + leWe (X0 + leWe E)) s :=
    CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.add_mem (CSet_mono zero_le hle0 hX0m)
      (leWe_mem (sjCl_mem hEs))))
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
  rw [hBa] at hBs
  -- the readings
  have e1 := sjLevT_all hl hX hEH hE1 hE hoff hd hG3 hG hEcl β Â hb le_rfl hÂ hbase
  unfold leTe at e1
  rw [add_zero, gxTh_zero, add_zero] at e1
  have hBE1 : 1 ≤ Bc.bcB S n E := by
    have := leB_le (n := n) hD1 hDE hE1; rwa [mwB_one] at this
  have hEcl' : ∀ Q, SC Q → S.psi (Bc.bcB S n β + leWe (X0B + leWe (Bc.bcB S n E))) (Om (1 + 1)) ≤ Q →
      LeCl (Om (1 + 1)) Q (Bc.bcB S n E) := fun Q hQ hQ' => hcl' hDs Q hQ (by rw [hBs]; exact hQ')
  have e1' := sjLevT_all hl' hX' hBEH hBE1 hBEε hoff' hd' hG3' hG' hEcl' (Bc.bcB S n β) Â'
    hb' le_rfl hÂ' hbase'
  unfold leTe at e1'
  rw [add_zero, gxTh_zero, add_zero] at e1'
  -- the own condition of `Â + Ω^{X̂₀ + Ω^{Θ̂ E}}`
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  have hOw : SgOwn S β X0 (fun y => y) (sgTmH E) :=
    sjOwn hl hX hβd hβown hX0cl (le_self_add.trans_lt hG3) hEcl hEH hE hX0m
  obtain ⟨-, hdat2, -, -⟩ := sgDat (S := S) (l := l) (b := β) (X0 := X0) (sgTmH E) (fun y => y)
    (fun _ _ h => h) hw hOw
  have hΘmem : sgThH S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) s) := by
    refine hdat2 _ ?_
    rw [hv]
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hyG : leOe (Xh0 + leOe (sgThH S l E)) < S.psi 0 (Om (1 + 1)) :=
    (leOe_lt_SC hG1 hΩG1 (le_self_add.trans_lt hG)).1
  have hownÂ : Â + leOe (Xh0 + leOe (sgThH S l E)) ∈ S.CSet (Â + leOe (Xh0 + leOe (sgThH S l E)))
      (S.psi (Â + leOe (Xh0 + leOe (sgThH S l E))) (Om 1)) := by
    refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leOe_mem (CSet.add_mem ?_ ?_))
    · rw [← e1]; exact CSet_mono zero_le (gxTh_mono hle0) hXh0m
    · rw [← e1]; exact leOe_mem (CSet_mono zero_le le_rfl hΘmem)
  -- `B_n(Ω^{X̂₀ + Ω^{Θ̂ E}}) = Ω^{X̂₀_B + Ω^{Θ̂'(B_n E)}}`
  obtain ⟨-, -, -, -, hDOO, hBOO⟩ := sjB_OO (n := n) hDOΘ hBOΘ
  obtain ⟨hDY, hBY⟩ := mvB_add (k := n) hDXh0 hDOO
  rw [hBXh0, hBOO, ← mul_add, ← mul_add] at hBY
  rw [← mul_add] at hDY
  obtain ⟨hDy0, hBy⟩ := ldB_opow (n := n) hDY
  rw [hBY] at hBy
  have hDy : MvD S (leOe (Xh0 + leOe (sgThH S l E))) := hDy0
  have hBy' : Bc.bcB S n (leOe (Xh0 + leOe (sgThH S l E))) = leOe (Xh0B + leOe (Bc.bcB S n (sgThH S l E))) := hBy
  -- the conclusion
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  refine ⟨hDs, hBs, ?_, ?_, ?_, ?_⟩
  · rw [hBs]
    obtain ⟨-, hβH', hβA', -, -⟩ := hb'
    rw [add_zero] at hβA'
    obtain ⟨-, hX0BH, -, -, -, -⟩ := rvOff_data hoff'
    exact ⟨_, CSet.add_mem hβH' (leWe_mem (CSet.add_mem hX0BH (leWe_mem hBEH))), hβA', rfl⟩
  · exact (leB_le (n := n) hDs hDθ hsθ).trans_lt (by rw [hBθ]; exact ljTh_lt_ThP)
  · rw [e1]; exact hÂc _ hyG
  · rw [hBs, e1', e1, hBÂ _ hDy hyG hownÂ, hBy', hΘ']

end Googology.Trans.PoR.InaccPsi.R2.Sj
