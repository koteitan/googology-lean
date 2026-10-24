import Googology.Trans.PoR.InaccPsi.R2.SwBr

/-!
# ONE level system up to `ε_{Ω₂+ω}` and its move under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `L_k = ε_{Ω₂+1+k}`, `L̂_k = ε_{Ω₁+1+k}`, `ε_{Ω₂+ω} = Sw.swTop`, `Θ̂ = Sw.swTh` (`Θ̂ L_k = L̂_k`,
`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`).

* `swThH_own` (**`Θ̂ E ∈ Cl(0, Θ T)` and `Θ̂ E` is a level-1 code over every strongly critical `Q ≥ Θ T`** when
  `E < ε_{Ω₂+ω}` in the hull is a code over every `Q ≥ T`), `swThH_lt_G`, `swOwP`;
* `swLS` (**THE LEVEL SYSTEM `St.StLS S λ ε_{Ω₂+ω} Θ̂`**: every level `1 ≤ E < ε_{Ω₂+ω}` of the hull, no
  hypothesis beyond the restart index);
* `swB_L` (`B_n L_k = L_k`), `swB_top`, `swB_thH` (**THE MOVE OF THE EXPONENTS BELOW `ε_{Ω₂+ω}`**: as
  `Sj.sjB_thH`, with the leaves fixed), `swLSB` (**`St.StLSB S n λ λ' ε_{Ω₂+ω} Θ̂`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- `κ·φ(1, a) = φ(1, a)` for `κ < a`, `κ` strongly critical. -/
theorem swK_mul_veb {κ a : Ordinal.{0}} (hκ : SC κ) (ha : κ < a) : κ * veblen 1 a = veblen 1 a := by
  have hE : ω ^ veblen 1 a = veblen 1 a := gg_veblen_eps one_ne_zero
  have h1 : κ < ω ^ veblen 1 a := by rw [hE]; exact ha.trans_le (right_le_veblen 1 a)
  calc κ * veblen 1 a = ω ^ κ * ω ^ veblen 1 a := by rw [gg_SC_eps hκ, hE]
    _ = ω ^ (κ + veblen 1 a) := (opow_add _ _ _).symm
    _ = ω ^ veblen 1 a := by rw [Ordinal.add_of_omega0_opow_le h1 hE.le]
    _ = veblen 1 a := hE

theorem swTop_We : leWe (swTop S) = swTop S := by
  unfold leWe swTop
  rw [swK_mul_veb ldOm2_SC (lt_add_of_pos_right _ omega0_pos), gg_veblen_eps one_ne_zero]

theorem swTop_lim : IsSuccLimit (swTop S) := by
  unfold swTop
  rw [← gg_veblen_eps (x := (1 : Ordinal.{0})) one_ne_zero]
  exact isSuccLimit_opow_left isSuccLimit_omega0 (veblen_pos).ne'

section Own

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The image `Θ̂ E` of an exponent that is a code above `T`** is in `Cl(0, Θ T)` and a level-1 code above `Θ T`. -/
theorem swThH_own : ∀ E, E ∈ cdHull S l → E < swTop S → ∀ T, SC T →
    (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E) →
    swTh S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q (swTh S l E) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE T hT hcl
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [swTh_zero]; exact ⟨CSet.zero_mem _ _, fun Q hQ _ => LeCl.zero hQ.1⟩
  by_cases hL : ∃ k, E = swL k
  · obtain ⟨k, rfl⟩ := hL
    rw [swTh_leaf]; exact ⟨swLh_mem k, fun Q hQ _ => swLh_cl hQ k⟩
  push Not at hL
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := swLW_lt_self hE1 hE hL
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hqH : E / leWe e ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH hE2
  have hqW : E / leWe e < Om (1 + 1) := by
    have h2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  have hqc : GxCl (upsilon l) (ldAtR S l) (E / leWe e) := (ldHull_iff hl hX hqW).1 hqH
  have hecl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ => (swCl_cnf hQ (hcl Q hQ hTQ)).1
  have hrcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (E % leWe e) := fun Q hQ hTQ =>
    (swCl_cnf hQ (hcl Q hQ hTQ)).2.1
  have hqT : E / leWe e < T := (swCl_cnf hT (hcl T hT le_rfl)).2.2
  have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
  obtain ⟨he1, he2⟩ := IH e hel heH (hel.trans hE) T hT hecl
  obtain ⟨hr1, hr2⟩ := IH _ hr hrH (hr.trans hE) T hT hrcl
  rw [swTh_cnf h1ρ hE1 hE hL]
  refine ⟨CSet.add_mem (leMulOe_mem he1 (CSet.of_lt hΘq)) hr1, fun Q hQ hTQ => ?_⟩
  refine LeCl.add ?_ (hr2 Q hQ hTQ)
  exact rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (he2 Q hQ hTQ)) Ph.ph_SC_Om1 _
    (LeCl.small (hΘq.trans_le hTQ))

/-- **`Θ̂ E < ψ_{Ω₂}(0)`** for every `E < ε_{Ω₂+ω}` in the hull. -/
theorem swThH_lt_G : ∀ E, E ∈ cdHull S l → E < swTop S → swTh S l E < S.psi 0 (Om (1 + 1)) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [swTh_zero]; exact hG1.1
  by_cases hL : ∃ k, E = swL k
  · obtain ⟨k, rfl⟩ := hL
    rw [swTh_leaf]; exact swLh_lt_G k
  push Not at hL
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := swLW_lt_self hE1 hE hL
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hqW : E / leWe e < Om (1 + 1) := by
    have h2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  have hΘq := (Sn.snTh_lt_Om1 hl hX hqW.le).trans hΩG1
  have h1 := IH e hel heH (hel.trans hE)
  have h2 := IH _ hr hrH (hr.trans hE)
  rw [swTh_cnf h1ρ hE1 hE hL]
  exact hG1.isPrincipal (ldMul_lt_SC hG1 (leOe_lt_SC hG1 hΩG1 h1).1 hΘq) h2

/-- **The closure condition is an own predicate with data** (`Sc.ScOwP`). -/
theorem swOwP {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < swTop S) :
    ScOwP S l (Sn.SnCL S E) E (swTh S l E) := by
  refine ⟨fun b X0 h => ?_, fun b β X0 X0' h hb hX' => Sn.snCL_mono h hb hX'⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨h1, h2⟩ := swThH_own hl hX E hEH hE _ hT h
  exact ⟨hE1, hEH, sjCl_mem (h _ hT le_rfl), h1, h, h2⟩

/-- **THE LEVEL SYSTEM UP TO `ε_{Ω₂+ω}`**: `St.StLS S λ ε_{Ω₂+ω} Θ̂`. -/
theorem swLS : StLS S l (swTop S) (swTh S) :=
  ⟨swTop_lim, swTop_lt_G3, fun E hEH _ hE => swThH_lt_G hl hX E hEH hE,
    fun _ hEH h1 hE => swOwP hl hX hEH h1 hE, fun _ hEH h1 hE => swLev hl hX hEH h1 hE⟩

end Own

/-! ## The move -/

/-- **`B_n` fixes the leaves** `φ(1, κ + (k+1))` over a fixed strongly critical `κ`. -/
theorem swB_leafK {n : ℕ} {κ : Ordinal.{0}} (hκ : SC κ) (hD : MvD S κ) (hB : Bc.bcB S n κ = κ) (k : ℕ) :
    MvD S (veblen 1 (κ + ((k : Ordinal.{0}) + 1))) ∧
      Bc.bcB S n (veblen 1 (κ + ((k : Ordinal.{0}) + 1))) = veblen 1 (κ + ((k : Ordinal.{0}) + 1)) := by
  have hk1 : ((k : Ordinal.{0}) + 1) = ((k + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ]
  have hDk : MvD S ((k + 1 : ℕ) : Ordinal.{0}) :=
    mvD_of_lt ((natCast_lt_omega0 _).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hD hDk
  rw [hB, mwB_nat] at hBa
  rw [hk1]
  have h1 : (1 : Ordinal.{0}) < veblen 1 (κ + ((k + 1 : ℕ) : Ordinal.{0})) := by
    rw [← hk1]; exact (gg_one_lt_of_SC hκ).trans (swK_lt_L k)
  have h2 : κ + ((k + 1 : ℕ) : Ordinal.{0}) < veblen 1 (κ + ((k + 1 : ℕ) : Ordinal.{0})) := by
    refine Ph.ph_veblen_prin 1 _ ?_ ?_
    · rw [← hk1]; exact swK_lt_L k
    · rw [← hk1]
      exact (swNat1_lt_SC hκ k).trans (swK_lt_L k)
  obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) (Sq.sqD_one (S := S)) hDa h1 h2
  rw [mwB_one, hBa] at hBv
  exact ⟨hDv, hBv⟩

theorem swB_L {n : ℕ} (k : ℕ) : MvD S (swL k) ∧ Bc.bcB S n (swL k) = swL k :=
  swB_leafK ldOm2_SC (ldOm2_D (k := n)).1 (ldOm2_D (k := n)).2 k

theorem swB_Lh {n : ℕ} (k : ℕ) : MvD S (swLh k) ∧ Bc.bcB S n (swLh k) = swLh k :=
  swB_leafK Ph.ph_SC_Om1 (mvB_Om1 (k := n)).1 (mvB_Om1 (k := n)).2 k

theorem swB_top {n : ℕ} : MvD S (swTop S) ∧ Bc.bcB S n (swTop S) = swTop S := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hDw : MvD S (ω : Ordinal.{0}) := mvD_of_lt (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
  have hBw : Bc.bcB S n (ω : Ordinal.{0}) = ω := Bc.bcB_fix (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hD2 hDw
  rw [hB2, hBw] at hBa
  have hW : Om (1 + 1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + ω) :=
    (lt_add_of_pos_right _ omega0_pos).trans_le (right_le_veblen 1 _)
  have hlt : Om (1 + 1 : Ordinal.{0}) + ω < veblen 1 (Om (1 + 1) + ω) :=
    Ph.ph_veblen_prin 1 _ hW ((Lw.lw_omega_lt_SC ldOm2_SC).trans hW)
  have h1 : (1 : Ordinal.{0}) < veblen 1 (Om (1 + 1) + ω) := (gg_one_lt_of_SC ldOm2_SC).trans hW
  obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) (Sq.sqD_one (S := S)) hDa h1 hlt
  rw [mwB_one, hBa] at hBv
  exact ⟨hDv, hBv⟩

end Googology.Trans.PoR.InaccPsi.R2.Sw
