import Googology.Trans.PoR.InaccPsi.R2.TdBr

/-!
# ONE level system up to `E_K = φ(K, Ω₂ + 1)`, `K = ψ_{Ω₁}(Ω_ω)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ̂ = Ta.taTh`, `CL = Sn.SnCL`, `G1 = ψ_{Ω₂}(0)`,
`G3 = ψ_{Ω₃}(0)`, `K = tdK S = ψ_{Ω₁}(Ω_ω)`, `TdSm S a`: `1 ≤ a < K`.

* `tdThH_own` (**`Θ̂ E ∈ Cl(0, Θ T)` and `Θ̂ E` is a level-1 code over every strongly critical `Q ≥ Θ T`** when
  `E < E_K` in `H_λ` is a code over every `Q ≥ T`, for `T ≥ K`), `tdThH_lt_G`, `tdOwP`;
* `tdTop_lim`, `tdTop_lt_G3`, `tdLS` (**THE LEVEL SYSTEM `St.StLS S λ E_K Θ̂`**: every level `1 ≤ E < E_K` of the
  hull; no hypothesis beyond the restart index).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

theorem tdTop_lim : IsSuccLimit (tdTop S) := taVeb_lim tdK_SC.1.ne'

theorem tdTop_lt_G3 : tdTop S < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  exact hG3.2 _ (tdK_lt_Om2.trans rwW_lt_G3) _ (hG3.isPrincipal rwW_lt_G3 (gg_one_lt_of_SC hG3))

section Own

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The image `Θ̂ E` of an exponent that is a code above `T`** is in `Cl(0, Θ T)` and a level-1 code above `Θ T`. -/
theorem tdThH_own : ∀ E, E ∈ cdHull S l → E < tdTop S → ∀ T, SC T → tdK S ≤ T →
    (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E) →
    taTh S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q (taTh S l E) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE T hT hTK hcl
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [taTh_zero]; exact ⟨CSet.zero_mem _ _, fun Q hQ _ => LeCl.zero hQ.1⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  swap
  · -- a node
    obtain ⟨ha, hΩy, hyE, hval⟩ := tdNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := (tdSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    have hycl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (invVeblen₂ E - Om (1 + 1)) := fun Q hQ hTQ => by
      have h : LeCl (Om (1 + 1)) Q (veblen (invVeblen₁ E) (invVeblen₂ E)) := by rw [hval]; exact hcl Q hQ hTQ
      have hy := taCl_inv hQ ldOm2_SC (tdSm_lt_Om2 ha) h
      exact (leClDec hQ ldOm2_SC _ hy).1 _ LeCl.om hΩy.le
    obtain ⟨h1, h2⟩ := IH _ hy'E hy'H (hy'E.trans hE) T hT hTK hycl
    have hgT : tdK S ≤ gxTh (upsilon l) (ldAtR S l) T := tdTh_K hl hX hTK
    rw [taTh_node hc ⟨hΩy, hyE⟩]
    exact ⟨CSet.phi_mem (tdSm_mem ha hgT) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) h1),
      fun Q hQ hTQ => LeCl.phi (LeCl.small (tdSm_lt ha (hgT.trans hTQ))) (LeCl.add LeCl.om (h2 Q hQ hTQ))⟩
  set e := sgLW E with he
  have hel : e < E := hc.2
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
  have hecl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ => (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).1
  have hrcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (E % leWe e) := fun Q hQ hTQ =>
    (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).2.1
  have hqT : E / leWe e < T := (Sw.swCl_cnf hT (hcl T hT le_rfl)).2.2
  have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
  obtain ⟨he1, he2⟩ := IH e hel heH (hel.trans hE) T hT hTK hecl
  obtain ⟨hr1, hr2⟩ := IH _ hr hrH (hr.trans hE) T hT hTK hrcl
  rw [tdTh_cnf h1ρ hc (tdTm_spec hl hX _ hrH (hr.trans hE)).1]
  refine ⟨CSet.add_mem (leMulOe_mem he1 (CSet.of_lt hΘq)) hr1, fun Q hQ hTQ => ?_⟩
  refine LeCl.add ?_ (hr2 Q hQ hTQ)
  exact rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (he2 Q hQ hTQ)) Ph.ph_SC_Om1 _
    (LeCl.small (hΘq.trans_le hTQ))

/-- **`Θ̂ E < ψ_{Ω₂}(0)`** for every `E < E_K` in the hull. -/
theorem tdThH_lt_G : ∀ E, E ∈ cdHull S l → E < tdTop S → taTh S l E < S.psi 0 (Om (1 + 1)) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [taTh_zero]; exact hG1.1
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  swap
  · obtain ⟨ha, hΩy, hyE, hval⟩ := tdNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := (tdSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    have h1 := IH _ hy'E hy'H (hy'E.trans hE)
    rw [taTh_node hc ⟨hΩy, hyE⟩]
    exact hG1.2 _ (tdSm_lt ha (tdK_le_psi2 0)) _ (hG1.isPrincipal hΩG1 h1)
  set e := sgLW E with he
  have hel : e < E := hc.2
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
  rw [tdTh_cnf h1ρ hc (tdTm_spec hl hX _ hrH (hr.trans hE)).1]
  exact hG1.isPrincipal (ldMul_lt_SC hG1 (leOe_lt_SC hG1 hΩG1 h1).1 hΘq) h2

/-- **The closure condition is an own predicate with data** (`Sc.ScOwP`). -/
theorem tdOwP {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < tdTop S) :
    ScOwP S l (Sn.SnCL S E) E (taTh S l E) := by
  refine ⟨fun b X0 h => ?_, fun b β X0 X0' h hb hX' => Sn.snCL_mono h hb hX'⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨h1, h2⟩ := tdThH_own hl hX E hEH hE _ hT (tdK_le_psi2 _) h
  exact ⟨hE1, hEH, sjCl_mem (h _ hT le_rfl), h1, h, h2⟩

/-- **THE LEVEL SYSTEM UP TO `E_K = φ(K, Ω₂ + 1)`**: `St.StLS S λ E_K Θ̂`. -/
theorem tdLS : StLS S l (tdTop S) (taTh S) :=
  ⟨tdTop_lim, tdTop_lt_G3, fun E hEH _ hE => tdThH_lt_G hl hX E hEH hE,
    fun _ hEH h1 hE => tdOwP hl hX hEH h1 hE, fun _ hEH h1 hE => tdLev hl hX hEH h1 hE⟩

end Own

end Googology.Trans.PoR.InaccPsi.R2.Td
