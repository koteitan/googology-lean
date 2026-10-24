import Googology.Trans.PoR.InaccPsi.R2.SnCl

/-!
# The closure condition as the own predicate of the levels `E < ε_{Ω₂+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂ = Sg.sgThH S λ`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(b, X₀) = ψ_{Ω₂}(b + W^{X₀ + W^E})`,
`G = ψ_{Ω₂}(0)`, `ε = ε_{Ω₂+1}`.

* `snOtp_lt` (**an order type of a countable set is countable**: `cdOtp C m < Ω₁` when `C ∩ m ⊆ Cl(A, ρ)`,
  `ρ < Ω₁`), `snTh_lt_Om1` (**`Θ_λ(x) < Ω₁` for every `x ≤ Ω₂`**, no reading needed);
* `snPred` (a code `x + 1` gives the code `x`);
* `snThH_own` (**`Θ̂ E ∈ Cl(0, Θ T)` and `Θ̂ E` is a level-1 code over every strongly critical `Q ≥ Θ T`** when
  `E < ε` in the hull is a code over every strongly critical `Q ≥ T`), `snThH_lt_G` (`Θ̂ E < G` for every
  `E < ε` in the hull);
* `SnCL S E b X₀` (**the closure condition**: `E` is a code over every strongly critical `Q ≥ T_E(b, X₀)`),
  `snCL_mono`, `snOwP` (**the closure condition is an own predicate with data**, `Sc.ScOwP`), `snLev`
  (**the level statement `Sc.ScLev (SnCL E) E (Θ̂ E)`** = `Sj.sjLevT_all`).

No new axiom.  New definition: the hypothesis name `SnCL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Cardinal Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

open Classical in
/-- **The order type of a set of codes inside a countable closure is countable.** -/
theorem snOtp_lt {C : Set Ordinal.{0}} {A ρ M : Ordinal.{0}} (hρ : ρ < Om 1)
    (hCD : ∀ c ∈ C, c < M → c ∈ S.CSet A ρ) : ∀ m, m ≤ M → cdOtp C m < Om 1 := by
  obtain ⟨hreg, hunc, hκord⟩ := (Low.InR_Om_one (S := S)).regular
  have hlim : Order.IsSuccLimit (Om 1 : Ordinal.{0}) := by rw [hκord]; exact isSuccLimit_ord hunc.le
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro hmM
  rw [cdOtp_eq]
  have hbdd : BddAbove (range fun x : ↥(C ∩ Iio m) => cdOtp C x.1 + 1) := Ordinal.bddAbove_of_small
  have hle : (⨆ c : Iio m, if c.1 ∈ C then cdOtp C c.1 + 1 else 0) ≤
      ⨆ x : ↥(C ∩ Iio m), cdOtp C x.1 + 1 := by
    refine ciSup_le' fun c => ?_
    split_ifs with h
    · exact le_ciSup (f := fun x : ↥(C ∩ Iio m) => cdOtp C x.1 + 1) hbdd ⟨c.1, h, c.2⟩
    · exact zero_le
  refine hle.trans_lt ?_
  have hρc : ρ < (Om 1 : Ordinal.{0}).card.ord := lt_of_lt_of_eq hρ hκord
  have h : (⨆ x : ↥(C ∩ Iio m), cdOtp C x.1 + 1) < (Om 1 : Ordinal.{0}).card.ord := by
    refine iSup_lt_ord_big hreg ?_ fun x => ?_
    · have hsub : C ∩ Iio m ⊆ S.CSet A ρ := fun c hc => hCD c hc.1 (lt_of_lt_of_le hc.2 hmM)
      refine lt_of_le_of_lt ((mk_le_mk_of_subset hsub).trans (mk_CSet_le A ρ)) ?_
      refine max_lt ?_ ?_
      · rw [Cardinal.lift_lt]; exact lt_ord.1 hρc
      · rw [← lift_aleph0.{1, 0}]; exact Cardinal.lift_lt.2 hunc
    · have h1 := IH x.1 x.2.2 (x.2.2.le.trans hmM)
      exact lt_of_lt_of_eq (hlim.succ_lt h1) hκord
  exact lt_of_lt_of_eq h hκord.symm

/-- **`Θ_λ(x) < Ω₁` for every `x ≤ Ω₂`.** -/
theorem snTh_lt_Om1 {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {x : Ordinal.{0}}
    (hx : x ≤ Om (1 + 1)) : gxTh (upsilon l) (ldAtR S l) x < Om 1 := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  exact snOtp_lt (S := S) (A := ConjT.Aη S (cdEta S l)) hρ1
    (fun c hc hcM => (ldHull_iff hl hX hcM).2 hc) x hx

/-- A code `x + 1` gives the code `x`. -/
theorem snPred {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) : ∀ x, LeCl κ Q (x + 1) → LeCl κ Q x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact LeCl.zero hQ.1
  have hlog : log ω (x + 1) = log ω x := by
    have h1 : (1 : Ordinal.{0}) < ω ^ log ω x * ω := by
      have := opow_pos (log ω x) omega0_pos
      calc (1 : Ordinal.{0}) < ω := one_lt_omega0
        _ ≤ ω ^ log ω x * ω := Ordinal.le_mul_right _ this
    refine le_antisymm ?_ (log_mono_right _ le_self_add)
    have hlt : x + 1 < ω ^ (log ω x + 1) := by
      rw [opow_add, opow_one]
      have hx1 : x < ω ^ log ω x * ω := by
        rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hpr : IsPrincipal (· + ·) (ω ^ log ω x * ω) := by
        rw [← opow_succ]; exact isPrincipal_add_omega0_opow _
      exact hpr hx1 h1
    exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt one_lt_omega0 (by simp)).1 hlt)
  obtain ⟨hsub, hl1⟩ := leClDec hQ hκ (x + 1) hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hlc : LeCl κ Q (ω ^ log ω x) := by rw [← hlog]; exact LeCl.opow hQ.1 hl1
  have hr := hsub _ hlc (hlead.trans le_self_add)
  have e : x + 1 - ω ^ log ω x = x - ω ^ log ω x + 1 := by
    refine Ordinal.sub_eq_of_add_eq ?_
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hlead]
  rw [e] at hr
  have h2 := IH _ (leRest_lt hx0) hr
  have e2 : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  rw [← e2]; exact LeCl.add hlc h2

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The image `Θ̂ E` of an exponent that is a code above `T`** is in `Cl(0, Θ T)` and a level-1 code above `Θ T`. -/
theorem snThH_own : ∀ E, E ∈ cdHull S l → E < veblen 1 (Om (1 + 1) + 1) → ∀ T, SC T →
    (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E) →
    sgThH S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q (sgThH S l E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE T hT hcl
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [sgThH_zero]; exact ⟨CSet.zero_mem _ _, fun Q hQ _ => LeCl.zero hQ.1⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := sgLW_lt_self hE1 hE
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
  have hecl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ =>
    sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC E (hcl Q hQ hTQ)).2
  have hrcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (E % leWe e) := fun Q hQ hTQ =>
    LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * e) (hcl Q hQ hTQ)
  have hqT : E / leWe e < T := by
    have hb := leCl_boundY hT ldOm2_SC (hecl T hT le_rfl) E (hcl T hT le_rfl) hE2
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 hb
  have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
  obtain ⟨he1, he2⟩ := IH e hel heH (hel.trans hE) T hT hecl
  obtain ⟨hr1, hr2⟩ := IH _ hr hrH (hr.trans hE) T hT hrcl
  rw [sgThH_cnf l hE1 hE]
  refine ⟨CSet.add_mem (leMulOe_mem he1 (CSet.of_lt hΘq)) hr1, fun Q hQ hTQ => ?_⟩
  refine LeCl.add ?_ (hr2 Q hQ hTQ)
  exact rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (he2 Q hQ hTQ)) Ph.ph_SC_Om1 _
    (LeCl.small (hΘq.trans_le hTQ))

/-- **`Θ̂ E < ψ_{Ω₂}(0)`** for every `E < ε_{Ω₂+1}` in the hull. -/
theorem snThH_lt_G : ∀ E, E ∈ cdHull S l → E < veblen 1 (Om (1 + 1) + 1) → sgThH S l E < S.psi 0 (Om (1 + 1)) := by
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [sgThH_zero]; exact hG1.1
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := sgLW_lt_self hE1 hE
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hqW : E / leWe e < Om (1 + 1) := by
    have h2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  have hΘq := (snTh_lt_Om1 hl hX hqW.le).trans hΩG1
  have h1 := IH e hel heH (hel.trans hE)
  have h2 := IH _ hr hrH (hr.trans hE)
  rw [sgThH_cnf l hE1 hE]
  exact hG1.isPrincipal (ldMul_lt_SC hG1 (leOe_lt_SC hG1 hΩG1 h1).1 hΘq) h2

end Main

/-- **The closure condition** of the exponent `E` over the offset `X₀` at the base `b`. -/
def SnCL (S : InaccSeq.{0}) (E b X0 : Ordinal.{0}) : Prop :=
  ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E

theorem snCL_mono {E b β X0 X0' : Ordinal.{0}} (h : SnCL S E b X0) (hb : b ≤ β) (hX : X0 ≤ X0') :
    SnCL S E β X0' :=
  fun Q hQ hQ' => h Q hQ ((scTop_mono (S := S) hb hX (le_refl E)).trans hQ')

section Main2

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The closure condition is an own predicate with data** (`Sc.ScOwP`). -/
theorem snOwP {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    ScOwP S l (SnCL S E) E (sgThH S l E) := by
  refine ⟨fun b X0 h => ?_, fun b β X0 X0' h hb hX' => snCL_mono h hb hX'⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨h1, h2⟩ := snThH_own hl hX E hEH hE _ hT h
  exact ⟨hE1, hEH, sjCl_mem (h _ hT le_rfl), h1, h, h2⟩

/-- **The level statement with the closure condition** (`Sj.sjLevT_all`). -/
theorem snLev {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    ScLev S l (SnCL S E) E (sgThH S l E) :=
  fun _ _ _ hoff hd hG3 hG hcl => sjLevT_all hl hX hEH hE1 hE hoff hd hG3 hG hcl

end Main2

end Googology.Trans.PoR.InaccPsi.R2.Sn
