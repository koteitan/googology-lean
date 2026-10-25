import Googology.Trans.PoR.InaccPsi.R2.UgCode

/-!
# The closure condition with `ψ₃`-atoms and the own property of the image past `Γ₂`

`T = Ug.ugTh S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `Γ₂ = Ua.uaGam = ψ₃(0)`,
`ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ₃(Ω₃)`, `C_k(Q) = Ug.UgC S k Q` (codes of level `k` with `ψ_{Ω_{k+1}}`-atoms).

* `ugC_toLe` (**a level-2 code below `Γ₂` is a code `LeCl Ω₂ Q`**: the atoms are `≥ Γ₂`);
* `UgCL S E b X₀` (**the closure condition with `ψ₃`-atoms**: `E ∈ C_2(Q)` for every strongly critical
  `Q ≥ ψ₂(b + W^{X₀ + W^E})`), `ugCL_of_sn` (`Sn.SnCL ⇒ UgCL`), `ugCL_iff_sn` (**below `Γ₂` they agree**),
  `ugCL_mono`, `ugCL_gam` (**`Γ₂` satisfies it at every base and offset**, while `Sn.SnCL` fails there:
  `Ug.ugSnCL_wall`);
* `ugOwn` (**THE OWN PROPERTY OF `T` PAST `Γ₂`**: an exponent `E ∈ H_λ ∩ Y₃` that is a level-2 code over every
  strongly critical `Q ≥ T₀` has `T E` a level-1 code (with `ψ₂`-atoms) over every strongly critical `Q ≥ Θ T₀`;
  `Ua.uaOwn` for the codes with atoms), `ugOwnCL` (the same from `UgCL`).

No new axiom.  New definition: `UgCL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **A level-2 code below `Γ₂` is a code without atoms.** -/
theorem ugC_toLe {Q x : Ordinal.{0}} (hx : UgC S (1 + 1) Q x) : x < uaGam → LeCl (Om (1 + 1)) Q x := by
  induction hx with
  | small h => exact fun _ => LeCl.small h
  | om => exact fun _ => LeCl.om
  | @add x y _ _ ihx ihy =>
    exact fun h => LeCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => LeCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @psi d _ _ _ => exact fun h => absurd (ugGam_le_psi3 (S := S) d) (not_le.2 h)

/-- **The closure condition with `ψ₃`-atoms** of the exponent `E` over the offset `X₀` at the base `b`. -/
def UgCL (S : InaccSeq.{0}) (E b X0 : Ordinal.{0}) : Prop :=
  ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q E

theorem ugCL_of_sn {E b X0 : Ordinal.{0}} (h : SnCL S E b X0) : UgCL S E b X0 :=
  fun Q hQ hQ' => UgC.of_le (h Q hQ hQ')

/-- **Below `Γ₂` the two closure conditions agree.** -/
theorem ugCL_iff_sn {E b X0 : Ordinal.{0}} (hE : E < uaGam) : UgCL S E b X0 ↔ SnCL S E b X0 :=
  ⟨fun h Q hQ hQ' => ugC_toLe (h Q hQ hQ') hE, ugCL_of_sn⟩

theorem ugCL_mono {E b β X0 X0' : Ordinal.{0}} (h : UgCL S E b X0) (hb : b ≤ β) (hX : X0 ≤ X0') :
    UgCL S E β X0' :=
  fun Q hQ hQ' => h Q hQ ((scTop_mono (S := S) hb hX (le_refl E)).trans hQ')

/-- **`Γ₂` satisfies the closure condition with `ψ₃`-atoms at every base and offset.** -/
theorem ugCL_gam (b X0 : Ordinal.{0}) : UgCL S uaGam b X0 :=
  fun _ hQ _ => ugC_gam hQ.1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE OWN PROPERTY OF `T` PAST `Γ₂`.** -/
theorem ugOwn : ∀ E, E ∈ cdHull S l → E < ugY S → ∀ T, SC T →
    (∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q E) →
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → UgC S 1 Q (ugTh S l E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hEY T hT hcl Q hQ hTQ
  rcases lt_or_ge E uaGam with hEG | hGE
  · rw [ugTh_lt hEG]
    have hle : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E := fun Q hQ hTQ => ugC_toLe (hcl Q hQ hTQ) hEG
    exact UgC.of_le ((uaOwn hl hX E hEH hEG T hT hle).2 Q hQ hTQ)
  have hpos : 0 < E := ugGam_pos.trans_le hGE
  by_cases hc : sgLW E < E
  · obtain ⟨heH, -, hqc, -, -, hrH, -, -⟩ := uaBase hl hX hEH hpos
    set e := sgLW E with he
    have hWe : leWe e ≤ E := sgLW_le hpos
    have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
    have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
    have hecl : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q e := fun Q hQ hTQ => (ugC_cnf hQ (hcl Q hQ hTQ)).1
    have hrcl : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q (E % leWe e) := fun Q hQ hTQ =>
      (ugC_cnf hQ (hcl Q hQ hTQ)).2.1
    have hqT : E / leWe e < T := (ugC_cnf hT (hcl T hT le_rfl)).2.2
    have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
    have he1 := IH e hc heH (hc.trans hEY) T hT hecl Q hQ hTQ
    have hr1 := IH _ hr hrH (hr.trans hEY) T hT hrcl Q hQ hTQ
    rw [ugTh_cnf hGE hc]
    have h1 : (1 : Ordinal.{0}) ≠ 0 := one_ne_zero
    refine UgC.add ?_ hr1
    exact ugC_mulOp hQ h1 (ugC_mulK hQ h1 _ he1) _ (UgC.small (hΘq.trans_le hTQ))
  by_cases hS : SC E
  · obtain ⟨d, hdH, hd, -, hEd⟩ := ugAtomH hl hX hEH hS (uaGam_spec.2.trans_le hGE) hEY
    have hdE : d < E := hEd ▸ hd
    have hdcl : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q d := fun Q hQ hTQ =>
      ugC_psiArg hd E (hcl Q hQ hTQ) hEd.symm
    have hTd := IH d hdE hdH (hdE.trans hEY) T hT hdcl Q hQ hTQ
    rw [← hEd, ugTh_atom hd]
    exact UgC.psi hTd (ugNormAll hl hX hdH (hdE.trans hEY)).2
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hGE hS hc
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hEH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    have hacl : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q (invVeblen₁ E) := fun Q hQ hTQ =>
      ugC_lev _ (hcl Q hQ hTQ) _ _ hv.symm hbE
    have hbcl : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q (invVeblen₂ E) := fun Q hQ hTQ =>
      ugC_arg hQ _ (hcl Q hQ hTQ) _ _ hv.symm hbE
    rw [ugTh_node hGE hc hS ⟨haE, hbE⟩]
    exact UgC.phi (IH _ haE hmem.1 (haE.trans hEY) T hT hacl Q hQ hTQ)
      (IH _ hbE hmem.2 (hbE.trans hEY) T hT hbcl Q hQ hTQ)

/-- **The own property from the closure condition with `ψ₃`-atoms.** -/
theorem ugOwnCL {E b X0 : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hEY : E < ugY S) (h : UgCL S E b X0) :
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) ≤ Q →
      UgC S 1 Q (ugTh S l E) :=
  ugOwn hl hX E hEH hEY _ (SC_psi (InR_Om_succ 1) _) h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ug
