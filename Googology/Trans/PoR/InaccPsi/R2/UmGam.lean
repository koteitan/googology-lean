import Googology.Trans.PoR.InaccPsi.R2.UmDer

/-!
# Readings past `Γ₂` at the levels `Ω₂` and `E < ε_{Ω₂+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`, `G₁ = ψ_{Ω₂}(0)`,
`Θ̂ = Sg.sgThH`, `ε = ε_{Ω₂+1} = φ(1, Ω₂ + 1)`, `CL E b X₀ = Sn.SnCL S E b X₀` (`E` is a code `Le.LeCl Ω₂ Q` over
every strongly critical `Q ≥ ψ_{Ω₂}(b + W^{X₀ + W^E})`).

The level statements of `Um.umLev_W` and `Um.umLev_sg` at the offset `Γ₂` (`Uj.ujGamOff`).

* `umGam_bounds` (`W^E ∣ Γ₂`, `Γ₂ + W^E + Ω₂ < Y₃`, `G₁ + Ω^Ê + Ω₁ < Y₂` for `E < Γ₂`, `Ê < G₁`);
* `umGamLevW`, `umGamReadW` (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{Ω₂}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{Ω₁}})`**, no own hypothesis);
* `umOwn_sg0` (the own predicate of the normal-form term of `E` at the base `b` and the offset `Γ₂` from the closure
  condition `CL E 0 0`, by `Sj.sjOwn` at `(0, 0)` and the monotonicity of the own data);
* `umGamLevSg`, `umGamReadSg` (**`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{Θ̂ E}})` for every
  `1 ≤ E < ε` of `H_λ` with `CL E 0 0`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- The bounds at `Γ₂ + W^E`, image `G₁ + Ω^Ê`, for `E < ψ_{Ω₃}(0)`, `Ê < ψ_{Ω₂}(0)`. -/
theorem umGam_bounds {E Eh : Ordinal.{0}} (hE : E < S.psi 0 (Om (1 + 1 + 1))) (hEh : Eh < S.psi 0 (Om (1 + 1))) :
    leWe E ∣ Ua.uaGam ∧ Ua.uaGam + leWe E + Om (1 + 1) < ugY S ∧
      S.psi 0 (Om (1 + 1)) + leOe Eh + Om 1 < ujY S 0 := by
  have hY : SC (ugY S) := ujY_SC (S := S) 1
  have hWY : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have hY2 : SC (ujY S 0) := ujY_SC 0
  have hΩY2 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hEG : E < Ua.uaGam := by rw [Ud.udGam_eq]; exact hE
  refine ⟨(leWe_lt_SC Ua.uaGam_spec.1 Ua.uaGam_spec.2 hEG).2,
    hY.isPrincipal (hY.isPrincipal ujGam_lt_Y (leWe_lt_SC hY hWY (hEG.trans ujGam_lt_Y)).1) hWY,
    hY2.isPrincipal (hY2.isPrincipal ujY2_gt_G1 (leOe_lt_SC hY2 hΩY2 (hEh.trans ujY2_gt_G1)).1) hΩY2⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`RvTop (Γ₂ + W^{Ω₂}) (G₁ + Ω^{Ω₁}) 0`** at every base. -/
theorem umGamLevW (b : Ordinal.{0}) :
    RvTop S l b (Ua.uaGam + leWe (Om (1 + 1))) (S.psi 0 (Om (1 + 1)) + leOe (Om 1)) 0 := by
  obtain ⟨hd, hG3, hG⟩ := umGam_bounds (S := S) rwW_lt_G3 rwO_lt_G
  exact umLev_W hl hX b _ _ (ujGamOff hl hX b) hd hG3 hG trivial

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{Ω₂}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{Ω₁}})`** at every restart `λ` with `A` own,
`ψ_{Ω₁}(A) = ρ_λ`. -/
theorem umGamReadW {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Ua.uaGam + leWe (Om (1 + 1)))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (Om 1))) (Om 1) := by
  obtain ⟨-, hG3, -⟩ := umGam_bounds (S := S) rwW_lt_G3 rwO_lt_G
  exact ujRead0 (umGamLevW hl hX 0) (lt_of_le_of_lt le_self_add hG3) hA hρ

/-- **The own predicate of the normal-form term of `E` at every base and the offset `Γ₂`** from the closure
condition `CL E 0 0`. -/
theorem umOwn_sg0 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hEcl : SnCL S E 0 0) (b : Ordinal.{0}) : SgOwn S b Ua.uaGam (fun y => y) (sgTmH E) := by
  have hEG : E < S.psi 0 (Om (1 + 1 + 1)) := hE.trans snEps_lt_G3
  have hWG : leWe E < S.psi 0 (Om (1 + 1 + 1)) := (leWe_mono le_self_add).trans_lt (St.stWe_lt_G3 hEG)
  have h0 : SgOwn S 0 0 (fun y => y) (sgTmH E) := by
    refine Sj.sjOwn hl hX (β := 0) (X0 := 0) (dvd_zero _) (fun d _ => CSet.zero_mem _ _)
      (fun Q hQ _ => LeCl.small hQ.1) (by rw [zero_add]; exact hWG) hEcl hEH hE (CSet.zero_mem _ _)
  exact (umOwP_sg hl hX hEH hE1 hE).mono 0 b 0 Ua.uaGam h0 zero_le zero_le

/-- **`RvTop (Γ₂ + W^E) (G₁ + Ω^{Θ̂ E}) 0`** at every base, for every `1 ≤ E < ε_{Ω₂+1}` of `H_λ` with `CL E 0 0`. -/
theorem umGamLevSg (b : Ordinal.{0}) {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E)
    (hE : E < veblen 1 (Om (1 + 1) + 1)) (hEcl : SnCL S E 0 0) :
    RvTop S l b (Ua.uaGam + leWe E) (S.psi 0 (Om (1 + 1)) + leOe (sgThH S l E)) 0 := by
  obtain ⟨hd, hG3, hG⟩ := umGam_bounds (S := S) (hE.trans snEps_lt_G3) (snThH_lt_G hl hX E hEH hE)
  exact umLev_sg hl hX hEH hE1 hE b _ _ (ujGamOff hl hX b) hd hG3 hG (umOwn_sg0 hl hX hEH hE1 hE hEcl b)

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{Θ̂ E}})`** for every `1 ≤ E < ε_{Ω₂+1}` of `H_λ`
with `CL E 0 0`, at every restart `λ` with `A` own, `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem umGamReadSg {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hEcl : SnCL S E 0 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Ua.uaGam + leWe E)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (sgThH S l E))) (Om 1) := by
  obtain ⟨-, hG3, -⟩ := umGam_bounds (S := S) (hE.trans snEps_lt_G3) (snThH_lt_G hl hX E hEH hE)
  exact ujRead0 (umGamLevSg hl hX 0 hEH hE1 hE hEcl) (lt_of_le_of_lt le_self_add hG3) hA hρ

end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
