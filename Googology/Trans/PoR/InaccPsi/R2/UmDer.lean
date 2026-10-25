import Googology.Trans.PoR.InaccPsi.R2.UmLim

/-!
# Soundness of the derivations past `Γ₂`, and the level statement past `Γ₂` at every exponent `E < ε_{Ω₂+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `G₃ = ψ_{Ω₃}(0) = Γ₂`,
`G₁ = ψ_{Ω₂}(0)`, `Θ̂ = Sg.sgThH`, `ε = ε_{Ω₂+1} = φ(1, Ω₂ + 1)`.

**One soundness theorem for the derivations `Sc.ScDer` over the offsets past `Γ₂`** (`umDer_sound`): a derivation of
`E` with the image `Ê` (any of its constructors: codes, successor, the level step over a shape, the small limit,
weakening) with `E < G₃` and `Ê < G₁` gives the level statement past `Γ₂` `Uj.UjLev Ow E Ê` and the own data
`Uj.UjOwP Ow E Ê`.  The derivation itself is the one of `Sc`: the same derivation now gives the top law at every
offset past `Γ₂` (`X₀ ∈ C(X₀, ·)`, `X₀ + W^E + Ω₂ < Y₃`), not only at the offsets below `Γ₂`.  With
`Sg.sgDer_all` (**every `1 ≤ E < ε` of `H_λ` is derived**) this gives `UjLev` at every such `E` (`umLev_sg`).

* `umDer_sound` (**SOUNDNESS PAST `Γ₂`**), `umDer_all` (the same with the data of `Sc`);
* `umLev_sg` (**THE LEVEL STATEMENT PAST `Γ₂` AT EVERY `1 ≤ E < ε_{Ω₂+1}` OF `H_λ`**, own predicate the one of
  the normal-form term, image `Θ̂ E`), `umOwP_sg`, `umSh_sg` (`X₀ + W^E` is a shift past `Γ₂`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Sound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **SOUNDNESS PAST `Γ₂`: every derivation of `E < Γ₂` with the image `Ê < ψ_{Ω₂}(0)` gives the level
statement over every offset past `Γ₂`.** -/
theorem umDer_sound {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : ScDer S l Ow E Eh) :
    E < S.psi 0 (Om (1 + 1 + 1)) → Eh < S.psi 0 (Om (1 + 1)) → UjLev S l Ow E Eh := by
  induction h with
  | code hE h1 hEW => exact fun _ _ => ujLev_code hl hX _ hE h1 hEW
  | succ hd IH =>
    intro hE hEh
    exact ujLev_succ hl hX (umOwP_of_sc (scDer_sound hl hX hd).2)
      (IH ((lt_add_one _).trans hE) ((lt_add_one _).trans hEh)) (fun _ _ h => h)
  | om hshp hmono _ IH =>
    intro hgs hghs
    refine umLev_om hl hX hshp hgs hghs (fun b β X0 hO hb => hmono b β X0 X0 hO hb le_rfl) ?_
    intro ζ hζ h1 hζW hΘ1 b X0 Xh0 hoff hd hG3 hG hO
    have hsh := hshp b X0 hO.1
    exact IH ζ hζ h1 hζW ((hsh.lt ζ hζW).trans hgs) ((hsh.lth _ hΘ1).trans hghs) b X0 Xh0 hoff hd hG3 hG hO
  | @lim Ow g gh gs ghs η hshp hmono hη hηW hlim _ IH =>
    intro hgη hghη
    refine umLev_lim hl hX hshp hmono hη hηW hlim ?_
    intro ζ hζ hζη b X0 Xh0 hoff hd hG3 hG hO
    have hsh := hshp b X0 hO.1
    have hζ1 : ζ + 1 < η := hlim.succ_lt hζη
    have hζ1c := rqCode_succ hl hX hζ (hζ1.trans hηW)
    have hΘl := hsh.sth (gxTh_lt (Z := upsilon l) (At := ldAtR S l) hζ1c hζ1)
    exact IH ζ hζ hζη ((hsh.st hζ1).trans hgη) (hΘl.trans hghη) b X0 Xh0 hoff hd hG3 hG hO
  | weaken _ himp _ IH =>
    intro hE hEh b X0 Xh0 hoff hd hG3 hG hO
    exact IH hE hEh b X0 Xh0 hoff hd hG3 hG (himp b X0 hO)

/-- **Soundness past `Γ₂` with the own data.** -/
theorem umDer_all {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : ScDer S l Ow E Eh)
    (hE : E < S.psi 0 (Om (1 + 1 + 1))) (hEh : Eh < S.psi 0 (Om (1 + 1))) :
    UjLev S l Ow E Eh ∧ UjOwP S l Ow E Eh :=
  ⟨umDer_sound hl hX h hE hEh, umOwP_of_sc (scDer_sound hl hX h).2⟩

/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY EXPONENT `1 ≤ E < ε_{Ω₂+1}` OF `H_λ`**: for every offset `X₀` past
`Γ₂` with `W^E ∣ X₀`, `X₀ + W^E + Ω₂ < Y₃`, `X̂₀ + Ω^{Θ̂ E} + Ω₁ < Y₂` and the own predicate of the normal-form
term of `E`: `Θ(ψ_{Ω₂}(β + W^{X₀ + W^E})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Θ̂ E}})`. -/
theorem umLev_sg {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    UjLev S l (fun b X0 => SgOwn S b X0 (fun y => y) (sgTmH E)) E (sgThH S l E) :=
  umDer_sound hl hX (sgDer_all hl hX hEH hE1 hE) (hE.trans Sn.snEps_lt_G3) (Sn.snThH_lt_G hl hX E hEH hE)

/-- The own data past `Γ₂` at every `1 ≤ E < ε_{Ω₂+1}` of `H_λ`. -/
theorem umOwP_sg {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    UjOwP S l (fun b X0 => SgOwn S b X0 (fun y => y) (sgTmH E)) E (sgThH S l E) :=
  umOwP_of_sc (scDer_sound hl hX (sgDer_all hl hX hEH hE1 hE)).2

/-- **`X₀ + W^E` is a shift past `Γ₂`** for every `1 ≤ E < ε_{Ω₂+1}` of `H_λ` own over an offset past `Γ₂`. -/
theorem umSh_sg {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : UjOff S l b X0 Xh0) (hG3 : X0 + leWe E + Om (1 + 1) < ugY S)
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < ujY S 0) (hOw : SgOwn S b X0 (fun y => y) (sgTmH E)) :
    UjSh S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) :=
  ujSh_own hoff ((umOwP_sg hl hX hEH hE1 hE).dat b X0 hOw) hG3 hG

end Sound

end Googology.Trans.PoR.InaccPsi.R2.Um
