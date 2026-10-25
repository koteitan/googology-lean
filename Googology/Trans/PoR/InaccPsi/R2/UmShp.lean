import Googology.Trans.PoR.InaccPsi.R2.UmOm

/-!
# The level step over a shape past `Γ₂`, and the level `Ω₂` over every offset past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `SQ_j = Sc.scSq` of the lifted
shape `ζ ↦ W^{g ζ}`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `G₃ = ψ_{Ω₃}(0) = Γ₂`, `G₁ = ψ_{Ω₂}(0)`.

`Sc.scLev_om` with the level statement past `Γ₂` (`Uj.UjLev`): a shape `Sc.ScShp` with its top `g* < G₃` and its
image top `ĝ* < G₁` (so its closure laws are the laws for the level codes, `Um.umShCl_of_sc`, `Um.umImCl_of_sc`),
whose members have `UjLev`, gives `UjLev` at the top, over every offset past `Γ₂`.

* `umWe_le_gam`, `umOe_le_G` (the bounds of the lifted closure laws);
* `umLev_om` (**THE LEVEL STEP PAST `Γ₂`**: the members `g ζ` (`1 ≤ ζ < Ω₂` codes with `Θ ζ < Ω₁`, image
  `ĝ(Θ ζ)`, own predicate `Ow ∧ ∃ j, ζ < SQ_j`) give the top `g*`, image `ĝ*`:
  `Θ(T_{X₀ + W^{g*}}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{ĝ*}})` at every offset `X₀` past `Γ₂`);
* `umLev_W` (**`UjLev ⊤ Ω₂ Ω₁`: the top at `W^{Ω₂}` over every offset past `Γ₂`**, the step at which the level
  statement past `Γ₂` stopped).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- `Ω₂·W^{g*} ≤ Γ₂` for `ω ≤ g* < ψ_{Ω₃}(0)`. -/
theorem umWe_le_gam {gs : Ordinal.{0}} (hinf : ω ≤ gs) (hgs : gs < S.psi 0 (Om (1 + 1 + 1))) :
    Om (1 + 1) * leWe gs ≤ Ua.uaGam := by
  rw [rvWe_mul, Ordinal.one_add_of_omega0_le hinf, Ud.udGam_eq]
  exact (leWe_mono le_self_add).trans (St.stWe_lt_G3 hgs).le

/-- `Ω₁·Ω^{ĝ*} ≤ ψ_{Ω₂}(0)` for `ω ≤ ĝ* < ψ_{Ω₂}(0)`. -/
theorem umOe_le_G {ghs : Ordinal.{0}} (hinf : ω ≤ ghs) (hghs : ghs < S.psi 0 (Om (1 + 1))) :
    Om 1 * leOe ghs ≤ S.psi 0 (Om (1 + 1)) := by
  rw [rwO_mul_Oe hinf]
  exact (leOe_mono le_self_add).trans (St.stOe_lt_G hghs).le

section Step

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop}
  (hshp : ∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
    (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)))
  (hgs : gs < S.psi 0 (Om (1 + 1 + 1))) (hghs : ghs < S.psi 0 (Om (1 + 1)))
  (hmono : ∀ b β X0, Ow b X0 → b ≤ β → Ow β X0)
  (hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
    gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
    UjLev S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
      (gh (gxTh (upsilon l) (ldAtR S l) ζ)))

include hl hX hshp hgs hghs hmono hmem

/-- **THE LEVEL STEP PAST `Γ₂`: the members of a shape give its limit exponent over every offset past `Γ₂`.** -/
theorem umLev_om : UjLev S l Ow gs ghs := by
  intro b X0 Xh0 hoffb hd hG3 hG hOw β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have hoff := ujOff_mono hbβ hoffb
  have hOwβ := hmono _ _ _ hOw hbβ
  have hsh := hshp _ _ hOwβ
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := ujOff_data hoff
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb
  rw [add_zero] at hβd hβown
  have hst : StrictMono (fun z => leWe (g z)) := fun a b h => leWe_lt (hsh.st h)
  have hlt : ∀ x, x < Om (1 + 1) → leWe (g x) < leWe gs := fun x hx => leWe_lt (hsh.lt x hx)
  have hG3' : X0 + leWe gs < ugY S := le_self_add.trans_lt hG3
  have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2
      (leWe_mono (hsh.st.monotone (Order.one_le_iff_pos.2 (Om_pos one_ne_zero)))))))).1
  have hGm : ∀ x c, x ∈ S.CSet 0 c → leTe S (X0 + leWe (g 1)) β ≤ c → leWe (g x) ∈ S.CSet 0 c :=
    fun x c hx hc => leWe_mem (hsh.mem x c hx hc)
  have hWG := umWe_le_gam hsh.inf hgs
  have hOG := umOe_le_G hsh.infh hghs
  have hcl : ∀ Q, SC Q → leTe S (X0 + leWe (g 1)) β ≤ Q → UmShCl S (fun z => leWe (g z)) (leWe gs) Q :=
    fun Q hQ hc => umShCl_of_sc (scShCl_lift hQ hsh.inf (hsh.cl Q hQ hc)) hWG
  refine umOmTop hl hX hst hlt (fun v hv => leOe_lt (hsh.lth v hv)) hoff hb' hÂ hbase
    (fun ζ hζ hζW => leWe_mem (hsh.hull ζ hζ hζW)) hGm hcl hG3' ?_ rfl
    (fun v c hv hc => leOe_mem (hsh.memh v c hv hc))
    (fun Q hQ hc => umImCl_of_sc (scImCl_lift hQ hsh.infh (hsh.clh Q hQ hc)) hOG)
    (scIdx_lift hl hX hsh.idx) (le_self_add.trans_lt hG) (leWe_mem hsh.hullS) hd
  intro ζ hζ h1 hζT hΘ1
  have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
  obtain ⟨j, hj⟩ := umSq_sup hst (fun x hx => (hlt x hx).le) hβown hX0m
    (fun x c hx hc => hGm x c hx (hbot.trans hc)) (fun Q hQ hc => hcl Q hQ (hbot.trans hc)) hβd hX0cl hG3' hζT
  have hgle : g ζ ≤ gs := (hsh.lt ζ hζW).le
  have ht := hmem ζ hζ h1 hζW hΘ1 β X0 Xh0 hoff ((leWe_dvd hgle).trans hd)
    (lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hgle)) _) hG3)
    (lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono (hsh.lth _ hΘ1).le)) _) hG)
    ⟨hOwβ, j, hj⟩
  have e1 := ht β Â (roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (leWe_mono hgle))
    zero_le) le_rfl hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at e1
  exact e1

end Step

section W

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `W^{Ω₂}` over every offset past `Γ₂`** (image `Ω^{Ω₁}`): `UjLev ⊤ Ω₂ Ω₁`, i.e.
`Θ(ψ_{Ω₂}(β + W^{X₀ + W^{Ω₂}})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Ω₁}})` for every offset `X₀` past `Γ₂`. -/
theorem umLev_W : UjLev S l (fun _ _ => True) (Om (1 + 1)) (Om 1) := by
  refine umLev_om (g := fun z => z) (gh := fun v => v) hl hX
    (fun b X0 _ => scShp_code hl hX _ _) rwW_lt_G3 rwO_lt_G (fun _ _ _ _ _ => trivial) ?_
  intro ζ hζ h1 hζW _ b X0 Xh0 hoff hd hG3 hG hOw
  obtain ⟨-, j, hj⟩ := hOw
  rw [scSq_code] at hj
  exact ujLev_code hl hX ζ hζ h1 hζW b X0 Xh0 hoff hd hG3 hG ⟨j, hj⟩

end W

end Googology.Trans.PoR.InaccPsi.R2.Um
