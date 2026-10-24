import Googology.Trans.PoR.InaccPsi.R2.SqBase

/-!
# A level system and its base-indexed family of shifts, generic in the levels

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`, `CL = Sn.SnCL`
(the closure condition), `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

**A level system** `StLS S λ E_b Th` (`E_b` a limit below `G3`, `Th λ E` the image of the level `E`): every
`1 ≤ E < E_b` in the hull has `Th λ E < G1`, the own data `Sc.ScOwP (CL E) E (Th λ E)` and the level statement
`Sc.ScLev (CL E) E (Th λ E)`.  The levels below `ε_{Ω₂+1}` with `Th = Sg.sgThH` are one system (`Sn.snOwP`,
`Sn.snLev`); a system that also contains levels `≥ ε_{Ω₂+1}` gives offsets with a leading `ε`-part (the roots
`ε·ζ`, `ε + W^E·ζ`, `W^{ε+n}` are members).

`StG S λ E_b Th β X X̂ E` (**the family over the base `β`**, `E` the last level): `X = W^{E₁}·ζ₁ + … + W^{E_k}·ζ_k`,
`X̂ = Ω^{Th E₁}·Θ ζ₁ + … + Ω^{Th E_k}·Θ ζ_k`, levels `E₁ > … > E_k = E` of the system, each with the closure
condition over `X_{<i}` at `β`, codes `ζ_i ≠ 0` below some `EE_j(X_{<i}, β, E_i)`.

* `stWe_lt_G3`, `stOe_lt_G`, `stG_data`, `stG_mono` (**hereditary**);
* `stG_sh` (**every member is a shift own relative to `β` with the top law at the bases `≥ β`**, `Sc.scFam` with
  the data of the system), `stShG`, `stShG_sh`, `stShG_mono`.

No new axiom.  New definitions: `StLS`, `StG`, `stShG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.St

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

/-- **A level system**: the levels `1 ≤ E < E_b` of the hull with images `Th λ E`, own data and level statements. -/
structure StLS (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}) : Prop where
  lim : IsSuccLimit Eb
  ltG3 : Eb < S.psi 0 (Om (1 + 1 + 1))
  ltG : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → Th l E < S.psi 0 (Om (1 + 1))
  own : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → ScOwP S l (SnCL S E) E (Th l E)
  lev : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → ScLev S l (SnCL S E) E (Th l E)

/-- **The family of the shifts of a level system over the base `β`** (last level `E`). -/
inductive StG (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}) :
    Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | one {β E ζ : Ordinal.{0}} : 1 ≤ E → E ∈ cdHull S l → E < Eb → SnCL S E β 0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S 0 β E j) →
      StG S l Eb Th β (leWe E * ζ) (leOe (Th l E) * gxTh (upsilon l) (ldAtR S l) ζ) E
  | add {β X0 Xh0 E0 E ζ : Ordinal.{0}} : StG S l Eb Th β X0 Xh0 E0 → 1 ≤ E → E < E0 → E ∈ cdHull S l →
      E < Eb → SnCL S E β X0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β E j) →
      StG S l Eb Th β (X0 + leWe E * ζ) (Xh0 + leOe (Th l E) * gxTh (upsilon l) (ldAtR S l) ζ) E

/-- The family `∃ E, StG β X X̂ E`. -/
def stShG (S : InaccSeq.{0}) (l Eb : Ordinal.{0}) (Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (b X Xh : Ordinal.{0}) : Prop := ∃ E, StG S l Eb Th b X Xh E

/-- `W^{E+1} < ψ_{Ω₃}(0)` for `E < ψ_{Ω₃}(0)`. -/
theorem stWe_lt_G3 {E : Ordinal.{0}} (hE : E < S.psi 0 (Om (1 + 1 + 1))) :
    leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  exact (leWe_lt_SC hG3 rwW_lt_G3 (hG3.isSuccLimit.succ_lt hE)).1

/-- `Ω^{x+1} < ψ_{Ω₂}(0)` for `x < ψ_{Ω₂}(0)`. -/
theorem stOe_lt_G {x : Ordinal.{0}} (hx : x < S.psi 0 (Om (1 + 1))) : leOe (x + 1) < S.psi 0 (Om (1 + 1)) := by
  have hG1 := rwG_SC (S := S)
  exact (leOe_lt_SC hG1 rwO_lt_G (hG1.isSuccLimit.succ_lt hx)).1

/-- `ψ_{Ω₃}(0) < Ω_ω`. -/
theorem stG3_lt_OmW : S.psi 0 (Om (1 + 1 + 1)) < Om (ω : Ordinal.{0}) := rwG3_lt_OmW

section Main

variable {l ηx Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}
  (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hS : StLS S l Eb Th)

include hl hX hS

/-- **The data of a member.** -/
theorem stG_data {β X Xh E : Ordinal.{0}} (h : StG S l Eb Th β X Xh E) :
    1 ≤ E ∧ E ∈ cdHull S l ∧ E < Eb ∧
      leWe E ∣ X ∧ X ≠ 0 ∧ X < S.psi 0 (Om (1 + 1 + 1)) ∧ Xh < S.psi 0 (Om (1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  have hterm : ∀ {E' X0 ζ : Ordinal.{0}}, E' ∈ cdHull S l → 1 ≤ E' → E' < Eb →
      GxCl (upsilon l) (ldAtR S l) ζ → (∃ j, ζ < rvEE S X0 β E' j) →
      leWe E' * ζ < S.psi 0 (Om (1 + 1 + 1)) ∧
        leOe (Th l E') * gxTh (upsilon l) (ldAtR S l) ζ < S.psi 0 (Om (1 + 1)) := by
    intro E' X0 ζ hEH h1 hE _ hj
    obtain ⟨j, hj⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj.trans (rvEE_lt_Om2 j)
    have hΘζ := snTh_lt_Om1 hl hX hζW.le
    refine ⟨(rvWe_lt_succ hζW).trans (stWe_lt_G3 (hE.trans hS.ltG3)), ?_⟩
    exact (rvOe_lt_succ hΘζ).trans (stOe_lt_G (hS.ltG E' hEH h1 hE))
  induction h with
  | @one E ζ h1 hEH hE _ hζ hζ0 hj =>
    obtain ⟨t1, t2⟩ := hterm hEH h1 hE hζ hj
    exact ⟨h1, hEH, hE, dvd_mul_right _ _, mul_ne_zero (leWe_pos E).ne' hζ0, t1, t2⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE _ hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, -, hX0, hXh0⟩ := ih
    obtain ⟨t1, t2⟩ := hterm hEH h1 hE hζ hj
    refine ⟨h1, hEH, hE, dvd_add ((leWe_dvd hEE.le).trans hd0) (dvd_mul_right _ _), ?_,
      hG3.isPrincipal hX0 t1, hG1.isPrincipal hXh0 t2⟩
    intro h'
    have := le_antisymm (h' ▸ le_add_self : leWe E * ζ ≤ 0) zero_le
    exact mul_ne_zero (leWe_pos E).ne' hζ0 this

omit hl hX hS in
/-- **The family is hereditary.** -/
theorem stG_mono {β β' X Xh E : Ordinal.{0}} (hββ : β ≤ β') (h : StG S l Eb Th β X Xh E) :
    StG S l Eb Th β' X Xh E := by
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j, hj⟩ := hj
    exact StG.one h1 hEH hE (snCL_mono hcl hββ le_rfl) hζ hζ0 ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩
  | @add X0 Xh0 E0 E ζ _ h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨j, hj⟩ := hj
    exact StG.add ih h1 hEE hEH hE (snCL_mono hcl hββ le_rfl) hζ hζ0
      ⟨j, hj.trans_le (rvEE_mono_base hββ j)⟩

omit hl hX hS in
theorem stShG_mono {b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : stShG S l Eb Th b X Xh) :
    stShG S l Eb Th b' X Xh := by
  obtain ⟨E, hE⟩ := h
  exact ⟨E, stG_mono hbb hE⟩

/-- **Every member is a shift own relative to `β` with the top law at the bases `≥ β`.** -/
theorem stG_sh {β X Xh E : Ordinal.{0}} (h : StG S l Eb Th β X Xh E) :
    RvSh S l β X Xh ∧ RvTop S l β X Xh 0 := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hne := (stG_data hl hX hS h).2.2.2.2.1
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := scFam hl hX (hS.own E hEH h1 hE) (hS.lev E hEH h1 hE) (X0 := 0) (Xh0 := 0) (β := β)
      (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal (stWe_lt_G3 (hE.trans hS.ltG3)) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal (stOe_lt_G (hS.ltG E hEH h1 hE)) hΩG1) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    rw [zero_add, zero_add] at h
    exact rvOff_ne h hne
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    obtain ⟨-, -, -, hd0, hne0, hX0, hXh0⟩ := stG_data hl hX hS h0
    obtain ⟨j0, hj0⟩ := hj
    have hζW : ζ < Om (1 + 1) := hj0.trans (rvEE_lt_Om2 j0)
    have h := scFam hl hX (hS.own E hEH h1 hE) (hS.lev E hEH h1 hE) (β := β)
      (Or.inr (ih hne0)) ((leWe_dvd (Order.add_one_le_of_lt hEE)).trans hd0)
      (hG3.isPrincipal (hG3.isPrincipal hX0 (stWe_lt_G3 (hE.trans hS.ltG3))) hWG3)
      (hG1.isPrincipal (hG1.isPrincipal hXh0 (stOe_lt_G (hS.ltG E hEH h1 hE))) hΩG1) hcl ζ hζ ⟨j0, hj0⟩
      (snTh_lt_Om1 hl hX hζW.le)
    exact rvOff_ne h hne

/-- **The family `stShG` meets the hypotheses of the own-atom layer** (`hSh` of `Rw.rwOwnRead`, `Rw.rwDigMove`). -/
theorem stShG_sh : ∀ b X Xh, stShG S l Eb Th b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh ⟨E, hE⟩
  obtain ⟨hs, ht⟩ := stG_sh hl hX hS hE
  exact ⟨hs, rvTopE hs hl hX ht⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.St
