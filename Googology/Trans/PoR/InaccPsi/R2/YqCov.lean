import Googology.Trans.PoR.InaccPsi.R2.YqIF
import Googology.Trans.PoR.InaccPsi.R2.YbLev
import Googology.Trans.PoR.InaccPsi.R2.YbSup

/-!
# The covering lemma and the non-silent supply on every window below a value of `ψ_{Ω₁}`, with no hypothesis

`υ = upsilon`, `L(ξ) = Nc.ncL S ξ = ψ_{Ω₁}(Ω_ω + Ω_ω + P′·ξ)`.  `Yb.ybLevK_of_IF` reads `YbIF` only at the least
strongly critical `q₀ ≥ x` of a node value `x < υ_{λ+β}`; when `υ_{λ+β} ≤ ψ_{Ω₁}(A)` this `q₀` is `≤ ψ_{Ω₁}(A)`, where
`Yq.yqIFN` proves `YbIF`.  So:

* `yqLevK` (**`Yb.YbLevK S λ β` for `0 < λ`, `υ_{λ+β} ≤ Ω₁`, `υ_{λ+β} ≤ ψ_{Ω₁}(A)`**), `yqCover` (**the covering
  lemma there**), `yqSupBound` (**the non-silent supply there**: from `Xo.XoSup S λ β` alone);
* `yqCover_L`, `yqSupBound_L` (**the same on every window `υ_{λ+β} ≤ L(ω+1)`**: no `YbIF` needed on the road's range).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Yb

variable {S : InaccSeq.{0}}

/-- **The level statement of the covering lemma below a value `ψ_{Ω₁}(A)`.** -/
theorem yqLevK {l β A : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hA : upsilon (l + β) ≤ S.psi A (Om 1)) : YbLevK S l β := by
  intro h M η h0 _ hΩM hηO hηT hξT hξ2 hτx hxβ _
  set τ := upsilon (l + h) with hτdef
  set x := vt τ (Om1 * M + η) with hxdef
  have hτP : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hτE : InE τ := upsPt_inE hτP
  have hx1 : x < Om1 := hxβ.trans_le hb1
  have hτ1 : τ < Om1 := hτx.trans_lt hx1
  have hx0 : 0 < x := (InE.pos hτE).trans_le hτx
  have hξθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτE hτ1 _ hξT hξ2
  have hMξ : M ≤ Om1 * M + η :=
    (Ordinal.le_mul_right M Rj.rj_Om1_inE.pos).trans le_self_add
  have hMθ : M < ConjT.th S := hMξ.trans_lt hξθ
  have hall := vdArg_dat hτE hτ1 hΩM hηO hξT
  have hMT : Vd.VdDatIn (· ∈ Tset τ) M := by
    by_cases hMB : M < Uc.ucB
    · exact Or.inl ⟨hMB, hall.1 hMB⟩
    · push Not at hMB
      exact Or.inr ⟨S, hMB, hMθ, hall.2 S hMB hMθ⟩
  have hlt := (vdLevel_lt hτE hτ1 hΩM hMT hηT hηO).1
  obtain ⟨q, hqS, hxq, hq1, hgap⟩ := ybSCnext hx1.le
  have hqA : q ≤ S.psi A (Om 1) := by
    by_contra hc
    push Not at hc
    exact hgap _ (hxβ.le.trans hA) hc (InaccSeq.SC_psi Low.InR_Om_one A)
  have hMq : YbK S q M := yqIFN A M q hΩM hMθ hqS hq1 hqA (fun hMB => (hlt.1 hMB).trans_le hxq)
    (fun hMB => hlt.2 S hMB hMθ q hqS hxq)
  exact ybK_lower (ybK_gap hx0 hgap) M hMq

/-- **The covering lemma below a value `ψ_{Ω₁}(A)`**, with no hypothesis. -/
theorem yqCover {l β A : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hA : upsilon (l + β) ≤ S.psi A (Om 1)) :
    ∀ x, x < upsilon (l + β) → x < Om1 → YbCov S l β x :=
  ybCover hl0 (yqLevK hl0 hb1 hA)

/-- **The non-silent supply below a value `ψ_{Ω₁}(A)`**: from `Xo.XoSup S λ β` alone. -/
theorem yqSupBound {l β A : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hA : upsilon (l + β) ≤ S.psi A (Om 1)) (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) :=
  ybSup_bound hl0 hb1 hl1 (yqLevK hl0 hb1 hA) hS

/-- **The covering lemma on every window `υ_{λ+β} ≤ L(ω+1)`.** -/
theorem yqCover_L {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1)
    (hL : upsilon (l + β) ≤ Nc.ncL S (ω + 1)) :
    ∀ x, x < upsilon (l + β) → x < Om1 → YbCov S l β x :=
  yqCover hl0 hb1 hL

/-- **The non-silent supply on every window `υ_{λ+β} ≤ L(ω+1)`.** -/
theorem yqSupBound_L {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hl1 : upsilon l < Om1)
    (hL : upsilon (l + β) ≤ Nc.ncL S (ω + 1)) (hS : Xo.XoSup S l β) :
    ∀ γ < upsilon l, ∀ G : Finset Ordinal.{0}, (∀ d ∈ G, d < β) →
      ∃ μ f B, ∃ Os : Finset Ordinal.{0}, G ⊆ Os ∧ CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
        μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Xo.XoCarry S l β μ f B Os ∧
        ∀ g ∈ G, 0 < g → ω ^ 2 ∣ g → cdR S (l + g) < upsilon (l + β) →
          ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = cdR S (l + g) ∧ Xo.XoR S l μ E ∧
            Xo.xoImg S l μ f E ≤ cdR S (μ + f g) :=
  yqSupBound hl0 hb1 hl1 hL hS

end Googology.Trans.PoR.InaccPsi.R2.Yq
