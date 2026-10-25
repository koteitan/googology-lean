import Googology.Trans.PoR.InaccPsi.R2.TnCore

/-!
# Every code below the bottom of `φ(Ω₂, 1)` is an own level of a node `φ(c, Ω₂ + 1)`

`W^E = Ω₂^E`, `T_y(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `G = φ(Ω₂, 1)`, codes of `λ` = `GxCl ρ_λ (ldAtR λ)`.

* `tnAtom_lt` (**the normal-form argument `d` of an atom `ψ_{Ω₂}(d) ≤ c` below `T_G(β, X₀)` is below
  `β + W^{X₀ + W^{φ(c, Ω₂+1)}}`**: the exponent `w` of the last `W`-digit of `d` above `X₀` is a code over
  `ψ_{Ω₂}(d)` below `G`, so `w < φ(ζ, Ω₂ + 1)` with a code `ζ < ψ_{Ω₂}(d) ≤ c`, `Td.tdCl_levDec` at the level
  `Ω₂`);
* `tnOwnMem` (**every code `c < T_G(β, X₀)` of `λ` is in `Cl(α, ψ_{Ω₂}(α))`, `α = β + W^{X₀ + W^{φ(c, Ω₂+1)}}`**),
  `tnOwnLev` (**`c < T_{φ(c, Ω₂+1)}(β, X₀)`**: no hypothesis on `β`, `X₀`), `tnOwnCL` (**the closure condition
  `Sn.SnCL (φ(c, Ω₂+1)) β X₀`**).

So at the level `Ω₂` the members `φ(c, Ω₂ + 1)` are own for every code `c` below the bottom `T_G`; the
cofinality the limit rule needs is the one among codes (`Tn.tnLevLimC`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- `W^{X₀} ≤ δ` gives `X₀ ≤ log_W δ`. -/
theorem tnLogW_ge {X0 δ : Ordinal.{0}} (h : leWe X0 ≤ δ) : X0 ≤ log ω δ / Om (1 + 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have h1 : Om (1 + 1) * X0 ≤ log ω δ := le_log_of_opow_le one_lt_omega0 h
  exact (Ordinal.le_div hW0).2 h1

/-- `δ < W^Y` gives `log_W δ < Y` for `δ ≠ 0`. -/
theorem tnLogW_lt {Y δ : Ordinal.{0}} (hδ0 : δ ≠ 0) (h : δ < leWe Y) : log ω δ / Om (1 + 1) < Y := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hlog : log ω δ < Om (1 + 1) * Y :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hδ0).trans_lt h)
  exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlog

/-- **The normal-form argument of an atom `ψ_{Ω₂}(d) ≤ c` below `T_G`** is below
`β + W^{X₀ + W^{φ(c, Ω₂+1)}}`. -/
theorem tnAtom_lt {β X0 c d : Ordinal.{0}} (hself : d ∈ S.CSet d (S.psi d (Om (1 + 1))))
    (hdc : S.psi d (Om (1 + 1)) ≤ c)
    (hcT : c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :
    d < β + leWe (X0 + leWe (veblen c (Om (1 + 1) + 1))) := by
  set φc := veblen c (Om (1 + 1) + 1) with hφc
  have hpos : 0 < leWe φc := leWe_pos _
  rcases lt_or_ge d β with hdβ | hβd
  · exact hdβ.trans_le le_self_add
  obtain ⟨δ, rfl⟩ := exists_add_of_le hβd
  refine (add_lt_add_iff_left β).2 ?_
  have hδG : δ < leWe (X0 + leWe (veblen (Om (1 + 1)) 1)) := by
    by_contra h
    push Not at h
    have := (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1
    exact absurd (this.trans hdc) (not_le.2 hcT)
  have hδC : δ ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := by
    have h1 := taSub_mem (S := S) _ hself β
    rwa [Ordinal.add_sub_cancel] at h1
  rcases lt_or_ge δ (leWe X0) with hδX | hδX
  · exact hδX.trans_le (leWe_mono le_self_add)
  have hδ0 : δ ≠ 0 := (lt_of_lt_of_le (leWe_pos X0) hδX).ne'
  set u := log ω δ / Om (1 + 1) with hu
  have hXu : X0 ≤ u := tnLogW_ge hδX
  have huG : u < X0 + leWe (veblen (Om (1 + 1)) 1) := tnLogW_lt hδ0 hδG
  have huC : u ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hδC)
  obtain ⟨v, hv⟩ := exists_add_of_le hXu
  have hvC : v ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := by
    have h1 := taSub_mem (S := S) _ huC X0
    rwa [hv, Ordinal.add_sub_cancel] at h1
  have hvG : v < leWe (veblen (Om (1 + 1)) 1) := by
    rw [hv] at huG; exact (add_lt_add_iff_left X0).1 huG
  -- `u + 1 ≤ X₀ + W^{φ(c, Ω₂+1)}`
  have hu1 : u + 1 ≤ X0 + leWe φc := by
    rw [hv, add_assoc]
    refine (add_le_add_iff_left X0).2 (Order.add_one_le_of_lt ?_)
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hpos
    set w := log ω v / Om (1 + 1) with hw
    have hwG : w < veblen (Om (1 + 1)) 1 := tnLogW_lt hv0 hvG
    have hwC : w ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hvC)
    have hsSC : SC (S.psi (β + δ) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hwc : LeCl (Om (1 + 1)) (S.psi (β + δ) (Om (1 + 1))) w :=
      snLeCl_mem hsSC le_rfl hwC (hwG.trans tjG_lt_G3)
    have hlt : w < veblen (Om (1 + 1)) (0 + 1) := by rw [zero_add]; exact hwG
    obtain ⟨ζ, hζ, hζW, hwζ⟩ := tdCl_levDec hsSC ldOm2_SC ldOm2_SC.isSuccLimit w hwc hlt
    have hζs : ζ < S.psi (β + δ) (Om (1 + 1)) := tdCl_lt hsSC ζ hζ hζW
    rw [ldOm2_SC.veblen_zero] at hwζ
    have hwφ : w < φc := hwζ.trans_le (veblen_left_monotone _ (hζs.le.trans hdc))
    exact (roLt_We_log v).trans_le (leWe_mono (Order.add_one_le_of_lt hwφ))
  exact (roLt_We_log δ).trans_le (leWe_mono hu1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every code `c < T_G(β, X₀)` of `λ` is in `Cl(α, ψ_{Ω₂}(α))`, `α = β + W^{X₀ + W^{φ(c, Ω₂+1)}}`.** -/
theorem tnOwnMem {β X0 c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcT : c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :
    c ∈ S.CSet (β + leWe (X0 + leWe (veblen c (Om (1 + 1) + 1))))
      (S.psi (β + leWe (X0 + leWe (veblen c (Om (1 + 1) + 1)))) (Om (1 + 1))) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  set α := β + leWe (X0 + leWe (veblen c (Om (1 + 1) + 1))) with hα
  have key : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x ≤ c → x ∈ S.CSet α (S.psi α (Om (1 + 1))) := by
    intro x hx
    induction hx with
    | small h => exact fun _ => CSet.of_lt (h.trans (hρ1.trans (psiS_bounds (S := S) _ 1).1))
    | om => exact fun _ => CSet.Om_mem (CSet.one_mem _ _)
    | @atom s hs =>
      intro hsc
      obtain ⟨a, haH, haA, rfl⟩ := hs
      obtain ⟨d, -, heq, -, -, hself⟩ := tnNf_atom hl hX haH haA
      rw [← heq] at hsc ⊢
      have hdα : d < α := tnAtom_lt hself hsc hcT
      exact CSet.psi_mem hdα (InR_Om_succ 1) (Mx.mxOm2_mem _ _)
        ((psi_mono (S := S) (InR_Om_succ 1) hdα.le).2 hself)
    | @add x y _ _ ihx ihy =>
      intro h
      exact CSet.add_mem (ihx (le_self_add.trans h)) (ihy (le_add_self.trans h))
    | @phi x y _ _ ihx ihy =>
      intro h
      exact CSet.phi_mem (ihx ((left_le_veblen x y).trans h)) (ihy ((right_le_veblen x y).trans h))
  exact key c hc le_rfl

/-- **`c < T_{φ(c, Ω₂+1)}(β, X₀)`** for every code `c < T_G(β, X₀)` of `λ`. -/
theorem tnOwnLev {β X0 c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcT : c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :
    c < S.psi (β + leWe (X0 + leWe (veblen c (Om (1 + 1) + 1)))) (Om (1 + 1)) :=
  lt_psi_of_mem (InR_Om_succ 1) (tnOwnMem hl hX hc hcT) (hcT.trans (psi_lt (InR_Om_succ 1) _))

/-- **The closure condition `Sn.SnCL (φ(c, Ω₂+1)) β X₀`** for every code `c < T_G(β, X₀)` of `λ`. -/
theorem tnOwnCL {β X0 c : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcT : c < S.psi (β + leWe (X0 + leWe (veblen (Om (1 + 1)) 1))) (Om (1 + 1))) :
    SnCL S (veblen c (Om (1 + 1) + 1)) β X0 := by
  intro Q hQ hQ'
  exact LeCl.phi (LeCl.small ((tnOwnLev hl hX hc hcT).trans_le hQ'))
    (LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ)))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tn
