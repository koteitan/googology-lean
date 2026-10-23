import Googology.Trans.PoR.InaccPsi.R2.RyLow

/-!
# `RuBlkHi` from a tail condition on the offsets `Γ_{Ω₁+1} ≤ ζ < θ` only

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)`, `A = A_{η_μ}`, `Â = A + θ·x`,
`β = Ω_ω + θ₂·x`, `ρ_μ = υ_μ`, `Θ = gxTh ρ_μ (ldAtR μ)` (`= Θ_μ` below `Ω₂`), `HCl = Bt.HCl`,
`ggGam = Γ_{Ω₁+1}`, `ψ_{Ω₃}(0) = Γ_{Ω₂+1}`, `ryTlow` the low atoms of `Ry.ryTail_low`.

* `RyTailHi S μ x` (**the tail condition above `Γ_{Ω₁+1}`**): a map `c` on the offsets `Γ_{Ω₁+1} ≤ ζ < θ` with
  `ψ_{Ω₃}(0) ≤ c(ζ)`, `ψ_{Ω₂}(β + c ζ)` an atom of `μ` below `G(x+1)`, and
  `ψ_{Ω₂}(β + c(e − Â)) < ψ_{Ω₂}(β + c ζ)` for every `e ∈ HCl(Â + ζ, Θ(ψ_{Ω₂}(β + c ζ)))` with `Â ≤ e < Â + ζ`
  and `e − Â ≥ Γ_{Ω₁+1}`;
* `ryTailAt_of_hi` (**`RyTailHi ⇒ RyTailAt`**: below `Γ_{Ω₁+1}` the low atoms `ryTlow` (`Ry.ryTail_low`), and a
  low tail of a high offset is read below the high atom (`Ry.ryTlow_lt`));
* `ryBlkAt_of_tailHi` (**`RpBlkAt` from the base reading and `RyTailHi`**), `ryHi_of_tailHi` (**`RuBlkHi`**),
  `ryReadAll_of_tailHi`, `ryRoadHi` (**the road `Ru.ruRoad` with `RyTailHi` in place of `RuBlkHi`**).

So the block step above `Γ_{Ω₁+1}` asks only for a choice of codes `c(ζ) ≥ Γ_{Ω₂+1}` that decreases along the
tails `≥ Γ_{Ω₁+1}` of the hulls; no reading inequality, no `+`-structure and no monotonicity of `c` is asked.

No new axiom.  New definition (hypothesis name only): `RyTailHi`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ry

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

/-- **The tail condition above `Γ_{Ω₁+1}`** at the block `x` of `μ`. -/
def RyTailHi (S : InaccSeq.{0}) (μ x : Ordinal.{0}) : Prop :=
  ∃ c : Ordinal.{0} → Ordinal.{0}, ∀ ζ, ggGam ≤ ζ → ζ < ConjT.th S →
    S.psi 0 (Om (1 + 1 + 1)) ≤ c ζ ∧
    S.psi (Om ω + Lc.lcTh S 2 * x + c ζ) (Om (1 + 1)) ∈ ldAtR S μ ∧
    S.psi (Om ω + Lc.lcTh S 2 * x + c ζ) (Om (1 + 1)) < Lc.lcG S (x + 1) ∧
    ∀ e, HCl S (ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ)
        (gxTh (upsilon μ) (ldAtR S μ) (S.psi (Om ω + Lc.lcTh S 2 * x + c ζ) (Om (1 + 1)))) e →
      ConjT.Aη S (cdEta S μ) + ConjT.th S * x ≤ e →
      e < ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ →
      ggGam ≤ e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) →
      S.psi (Om ω + Lc.lcTh S 2 * x + c (e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x))) (Om (1 + 1)) <
        S.psi (Om ω + Lc.lcTh S 2 * x + c ζ) (Om (1 + 1))

/-- **`RyTailHi ⇒ RyTailAt`.** -/
theorem ryTailAt_of_hi {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ) (h : RyTailHi S μ x) :
    RyTailAt S μ x := by
  obtain ⟨c, hcH⟩ := h
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hxρ
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  have hlow := ryTail_low hR hc hx
  have hz3 : 0 < S.psi 0 (Om (1 + 1 + 1)) := (SC_psi (InR_Om_succ (1 + 1)) 0).1
  refine ⟨fun ζ => if ζ < ggGam then ryTlow S μ x ζ else S.psi (β + c ζ) (Om (1 + 1)), fun ζ hζ => ?_⟩
  by_cases hG : ζ < ggGam
  · simp only [if_pos hG]
    obtain ⟨h1, h2, h3, h4⟩ := hlow ζ hG
    refine ⟨h1, h2, h3, fun e he he1 he2 => ?_⟩
    have hlt : e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) < ggGam := (rySub_lt he1 he2).trans hG
    simp only [if_pos hlt]
    exact h4 e he he1 he2
  · simp only [if_neg hG]
    have hGe : ggGam ≤ ζ := not_lt.1 hG
    obtain ⟨hcz, hat, hlt1, htail⟩ := hcH ζ hGe hζ
    have hc0 : 0 < c ζ := hz3.trans_le hcz
    refine ⟨hat, hlt1, ?_, fun e he he1 he2 => ?_⟩
    · refine psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β hc0) ?_
      refine Rp.rpThx_mem (lt_of_le_of_lt le_self_add (lt_add_of_pos_right β hc0)) ?_
      exact hx1.trans (psiS_bounds (S := S) _ 1).1
    · by_cases hG' : e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) < ggGam
      · simp only [if_pos hG']
        have hs := hAt _ hat
        have hTSC : SC (gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + c ζ) (Om (1 + 1)))) :=
          gxTh_SC hZ hAt hs.1 (hZ1.trans hs.2)
        have heG : e < ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ggGam := by
          calc e = ConjT.Aη S (cdEta S μ) + ConjT.th S * x +
                (e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x)) :=
                (Ordinal.add_sub_cancel_of_le he1).symm
            _ < _ := (add_lt_add_iff_left _).2 hG'
        have hgg := ruTail hTSC.1 (ruDvd (cdEta S μ) x) le_rfl he he1 heG
        exact ryTlow_lt hR hx hcz hlt1 hgg.1 hG'
      · simp only [if_neg hG']
        exact htail e he he1 he2 (not_lt.1 hG')

/-- **`RpBlkAt` from the base reading and `RyTailHi`.** -/
theorem ryBlkAt_of_tailHi {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ)
    (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RyTailHi S μ x) : Rp.RpBlkAt S μ x :=
  ryBlkAt_of_tail hR hc hx hP (ryTailAt_of_hi hR hc hx h)

/-- **`RuBlkHi` from the base reading and `RyTailHi`.** -/
theorem ryHi_of_tailHi {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ)
    (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RyTailHi S μ x) : RuBlkHi S μ x :=
  ruHi_of_blkAt (ryBlkAt_of_tailHi hR hc hx hP h)

/-- **`RpReadAll` from `RyTailHi` at every block whose base is read.** -/
theorem ryReadAll_of_tailHi {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RyTailHi S μ x) :
    Rp.RpReadAll S k :=
  Rp.rpReadAll_of_blkAt fun μ hR hω hc x hx hP => ryBlkAt_of_tailHi hR hc hx hP (h μ hR hω hc x hx hP)

/-- **The road `Ru.ruRoad` with `RyTailHi` in place of `RuBlkHi`.** -/
theorem ryRoadHi {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hth : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RyTailHi S μ x)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hout : Rp.RpLnOut S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ruRoad hU hO hL hV hVt hEQ htop
    (fun μ hR hω hc x hx hP => ryHi_of_tailHi hR hc hx hP (hth μ hR hω hc x hx hP)) h0 hn hout hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Ry
