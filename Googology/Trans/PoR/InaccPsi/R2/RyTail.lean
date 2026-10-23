import Googology.Trans.PoR.InaccPsi.R2.RyNF

/-!
# The block step from a choice of atoms that increases along the tails of the hull

`Θ = gxTh Z At` (the reading of the codes over `Z` with the atoms `At`), `HCl = Bt.HCl` (`Cl` without countable
collapses), `θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)` (`Lc.lcG`), `A = A_{η_μ}`,
`Â = A + θ·x`, `ρ_μ = υ_μ`, `Θ_μ` the reading at `μ`, `RpBlkAt`, `RuBlkHi` as in `Rp.RpBlkAt`, `Ru.RuBlkHi`.

* `ryLiftT` (**THE TAIL LIFT LEMMA**): let `ψ_{Ω₂}(β)` be an atom with `ψ_{Ω₁}(Â) ≤ Θ(ψ_{Ω₂}(β))`, `D` a set of
  offsets and `t : D → At` with `ψ_{Ω₂}(β) < t(ζ)`, such that for every `ζ ∈ D` and every `e ∈ HCl(Â + ζ, Θ(t ζ))`
  with `Â ≤ e < Â + ζ`: `e − Â ∈ D` and `t(e − Â) < t(ζ)`.  Then `ψ_{Ω₁}(Â + ζ) ≤ Θ(t ζ)` for all `ζ ∈ D`.  No
  monotonicity of `t` on `D`, no `+`-structure and no shape `ψ_{Ω₂}(β + κ ζ)` of the atoms is asked
  (`Ru.ruLift` is the case `t ζ = ψ_{Ω₂}(β + κ ζ)`);
* `RyTailAt S μ x` (**the tail condition at the block `x` of `μ`**): a map `t` from the offsets `ζ < θ` to the
  atoms of `μ` in `(G(x), G(x+1))` with `t(e − Â) < t(ζ)` for every `e ∈ HCl(Â + ζ, Θ_μ(t ζ))`,
  `Â ≤ e < Â + ζ`;
* `ryBlkAt_of_tail` (**`RpBlkAt` from the base reading and `RyTailAt`**, all offsets `ζ < θ` at once),
  `ryHi_of_tail` (**`RuBlkHi`**), `ryReadAll_of_tail` (**`RpReadAll`**), `ryRoad` (**the road `Ru.ruRoad` with
  `RyTailAt` in place of `RuBlkHi`**).

No new axiom.  New definition (hypothesis name only): `RyTailAt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ry

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

section Lift

variable {Z β Â : Ordinal.{0}} {At : Set Ordinal.{0}} {D : Set Ordinal.{0}} {t : Ordinal.{0} → Ordinal.{0}}

/-- **THE TAIL LIFT LEMMA**: `ψ_{Ω₁}(Â + ζ) ≤ Θ(t ζ)` for every `ζ ∈ D`. -/
theorem ryLiftT (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hβ : S.psi β (Om (1 + 1)) ∈ At)
    (hbase : S.psi Â (Om 1) ≤ gxTh Z At (S.psi β (Om (1 + 1))))
    (hat : ∀ ζ ∈ D, t ζ ∈ At)
    (hpos : ∀ ζ ∈ D, S.psi β (Om (1 + 1)) < t ζ)
    (htail : ∀ ζ ∈ D, ∀ e, HCl S (Â + ζ) (gxTh Z At (t ζ)) e → Â ≤ e → e < Â + ζ →
      e - Â ∈ D ∧ t (e - Â) < t ζ) :
    ∀ ζ ∈ D, S.psi (Â + ζ) (Om 1) ≤ gxTh Z At (t ζ) := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  have hs := hAt _ (hat ζ hζ)
  have hT : SC (gxTh Z At (t ζ)) := gxTh_SC hZ hAt hs.1 (hZ1.trans hs.2)
  refine psi_le_of_key hT fun e he heA => ?_
  have hβlt : gxTh Z At (S.psi β (Om (1 + 1))) < gxTh Z At (t ζ) :=
    gxTh_lt (GxCl.atom hβ) (hpos ζ hζ)
  rcases lt_or_ge e Â with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans hbase).trans_lt hβlt
  · obtain ⟨hD, hlt'⟩ := htail ζ hζ e he h1 heA
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - Â < ζ := by
      have h2 := heA
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact (IH _ hlt hD).trans_lt (gxTh_lt (GxCl.atom (hat _ hD)) hlt')

end Lift

/-- `Â ≤ e < Â + ζ` gives `e − Â < ζ`. -/
theorem rySub_lt {Â e ζ : Ordinal.{0}} (h1 : Â ≤ e) (h2 : e < Â + ζ) : e - Â < ζ := by
  have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
  rw [e1] at h2
  exact (add_lt_add_iff_left _).1 h2

/-- **The tail condition at the block `x` of `μ`.** -/
def RyTailAt (S : InaccSeq.{0}) (μ x : Ordinal.{0}) : Prop :=
  ∃ t : Ordinal.{0} → Ordinal.{0}, ∀ ζ < ConjT.th S,
    t ζ ∈ ldAtR S μ ∧ t ζ < Lc.lcG S (x + 1) ∧ Lc.lcG S x < t ζ ∧
    ∀ e, HCl S (ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ) (gxTh (upsilon μ) (ldAtR S μ) (t ζ)) e →
      ConjT.Aη S (cdEta S μ) + ConjT.th S * x ≤ e →
      e < ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ →
      t (e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x)) < t ζ

/-- **`RpBlkAt` from the base reading and the tail condition.** -/
theorem ryBlkAt_of_tail {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ)
    (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RyTailAt S μ x) : Rp.RpBlkAt S μ x := by
  obtain ⟨t, ht⟩ := h
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S μ m = gxTh (upsilon μ) (ldAtR S μ) m :=
    fun m hm => ldTheta hR.1 hX hm
  have hβA : β < A := Ru.ruExp_lt hR hc hxρ
  have hβH : β ∈ cdHull S μ := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine Rp.rpThx_mem ?_ hxρ
      exact (show Om ω ≤ β from le_self_add).trans_lt hβA
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S μ := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon μ) (ldAtR S μ) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le, ← Rg.rgUps_eq hR hxρ.le]; exact hP
  have hL := ryLiftT hZ hZ1 hAt hβat hbase (D := Set.Iio (ConjT.th S)) (t := t)
    (fun ζ hζ => (ht ζ hζ).1) (fun ζ hζ => (ht ζ hζ).2.2.1)
    (fun ζ hζ e he h1 h2 => ⟨(rySub_lt h1 h2).trans hζ, (ht ζ hζ).2.2.2 e he h1 h2⟩)
  intro ζ hζ
  refine ⟨t ζ, ?_, (ht ζ hζ).2.1, ?_⟩
  · rw [Le.leAt_eq]; exact (ht ζ hζ).1
  · rw [hTh _ ((ht ζ hζ).2.1.trans (Lc.lcG_lt_Om2 _)).le, ← add_assoc]
    exact hL ζ hζ

/-- **`RuBlkHi` from the base reading and the tail condition.** -/
theorem ryHi_of_tail {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ)
    (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RyTailAt S μ x) : Ru.RuBlkHi S μ x :=
  Ru.ruHi_of_blkAt (ryBlkAt_of_tail hR hc hx hP h)

/-- **`RpReadAll` from the tail condition at every block whose base is read.** -/
theorem ryReadAll_of_tail {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RyTailAt S μ x) :
    Rp.RpReadAll S k :=
  Rp.rpReadAll_of_blkAt fun μ hR hω hc x hx hP => ryBlkAt_of_tail hR hc hx hP (h μ hR hω hc x hx hP)

/-- **The road `Ru.ruRoad` with `RyTailAt` in place of `RuBlkHi`.** -/
theorem ryRoad {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (htl : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RyTailAt S μ x)
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
  Ru.ruRoad hU hO hL hV hVt hEQ htop
    (fun μ hR hω hc x hx hP => ryHi_of_tail hR hc hx hP (htl μ hR hω hc x hx hP)) h0 hn hout hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Ry
