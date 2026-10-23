import Googology.Trans.PoR.InaccPsi.R2.RxTail

/-!
# The block step below `ψ_{Ω₂}(Ω₂)`: the atoms `ψ_{Ω₂}(Ω_ω + θ₂·x + κ ζ)` cover `ψ_{Ω₁}(A + θ·x + ζ)`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)` (`Lc.lcG`), `G' = Ls.lsG S (k+1)`, `A = A_{η_μ}`,
`Â = A + θ·x`, `β = Ω_ω + θ₂·x`, `ρ_μ = υ_μ`, `Θ = gxTh ρ_μ (ldAtR μ)` (`= Θ_μ` below `Ω₂`), `P₂ = ψ_{Ω₂}(Ω₂)`
(`Rx.rxP2`), `κ = Rx.rxK S ρ_μ (ldAtR μ)` (the level shift `Ω₁ ↦ Ω₂`, `ψ_{Ω₂}(d) ↦ ψ_{Ω₃}(κ d)`), `RxC` the codes
with normal `ψ_{Ω₂}`-atoms, `W = Rx.rxW` (`min(Θ(Ω₂), Ω₁)`).

* `rxLift` (**THE LIFT LEMMA, countable case**): `Ru.ruLift` with the tail hypothesis asked only when the reading
  `Θ(ψ_{Ω₂}(β + κ ζ))` is countable (otherwise `ψ_{Ω₁}(Â + ζ) < Ω₁ ≤ Θ(…)` holds at once);
* `rxBlkP2` (**THE BLOCK STEP BELOW `P₂`**: at a Range restart `μ` with code `G' + 1`, for `x + 1 < ρ_μ`, the
  reading of the base `υ_{μ+x} ≤ Θ_μ(G(x))` gives, for every `ζ < ψ_{Ω₂}(Ω₂)`, an atom `t < G(x+1)` of `μ` with
  `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`; the atoms are `ψ_{Ω₂}(β + κ w)` for the codes `w ≥ ζ` over `2`);
* `RxBlkHi2 S μ x` (**the block above `P₂`**: `Ru.RuBlkHi` asked only at `P₂ ≤ ζ < θ`), `rxHi_of_hi2`
  (`RxBlkHi2 ⇒ RuBlkHi`), `rxBlkAt_of_hi2` (`⇒ RpBlkAt`), `rxReadAll_of_hi2` (`⇒ RpReadAll`), `rxRoad` (**the road
  `Ru.ruRoad` with `RxBlkHi2` in place of `RuBlkHi`**).

So the offsets `ζ < ψ_{Ω₂}(Ω₂)` of every block are covered without hypothesis; `RuBlkHi` is reduced to the
offsets `ψ_{Ω₂}(Ω₂) ≤ ζ < θ`.

No new axiom.  New definition (hypothesis name only): `RxBlkHi2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

section Lift

variable {Z β Â : Ordinal.{0}} {At : Set Ordinal.{0}} {D : Set Ordinal.{0}} {κ : Ordinal.{0} → Ordinal.{0}}

/-- **THE LIFT LEMMA, countable case.** -/
theorem rxLift (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hβ : S.psi β (Om (1 + 1)) ∈ At)
    (hbase : S.psi Â (Om 1) ≤ gxTh Z At (S.psi β (Om (1 + 1))))
    (hmono : ∀ ζ ∈ D, ∀ ζ' ∈ D, ζ' < ζ → κ ζ' < κ ζ)
    (hat : ∀ ζ ∈ D, S.psi (β + κ ζ) (Om (1 + 1)) ∈ At)
    (hpos : ∀ ζ ∈ D, ζ ≠ 0 → S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)))
    (hcl : ∀ ζ ∈ D, gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (Â + ζ) (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) e → Â ≤ e →
      e < Â + ζ → e - Â ∈ D ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1)))) :
    ∀ ζ ∈ D, S.psi (Â + ζ) (Om 1) ≤ gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  rcases le_or_gt (Om 1) (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) with hbig | hcnt
  · exact (psi_lt Low.InR_Om_one _).le.trans hbig
  have hT : SC (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · rw [add_zero]
    exact hbase.trans (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1)
  refine psi_le_of_key hT fun e he heA => ?_
  have hβlt : gxTh Z At (S.psi β (Om (1 + 1))) < gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) :=
    gxTh_lt (GxCl.atom hβ) (hpos ζ hζ hζ0)
  rcases lt_or_ge e Â with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans hbase).trans_lt hβlt
  · obtain ⟨hD, hmem⟩ := hcl ζ hζ hcnt e he h1 heA
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - Â < ζ := by
      have h2 := heA; rw [e1] at h2; exact (add_lt_add_iff_left _).1 h2
    have hκ := hmono ζ hζ _ hD hlt
    have hs : S.psi (β + κ (e - Â)) (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hκ) hmem
    rw [e1]
    exact (IH _ hlt hD).trans_lt (gxTh_lt (GxCl.atom (hat _ hD)) hs)

end Lift

theorem rxTh2_eq : Lc.lcTh S 2 = S.psi (Om ω) (Om (1 + 1 + 1)) := by
  unfold Lc.lcTh; norm_num

theorem rxOm3_le_W : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Om ω := Ry.ryOm3_lt.le

/-- **THE BLOCK STEP BELOW `ψ_{Ω₂}(Ω₂)`.** -/
theorem rxBlkP2 {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) :
    ∀ ζ, ζ < rxP2 S → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hxρ
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  set Z2 := gxTh (upsilon μ) (ldAtR S μ) (Om (1 + 1)) with hZ2def
  set W := rxW (upsilon μ) (ldAtR S μ) with hWdef
  set κ := rxK S (upsilon μ) (ldAtR S μ) with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S μ m = gxTh (upsilon μ) (ldAtR S μ) m :=
    fun m hm => ldTheta hR.1 hX hm
  have hβA : β < A := ruExp_lt hR hc hxρ
  have hβ1A : Om ω + Lc.lcTh S 2 * (x + 1) < A := ruExp_lt hR hc hx
  have hWβ : Om ω ≤ β := le_self_add
  have hA3 : Om (1 + 1 + 1 : Ordinal.{0}) ≤ A := rxOm3_le_W.trans (hWβ.trans hβA.le)
  have hmemβ : ∀ a b, Om ω < a → x < b → β ∈ S.CSet a b := fun a b ha hb => Rp.rpThx_mem ha hb
  have hβH : β ∈ cdHull S μ := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine hmemβ _ _ ?_ hxρ
      exact hWβ.trans_lt hβA
  -- the codes `κ ζ` lie in the hull, below `θ₂`
  have hκH : ∀ ζ, RxC S W ζ → κ ζ ∈ cdHull S μ :=
    fun ζ hζ => rxK_mem hZ hZ1 hAt hW le_rfl hA3 (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hR.1 hX hlt2).2 hcode) ζ hζ
  have hκ2 : ∀ ζ, RxC S W ζ → κ ζ < Lc.lcTh S 2 := fun ζ hζ => by
    rw [rxTh2_eq]; exact rxK_lt_psi3 hZ hZ1 hAt rxOm3_le_W ζ hζ
  have hκθ : ∀ ζ, RxC S W ζ → β + κ ζ < Om ω + Lc.lcTh S 2 * (x + 1) := fun ζ hζ => by
    rw [mul_add_one, ← add_assoc]
    exact (add_lt_add_iff_left _).2 (hκ2 ζ hζ)
  have hat : ∀ ζ, RxC S W ζ → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S μ := fun ζ hζ =>
    ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ).trans hβ1A, rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S μ := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon μ) (ldAtR S μ) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le, ← Rg.rgUps_eq hR hxρ.le]; exact hP
  have hβmem : ∀ ζ, RxC S W ζ → ζ ≠ 0 → β ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) :=
    fun ζ hζ h0 => hmemβ _ _ (hWβ.trans_lt (lt_add_of_pos_right β (rxK_pos hZ hZ1 hAt hζ h0)))
      (hx1.trans (psiS_bounds (S := S) _ 1).1)
  have hpos : ∀ ζ, RxC S W ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (rxK_pos hZ hZ1 hAt hζ h0))
      (hβmem ζ hζ h0)
  have hcl : ∀ ζ, RxC S W ζ ∧ ζ < rxP2 S →
      gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (Â + ζ) (gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → (RxC S W (e - Â) ∧ e - Â < rxP2 S) ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζ hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    have htSC : SC (gxTh (upsilon μ) (ldAtR S μ) t) :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : gxTh (upsilon μ) (ldAtR S μ) t ≤ Z2 := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    have hTW : gxTh (upsilon μ) (ldAtR S μ) t ≤ W := le_min hTZ hcnt.le
    obtain ⟨hg, hlt⟩ := rxTail htSC.1 hcnt.le (rxDvd (cdEta S μ) x) hζ.2.le he h1 h2
    refine ⟨⟨hg.mono hTW, hlt.trans hζ.2⟩, CSet.add_mem ?_ ?_⟩
    · have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hlt; exact absurd hlt (not_lt.2 zero_le)
      exact hβmem ζ hζ.1 hζ0
    · exact rxK_mem hZ hZ1 hAt htSC hTW (rxOm3_le_W.trans (hWβ.trans le_self_add))
        (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hg
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := {ζ | RxC S W ζ ∧ ζ < rxP2 S})
    (fun ζ hζ ζ' hζ' h => rxK_mono hZ hZ1 hAt ζ hζ.1 ζ' hζ'.1 h) (fun ζ hζ => hat ζ hζ.1)
    (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  intro ζ hζE
  obtain ⟨w, hw, hn, hwG⟩ := rxCof hζE
  have hwD : RxC S W w := hw.mono (ruTwo_le hW)
  set t := S.psi (β + κ w) (Om (1 + 1)) with htdef
  have hG1 : Lc.lcG S (x + 1) = S.psi (Om ω + Lc.lcTh S 2 * (x + 1)) (Om (1 + 1)) := rfl
  have htlt : t < Lc.lcG S (x + 1) := by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w hwD) (CSet.add_mem ?_ ?_)
    · refine hmemβ _ _ ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one x)))
    · set T1 := gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1)) with hT1def
      have hT1SC : SC T1 :=
        gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
      have hTZ : T1 ≤ Z2 := gxTh_mono (Lc.lcG_lt_Om2 _).le
      have hmSC : SC (min T1 (Om 1)) := by
        rcases le_total T1 (Om 1) with h | h
        · rw [min_eq_left h]; exact hT1SC
        · rw [min_eq_right h]; exact Ph.ph_SC_Om1
      have hmW : min T1 (Om 1) ≤ W := min_le_min_right _ hTZ
      have h3 : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Om ω + Lc.lcTh S 2 * (x + 1) := rxOm3_le_W.trans le_self_add
      exact rxK_mem hZ hZ1 hAt hmSC hmW h3
        (fun g hg' => CSet.of_lt (ruInv_spec (hg'.trans_le (min_le_left _ _))).2.1) w
        (hw.mono (ruTwo_le hmSC))
  refine ⟨t, ?_, htlt, ?_⟩
  · rw [Le.leAt_eq]; exact hat w hwD
  · rw [hTh t (psi_lt (InR_Om_succ 1) _).le, ← add_assoc]
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hn)).1.trans (hLift w ⟨hwD, hwG⟩)

/-- **The block above `ψ_{Ω₂}(Ω₂)`**: `Ru.RuBlkHi` asked only at `P₂ ≤ ζ < θ`. -/
def RxBlkHi2 (S : InaccSeq.{0}) (μ x : Ordinal.{0}) : Prop :=
  ∀ ζ, rxP2 S ≤ ζ → ζ < ConjT.th S → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ),
    t < Lc.lcG S (x + 1) ∧ S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t

/-- **`RxBlkHi2 ⇒ RuBlkHi`** given the base reading. -/
theorem rxHi_of_hi2 {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RxBlkHi2 S μ x) :
    RuBlkHi S μ x := by
  intro ζ _ hζ
  rcases lt_or_ge ζ (rxP2 S) with hE | hE
  · exact rxBlkP2 hR hc hx hP ζ hE
  · exact h ζ hE hζ

/-- **`RuBlkHi ⇒ RxBlkHi2`** (so the two agree given the base reading). -/
theorem rxHi2_of_hi {μ x : Ordinal.{0}} (h : RuBlkHi S μ x) : RxBlkHi2 S μ x :=
  fun ζ hE hζ => h ζ (ggGam_le rxP2_SC rxP2_gt |>.trans hE) hζ

/-- **`RpBlkAt` from the base reading and `RxBlkHi2`.** -/
theorem rxBlkAt_of_hi2 {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ)
    (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RxBlkHi2 S μ x) : Rp.RpBlkAt S μ x :=
  ruBlkAt_of_hi hR hc hx hP (rxHi_of_hi2 hR hc hx hP h)

/-- **`RpReadAll` from `RxBlkHi2` at every block whose base is read.** -/
theorem rxReadAll_of_hi2 {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RxBlkHi2 S μ x) :
    Rp.RpReadAll S k :=
  Rp.rpReadAll_of_blkAt fun μ hR hω hc x hx hP => rxBlkAt_of_hi2 hR hc hx hP (h μ hR hω hc x hx hP)

/-- **The road `Ru.ruRoad` with `RxBlkHi2` in place of `RuBlkHi`.** -/
theorem rxRoad {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hhi : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RxBlkHi2 S μ x)
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
    (fun μ hR hω hc x hx hP => rxHi_of_hi2 hR hc hx hP (hhi μ hR hω hc x hx hP)) h0 hn hout hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Rx
