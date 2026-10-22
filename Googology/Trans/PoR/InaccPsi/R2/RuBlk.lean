import Googology.Trans.PoR.InaccPsi.R2.RuK

/-!
# The block step below `Γ_{Ω₁+1}`: the atoms `ψ_{Ω₂}(Ω_ω + θ₂·x + κ ζ)` cover `ψ_{Ω₁}(A + θ·x + ζ)`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)` (`Lc.lcG`), `G' = Ls.lsG S (k+1)`, `A = A_{η_μ}`,
`ρ_μ = ψ_{Ω₁}(A)`, `Θ_μ` the reading, `κ = Ru.ruK ρ_μ (ldAtR μ)` (`Ru.ruK`), `ggGam = Γ_{Ω₁+1}` (the least strongly
critical ordinal above `Ω₁`), `RpBlkAt` as in `Rp.RpBlkAt`.

* `ruExp_lt` (`Ω_ω + θ₂·z < A` for `z < ρ_μ` at a Range restart with code `G' + 1`), `ruDvd` (`ggGam ∣ A + θ·x`),
  `ruGam_cof` (**the codes over `2` are cofinal in `ggGam`**);
* `ruBlkLow` (**THE BLOCK STEP BELOW `Γ_{Ω₁+1}`**: at a Range restart `μ` with code `G' + 1`, for `x + 1 < ρ_μ`,
  the reading of the base `υ_{μ+x} ≤ Θ_μ(G(x))` gives, for every `ζ < Γ_{Ω₁+1}`, an atom `t < G(x+1)` with
  `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`; `Ru.ruLift` at the base `β = Ω_ω + θ₂·x`, `Â = A + θ·x`, with the lift `κ`:
  the level shift `Ω₁ ↦ Ω₂`, `g ↦ Θ_μ⁻¹(g)`, commuting with `+`, `ω^·` and `φ`, on the codes below `Γ_{Ω₁+1}`);
* `RuBlkHi S μ x` (**the block above `Γ_{Ω₁+1}`**: `RpBlkAt` asked only at `Γ_{Ω₁+1} ≤ ζ < θ`), `ruBlkAt_of_hi`,
  `ruHi_of_blkAt` (so `RuBlkHi ⇔ RpBlkAt` given the base reading),
  `ruReadAll_of_hi` (**`RpReadAll` from `RuBlkHi` at every block whose base is read**), `ruRoad` (**the road
  `Rp.rpRoad_read` with `RuBlkHi` in place of `RpReadAll`**).

No new axiom.  New definition (hypothesis name only): `RuBlkHi`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ru

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem ruOm2_lt_th2 : Om (1 + 1 : Ordinal.{0}) < Lc.lcTh S 2 := by
  have h := (psiS_bounds (S := S) (Om ω) ((2 : ℕ) : Ordinal.{0})).1
  have e : Om (1 + 1 : Ordinal.{0}) = Om ((2 : ℕ) : Ordinal.{0}) := by norm_num
  rw [e]; exact h

/-- `Ω_ω + θ₂·z < A` for `z < ρ_μ` at a Range restart with code `G' + 1`. -/
theorem ruExp_lt {μ z : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hz : z < upsilon μ) : Om ω + Lc.lcTh S 2 * z < ConjT.Aη S (cdEta S μ) := by
  have hGz := Rp.rpG_lt (S := S) k (Rg.rgGam_lt hR hz)
  obtain ⟨e, heA, -, hGe⟩ := Rp.rpG'_atom hR hc
  have hlt : Om ω + Lc.lcTh S 2 * z < e := by
    by_contra hle
    push Not at hle
    have h1 : S.psi e (Om (1 + 1)) ≤ Lc.lcG S z := (psi_mono (S := S) (InR_Om_succ 1) hle).1
    rw [← hGe] at h1
    exact absurd (h1.trans_lt hGz) (lt_irrefl _)
  exact hlt.trans heA

/-- `ggGam ∣ A_η + θ·x`. -/
theorem ruDvd (η x : Ordinal.{0}) : ggGam ∣ ConjT.Aη S η + ConjT.th S * x := by
  have hG := ggGam_spec.1
  have hθ : ggGam ∣ ConjT.th S := by
    rw [← gg_SC_eps hG, ← gg_SC_eps (ConjT.SC_th S)]
    exact opow_dvd_opow ω (ggGam_le (ConjT.SC_th S) Om1_lt_th)
  have hW : ggGam ∣ Om ω := by
    rw [← gg_SC_eps hG, ← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
    exact opow_dvd_opow ω (ggGam_le (SC_Om omega0_ne_zero) (Om_lt_Om.2 one_lt_omega0))
  unfold ConjT.Aη
  exact dvd_add (dvd_add hW (hθ.mul_right _)) (hθ.mul_right _)

theorem ruTwo_le {T : Ordinal.{0}} (hT : SC T) : (2 : Ordinal.{0}) ≤ T :=
  ((natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC hT)).le

/-- **The codes over `2` are cofinal in `ggGam`**: every `ζ < ggGam` is at most such a code below `ggGam`. -/
theorem ruGam_cof {ζ : Ordinal.{0}} (h : ζ < ggGam) : ∃ w, GgCl 2 w ∧ ζ ≤ w ∧ w < ggGam := by
  have hG := ggGam_spec
  have hcl : ∀ w, GgCl 2 w → w < ggGam := by
    intro w hw
    induction hw with
    | small h => exact h.trans_le (ruTwo_le hG.1)
    | om => exact hG.2
    | add _ _ ihx ihy => exact hG.1.isPrincipal ihx ihy
    | phi _ _ ihx ihy => exact hG.1.2 _ ihx _ ihy
  by_contra hno
  push Not at hno
  have hall : ∀ w, GgCl 2 w → w < ζ := fun w hw => by
    by_contra hc
    push Not at hc
    exact absurd (hcl w hw) (not_lt.2 (hno w hw hc))
  have hne : ({w | GgCl 2 w} : Set Ordinal.{0}).Nonempty := ⟨0, GgCl.zero two_pos⟩
  have hbdd : BddAbove ({w | GgCl 2 w} : Set Ordinal.{0}) := ⟨ζ, fun w hw => (hall w hw).le⟩
  have hsζ : sSup {w | GgCl (2 : Ordinal.{0}) w} ≤ ζ := csSup_le hne fun w hw => (hall w hw).le
  have hΩ : Om 1 < sSup {w | GgCl (2 : Ordinal.{0}) w} :=
    (lt_add_one _).trans_le (le_csSup hbdd (GgCl.add GgCl.om (GgCl.small one_lt_two)))
  have hSC : SC (sSup {w | GgCl (2 : Ordinal.{0}) w}) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩ, fun x hx y hy => ?_⟩
    obtain ⟨c, hc, hxc⟩ := exists_lt_of_lt_csSup hne hx
    obtain ⟨d, hd, hyd⟩ := exists_lt_of_lt_csSup hne hy
    have hm : GgCl (2 : Ordinal.{0}) (max c d) := by
      rcases le_total c d with h | h
      · rw [max_eq_right h]; exact hd
      · rw [max_eq_left h]; exact hc
    calc veblen x y ≤ veblen (max c d) y := veblen_left_monotone y (hxc.le.trans (le_max_left c d))
      _ ≤ veblen (max c d) (max c d) :=
          veblen_le_veblen_iff_right.2 (hyd.le.trans (le_max_right c d))
      _ < veblen (max c d) (max c d + 1) := veblen_lt_veblen_iff_right.2 (lt_add_one _)
      _ ≤ _ := le_csSup hbdd (GgCl.phi hm (GgCl.add hm (GgCl.small one_lt_two)))
  exact absurd ((ggGam_le hSC hΩ).trans hsζ) (not_le.2 h)

/-- **THE BLOCK STEP BELOW `Γ_{Ω₁+1}`.** -/
theorem ruBlkLow {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) :
    ∀ ζ, ζ < ggGam → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hxρ
  have hθ2 := ruOm2_lt_th2 (S := S)
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  set Z2 := gxTh (upsilon μ) (ldAtR S μ) (Om (1 + 1)) with hZ2def
  have hZ2 : SC Z2 := ruZ2_SC hZ hZ1 hAt
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S μ m = gxTh (upsilon μ) (ldAtR S μ) m :=
    fun m hm => ldTheta hR.1 hX hm
  have hβA : β < A := ruExp_lt hR hc hxρ
  have hβ1A : Om ω + Lc.lcTh S 2 * (x + 1) < A := ruExp_lt hR hc hx
  have hmemβ : ∀ a b, Om ω < a → x < b → β ∈ S.CSet a b := fun a b ha hb => Rp.rpThx_mem ha hb
  have hβH : β ∈ cdHull S μ := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine hmemβ _ _ ?_ hxρ
      exact (show Om ω ≤ β from le_self_add).trans_lt hβA
  -- the codes `κ ζ` lie in the hull, below `θ₂`
  have hκH : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → ruK (upsilon μ) (ldAtR S μ) ζ ∈ cdHull S μ :=
    fun ζ hζ => ruK_mem hZ hZ1 hAt hZ2 le_rfl (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec hg
      exact (ldHull_iff hR.1 hX hlt2).2 hcode) ζ hζ.1 hζ.2
  have hκθ : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → β + ruK (upsilon μ) (ldAtR S μ) ζ <
      Om ω + Lc.lcTh S 2 * (x + 1) := fun ζ hζ => by
    rw [mul_add_one, ← add_assoc]
    exact (add_lt_add_iff_left _).2 (ruK_lt hZ hZ1 hAt hθ2SC hθ2 ζ hζ)
  have hat : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ →
      S.psi (β + ruK (upsilon μ) (ldAtR S μ) ζ) (Om (1 + 1)) ∈ ldAtR S μ := fun ζ hζ =>
    ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ).trans hβ1A, rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S μ := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon μ) (ldAtR S μ) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le, ← Rg.rgUps_eq hR hxρ.le]; exact hP
  have hpos : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + ruK (upsilon μ) (ldAtR S μ) ζ) (Om (1 + 1)) := by
    intro ζ hζ h0
    have hk := ruK_pos hZ hZ1 hAt hζ h0
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β hk)
      (hmemβ _ _ (lt_of_le_of_lt le_self_add (lt_add_of_pos_right β hk)) ?_)
    exact hx1.trans (psiS_bounds (S := S) _ 1).1
  have hcl : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → ∀ e,
      HCl S (Â + ζ) (gxTh (upsilon μ) (ldAtR S μ)
        (S.psi (β + ruK (upsilon μ) (ldAtR S μ) ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → RuDom (upsilon μ) (ldAtR S μ) (e - Â) ∧
        β + ruK (upsilon μ) (ldAtR S μ) (e - Â) ∈
          S.CSet (β + ruK (upsilon μ) (ldAtR S μ) ζ)
            (S.psi (β + ruK (upsilon μ) (ldAtR S μ) ζ) (Om (1 + 1))) := by
    intro ζ hζ e he h1 h2
    set t := S.psi (β + ruK (upsilon μ) (ldAtR S μ) ζ) (Om (1 + 1)) with htdef
    have htSC : SC (gxTh (upsilon μ) (ldAtR S μ) t) :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : gxTh (upsilon μ) (ldAtR S μ) t ≤ Z2 := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    obtain ⟨hg, hlt⟩ := ruTail htSC.1 (ruDvd (cdEta S μ) x) hζ.2.le he h1 h2
    have hD : RuDom (upsilon μ) (ldAtR S μ) (e - Â) := ⟨hg.mono hTZ, hlt.trans hζ.2⟩
    refine ⟨hD, CSet.add_mem ?_ ?_⟩
    · have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hlt; exact absurd hlt (not_lt.2 zero_le)
      exact hmemβ _ _ (lt_of_le_of_lt le_self_add
        (lt_add_of_pos_right β (ruK_pos hZ hZ1 hAt hζ hζ0)))
        (hx1.trans (psiS_bounds (S := S) _ 1).1)
    · exact ruK_mem hZ hZ1 hAt htSC hTZ (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hg hD.2
  have hLift := ruLift hZ hZ1 hAt hβat hbase (D := {ζ | RuDom (upsilon μ) (ldAtR S μ) ζ})
    (fun ζ hζ ζ' hζ' h => ruK_mono hZ hZ1 hAt ζ hζ ζ' hζ' h) hat hpos hcl
  intro ζ hζE
  obtain ⟨w, hw, hn, hwG⟩ := ruGam_cof hζE
  have hwD : RuDom (upsilon μ) (ldAtR S μ) w := ⟨hw.mono (ruTwo_le hZ2), hwG⟩
  set t := S.psi (β + ruK (upsilon μ) (ldAtR S μ) w) (Om (1 + 1)) with htdef
  have hG1 : Lc.lcG S (x + 1) = S.psi (Om ω + Lc.lcTh S 2 * (x + 1)) (Om (1 + 1)) := rfl
  have htlt : t < Lc.lcG S (x + 1) := by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w hwD) (CSet.add_mem ?_ ?_)
    · refine hmemβ _ _ ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one x)))
    · have hTSC : SC (gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1))) :=
        gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
      have hTZ : gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1)) ≤ Z2 :=
        gxTh_mono (Lc.lcG_lt_Om2 _).le
      exact ruK_mem hZ hZ1 hAt hTSC hTZ (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) w
        (hw.mono (ruTwo_le hTSC)) hwG
  refine ⟨t, ?_, htlt, ?_⟩
  · rw [Le.leAt_eq]; exact hat w hwD
  · rw [hTh t (psi_lt (InR_Om_succ 1) _).le, ← add_assoc]
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hn)).1.trans (hLift w hwD)

/-- **The block above `Γ_{Ω₁+1}`**: the atoms below `G(x+1)` cover `ψ_{Ω₁}(A + θ·x + ζ)` for `Γ_{Ω₁+1} ≤ ζ < θ`. -/
def RuBlkHi (S : InaccSeq.{0}) (μ x : Ordinal.{0}) : Prop :=
  ∀ ζ, ggGam ≤ ζ → ζ < ConjT.th S → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ),
    t < Lc.lcG S (x + 1) ∧ S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t

/-- **The base reading and `RuBlkHi` give `RpBlkAt`.** -/
theorem ruBlkAt_of_hi {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x + 1 < upsilon μ) (hP : upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x)) (h : RuBlkHi S μ x) :
    Rp.RpBlkAt S μ x := by
  intro ζ hζ
  rcases lt_or_ge ζ ggGam with hE | hE
  · exact ruBlkLow hR hc hx hP ζ hE
  · exact h ζ hE hζ

/-- **`RuBlkHi` asks no more than `RpBlkAt`.** -/
theorem ruHi_of_blkAt {μ x : Ordinal.{0}} (h : Rp.RpBlkAt S μ x) : RuBlkHi S μ x :=
  fun ζ _ hζ => h ζ hζ

/-- **`RpReadAll` from `RuBlkHi`** at every block whose base is read. -/
theorem ruReadAll_of_hi {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RuBlkHi S μ x) :
    Rp.RpReadAll S k :=
  Rp.rpReadAll_of_blkAt fun μ hR hω hc x hx hP => ruBlkAt_of_hi hR hc hx hP (h μ hR hω hc x hx hP)

/-- **The road `Rp.rpRoad_read` with `RuBlkHi` in place of `RpReadAll`.** -/
theorem ruRoad {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hhi : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RuBlkHi S μ x)
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
  Rp.rpRoad_read hU hO hL hV hVt hEQ htop (ruReadAll_of_hi hhi) h0 hn hout hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Ru
