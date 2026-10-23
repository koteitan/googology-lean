import Googology.Trans.PoR.InaccPsi.R2.RyTail

/-!
# The tail condition holds on the offsets below `Γ_{Ω₁+1}` (a satisfiability check of `RyTailAt`)

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)`, `A = A_{η_μ}`, `Â = A + θ·x`,
`β = Ω_ω + θ₂·x`, `ρ_μ = υ_μ`, `Θ = gxTh ρ_μ (ldAtR μ)`, `κ = Ru.ruK ρ_μ (ldAtR μ)` (the lift of the previous
round), `ggGam = Γ_{Ω₁+1}`, `RuDom` the codes over `Θ(Ω₂)` below `ggGam`.

* `ryW T ζ` (the least code over `T` at or above `ζ`, below `ggGam`), `ryW_spec`, `ryW_code` (`ryW T ζ = ζ` on
  codes over `T`), `ryCode_succ`;
* `ryTlow` (the low atoms), `ryTail_low` (**the conditions of `RyTailAt` on `[0, Γ_{Ω₁+1})`**): at a Range
  restart `μ` with code `G' + 1` and `x + 1 < ρ_μ`, the map `t ζ = ψ_{Ω₂}(β + κ(ryW T₁ ζ + 1))`,
  `T₁ = Θ(G(x+1))`, sends every `ζ < Γ_{Ω₁+1}` to an atom of `μ` in `(G(x), G(x+1))`, and `t(e − Â) < t(ζ)`
  for every `e ∈ HCl(Â + ζ, Θ(t ζ))` with `Â ≤ e < Â + ζ`.  No reading of the base is used;
* `ryTlow_lt` (**the low atoms lie below every high atom**): `ryTlow ζ' < ψ_{Ω₂}(β + c)` for a code `ζ' < Γ_{Ω₁+1}`
  over `Θ_μ(ψ_{Ω₂}(β + c))`, when `ψ_{Ω₃}(0) ≤ c` and `ψ_{Ω₂}(β + c) < G(x+1)`.

So the tail condition is not contradictory: on the offsets below `Γ_{Ω₁+1}` it is met by the lift `κ`; what
`RyTailAt` adds over this is the offsets `Γ_{Ω₁+1} ≤ ζ < θ` (the content of `Ru.RuBlkHi`).

No new axiom.  New definitions: `ryW`, `ryTlow`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ry

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

/-- **The least code over `T` at or above `ζ`** below `ggGam`. -/
noncomputable def ryW (T ζ : Ordinal.{0}) : Ordinal.{0} := sInf {w | GgCl T w ∧ w < ggGam ∧ ζ ≤ w}

theorem ryW_spec {T ζ : Ordinal.{0}} (hT : 2 ≤ T) (hζ : ζ < ggGam) :
    GgCl T (ryW T ζ) ∧ ryW T ζ < ggGam ∧ ζ ≤ ryW T ζ := by
  obtain ⟨w, hw, hn, hwG⟩ := ruGam_cof hζ
  have hne : {w | GgCl T w ∧ w < ggGam ∧ ζ ≤ w}.Nonempty := ⟨w, hw.mono hT, hwG, hn⟩
  exact csInf_mem hne

theorem ryW_code {T ζ : Ordinal.{0}} (hT : 2 ≤ T) (hc : GgCl T ζ) (hζ : ζ < ggGam) : ryW T ζ = ζ :=
  le_antisymm (csInf_le' ⟨hc, hζ, le_rfl⟩) (ryW_spec hT hζ).2.2

/-- `ζ ↦ ζ + 1` keeps the codes below `ggGam`. -/
theorem ryCode_succ {T ζ : Ordinal.{0}} (hT : SC T) (hc : GgCl T ζ) (hζ : ζ < ggGam) :
    GgCl T (ζ + 1) ∧ ζ + 1 < ggGam := by
  refine ⟨GgCl.add hc (GgCl.small ?_), ggGam_spec.1.add_one_lt hζ⟩
  have h1 : (1 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 1
  exact h1.trans (Lw.lw_omega_lt_SC hT)

/-- **The low choice of atoms** `t ζ = ψ_{Ω₂}(β + κ(ryW T₁ ζ + 1))`, `T₁ = Θ_μ(G(x+1))`. -/
noncomputable def ryTlow (S : InaccSeq.{0}) (μ x ζ : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om ω + Lc.lcTh S 2 * x + ruK (upsilon μ) (ldAtR S μ)
    (ryW (gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1))) ζ + 1)) (Om (1 + 1))

/-- **The conditions of `RyTailAt` on the offsets below `Γ_{Ω₁+1}`.** -/
theorem ryTail_low {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
    (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) (hx : x + 1 < upsilon μ) :
    ∀ ζ < ggGam,
      ryTlow S μ x ζ ∈ ldAtR S μ ∧ ryTlow S μ x ζ < Lc.lcG S (x + 1) ∧ Lc.lcG S x < ryTlow S μ x ζ ∧
      ∀ e, HCl S (ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ)
          (gxTh (upsilon μ) (ldAtR S μ) (ryTlow S μ x ζ)) e →
        ConjT.Aη S (cdEta S μ) + ConjT.th S * x ≤ e →
        e < ConjT.Aη S (cdEta S μ) + ConjT.th S * x + ζ →
        ryTlow S μ x (e - (ConjT.Aη S (cdEta S μ) + ConjT.th S * x)) < ryTlow S μ x ζ := by
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
  set κ := ruK (upsilon μ) (ldAtR S μ) with hκdef
  have hZ2 : SC Z2 := ruZ2_SC hZ hZ1 hAt
  have hβA : β < A := ruExp_lt hR hc hxρ
  have hβ1A : Om ω + Lc.lcTh S 2 * (x + 1) < A := ruExp_lt hR hc hx
  have hmemβ : ∀ a b, Om ω < a → x < b → β ∈ S.CSet a b := fun a b ha hb => Rp.rpThx_mem ha hb
  have hβH : β ∈ cdHull S μ := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine hmemβ _ _ ?_ hxρ
      exact (show Om ω ≤ β from le_self_add).trans_lt hβA
  have hκH : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → κ ζ ∈ cdHull S μ :=
    fun ζ hζ => ruK_mem hZ hZ1 hAt hZ2 le_rfl (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec hg
      exact (ldHull_iff hR.1 hX hlt2).2 hcode) ζ hζ.1 hζ.2
  have hκθ : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → β + κ ζ < Om ω + Lc.lcTh S 2 * (x + 1) :=
    fun ζ hζ => by
      rw [mul_add_one, ← add_assoc]
      exact (add_lt_add_iff_left _).2 (ruK_lt hZ hZ1 hAt hθ2SC hθ2 ζ hζ)
  have hat : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S μ :=
    fun ζ hζ => ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ).trans hβ1A, rfl⟩
  have hβmem : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → ζ ≠ 0 →
      β ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := fun ζ hζ h0 =>
    hmemβ _ _ (lt_of_le_of_lt le_self_add (lt_add_of_pos_right β (ruK_pos hZ hZ1 hAt hζ h0)))
      (hx1.trans (psiS_bounds (S := S) _ 1).1)
  have hG1 : Lc.lcG S (x + 1) = S.psi (Om ω + Lc.lcTh S 2 * (x + 1)) (Om (1 + 1)) := rfl
  have hlt0 : ∀ ζ, RuDom (upsilon μ) (ldAtR S μ) ζ → ζ ≠ 0 →
      Lc.lcG S x < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (ruK_pos hZ hZ1 hAt hζ h0)) (hβmem ζ hζ h0)
  set T1 := gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1)) with hT1def
  have hT1SC : SC T1 :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hT1Z : T1 ≤ Z2 := gxTh_mono (Lc.lcG_lt_Om2 _).le
  have hT12 : (2 : Ordinal.{0}) ≤ T1 := ruTwo_le hT1SC
  have hdom : ∀ w, GgCl T1 w → w < ggGam → RuDom (upsilon μ) (ldAtR S μ) w :=
    fun w hw hwG => ⟨hw.mono hT1Z, hwG⟩
  have hlt1 : ∀ w, GgCl T1 w → w < ggGam → S.psi (β + κ w) (Om (1 + 1)) < Lc.lcG S (x + 1) :=
    fun w hw hwG => by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w (hdom w hw hwG)) (CSet.add_mem ?_ ?_)
    · refine hmemβ _ _ ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one x)))
    · exact ruK_mem hZ hZ1 hAt hT1SC hT1Z (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) w hw hwG
  have hTl : ryTlow S μ x = fun ζ => S.psi (β + κ (ryW T1 ζ + 1)) (Om (1 + 1)) := rfl
  rw [hTl]
  intro ζ hζ
  obtain ⟨hWc, hWG, hζW⟩ := ryW_spec hT12 hζ
  obtain ⟨hW1c, hW1G⟩ := ryCode_succ hT1SC hWc hWG
  have hW1 := hdom _ hW1c hW1G
  have hW10 : ryW T1 ζ + 1 ≠ 0 := (Order.lt_add_one_iff.2 zero_le).ne'
  refine ⟨hat _ hW1, hlt1 _ hW1c hW1G, hlt0 _ hW1 hW10, fun e he h1 h2 => ?_⟩
  set t := S.psi (β + κ (ryW T1 ζ + 1)) (Om (1 + 1)) with htdef
  show S.psi (β + κ (ryW T1 (e - Â) + 1)) (Om (1 + 1)) < t
  have htSC : SC (gxTh (upsilon μ) (ldAtR S μ) t) :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have htT1 : gxTh (upsilon μ) (ldAtR S μ) t ≤ T1 := gxTh_mono (hlt1 _ hW1c hW1G).le
  have hTZ : gxTh (upsilon μ) (ldAtR S μ) t ≤ Z2 := htT1.trans hT1Z
  obtain ⟨hg, hlt⟩ := ruTail htSC.1 (ruDvd (cdEta S μ) x) hζ.le he h1 h2
  have hltG : e - Â < ggGam := hlt.trans hζ
  rw [ryW_code hT12 (hg.mono htT1) hltG]
  obtain ⟨hg1, hD1G⟩ := ryCode_succ htSC hg hltG
  have hD1 : RuDom (upsilon μ) (ldAtR S μ) (e - Â + 1) := ⟨hg1.mono hTZ, hD1G⟩
  have hord : e - Â + 1 < ryW T1 ζ + 1 := (Order.add_one_le_of_lt (hlt.trans_le hζW)).trans_lt (lt_add_one _)
  have hκ := ruK_mono hZ hZ1 hAt _ hW1 _ hD1 hord
  have hmem : β + κ (e - Â + 1) ∈ S.CSet (β + κ (ryW T1 ζ + 1)) t :=
    CSet.add_mem (hβmem _ hW1 hW10)
      (ruK_mem hZ hZ1 hAt htSC hTZ (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hg1 hD1G)
  exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hκ) hmem

/-- **A low atom below a high one**: for an atom `s = ψ_{Ω₂}(β + c) < G(x+1)` with `ψ_{Ω₃}(0) ≤ c`, every code
`ζ' < Γ_{Ω₁+1}` over `Θ_μ(s)` has `ryTlow ζ' < s`. -/
theorem ryTlow_lt {μ x c ζ' : Ordinal.{0}} (hR : CdRange S μ) (hx : x + 1 < upsilon μ)
    (hcz : S.psi 0 (Om (1 + 1 + 1)) ≤ c)
    (hs : S.psi (Om ω + Lc.lcTh S 2 * x + c) (Om (1 + 1)) < Lc.lcG S (x + 1))
    (hg : GgCl (gxTh (upsilon μ) (ldAtR S μ) (S.psi (Om ω + Lc.lcTh S 2 * x + c) (Om (1 + 1)))) ζ')
    (hζ' : ζ' < ggGam) :
    ryTlow S μ x ζ' < S.psi (Om ω + Lc.lcTh S 2 * x + c) (Om (1 + 1)) := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hxρ : x < upsilon μ := (lt_add_one x).trans hx
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hxρ
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set s := S.psi (β + c) (Om (1 + 1)) with hsdef
  set T := gxTh (upsilon μ) (ldAtR S μ) s with hTdef
  set T1 := gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (x + 1)) with hT1def
  set Z2 := gxTh (upsilon μ) (ldAtR S μ) (Om (1 + 1)) with hZ2def
  have hTSC : SC T :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hT1SC : SC T1 :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hTT1 : T ≤ T1 := gxTh_mono hs.le
  have hTZ : T ≤ Z2 := hTT1.trans (gxTh_mono (Lc.lcG_lt_Om2 _).le)
  rw [show ryTlow S μ x ζ' = S.psi (β + ruK (upsilon μ) (ldAtR S μ) (ryW T1 ζ' + 1)) (Om (1 + 1)) from rfl,
    ryW_code (ruTwo_le hT1SC) (hg.mono hTT1) hζ']
  obtain ⟨hg1, hG1⟩ := ryCode_succ hTSC hg hζ'
  have hD1 : RuDom (upsilon μ) (ldAtR S μ) (ζ' + 1) := ⟨hg1.mono hTZ, hG1⟩
  have hX3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have h23 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hκc : ruK (upsilon μ) (ldAtR S μ) (ζ' + 1) < c :=
    (ruK_lt hZ hZ1 hAt hX3 h23 _ hD1).trans_le hcz
  have hc0 : 0 < c := lt_of_le_of_lt zero_le hκc
  have hmem : β + ruK (upsilon μ) (ldAtR S μ) (ζ' + 1) ∈ S.CSet (β + c) s := by
    refine CSet.add_mem (Rp.rpThx_mem ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)) ?_
    · exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right β hc0)
    · exact ruK_mem hZ hZ1 hAt hTSC hTZ (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hg1 hG1
  exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hκc) hmem

end Googology.Trans.PoR.InaccPsi.R2.Ry
