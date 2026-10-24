import Googology.Trans.PoR.InaccPsi.R2.ThUp

/-!
# A lower bound for the reading at every named restart: `ψ_{Ω₁}(A + θ·x) ≤ Θ_λ(G(x))` for `x < ρ_λ`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(x) = ψ_{Ω₂}(Ω_ω + θ₂·x)` (`Lc.lcG`), `A = A_{η_λ}`, `ρ_λ = υ_λ`,
`Θ_λ = Cd.cdTheta` (`= gxTh ρ_λ (ldAtR λ)` below `Ω₂`), `κ` the level shift of `Rx.rxL`.

* `thBlk` (**THE BLOCK STEP AT EVERY NAMED RESTART**): `Rx.rxBlkTh` without its Range and code hypotheses;
  at a named restart `λ` with `Ω_ω + θ₂·(x+1) < A` and `x < ρ_λ`, the base reading
  `ψ_{Ω₁}(A + θ·x) ≤ Θ_λ(G(x))` gives, for every `ζ < θ`, an atom `t < G(x+1)` of `λ` with
  `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_λ(t)` (the atoms `ψ_{Ω₂}(Ω_ω + θ₂·x + κ w)`);
* `thRead` (**THE BLOCK READINGS**): if `Ω_ω + θ₂·ρ_λ ≤ A` then `ψ_{Ω₁}(A + θ·x) ≤ Θ_λ(G(x))` for every
  `x < ρ_λ` (induction on `x`, the key lemma `Bt.psi_le_of_key` at `Θ_λ(G(x))`);
* `thRead_Pp` (**`ψ_{Ω₁}(A + θ·ρ_λ) ≤ Θ_λ(P')`** under the same hypothesis);
* `thTheta_L_bounds` (**`ψ_{Ω₁}(A + θ·L(k)) ≤ Θ_{L(k)}(P') ≤ L(k+1)`** and the same at `L(ω)`, with
  `A = Ω_ω·2 + P'·k`, no hypothesis).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Th

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **THE BLOCK STEP AT EVERY NAMED RESTART.** -/
theorem thBlk {l ηx x : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hxρ : x < upsilon l) (hβ1A : Om ω + Lc.lcTh S 2 * (x + 1) < ConjT.Aη S (cdEta S l))
    (hP : S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S * x) (Om 1) ≤ cdTheta S l (Lc.lcG S x)) :
    ∀ ζ, ζ < ConjT.th S → ∃ t ∈ ldAtR S l, t < Lc.lcG S (x + 1) ∧
      S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S l t := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hx1 : x < Om 1 := hxρ.trans hZ1
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hθSC := ConjT.SC_th S
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set β := Om ω + Lc.lcTh S 2 * x with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  set Z2 := gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) with hZ2def
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S l m = gxTh (upsilon l) (ldAtR S l) m :=
    fun m hm => ldTheta hl hX hm
  have hβA : β < A := by
    refine lt_of_le_of_lt ?_ hβ1A
    rw [hβdef]
    exact add_le_add_right (mul_le_mul_right le_self_add _) _
  have hWβ : Om ω ≤ β := le_self_add
  have hWA : Om ω ≤ A := hWβ.trans hβA.le
  have hmemβ : ∀ a b, Om ω < a → x < b → β ∈ S.CSet a b := fun a b ha hb => Rp.rpThx_mem ha hb
  have hβH : β ∈ cdHull S l := by
    rcases eq_or_ne x 0 with h0 | h0
    · rw [hβdef, h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
    · refine hmemβ _ _ ?_ hxρ
      exact lt_of_lt_of_le (lt_add_of_pos_right _ (mul_pos hθ2SC.1 (pos_iff_ne_zero.2 h0))) hβA.le
  have hθW : ConjT.th S < Om ω := (psi_lt (InR_Om_succ 1) _).trans (Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ cdHull S l :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hl hX hlt2).2 hcode) ζ hζ
  have hκ2 : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → κ ζ < Lc.lcTh S 2 := fun ζ hζ hζθ => by
    rw [rxTh2_eq]; exact rxL_lt_th2 hZ hZ1 hAt ζ hζ hζθ
  have hκθ : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → β + κ ζ < Om ω + Lc.lcTh S 2 * (x + 1) :=
    fun ζ hζ hζθ => by
      rw [mul_add_one, ← add_assoc]
      exact (add_lt_add_iff_left _).2 (hκ2 ζ hζ hζθ)
  have hat : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ hζθ => ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ hζθ).trans hβ1A, rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le]; exact hP
  have hβmem : ∀ ζ, RxE S W ζ → ζ ≠ 0 → β ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) :=
    fun ζ hζ h0 => hmemβ _ _ (hWβ.trans_lt (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0)))
      (hx1.trans (psiS_bounds (S := S) _ 1).1)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0))
      (hβmem ζ hζ h0)
  have hcl : ∀ ζ, RxE S W ζ ∧ ζ < ConjT.th S →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (Â + ζ) (gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → (RxE S W (e - Â) ∧ e - Â < ConjT.th S) ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζ hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon l) (ldAtR S l) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ Z2 := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have hlt : e - Â < ζ := Ry.rySub_lt h1 h2
    have hltθ : e - Â < ConjT.th S := hlt.trans hζ.2
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hm : e % ConjT.th S = e - Â := by
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC Â hltθ, Ordinal.mod_eq_zero_of_dvd (rxDvdTh (cdEta S l) x), zero_add]
    have hN : RxN S Tt (e - Â) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - Â) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltθ⟩, CSet.add_mem ?_ ?_⟩
    · have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hlt; exact absurd hlt (not_lt.2 zero_le)
      exact hβmem ζ hζ.1 hζ0
    · exact rxL_memH hZ hZ1 hAt htSC hTW (hWβ.trans le_self_add)
        (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := {ζ | RxE S W ζ ∧ ζ < ConjT.th S})
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h) (fun ζ hζ => hat ζ hζ.1 hζ.2)
    (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  intro ζ hζE
  obtain ⟨w, hw, hn, hwθ⟩ := rxCofTh hζE
  have hwD : RxE S W w := hEθ (hw.mono (ruTwo_le hW)) hwθ
  set t := S.psi (β + κ w) (Om (1 + 1)) with htdef
  have hG1 : Lc.lcG S (x + 1) = S.psi (Om ω + Lc.lcTh S 2 * (x + 1)) (Om (1 + 1)) := rfl
  have htlt : t < Lc.lcG S (x + 1) := by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w hwD hwθ) (CSet.add_mem ?_ ?_)
    · refine hmemβ _ _ ?_ (hx1.trans (psiS_bounds (S := S) _ 1).1)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one x)))
    · set T1 := gxTh (upsilon l) (ldAtR S l) (Lc.lcG S (x + 1)) with hT1def
      have hT1SC : SC T1 :=
        gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
      have hTZ : T1 ≤ Z2 := gxTh_mono (Lc.lcG_lt_Om2 _).le
      have hmSC : SC (min T1 (Om 1)) := by
        rcases le_total T1 (Om 1) with h | h
        · rw [min_eq_left h]; exact hT1SC
        · rw [min_eq_right h]; exact Ph.ph_SC_Om1
      have hmW : min T1 (Om 1) ≤ W := min_le_min_right _ hTZ
      exact rxL_memH hZ hZ1 hAt hmSC hmW le_self_add
        (fun g hg' => CSet.of_lt (ruInv_spec (hg'.trans_le (min_le_left _ _))).2.1) w
        (hEθ (hw.mono (ruTwo_le hmSC)) hwθ)
  refine ⟨t, hat w hwD hwθ, htlt, ?_⟩
  rw [hTh t (psi_lt (InR_Om_succ 1) _).le, ← add_assoc]
  exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hn)).1.trans
    (hLift w ⟨hwD, hwθ⟩)

/-- `G` is monotone. -/
theorem thG_mono {x y : Ordinal.{0}} (h : x ≤ y) : Lc.lcG S x ≤ Lc.lcG S y := by
  unfold Lc.lcG
  exact (psi_mono (S := S) (InR_Om_succ 1) (add_le_add le_rfl (mul_le_mul_right h _))).1

/-- The division by `θ`: `δ = θ·(δ/θ) + δ mod θ` with `δ mod θ < θ`, and `δ < θ·x ⇒ δ/θ < x`. -/
theorem thDiv {δ x : Ordinal.{0}} (h : δ < ConjT.th S * x) :
    δ / ConjT.th S < x ∧ δ % ConjT.th S < ConjT.th S ∧
      δ = ConjT.th S * (δ / ConjT.th S) + δ % ConjT.th S := by
  have hθ0 : ConjT.th S ≠ 0 := (ConjT.SC_th S).1.ne'
  refine ⟨(Ordinal.lt_mul_iff_div_lt hθ0).1 h, Ordinal.mod_lt δ hθ0, (Ordinal.div_add_mod δ _).symm⟩

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
  (hρA : Om ω + Lc.lcTh S 2 * upsilon l ≤ ConjT.Aη S (cdEta S l))
include hl hX hρA

/-- **THE BLOCK READINGS**: `ψ_{Ω₁}(A + θ·x) ≤ Θ_λ(G(x))` for every `x < ρ_λ`. -/
theorem thRead : ∀ x, x < upsilon l →
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S * x) (Om 1) ≤ cdTheta S l (Lc.lcG S x) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hβ1A : ∀ x, x < upsilon l → Om ω + Lc.lcTh S 2 * (x + 1) < ConjT.Aη S (cdEta S l) := by
    intro x hx
    refine lt_of_lt_of_le ?_ hρA
    exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hθ2SC.1).2 (hZ.add_one_lt hx))
  have hGat : ∀ x, x < upsilon l → Lc.lcG S x ∈ ldAtR S l := by
    intro x hx
    refine ⟨Om ω + Lc.lcTh S 2 * x, ?_, ?_, rfl⟩
    · rcases eq_or_ne x 0 with h0 | h0
      · rw [h0, mul_zero, add_zero]; exact ConjT.OmW_mem S _ _
      · refine Rp.rpThx_mem ?_ hx
        refine lt_of_lt_of_le (lt_add_of_pos_right _ (mul_pos hθ2SC.1 (pos_iff_ne_zero.2 h0))) ?_
        exact (add_le_add le_rfl (mul_le_mul_right le_self_add _)).trans (hβ1A x hx).le
    · exact lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_right le_self_add _)) (hβ1A x hx)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hG2 : Lc.lcG S x ≤ Om (1 + 1) := (Lc.lcG_lt_Om2 x).le
  rw [ldTheta hl hX hG2]
  have hTSC : SC (gxTh (upsilon l) (ldAtR S l) (Lc.lcG S x)) :=
    gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hρT : upsilon l < gxTh (upsilon l) (ldAtR S l) (Lc.lcG S x) := by
    have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om
      (psiS_bounds (S := S) (Om ω + Lc.lcTh S 2 * x) 1).1
    rwa [← ldTheta hl hX (Om_le_Om.2 le_self_add), cdTheta_Om1 hpv] at h1
  refine psi_le_of_key hTSC fun e _ he => ?_
  rcases lt_or_ge e (ConjT.Aη S (cdEta S l)) with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans_eq hρ).trans_lt hρT
  obtain ⟨δ, rfl⟩ := exists_add_of_le h1
  have hδ : δ < ConjT.th S * x := (add_lt_add_iff_left _).1 he
  obtain ⟨hq, hr, hdec⟩ := thDiv hδ
  set x' := δ / ConjT.th S
  have hx' : x' < upsilon l := hq.trans hx
  obtain ⟨t, htA, htG, hle⟩ := thBlk hl hX hx' (hβ1A x' hx') (IH x' hq hx') _ hr
  rw [← hdec] at hle
  have ht2 : t ≤ Om (1 + 1) := (htG.trans (Lc.lcG_lt_Om2 _)).le
  rw [ldTheta hl hX ht2] at hle
  exact hle.trans_lt (gxTh_lt (GxCl.atom htA) (htG.trans_le (thG_mono (Order.add_one_le_of_lt hq))))

omit hl hX hρA in
/-- `G(x) < P'` for every `x < Ω₁`. -/
theorem thG_lt_Pp {x : Ordinal.{0}} (hx : x < Om 1) : Lc.lcG S x < Nc.ncPp S := by
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hWW : Om ω < Om ω + Om ω := lt_add_of_pos_right _ (Om_pos omega0_ne_zero)
  have hlt : Om ω + Lc.lcTh S 2 * x < Om ω + Om ω := by
    refine (add_lt_add_iff_left _).2 (ldMul_lt_SC (SC_Om omega0_ne_zero) ?_ ?_)
    · exact (psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 (by exact_mod_cast natCast_lt_omega0 3))
    · exact hx.trans (Om_lt_Om.2 one_lt_omega0)
  refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt (Rp.rpThx_mem hWW ?_)
  exact hx.trans (psiS_bounds (S := S) _ 1).1

/-- **`ψ_{Ω₁}(A + θ·ρ_λ) ≤ Θ_λ(P')`.** -/
theorem thRead_Pp :
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S * upsilon l) (Om 1) ≤ cdTheta S l (Nc.ncPp S) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  have hP2 : Nc.ncPp S ≤ Om (1 + 1) := (psiS_bounds (S := S) _ 1).2.le
  rw [ldTheta hl hX hP2]
  have hTSC : SC (gxTh (upsilon l) (ldAtR S l) (Nc.ncPp S)) :=
    gxTh_SC hZ hAt (Nc.ncPp_SC S) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hρT : upsilon l < gxTh (upsilon l) (ldAtR S l) (Nc.ncPp S) := by
    have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om
      (psiS_bounds (S := S) (Om ω + Om ω) 1).1
    rwa [← ldTheta hl hX (Om_le_Om.2 le_self_add), cdTheta_Om1 hpv] at h1
  refine psi_le_of_key hTSC fun e _ he => ?_
  rcases lt_or_ge e (ConjT.Aη S (cdEta S l)) with h1 | h1
  · exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans_eq hρ).trans_lt hρT
  obtain ⟨δ, rfl⟩ := exists_add_of_le h1
  have hδ : δ < ConjT.th S * upsilon l := (add_lt_add_iff_left _).1 he
  obtain ⟨hq, hr, hdec⟩ := thDiv hδ
  set x' := δ / ConjT.th S
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hβ1A : Om ω + Lc.lcTh S 2 * (x' + 1) < ConjT.Aη S (cdEta S l) :=
    lt_of_lt_of_le ((add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hθ2SC.1).2 (hZ.add_one_lt hq))) hρA
  obtain ⟨t, htA, htG, hle⟩ := thBlk hl hX hq hβ1A (thRead hl hX hρA x' hq) _ hr
  rw [← hdec] at hle
  have ht2 : t ≤ Om (1 + 1) := (htG.trans (Lc.lcG_lt_Om2 _)).le
  rw [ldTheta hl hX ht2] at hle
  exact hle.trans_lt (gxTh_lt (GxCl.atom htA)
    (htG.trans (thG_lt_Pp ((hZ.add_one_lt hq).trans hZ1))))

end Read

/-- `Ω_ω + θ₂·x ≤ Ω_ω·2 + P'·ξ` for every countable `x`. -/
theorem thW_le_A {x : Ordinal.{0}} (hx : x < Om 1) (ξ : Ordinal.{0}) :
    Om ω + Lc.lcTh S 2 * x ≤ Om ω + Om ω + Nc.ncPp S * ξ := by
  refine le_trans ?_ le_self_add
  refine (add_le_add_iff_left _).2 (ldMul_lt_SC (SC_Om omega0_ne_zero) ?_ ?_).le
  · exact (psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 (by exact_mod_cast natCast_lt_omega0 3))
  · exact hx.trans (Om_lt_Om.2 one_lt_omega0)

/-- **`ψ_{Ω₁}(Ω_ω·2 + P'·k + θ·L(k)) ≤ Θ_{L(k)}(P') ≤ L(k+1)`** for every `k < ω`. -/
theorem thTheta_Lk_bounds (k : ℕ) :
    S.psi (Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}) + ConjT.th S * Nc.ncL S (k : Ordinal.{0})) (Om 1) ≤
        cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ∧
      cdTheta S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncPp S) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  refine ⟨?_, thTheta_Lk k⟩
  obtain ⟨⟨hl, -, hlt, -⟩, -⟩ := Te.teHi_mem (S := S) k
  have hX : upsilon (Nc.ncL S (k : Ordinal.{0})) < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq]; exact hlt
  have hl0 := Te.teUps_L (S := S) k
  have hη : cdEta S (Nc.ncL S (k : Ordinal.{0})) = Om ω + Nc.ncPp S * (k : Ordinal.{0}) := by
    cases k with
    | zero =>
      have h0 : upsilon (Nc.ncL S (0 : Ordinal.{0})) = Nc.ncL S 0 := by simpa using hl0
      simpa using (cdCode_L0 h0).1
    | succ n => exact cdEta_L n hl0
  have hA : ConjT.Aη S (cdEta S (Nc.ncL S (k : Ordinal.{0}))) =
      Om ω + Om ω + Nc.ncPp S * (k : Ordinal.{0}) := by rw [hη, thA_L]
  have hρ1 : upsilon (Nc.ncL S (k : Ordinal.{0})) < Om 1 := (Le.leRho hl hX).2
  have hρA : Om ω + Lc.lcTh S 2 * upsilon (Nc.ncL S (k : Ordinal.{0})) ≤
      ConjT.Aη S (cdEta S (Nc.ncL S (k : Ordinal.{0}))) := by
    rw [hA]; exact thW_le_A hρ1 _
  have h := thRead_Pp hl hX hρA
  rwa [hA, hl0] at h

/-- **`ψ_{Ω₁}(Ω_ω·2 + P'·ω + θ·L(ω)) ≤ Θ_{L(ω)}(P') ≤ L(ω+1)`.** -/
theorem thTheta_Lw_bounds :
    S.psi (Om ω + Om ω + Nc.ncPp S * ω + ConjT.th S * Nc.ncL S ω) (Om 1) ≤
        cdTheta S (Nc.ncL S ω) (Nc.ncPp S) ∧
      cdTheta S (Nc.ncL S ω) (Nc.ncPp S) ≤ Nc.ncL S (ω + 1) := by
  refine ⟨?_, thTheta_Lw⟩
  obtain ⟨-, hl, -, hlt, -⟩ := Te.teHi_mem (S := S) 0
  have hX : upsilon (Nc.ncL S ω) < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq]; exact hlt
  have hA : ConjT.Aη S (cdEta S (Nc.ncL S ω)) = Om ω + Om ω + Nc.ncPp S * ω := by
    rw [cdEta_Lω Rc.rcUps_Lw, thA_L]
  have hρ1 : upsilon (Nc.ncL S ω) < Om 1 := (Le.leRho hl hX).2
  have hρA : Om ω + Lc.lcTh S 2 * upsilon (Nc.ncL S ω) ≤ ConjT.Aη S (cdEta S (Nc.ncL S ω)) := by
    rw [hA]; exact thW_le_A hρ1 _
  have h := thRead_Pp hl hX hρA
  rwa [hA, Rc.rcUps_Lw] at h

end Googology.Trans.PoR.InaccPsi.R2.Th
