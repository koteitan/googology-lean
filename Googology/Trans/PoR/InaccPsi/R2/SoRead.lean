import Googology.Trans.PoR.InaccPsi.R2.RxTh
import Googology.Trans.PoR.InaccPsi.R2.SlRoad

/-!
# The readings past `ρ_μ`: the block step with a code `z` and a reading `x`, and the supply `SlSupW`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

`θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `G(z) = ψ_{Ω₂}(Ω_ω + θ₂·z)` (`Lc.lcG`), `G' = Ls.lsG S (k+1)`,
`A = A_{η_μ}`, `ρ_μ = υ_μ = ψ_{Ω₁}(A)`, `Θ_μ(m) = otp(Cl(A, ρ_μ) ∩ m)`.

`Rp.RpRead` reads `υ_{μ+x+1} ≤ Θ_μ(G(x+1))` only for `x < ρ_μ`: there the code of the block is `x` itself.
Past `ρ_μ` the reading `x` is not a member of the hull; its code is a different ordinal `z` (for
`x = ρ_μ·j + e` the code `Ω₁·j + e`).  The block step of `Rx.rxBlkTh` never ties the code of the block to
its reading: it needs only that `Ω_ω + θ₂·z` is a member over every `a > Ω_ω`, `b ≥ ρ_μ`, that
`Ω_ω + θ₂·(z+1) < A`, and the reading of the base.

* `soBlk` (**the block step with code `z` and reading `x`**): `ψ_{Ω₁}(A + θ·x) ≤ Θ_μ(G(z))` gives, for every
  `ζ < θ`, an atom `t < G(z+1)` with `ψ_{Ω₁}(A + θ·x + ζ) ≤ Θ_μ(t)`;
* `soStep` (**`ψ_{Ω₁}(A + θ·(x+1)) ≤ Θ_μ(G(z+1))`**), `soUps` (`υ_{μ+x} = ψ_{Ω₁}(A + θ·x)` when every
  `η_μ + y`, `y < x`, is good), `soGood` (`η + y` is good for `y < P(η)^ω`);
* `soRead_gen` (**the reading along any code map `c`**: `c` monotone, `c(x+1) = c(x)+1`, members, `c x < θ_{k+1}`
  give `υ_{μ+x} ≤ Θ_μ(G(c x))` for every `x < X`), `soSup_gen` (`υ_{μ+X} ≤ r(μ)` at a limit `X`);
* `soSupW` (**`Sl.SlSupW S k` for every `k`, unconditionally**: the code map `x ↦ Ω₁·(x/ρ_μ) + x mod ρ_μ`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

theorem soRho_lt_Om1 {μ : Ordinal.{0}} (hR : CdRange S μ) : upsilon μ < Om 1 := by
  rw [← Ls.lsPv_range hR]; exact Nm.Pv_lt_Om1 S _

/-- **The block step with code `z` and reading `x`.** -/
theorem soBlk {μ x z : Ordinal.{0}} (hR : CdRange S μ)
    (hzA : Om ω + Lc.lcTh S 2 * (z + 1) < ConjT.Aη S (cdEta S μ))
    (hmem : ∀ a b, Om ω < a → upsilon μ ≤ b → Om ω + Lc.lcTh S 2 * z ∈ S.CSet a b)
    (hP : S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) (Om 1) ≤ cdTheta S μ (Lc.lcG S z)) :
    ∀ ζ, ζ < ConjT.th S → ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (z + 1) ∧
      S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  have hAt : GxAt (ldAtR S μ) := ldAt_GxAt _ _
  have hρ1 := soRho_lt_Om1 hR
  have hρb : ∀ e, upsilon μ ≤ S.psi e (Om (1 + 1)) := fun e => (hρ1.trans (psiS_bounds (S := S) e 1).1).le
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hθSC := ConjT.SC_th S
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set β := Om ω + Lc.lcTh S 2 * z with hβdef
  set Â := A + ConjT.th S * x with hÂdef
  set Z2 := gxTh (upsilon μ) (ldAtR S μ) (Om (1 + 1)) with hZ2def
  set W := rxW (upsilon μ) (ldAtR S μ) with hWdef
  set κ := rxL S (upsilon μ) (ldAtR S μ) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hTh : ∀ m, m ≤ Om (1 + 1) → cdTheta S μ m = gxTh (upsilon μ) (ldAtR S μ) m :=
    fun m hm => ldTheta hR.1 hX hm
  have hβA : β < A :=
    lt_of_le_of_lt ((add_le_add_iff_left _).2 (mul_le_mul_of_nonneg_left le_self_add zero_le)) hzA
  have hWβ : Om ω ≤ β := le_self_add
  have hWA : Om ω ≤ A := hWβ.trans hβA.le
  have hβH : β ∈ cdHull S μ := hmem _ _ (hWβ.trans_lt hβA) le_rfl
  have hθW : ConjT.th S < Om ω := (psi_lt (InR_Om_succ 1) _).trans (Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ cdHull S μ :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hR.1 hX hlt2).2 hcode) ζ hζ
  have hκ2 : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → κ ζ < Lc.lcTh S 2 := fun ζ hζ hζθ => by
    rw [rxTh2_eq]; exact rxL_lt_th2 hZ hZ1 hAt ζ hζ hζθ
  have hκθ : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → β + κ ζ < Om ω + Lc.lcTh S 2 * (z + 1) :=
    fun ζ hζ hζθ => by
      rw [mul_add_one, ← add_assoc]
      exact (add_lt_add_iff_left _).2 (hκ2 ζ hζ hζθ)
  have hat : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S μ :=
    fun ζ hζ hζθ => ⟨_, CSet.add_mem hβH (hκH ζ hζ), (hκθ ζ hζ hζθ).trans hzA, rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S μ := ⟨β, hβH, hβA, rfl⟩
  have hbase : S.psi Â (Om 1) ≤ gxTh (upsilon μ) (ldAtR S μ) (S.psi β (Om (1 + 1))) := by
    rw [← hTh _ (psi_lt (InR_Om_succ 1) _).le]; exact hP
  have hβmem : ∀ ζ, RxE S W ζ → ζ ≠ 0 → β ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) :=
    fun ζ hζ h0 => hmem _ _ (hWβ.trans_lt (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0))) (hρb _)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt hζ h0))
      (hβmem ζ hζ h0)
  have hcl : ∀ ζ, RxE S W ζ ∧ ζ < ConjT.th S →
      gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (Â + ζ) (gxTh (upsilon μ) (ldAtR S μ) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → (RxE S W (e - Â) ∧ e - Â < ConjT.th S) ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζ hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon μ) (ldAtR S μ) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ Z2 := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - Â < ζ := Ry.rySub_lt h1 h2
    have hltθ : e - Â < ConjT.th S := hlt.trans hζ.2
    have hm : e % ConjT.th S = e - Â := by
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC Â hltθ, Ordinal.mod_eq_zero_of_dvd (rxDvdTh (cdEta S μ) x), zero_add]
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
  have hG1 : Lc.lcG S (z + 1) = S.psi (Om ω + Lc.lcTh S 2 * (z + 1)) (Om (1 + 1)) := rfl
  have htlt : t < Lc.lcG S (z + 1) := by
    rw [hG1]
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (hκθ w hwD hwθ) (CSet.add_mem ?_ ?_)
    · refine hmem _ _ ?_ (hρb _)
      exact lt_add_of_pos_right _ (mul_pos hθ2SC.1 (lt_of_le_of_lt zero_le (lt_add_one z)))
    · set T1 := gxTh (upsilon μ) (ldAtR S μ) (Lc.lcG S (z + 1)) with hT1def
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
  refine ⟨t, ?_, htlt, ?_⟩
  · rw [Le.leAt_eq]; exact hat w hwD hwθ
  · rw [hTh t (psi_lt (InR_Om_succ 1) _).le, ← add_assoc]
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hn)).1.trans
      (hLift w ⟨hwD, hwθ⟩)

/-- **One step**: `ψ_{Ω₁}(A + θ·x) ≤ Θ_μ(G(z))` gives `ψ_{Ω₁}(A + θ·(x+1)) ≤ Θ_μ(G(z+1))`. -/
theorem soStep {μ x z : Ordinal.{0}} (hR : CdRange S μ) (hd : ω ^ Om 1 ∣ cdEta S μ) (hx1 : x + 1 < Om 1)
    (hzA : Om ω + Lc.lcTh S 2 * (z + 1) < ConjT.Aη S (cdEta S μ))
    (hmem : ∀ a b, Om ω < a → upsilon μ ≤ b → Om ω + Lc.lcTh S 2 * z ∈ S.CSet a b)
    (hP : S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) (Om 1) ≤ cdTheta S μ (Lc.lcG S z)) :
    S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * (x + 1)) (Om 1) ≤ cdTheta S μ (Lc.lcG S (z + 1)) := by
  have hB := soBlk hR hzA hmem hP
  have hρ1 := soRho_lt_Om1 hR
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hβA : Om ω + Lc.lcTh S 2 * z < ConjT.Aη S (cdEta S μ) :=
    lt_of_le_of_lt ((add_le_add_iff_left _).2 (mul_le_mul_of_nonneg_left le_self_add zero_le)) hzA
  refine Rg.rgPsi_le_cover (Ls.lsPv_range hR) (SC_psi (InR_Om_succ 1) _) (psiS_bounds (S := S) _ 1).1
    (psi_lt (InR_Om_succ 1) _).le (Rg.rgDvd_A hd) (Rg.rgD_le hx1) ?_
  intro ζ _ hζ
  right
  rcases lt_or_ge ζ (ConjT.th S * x) with hlo | hhi
  · have hlt : Om ω + Lc.lcTh S 2 * z < Om ω + Lc.lcTh S 2 * (z + 1) :=
      (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hθ2SC.1).2 (lt_add_one z))
    refine ⟨Lc.lcG S z, ⟨_, hβA, hmem _ _ (le_self_add.trans_lt hβA) le_rfl, rfl⟩, ?_, ?_⟩
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt
        (hmem _ _ (le_self_add.trans_lt hlt) (hρ1.trans (psiS_bounds (S := S) _ 1).1).le)
    · exact (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hlo.le)).1.trans hP
  · obtain ⟨ζ', rfl⟩ := exists_add_of_le hhi
    have hζ' : ζ' < ConjT.th S := by
      rw [mul_add_one] at hζ; exact (add_lt_add_iff_left _).1 hζ
    exact hB ζ' hζ'

/-- `υ_{μ+x} = ψ_{Ω₁}(A_{η_μ} + θ·x)` when every `η_μ + y`, `y < x`, is good. -/
theorem soUps {μ x : Ordinal.{0}} (hR : CdRange S μ) (hg : ∀ y < x, Bt.Good S (cdEta S μ + y)) :
    upsilon (μ + x) = S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) (Om 1) := by
  obtain ⟨-, hιμ, -⟩ := Ra.raName hR
  have hsh : Bt.iota S (cdEta S μ + x) = μ + x := by rw [Pp.ppIota_add _ _ hg, hιμ]
  rw [← hsh, Bt.ups_iota]
  show S.psi (ConjT.Aη S (cdEta S μ + x)) (Om 1) = _
  rw [Ra.raA_add]

/-- `x^y < e` for `x, y < e`, `e` an `ε`-number. -/
theorem soE_opow_lt {e x y : Ordinal.{0}} (he : InE e) (hx : x < e) (hy : y < e) : x ^ y < e := by
  have h1 : x ^ y ≤ (ω ^ x) ^ y := opow_le_opow_left y (right_le_opow x one_lt_omega0)
  rw [← opow_mul] at h1
  have h2 : ω ^ (x * y) < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 (Sl.slE_mul_lt he hx hy)
  have h3 : ω ^ e = e := he
  exact h1.trans_lt (h2.trans_eq h3)

/-- `η + y` is good for every `y < P(η)^ω`. -/
theorem soGood {η y : Ordinal.{0}} (hg : Bt.Good S η) (hy : y < Nm.Pv S η ^ ω) : Bt.Good S (η + y) := by
  refine Rz.rz_good_shift hg ?_
  by_cases hyP : y < Nm.Pv S η
  · exact hyP.trans_le (Nm.Pv_mono le_self_add)
  · have h1 : 1 ≤ y := Order.one_le_iff_ne_zero.2 fun h0 => by
      rw [h0] at hyP; exact hyP (Sl.slPv_E (S := S) η).pos
    have hE := Sl.slPv_E (S := S) (η + 1)
    exact (hy.trans (soE_opow_lt hE (Nm.Pv_lt_succ hg) (Sl.slE_omega_lt hE))).trans_le
      (Nm.Pv_mono (add_le_add le_rfl h1))

/-- `P(η)^ω < Ω₁` for a good `η`. -/
theorem soPvOpow_lt_Om1 (η : Ordinal.{0}) (hg : Bt.Good S η) : Nm.Pv S η ^ ω < Om 1 := by
  have hE := Sl.slPv_E (S := S) (η + 1)
  exact (soE_opow_lt hE (Nm.Pv_lt_succ hg) (Sl.slE_omega_lt hE)).trans (Nm.Pv_lt_Om1 S _)

/-- `Ω_ω + θ₂·(z+1) < A_{η_μ}` for a member `z < θ_{k+1}` at a Range restart with code `G' + 1`. -/
theorem soA_lt {μ z : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hmem : ∀ a b, Om ω < a → upsilon μ ≤ b → Om ω + Lc.lcTh S 2 * z ∈ S.CSet a b)
    (hz : z < Lc.lcTh S (k + 1)) :
    Om ω + Lc.lcTh S 2 * (z + 1) < ConjT.Aη S (cdEta S μ) := by
  obtain ⟨e, heA, -, hGe⟩ := Rp.rpG'_atom hR hc
  have hθ2SC : SC (Lc.lcTh S 2) := Ls.lsTh_SC 2
  have hz1 : z + 1 < Lc.lcTh S (k + 1) * ω ^ 2 :=
    ((Ls.lsTh_SC (k + 1)).add_one_lt hz).trans_le (Ordinal.le_mul_left _ (pow_pos omega0_pos 2))
  have hlt : Om ω + Lc.lcTh S 2 * (z + 1) < Om ω + Lc.lcTh S 2 * (Lc.lcTh S (k + 1) * ω ^ 2) :=
    (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hθ2SC.1).2 hz1)
  have hG : Lc.lcG S (z + 1) < Ls.lsG S (k + 1) := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt ?_
    rw [mul_add_one, ← add_assoc]
    have ha : Om ω < Om ω + Lc.lcTh S 2 * (Lc.lcTh S (k + 1) * ω ^ 2) := lt_of_le_of_lt le_self_add hlt
    exact CSet.add_mem (hmem _ _ ha ((soRho_lt_Om1 hR).trans (psiS_bounds (S := S) _ 1).1).le)
      (Ls.lsTh_mem ha 2)
  have hlt' : Om ω + Lc.lcTh S 2 * (z + 1) < e := by
    by_contra hle
    push Not at hle
    have h1 : S.psi e (Om (1 + 1)) ≤ Lc.lcG S (z + 1) := (psi_mono (S := S) (InR_Om_succ 1) hle).1
    rw [← hGe] at h1
    exact absurd (h1.trans_lt hG) (lt_irrefl _)
  exact hlt'.trans heA

/-- **The reading along a code map `c`.** -/
theorem soRead_gen {μ X : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hgood : ∀ y < X, Bt.Good S (cdEta S μ + y)) (hX1 : X ≤ Om 1) (c : Ordinal.{0} → Ordinal.{0})
    (hsucc : ∀ x, x + 1 < X → c (x + 1) = c x + 1)
    (hmono : ∀ y x, y ≤ x → x < X → c y ≤ c x)
    (hmem : ∀ x < X, ∀ a b, Om ω < a → upsilon μ ≤ b → Om ω + Lc.lcTh S 2 * c x ∈ S.CSet a b)
    (hlt : ∀ x < X, c x < Lc.lcTh S (k + 1)) :
    ∀ x < X, upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S (c x)) := by
  have hpv := Ls.lsPv_range hR
  have hd := Ls.lsDiv_of_code hc
  have hbase : ∀ x, upsilon μ ≤ cdTheta S μ (Lc.lcG S x) := fun x => by
    rw [← cdTheta_Om1 hpv]; exact cdTheta_mono S μ (psiS_bounds (S := S) _ 1).1.le
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases zero_or_succ_or_isSuccLimit x with rfl | ⟨y, rfl⟩ | hlim
  · rw [add_zero]; exact hbase _
  · rw [Order.succ_eq_add_one] at hx ⊢
    have hy : y < X := (lt_add_one y).trans hx
    have IHy := IH y (lt_add_one y) hy
    rw [soUps hR fun y' hy' => hgood y' (hy'.trans hy)] at IHy
    rw [soUps hR fun y' hy' => hgood y' (hy'.trans hx), hsucc y hx]
    have hx1 : y + 1 < Om 1 := hx.trans_le hX1
    exact soStep hR hd hx1 (soA_lt hR hc (hmem y hy) (hlt y hy)) (hmem y hy) IHy
  · refine (upsilon_normal.le_iff_forall_le (isSuccLimit_add μ hlim)).2 fun a ha => ?_
    rcases lt_or_ge a μ with haμ | haμ
    · exact (upsilon_normal.strictMono haμ).le.trans (hbase _)
    · obtain ⟨z, rfl⟩ := exists_add_of_le haμ
      have hz : z < x := (add_lt_add_iff_left μ).1 ha
      exact (IH z hz (hz.trans hx)).trans (cdTheta_mono S μ (Rp.rpG_mono (hmono z x hz.le hx)))

/-- **The supply from a code map**: at a limit `X`, `υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)`. -/
theorem soSup_gen {μ X : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hXl : IsSuccLimit X)
    (hgood : ∀ y < X, Bt.Good S (cdEta S μ + y)) (hX1 : X ≤ Om 1) (c : Ordinal.{0} → Ordinal.{0})
    (hsucc : ∀ x, x + 1 < X → c (x + 1) = c x + 1)
    (hmono : ∀ y x, y ≤ x → x < X → c y ≤ c x)
    (hmem : ∀ x < X, ∀ a b, Om ω < a → upsilon μ ≤ b → Om ω + Lc.lcTh S 2 * c x ∈ S.CSet a b)
    (hlt : ∀ x < X, c x < Lc.lcTh S (k + 1)) :
    upsilon (μ + X) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧ upsilon (μ + X) ≤ cdR S μ := by
  have hP := soRead_gen hR hc hgood hX1 c hsucc hmono hmem hlt
  have hpv := Ls.lsPv_range hR
  have hbase : upsilon μ ≤ cdTheta S μ (Ls.lsG S (k + 1)) := by
    rw [← cdTheta_Om1 hpv]; exact cdTheta_mono S μ (psiS_bounds (S := S) _ 1).1.le
  have hG : ∀ x < X, Lc.lcG S (c x) ≤ Ls.lsG S (k + 1) := fun x hx =>
    Rp.rpG_mono ((hlt x hx).le.trans (Ordinal.le_mul_left _ (pow_pos omega0_pos 2)))
  have h1 : upsilon (μ + X) ≤ cdTheta S μ (Ls.lsG S (k + 1)) := by
    refine (upsilon_normal.le_iff_forall_le (isSuccLimit_add μ hXl)).2 fun a ha => ?_
    rcases lt_or_ge a μ with haμ | haμ
    · exact (upsilon_normal.strictMono haμ).le.trans hbase
    · obtain ⟨z, rfl⟩ := exists_add_of_le haμ
      have hz : z < X := (add_lt_add_iff_left μ).1 ha
      exact (hP z hz).trans (cdTheta_mono S μ (hG z hz))
  refine ⟨h1, h1.trans ?_⟩
  refine (cdTheta_mono S μ (le_self_add : Ls.lsG S (k + 1) ≤ Ls.lsG S (k + 1) + 1)).trans ?_
  rw [← hc]
  exact le_add_self.trans (Ra.raR_ge_add S μ)

/-! ## The linear code map and `SlSupW` -/

/-- `Ω₁·ω < θ_{k+1}`. -/
theorem soOm1W_lt_th (k : ℕ) : Om 1 * ω < Lc.lcTh S (k + 1) := by
  have hSC := Ls.lsTh_SC (S := S) (k + 1)
  have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC hSC
  exact Sl.slE_mul_omega_lt hE (Rp.rpOm1_lt_th k)

/-- `θ₂·ω^e·q` is a member over `a > Ω_ω` when `e` is a member and `q < b`. -/
theorem soMemTerm {a b e q : Ordinal.{0}} (ha : Om ω < a) (he : e ∈ S.CSet a b) (hq : q < b) :
    Lc.lcTh S 2 * (ω ^ e * q) ∈ S.CSet a b := by
  have h := Nm.mem_opow_mul (S := S) (CSet.add_mem (Ls.lsTh_mem ha 2) he) hq
  rwa [opow_add, Ls.lsTh_opow, mul_assoc] at h

/-- `Ω₁ = ω^{Ω₁}`. -/
theorem soOm1_opow : ω ^ Om (1 : Ordinal.{0}) = Om 1 :=
  Low.opow_eq_self_of_SC (SC_Om one_ne_zero)

/-- **The linear code map is a member**: `Ω_ω + θ₂·(Ω₁·j + e)` for `j < ω`, `e < b`. -/
theorem soLinMem {a b j e : Ordinal.{0}} (ha : Om ω < a) (hj : j < ω) (hb : ω ≤ b) (he : e < b) :
    Om ω + Lc.lcTh S 2 * (Om 1 * j + e) ∈ S.CSet a b := by
  rw [mul_add]
  refine CSet.add_mem (ConjT.OmW_mem S a b) (CSet.add_mem ?_ ?_)
  · have h := soMemTerm (S := S) ha (CSet.Om_mem (CSet.one_mem a b)) (hj.trans_le hb)
    rwa [soOm1_opow] at h
  · have h := soMemTerm (S := S) ha (CSet.zero_mem a b) he
    rwa [opow_zero, one_mul] at h

/-- **`Sl.SlSupW S k` for every `k`**: `υ_{μ+ρ_μ·ω} ≤ r(μ)` at every Range restart with code `G_{k+1}+1`. -/
theorem soSupW (k : ℕ) : Sl.SlSupW S k := by
  intro μ hR hc
  obtain ⟨hgμ, -, hpv⟩ := Ra.raName hR
  set ρ := upsilon μ with hρdef
  have hρE : InE ρ := by rw [← hpv]; exact Sl.slPv_E _
  have hρ0 : ρ ≠ 0 := hρE.pos.ne'
  have hρω : ω ≤ ρ := (Sl.slE_omega_lt hρE).le
  have hlim : IsSuccLimit (ρ * ω) := isSuccLimit_mul_right hρE.pos isSuccLimit_omega0
  have hρlim : ∀ r, r < ρ → r + 1 < ρ := fun r hr =>
    hρE.add_lt hr (lt_of_lt_of_le one_lt_omega0 hρω)
  set c : Ordinal.{0} → Ordinal.{0} := Sl.slLin (Om 1) ρ with hcdef
  have hdec : ∀ x, x < ρ * ω → (x / ρ < ω ∧ x % ρ < ρ) := fun x hx =>
    ⟨(Ordinal.lt_mul_iff_div_lt hρ0).1 hx, Ordinal.mod_lt x hρ0⟩
  refine (soSup_gen hR hc hlim (fun y hy => Sl.slGood hgμ (by rw [hpv]; exact hy))
    (by rw [← hpv]; exact (Sl.slPvW_lt_Om1 _ hgμ).le) c ?_ ?_ ?_ ?_).2
  · intro x _
    have hm := Ordinal.mod_lt x hρ0
    have h1 : x + 1 = ρ * (x / ρ) + (x % ρ + 1) := by rw [← add_assoc, Ordinal.div_add_mod]
    have hm1 := hρlim _ hm
    simp only [hcdef, Sl.slLin]
    rw [h1, Ordinal.mul_add_div _ hρ0, Ordinal.div_eq_zero_of_lt hm1, add_zero,
      Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hm1, add_assoc]
  · intro y x hyx _
    rcases hyx.lt_or_eq with h | h
    · exact (Sl.slLin_lt hρ0 h ((Ordinal.mod_lt y hρ0).trans (soRho_lt_Om1 hR))).le
    · rw [h]
  · intro x hx a b ha hb
    obtain ⟨h1, h2⟩ := hdec x hx
    exact soLinMem ha h1 (hρω.trans hb) (h2.trans_le hb)
  · intro x hx
    obtain ⟨h1, h2⟩ := hdec x hx
    refine lt_of_lt_of_le ?_ (soOm1W_lt_th (S := S) k).le
    show Om 1 * (x / ρ) + x % ρ < Om 1 * ω
    obtain ⟨n, hn⟩ := lt_omega0.1 h1
    rw [hn]
    calc Om 1 * (n : Ordinal.{0}) + x % ρ < Om 1 * (n : Ordinal.{0}) + Om 1 :=
          (add_lt_add_iff_left _).2 (h2.trans (soRho_lt_Om1 hR))
      _ = Om 1 * ((n + 1 : ℕ) : Ordinal.{0}) := by push_cast; rw [mul_add_one]
      _ < Om 1 * ω := (mul_lt_mul_iff_right₀ (SC_Om one_ne_zero).1).2 (natCast_lt_omega0 _)

end Googology.Trans.PoR.InaccPsi.R2.So
