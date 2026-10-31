import Googology.Trans.PoR.InaccPsi.R2.WzLift
import Googology.Trans.PoR.InaccPsi.R2.VhAdd

/-!
# The candidate law at `k = 0`, `β = Ω₃`: the lower half `ψ_{Ω₁}(A + X̂) ≤ Θ(ψ_{Ω₂}(Ω₃·2))`

`Θ = gxTh ρ_λ (ldAtR λ)`, `κ = rxL` (the level shift of `Rx`), `W = rxW ρ_λ At_λ`, `A = A_{η_λ}`,
`X̂ = ψ_{Ω₂}(Ω₂ + Ω₂) = Wv.wvX0 S λ 0 Ω₃` (the candidate image `ψ₂(T Ω₃ + Ω₂)`), `Y₂ = ψ_{Ω₂}(Ω₂)`,
`z_{n+1} = ψ_{Ω₂}(Ω₂ + z_n)` (`Wz.wzZ`).

The lift of `Rx.rxBlkTh` at the base `Ω₃` (`Wl.wlBlk0` takes the bases `Ω_{k+2}` and the offsets `ζ < ψ₂(Ω_{k+1})`):
for an offset `ζ < X̂` the members `e − A` of the `ψ₁`-hull below `A + ζ` lie in `Cl(Ω₂ + ζ, ψ₂(Ω₂ + ζ))`
(`ζ < ψ₂(Ω₂ + ζ)`, `Wz.wzLtPsi`), so `κ(e − A) ∈ Cl(Ω₃ + κ ζ, ·)` by `Wz.wzL_memL` with `L = Ω₂ + ζ`,
`κ L = Ω₃ + κ ζ` (`Vh.vhK_add`).

* `wzLift` (**`ψ₁(A + ζ) ≤ Θ(ψ₂(Ω₃ + κ ζ))` for every member `ζ < X̂`**);
* `wzLowAll` (**`ψ₁(A + ζ) < Θ(ψ₂(Ω₃·2))` for every `ζ < X̂`**), `wzLow` (**`ψ₁(A + X̂) ≤ Θ(ψ₂(Ω₃·2))`**);
* `wzBase` (`Θ(ψ₂(Ω₃)) = ψ₁(A + 1 + Y₂)`), `wzHat_eq` (the own base image at `Ω₃` is `A + 1 + Y₂`),
  `wzX0_Om3` (`X̂⁰_0(Ω₃) = ψ₂(Ω₂ + Ω₂)`);
* `wzLawLow` (**the lower half of `skX0Law` at `k = 0`, `β = Ω₃`**), `wzLaw_iff` (**the law there ⇔ its upper half
  `Θ(ψ₂(Ω₃·2)) ≤ ψ₁(A + X̂)`**);
* `wzImg0_ge` (every image `Z` of the law at `Ω₃` over the base `Ω₃` has `X̂ ≤ Ω^Z`), `wzImg1_gt` (every image `Z`
  of the law at `Ω₄` over the base `0` has `X̂ < Ω^Z`; sharpens `Wv.wvImg1_gt`, `Y₂ + Y₂ < X̂`), `wzWit`
  (non-vacuity at the restart of `m* = L(0)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

theorem wzTwo : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num [one_add_one_eq_two]

theorem wzX_SC : SC (S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _

theorem wzY2_lt_X : S.psi (Om (1 + 1)) (Om (1 + 1)) < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ ldOm2_SC.1) (mxOm2_mem _ _)

/-- `1 + (Y₂ + X̂) = X̂`. -/
theorem wzAbs : 1 + (S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) =
    S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) := by
  have hε := gg_SC_eps (wzX_SC (S := S))
  have hω : ω ≤ S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) := (Lw.lw_omega_lt_SC (wzX_SC (S := S))).le
  have e1 : S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) =
      S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
    Ordinal.add_of_omega0_opow_le (by rw [hε]; exact wzY2_lt_X (S := S)) hε.le
  rw [e1, one_add_of_omega0_le hω]

/-- `T_{Ω₃}(Ω₃) = ψ₂(Ω₃ + Ω₃)`. -/
theorem wzTe : leTe S (Om (1 + 1 + 1) + 0) (Om (1 + 1 + 1)) = S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1)) := by
  unfold leTe; rw [add_zero, Vn.vnWe_Om3]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LIFT AT THE BASE `Ω₃`**: `ψ₁(A + ζ) ≤ Θ(ψ₂(Ω₃ + κ ζ))` for every member `ζ < ψ₂(Ω₂ + Ω₂)`. -/
theorem wzLift {ζ : Ordinal.{0}} (hζ : RxE S (rxW (upsilon l) (ldAtR S l)) ζ)
    (hζX : ζ < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) :
    S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l)
        (S.psi (Om (1 + 1 + 1) + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hpv : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := cdEta_pv hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  set Xh := S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) with hXh
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hθSC := ConjT.SC_th S
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hθW : ConjT.th S < Om ω := hθ2.trans vkOmW.2
  have hWA : Om ω ≤ A := le_self_add
  have hdvd : ConjT.th S ∣ A := by
    have := rxDvdTh (S := S) (cdEta S l) 0; rwa [mul_zero, add_zero] at this
  have hXθ : Xh < ConjT.th S := wzX_lt_th
  have hX2 : Xh < Om (1 + 1) := psi_lt hκ2 _
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ S.CSet A (upsilon l) :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hl hX hlt2).2 hcode) ζ hζ
  have hκ3 : ∀ ζ, RxE S W ζ → ζ < Om (1 + 1) → κ ζ < Om (1 + 1 + 1) := fun ζ hζ h2 => by
    have h := rxL_lt_lev hZ hZ1 hAt ζ hζ 1 (by rw [Nat.cast_one]; exact h2)
    rwa [Nat.cast_one] at h
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Ry.ryOm3_lt
  have hβκ : ∀ ζ, RxE S W ζ → ζ < Om (1 + 1) → Om (1 + 1 + 1) + κ ζ < Om ω :=
    fun ζ hζ h2 => vkOmW.1.isPrincipal h3W ((hκ3 ζ hζ h2).trans h3W)
  have hat : ∀ ζ, RxE S W ζ → ζ < Om (1 + 1) →
      S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ h2 => ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (hκH ζ hζ), (hβκ ζ hζ h2).trans_le hWA, rfl⟩
  have hβat : S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, Ry.ryOm3_mem _ _, h3W.trans_le hWA, rfl⟩
  have hbase : S.psi A (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) := by
    rw [hpv]
    exact (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) _ 1).1.le)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 →
      S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) < S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ (rxL_pos hZ hZ1 hAt hζ h0)) (Ry.ryOm3_mem _ _)
  -- `Ω₂` in the domain, `κ Ω₂ = Ω₃`
  have hO : RxE S W (Om (1 + 1 : Ordinal.{0})) := by
    have h := Wk.wkOm_E (S := S) (T := W) 2; rwa [wzTwo] at h
  have hKO : κ (Om (1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1) := by
    have h := rxL_Om (S := S) (Z := upsilon l) (At := ldAtR S l) (T := W) (k := 2) (by norm_num)
    rwa [wzTwo] at h
  set D : Set Ordinal.{0} := {ζ | RxE S W ζ ∧ ζ < Xh} with hDdef
  have hcl : ∀ ζ ∈ D, gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1))) < Om 1 →
      ∀ e, HCl S (A + ζ) (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1)))) e →
      A ≤ e → e < A + ζ → e - A ∈ D ∧
        Om (1 + 1 + 1) + κ (e - A) ∈
          S.CSet (Om (1 + 1 + 1) + κ ζ) (S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1))) := by
    intro ζ hζD hcnt e he h1 h2
    set t := S.psi (Om (1 + 1 + 1) + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon l) (ldAtR S l) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_mono (psi_lt hκ2 _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have hlt : e - A < ζ := Ry.rySub_lt h1 h2
    have hltX : e - A < Xh := hlt.trans hζD.2
    have hltθ : e - A < ConjT.th S := hltX.trans hXθ
    have hm : e % ConjT.th S = e - A := by
      have e1 : e = A + (e - A) := (Ordinal.add_sub_cancel_of_le h1).symm
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC A hltθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hN : RxN S Tt (e - A) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - A) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltX⟩, CSet.add_mem (Ry.ryOm3_mem _ _) ?_⟩
    have hLE : RxE S W (Om (1 + 1) + ζ) := Vh.vhE_add hO hζD.1
    have hKL : κ (Om (1 + 1) + ζ) = Om (1 + 1 + 1) + κ ζ := by
      have h : κ (Om (1 + 1) + ζ) = κ (Om (1 + 1)) + κ ζ := Vh.vhK_add hl hX (Om (1 + 1)) hO ζ hζD.1
      rw [hKO] at h; exact h
    exact wzL_memL hZ hZ1 hAt htSC hTW hLE hKL.le (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET
      ⟨Om (1 + 1) + ζ, le_rfl, CSet.of_lt (hlt.trans (wzLtPsi hζD.2))⟩
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := D)
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h)
    (fun ζ hζ => hat ζ hζ.1 (hζ.2.trans hX2)) (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  exact hLift ζ ⟨hζ, hζX⟩

/-- **`ψ₁(A + ζ) < Θ(ψ₂(Ω₃ + Ω₃))` for every `ζ < X̂`.** -/
theorem wzLowAll {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {ζ : Ordinal.{0}} (hζX : ζ < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) :
    S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) <
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hown, -⟩ := Wg.wgOwnEta hl hX hA hρ
  clear hA hρ
  set A := ConjT.Aη S (cdEta S l) with hAdef
  obtain ⟨n, hn⟩ := (lt_ciSup_iff (wzZ_bdd (S := S))).1 (hζX.trans_le wzX_le_sup)
  have h1 := wzLift hl hX (wzZ_E (n + 1)) (wzZ_lt_X (n + 1))
  have hκz : rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (wzZ S (n + 1)) < Om (1 + 1 + 1) := by
    have h := rxL_lt_lev hZ hZ1 hAt (wzZ S (n + 1)) (wzZ_E (n + 1)) 1 (by rw [Nat.cast_one]; exact wzZ_lt_Om2 _)
    rwa [Nat.cast_one] at h
  have h2 := gxTh_mono (Z := upsilon l) (At := ldAtR S l) (psi_mono hκ2 (add_le_add (le_refl (Om (1 + 1 + 1 : Ordinal.{0}))) hκz.le)).1
  have hAz : Om (1 + 1) + Om (1 + 1) ≤ A + wzZ S (n + 1) :=
    (vkOmW.1.isPrincipal vkOmW.2 vkOmW.2).le.trans ((ConjT.OmW_le_A S _).trans le_self_add)
  have h3 : S.psi (A + wzZ S n) (Om 1) < S.psi (A + wzZ S (n + 1)) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 (wzZ_lt n))
      (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (wzZ_mem hAz n))
  exact ((psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hn.le)).1.trans_lt h3).trans_le (h1.trans h2)


/-- **THE LOWER HALF**: `ψ₁(A + X̂) ≤ Θ(ψ₂(Ω₃ + Ω₃))` (continuity of `ψ₁` at the limit `A + X̂`). -/
theorem wzLow {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    S.psi (ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  set B := ConjT.Aη S (cdEta S l) with hB
  set Xh := S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) with hXh
  have hlim : IsSuccLimit (B + Xh) := isSuccLimit_add _ (wzX_SC (S := S)).isSuccLimit
  rw [Lw.lw_psi_limit S Low.InR_Om_one hlim]
  refine ciSup_le' fun e => ?_
  rcases lt_or_ge e.1 B with h1 | h1
  · have h0 := wzLowAll hl hX hA hρ (ζ := 0) (wzX_SC (S := S)).1
    rw [add_zero] at h0
    exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans_lt h0).le
  · have e1 : e.1 = B + (e.1 - B) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e.1 - B < Xh := by
      have h2 := e.2
      change e.1 < B + Xh at h2
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact (wzLowAll hl hX hA hρ hlt).le

/-- `Θ(ψ₂(Ω₃)) = ψ₁(A + 1 + Y₂)` (`Wg.wgTop0_base0`). -/
theorem wzBase {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have h := Wg.wgTop0_base0 hl hX hA hρ (A + 1) (Vx.vxHatA1 hA) (ldBlk_zero hA hρ)
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  simp only [gxTh_zero, add_zero] at h
  rw [Ua.uaOe_fix (gg_SC_eps hY2SC) (psiS_bounds (S := S) _ 1).1] at h
  unfold leTe at h
  rwa [zero_add, Vn.vnWe_Om3] at h

/-- `A + 1 + Y₂` is own. -/
theorem wzOwnY {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) ∈ S.CSet (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)))
      (S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1)) := by
  have hle : A ≤ A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    (vkOmW.2.trans_le (Vn.vnA_ge hl hX hA hρ)).trans_le hle
  exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hle).2 hA) (CSet.one_mem _ _))
    (Vq.vqY2_mem hΩ2)

/-- **The own base image at `Ω₃` is `A + 1 + Y₂`.** -/
theorem wzHat_eq {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Â : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) = S.psi Â (Om 1)) :
    Â = A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have hown := wzOwnY hl hX hA hρ
  have e := wzBase hl hX hA hρ
  exact le_antisymm (Sf.sfArg_le hÂ hown (by rw [← hb, e])) (Sf.sfArg_le hown hÂ (by rw [← hb, e]))

/-- `X̂⁰_0(Ω₃) = ψ₂(Ω₂ + Ω₂)`. -/
theorem wzX0_Om3 : Wv.wvX0 S l 0 (Om (1 + 1 + 1)) = S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) := by
  unfold Wv.wvX0
  have hO := Vb.vbT_Om (S := S) hl hX (k := 2) (by norm_num)
  rw [wzTwo] at hO
  rw [hO, Nat.cast_zero, zero_add]

/-- The right-hand side of the law at `k = 0`, `β = Ω₃`, at every own base image `Â`, is `ψ₁(A + X̂)`. -/
theorem wzRHS {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Â : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) = S.psi Â (Om 1)) :
    S.psi (Â + leOe (Wv.wvX0 S l 0 (Om (1 + 1 + 1)) + gxTh (upsilon l) (ldAtR S l) 0)) (Om 1) =
      S.psi (ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  have eÂ := wzHat_eq hl hX hA hρ hÂ hb
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  rw [eÂ, wzX0_Om3 hl hX, gxTh_zero, add_zero,
    Ua.uaOe_fix (gg_SC_eps (wzX_SC (S := S))) (psiS_bounds (S := S) _ 1).1, add_assoc, add_assoc, wzAbs]

/-- **THE LOWER HALF OF THE CANDIDATE LAW AT `k = 0`, `β = Ω₃`**: for every own `Â` with `Θ(ψ₂(Ω₃)) = ψ₁(Â)`,
`ψ₁(Â + Ω^{X̂⁰_0(Ω₃) + Θ 0}) ≤ Θ(T_{Ω₃}(Ω₃))`. -/
theorem wzLawLow {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ Â, Â ∈ S.CSet Â (S.psi Â (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) = S.psi Â (Om 1) →
      S.psi (Â + leOe (Wv.wvX0 S l 0 (Om (1 + 1 + 1)) + gxTh (upsilon l) (ldAtR S l) 0)) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1) + 0) (Om (1 + 1 + 1))) := by
  intro Â hÂ hb
  rw [wzRHS hl hX hA hρ hÂ hb, wzTe]
  exact wzLow hl hX hA hρ

/-- **THE LAW AT `k = 0`, `β = Ω₃` ⇔ ITS UPPER HALF** `Θ(ψ₂(Ω₃ + Ω₃)) ≤ ψ₁(A + X̂)`. -/
theorem wzLaw_iff {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) ↔
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) ≤
        S.psi (ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1) := by
  constructor
  · intro h
    have h1 := h _ (wzOwnY hl hX hA hρ) (wzBase hl hX hA hρ)
    rw [wzRHS hl hX hA hρ (wzOwnY hl hX hA hρ) (wzBase hl hX hA hρ), wzTe] at h1
    exact h1.le
  · intro hup Â hÂ hb
    rw [wzRHS hl hX hA hρ hÂ hb, wzTe]
    exact le_antisymm hup (wzLow hl hX hA hρ)

/-- **Lower test at `k = 0`, `β = Ω₃`**: every image `Z` of the law at `Ω₃` over the base `Ω₃` has `X̂ ≤ Ω^Z`. -/
theorem wzImg0_ge {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Z : Ordinal.{0}} (hT : Wg.WgTopAt S l (Om (1 + 1 + 1)) Z 0 (Om (1 + 1 + 1))) :
    S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) ≤ leOe Z := by
  have h := hT _ (wzOwnY hl hX hA hρ) (wzBase hl hX hA hρ)
  simp only [gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [Vn.vnWe_Om3] at h
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  by_contra hc
  push Not at hc
  have hP := (wzX_SC (S := S)).isPrincipal
  have h1 : (1 : Ordinal.{0}) < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
    lt_of_lt_of_le one_lt_omega0 (Lw.lw_omega_lt_SC (wzX_SC (S := S))).le
  have hζ : 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) + leOe Z < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
    hP (hP h1 wzY2_lt_X) hc
  have hl' := wzLowAll hl hX hA hρ hζ
  rw [h, ← add_assoc, ← add_assoc] at hl'
  exact lt_irrefl _ hl'

/-- **Lower test at `k = 1`, `β = 0`**: every image `Z` of the law at `Ω₄` over the base `0` has `X̂ < Ω^Z`
(sharpens `Wv.wvImg1_gt`: `Y₂ + Y₂ < X̂`).  The candidate `X̂⁰_1(0) = ψ₂(Ω₃)` passes it. -/
theorem wzImg1_gt {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {Z : Ordinal.{0}} (hT : Wg.WgTopAt S l (Om (1 + 1 + 1 + 1)) Z 0 0) :
    S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) < leOe Z := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hW4 : leWe (Om (1 + 1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1 + 1) := by
    have h := Vn.vnWe_OmK 1; rw [Nat.cast_one] at h; exact h
  have h := hT (A + 1) (Vx.vxHatA1 hA) (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [zero_add, hW4] at h
  have hlow := wzLow hl hX hA hρ
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  have h4 : (1 + 1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h34 : Om (1 + 1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have hlt4 : Om (1 + 1 + 1) + Om (1 + 1 + 1) < Om (1 + 1 + 1 + 1 : Ordinal.{0}) :=
    (SC_Om h4).isPrincipal h34 h34
  have hat : S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _),
      (vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt).trans_le (ConjT.OmW_le_A S _), rfl⟩
  have hψ : S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1)) < S.psi (Om (1 + 1 + 1 + 1)) (Om (1 + 1)) :=
    psi_lt_psi_of_mem hκ2 hlt4 (CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _))
  have hlt := hlow.trans_lt (gxTh_lt (Z := upsilon l) (GxCl.atom hat) hψ)
  rw [h] at hlt
  by_contra hc
  push Not at hc
  have hle : ConjT.Aη S (cdEta S l) + 1 + leOe Z ≤
      ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) := by
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    calc 1 + leOe Z ≤ 1 + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) := add_le_add le_rfl hc
      _ = S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) :=
        one_add_of_omega0_le (Lw.lw_omega_lt_SC (wzX_SC (S := S))).le
  exact absurd hlt (not_lt.2 (psi_mono (S := S) Low.InR_Om_one hle).1)

end Main

/-- **Non-vacuity at the witness restart** (`m* = L(0)`): a restart with an own `A`, `ψ₁(A) = ρ_λ`, where
`Θ(ψ₂(Ω₃)) = ψ₁(A + 1 + Y₂)` and the lower half `ψ₁(A + X̂) ≤ Θ(ψ₂(Ω₃·2))` hold. -/
theorem wzWit (S : InaccSeq.{0}) :
    ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) ∧
      S.psi (A + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := Vq.vqA_spec hl hX (n := 0) hn
  refine ⟨l, _, hl, e.symm, hA, hρ, wzBase hl hX hA hρ, ?_⟩
  have h := wzLow hl hX hA hρ
  rwa [← (Wg.wgOwnEta hl hX hA hρ).2] at h

end Googology.Trans.PoR.InaccPsi.R2.Wz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLift
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLowAll
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzBase
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzHat_eq
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzX0_Om3
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLawLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzLaw_iff
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzImg0_ge
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzImg1_gt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wz.wzWit
