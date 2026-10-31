import Googology.Trans.PoR.InaccPsi.R2.WkLift
import Googology.Trans.PoR.InaccPsi.R2.WcPast
import Googology.Trans.PoR.InaccPsi.R2.WgTh

/-!
# The first reading `WcRead0` is a theorem: `Θ_C(θ) = υ_{μ+1}` at every Range restart with code `G_{k+1}+1`

`ρ = υ_μ`, `A = A_{η_μ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `At_C = Ld.ldAt S (Ω_ω+1) ρ` (the atoms `ψ_{Ω₂}(x)`, `x ∈ Cl(Ω_ω+1, ρ)`,
`x ≤ Ω_ω`), `Θ_C = gxTh ρ At_C`, `κ = rxL S ρ At_C W` the level shift (`Rx`), `W = rxW ρ At_C`.

The lift of `Rx.rxBlkTh` uses the atoms `ψ_{Ω₂}(Ω_ω + κ ζ)`, above `θ`.  Below `θ` the lift is done one level at a
time: for the members `ζ < ψ_{Ω₂}(Ω_n)` (`n ≥ 1`) the atoms are `ψ_{Ω₂}(Ω_{n+1} + κ ζ)`, whose arguments lie below
`Ω_ω` and in `Cl(Ω_ω+1, ρ)`, so they are atoms of `At_C` below `θ`; the closure condition of `Rx.rxLift` is
`κ(e − A) ∈ Cl(Ω_{n+1} + κ ζ, …)`, which is `Wk.wkL_memN_lt` (the tail `e − A < ζ < ψ_{Ω₂}(Ω_n)`).

* `wkTh_cof` (**`θ = sup_n ψ_{Ω₂}(Ω_n)`**: every `w < θ` is below some `ψ_{Ω₂}(Ω_n)`, `n ≥ 1`);
* `wkStep` (**`ψ_{Ω₁}(A + ζ) < Θ_C(θ)` for every `ζ < θ`**);
* `wkRead0` (**`WcRead0 S μ` IS A THEOREM**: `υ_{μ+1} ≤ Θ_C(θ)`, by continuity of `ψ_{Ω₁}` at `A + θ`);
* `wkRead0_eq` (`Θ_C(θ) = υ_{μ+1}`), `wkTheta_th` (**`Θ_μ(θ) = υ_{μ+1} = ψ_{Ω₁}(A + θ)`**), `wkThLow`
  (**`Wg.WgThLow S μ`**, the lower half of the reading of `θ`, open in `Wg`, at these restarts).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`θ = sup_n ψ_{Ω₂}(Ω_n)`**: every `w < θ` is below some `ψ_{Ω₂}(Ω_n)` with `n ≥ 1`. -/
theorem wkTh_cof {w : Ordinal.{0}} (hw : w < ConjT.th S) :
    ∃ n : ℕ, 1 ≤ n ∧ w < S.psi (Om (n : Ordinal.{0})) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hlim : IsSuccLimit (Om ω : Ordinal.{0}) := (SC_Om omega0_ne_zero).isSuccLimit
  have e : ConjT.th S = ⨆ e : Iio (Om ω : Ordinal.{0}), S.psi e.1 (Om (1 + 1)) :=
    Lw.lw_psi_limit S hκ2 hlim
  have hbdd : BddAbove (range fun e : Iio (Om ω : Ordinal.{0}) => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
  haveI : Nonempty (Iio (Om ω : Ordinal.{0})) := ⟨⟨0, Om_pos omega0_ne_zero⟩⟩
  rw [e] at hw
  obtain ⟨⟨x, hx⟩, hwx⟩ := (lt_ciSup_iff hbdd).1 hw
  obtain ⟨n, hn⟩ := rxOmW_nat hx
  refine ⟨n + 1, by omega, hwx.trans_le ?_⟩
  refine (psi_mono (S := S) hκ2 (hn.le.trans (Om_le_Om.2 ?_))).1
  exact_mod_cast Nat.le_succ n

/-- `ψ_{Ω₂}(Ω_n) < θ`. -/
theorem wkPsiOm_lt_th (n : ℕ) : S.psi (Om (n : Ordinal.{0})) (Om (1 + 1)) < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (Om_lt_Om.2 (natCast_lt_omega0 n)) (rxC_Om_nat _ _ n)

section General

variable {μ ηx : Ordinal.{0}} (hl : IsRestartIdx μ) (hX : upsilon μ < Nm.Pv S ηx)
include hl hX

/-- **`ψ_{Ω₁}(A + ζ) < Θ_C(θ)` for every `ζ < θ`**, at every restart `μ` (`A = A_{η_μ}`, `ρ = υ_μ`). -/
theorem wkStepG {ζ : Ordinal.{0}} (hζ : ζ < ConjT.th S) :
    S.psi (ConjT.Aη S (cdEta S μ) + ζ) (Om 1) <
      gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hpv : S.psi (ConjT.Aη S (cdEta S μ)) (Om 1) = upsilon μ := cdEta_pv (S := S) hl.1 hX
  set Z := upsilon μ with hZdef
  set At := Ld.ldAt S (Om ω + 1) Z with hAtdef
  have hAt : GxAt At := Ld.ldAt_GxAt _ _
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  set W := rxW Z At with hWdef
  set κ := rxL S Z At W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hθSC := ConjT.SC_th S
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hOmW : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have hθW : ConjT.th S < Om ω := hθ2.trans (Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  -- the cofinal member and its level
  obtain ⟨w, hw, hζw, hwθ⟩ := rxCofTh hζ
  obtain ⟨n, hn, hwn⟩ := wkTh_cof (S := S) hwθ
  set β := Om ((n : Ordinal.{0}) + 1) with hβdef
  have hβW : β < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 (n + 1); exact_mod_cast this)
  have hβC : ∀ a b, β ∈ S.CSet a b := fun a b => rxC_Om_succ a b n
  have hκW : ∀ ζ, RxE S W ζ → κ ζ < Om ω := fun ζ h => rxL_lt_OmW hZ hZ1 hAt h
  have hinvC : ∀ g, g < W → ruInv Z At g ∈ S.CSet (Om ω + 1) Z := fun g hg => by
    obtain ⟨hcode, -, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
    exact Wc.wcCode_mem hcode _ _ (lt_add_one _) le_rfl
  have hκC : ∀ ζ, RxE S W ζ → κ ζ ∈ S.CSet (Om ω + 1) Z := fun ζ h =>
    rxL_memH hZ hZ1 hAt hW le_rfl le_self_add hinvC ζ h
  have hat : ∀ ζ, RxE S W ζ → S.psi (β + κ ζ) (Om (1 + 1)) ∈ At := fun ζ h =>
    ⟨β + κ ζ, CSet.add_mem (hβC _ _) (hκC ζ h),
      (hOmW.isPrincipal hβW (hκW ζ h)).trans (lt_add_one _), rfl⟩
  have hβat : S.psi β (Om (1 + 1)) ∈ At := ⟨β, hβC _ _, hβW.trans (lt_add_one _), rfl⟩
  have hbase : S.psi A (Om 1) ≤ gxTh Z At (S.psi β (Om (1 + 1))) := by
    rw [hpv]
    exact (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) β 1).1.le)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ h h0 =>
    psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right β (rxL_pos hZ hZ1 hAt h h0)) (hβC _ _)
  set D : Set Ordinal.{0} :=
    {ζ | RxE S W ζ ∧ ζ < S.psi (Om (n : Ordinal.{0})) (Om (1 + 1))} with hDdef
  have hdvd : ConjT.th S ∣ A := by
    have := rxDvdTh (S := S) (cdEta S μ) 0; rwa [mul_zero, add_zero] at this
  have hcl : ∀ ζ ∈ D, gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 → ∀ e,
      HCl S (A + ζ) (gxTh Z At (S.psi (β + κ ζ) (Om (1 + 1)))) e → A ≤ e → e < A + ζ →
      e - A ∈ D ∧ β + κ (e - A) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζD hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh Z At t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ gxTh Z At (Om (1 + 1)) := gxTh_mono (psi_lt hκ2 _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have e1 : e = A + (e - A) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e - A < ζ := Ry.rySub_lt h1 h2
    have hltn : e - A < S.psi (Om (n : Ordinal.{0})) (Om (1 + 1)) := hlt.trans hζD.2
    have hltθ : e - A < ConjT.th S := hltn.trans (wkPsiOm_lt_th n)
    have hm : e % ConjT.th S = e - A := by
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC A hltθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hN : RxN S Tt (e - A) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - A) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltn⟩, CSet.add_mem (hβC _ _) ?_⟩
    exact wkL_memN_lt hZ hZ1 hAt hn htSC hTW le_self_add
      (fun g hg => CSet.of_lt (ruInv_spec hg).2.1) hET hltn
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := D)
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h) (fun ζ hζ => hat ζ hζ.1)
    (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  have hwD : w ∈ D := ⟨hEθ (hw.mono (ruTwo_le hW)) hwθ, hwn⟩
  -- the atom of `w` is below `θ`
  have htθ : S.psi (β + κ w) (Om (1 + 1)) < ConjT.th S := by
    set T' := min (gxTh Z At (ConjT.th S)) (Om 1) with hT'
    have hT'SC : SC T' := by
      rcases le_total (gxTh Z At (ConjT.th S)) (Om 1) with h | h
      · rw [hT', min_eq_left h]
        exact gxTh_SC hZ hAt hθSC (hZ1.trans (psiS_bounds (S := S) _ 1).1)
      · rw [hT', min_eq_right h]; exact Ph.ph_SC_Om1
    have hT'W : T' ≤ W := min_le_min_right _ (gxTh_mono hθ2.le)
    have hκwC : κ w ∈ S.CSet (Om ω) (ConjT.th S) :=
      rxL_memH hZ hZ1 hAt hT'SC hT'W le_rfl
        (fun g hg => CSet.of_lt (ruInv_spec (hg.trans_le (min_le_left _ _))).2.1) w
        (hEθ (hw.mono (ruTwo_le hT'SC)) hwθ)
    exact psi_lt_psi_of_mem hκ2 (hOmW.isPrincipal hβW (hκW w hwD.1))
      (CSet.add_mem (hβC _ _) hκwC)
  have htAt : GxCl Z At (S.psi (β + κ w) (Om (1 + 1))) := GxCl.atom (hat w hwD.1)
  calc S.psi (A + ζ) (Om 1) ≤ S.psi (A + w) (Om 1) :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hζw)).1
    _ ≤ gxTh Z At (S.psi (β + κ w) (Om (1 + 1))) := hLift w hwD
    _ < gxTh Z At (ConjT.th S) := gxTh_lt htAt htθ

omit hl hX in
/-- **The atoms `At_C` are atoms of the hull** when `Ω_ω < A`: `Θ_C ≤ Θ_λ` below `Ω₂`. -/
theorem wkThC_le (hA : Om ω < ConjT.Aη S (cdEta S μ)) (m : Ordinal.{0}) :
    gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) m ≤ gxTh (upsilon μ) (ldAtR S μ) m := by
  have hsub : Ld.ldAt S (Om ω + 1) (upsilon μ) ⊆ ldAtR S μ := by
    rintro s ⟨x, hx, hxlt, rfl⟩
    have h1 : Om ω + 1 ≤ ConjT.Aη S (cdEta S μ) := Order.add_one_le_of_lt hA
    exact ⟨x, CSet_mono h1 le_rfl hx, hxlt.trans_le h1, rfl⟩
  exact Wc.wcOtp_sub (fun _ h => GxCl.mono le_rfl hsub h) m

/-- **`Wg.WgThLow S μ` at every restart with `Ω_ω < A_{η_μ}`**: `ψ_{Ω₁}(A + θ) ≤ Θ_μ(θ)`. -/
theorem wkThLowG (hA : Om ω < ConjT.Aη S (cdEta S μ)) : Wg.WgThLow S μ :=
  Wg.wgLow_of_all fun _ hζ => (wkStepG hl hX hζ).trans_le (wkThC_le hA _)

/-- **`θ ∈ At_λ ⇒ Ω_ω < A_{η_λ}`** (else the argument of `θ = ψ_{Ω₂}(a)` is below `Ω_ω`). -/
theorem wkA_gt (hθ : ConjT.th S ∈ ldAtR S μ) : Om ω < ConjT.Aη S (cdEta S μ) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  obtain ⟨a, haC, haA, hθa⟩ := hθ
  have hge : Om ω ≤ ConjT.Aη S (cdEta S μ) := le_self_add
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at haC haA
    have hρθ : upsilon μ ≤ ConjT.th S :=
      (hZ1.trans (psiS_bounds (S := S) (Om ω) 1).1).le
    have hlt : S.psi a (Om (1 + 1)) < ConjT.th S :=
      psi_lt_psi_of_mem (InR_Om_succ 1) haA (CSet_mono le_rfl hρθ haC)
    rw [← hθa] at hlt
    exact lt_irrefl _ hlt

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + θ)` at every restart with `θ ∈ At_λ`** (the value `SkR.skThVal`; with `Wg.wgTheta_le`). -/
theorem wkThVal {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon μ)
    (hθ : ConjT.th S ∈ ldAtR S μ) :
    gxTh (upsilon μ) (ldAtR S μ) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) :=
  Wg.wgThVal_of_low hl hX hA hρ (wkThLowG hl hX (wkA_gt hl hX hθ))

end General

section Main

variable {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
  (hω : upsilon μ < Nc.ncL S ω)
include hR hc hω

/-- **`ψ_{Ω₁}(A + ζ) < Θ_C(θ)` for every `ζ < θ`** at the Range restarts with code `G_{k+1}+1`. -/
theorem wkStep {ζ : Ordinal.{0}} (hζ : ζ < ConjT.th S) :
    S.psi (ConjT.Aη S (cdEta S μ) + ζ) (Om 1) <
      gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S) :=
  wkStepG hR.1 (Wc.wcX_pv hR hc hω) hζ

/-- **`WcRead0 S μ` IS A THEOREM**: `υ_{μ+1} ≤ Θ_C(θ)` at every Range restart `μ` with code `G_{k+1}+1` below
`L(ω)`. -/
theorem wkRead0 : Wc.WcRead0 S μ := by
  unfold Wc.WcRead0
  rw [Wc.wcUps1 hR hc hω]
  set A := ConjT.Aη S (cdEta S μ) with hAdef
  have hθSC := ConjT.SC_th S
  have hlim : IsSuccLimit (A + ConjT.th S) := isSuccLimit_add _ hθSC.isSuccLimit
  rw [Lw.lw_psi_limit S Low.InR_Om_one hlim]
  refine ciSup_le' fun e => ?_
  rcases lt_or_ge e.1 A with h1 | h1
  · have h0 := wkStep hR hc hω hθSC.1
    rw [add_zero] at h0
    exact ((psi_mono (S := S) Low.InR_Om_one h1.le).1.trans_lt h0).le
  · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt : e.1 - A < ConjT.th S := by
      have h2 := e.2
      change e.1 < A + ConjT.th S at h2
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact (wkStep hR hc hω hlt).le

/-- **`Θ_C(θ) = υ_{μ+1}`.** -/
theorem wkRead0_eq :
    gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S) = upsilon (μ + 1) := by
  refine le_antisymm ?_ (wkRead0 hR hc hω)
  obtain ⟨h1, h2⟩ := Wc.wcOtp_th hR hc hω
  exact (Wc.wcOtp_sub (fun _ h => Wc.wcCode_vyC h) _).trans (h1.trans h2)

/-- **`Θ_μ(θ) = υ_{μ+1}`** (the reading of `θ` by the full hull). -/
theorem wkTheta_th : cdTheta S μ (ConjT.th S) = upsilon (μ + 1) := by
  obtain ⟨h1, h2⟩ := Wc.wcOtp_th hR hc hω
  refine le_antisymm h2 ((wkRead0 hR hc hω).trans ?_)
  exact (Wc.wcOtp_sub (fun _ h => Wc.wcCode_vyC h) _).trans h1

/-- **`Wg.WgThLow S μ`**: `ψ_{Ω₁}(A + θ) ≤ Θ_μ(θ)` (the lower half of the reading of `θ`). -/
theorem wkThLow : Wg.WgThLow S μ := by
  have hX := Wc.wcX_pv hR hc hω
  have hθ2 : ConjT.th S ≤ Om (1 + 1) := (psi_lt (InR_Om_succ 1) _).le
  unfold Wg.WgThLow
  rw [← ldTheta hR.1 hX hθ2, wkTheta_th hR hc hω, Wc.wcUps1 hR hc hω]

end Main

/-- **Non-vacuity**: below every `L(n+1)` the Range restarts with code `G_{k+1}+1` are cofinal, and `WcRead0` holds at
each of them. -/
theorem wkRead0_cof (n k : ℕ) : ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ cdCode S μ = Ls.lsG S (k + 1) + 1 ∧ Wc.WcRead0 S μ := by
  intro γ hγ
  obtain ⟨μ, hR, hγμ, hlt, hc⟩ := Ls.lsNames_L (S := S) n k γ hγ
  exact ⟨μ, hR, hγμ, hlt, hc, wkRead0 hR hc (hlt.trans (Qq.qqL_lt_omega S (n + 1)))⟩

end Googology.Trans.PoR.InaccPsi.R2.Wk

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkTh_cof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkStepG
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkThC_le
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkThLowG
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkA_gt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkThVal
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkStep
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkRead0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkRead0_eq
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkTheta_th
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkThLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wk.wkRead0_cof
