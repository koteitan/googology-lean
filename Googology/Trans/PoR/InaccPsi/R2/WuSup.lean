import Googology.Trans.PoR.InaccPsi.R2.WcPast

/-!
# The supply past `Wc.wcX`: `υ_{μ+φ(1, υ_{μ+1}+1)} ≤ r(μ)` from the first reading

`ρ = υ_μ`, `u' = υ_{μ+1}`, `θ = ψ_{Ω₂}(Ω_ω)`, `C = Vy.vyC S ρ`, `At_C = Ld.ldAt S (Ω_ω+1) ρ`, `Θ_C = gxTh ρ At_C`.

`Wc.wcPast` reads the code `ω^{ω^{θ+1}+1}`.  The code set is closed under `φ` (`GxCl.phi`) and `Θ_C` keeps `φ`
(`gxTh_phi`), so the code `φ(1, θ+1) = ε_{θ+1} < Ω₂` reads `φ(1, Θ_C(θ)+1) ≥ φ(1, u'+1)`, an `ε`-number above `u'`.

* `wuX u = φ(1, u+1)`; `wuX_E` (an `ε`-number), `wuX_gt` (`u < wuX u`), `wuEN_le` (`ε_{u+1} = eN u ≤ wuX u`),
  `wuX_wcX` (`wcX u < wuX u`), `wuX_lt_SC`;
* `wuGood` (**`η_μ + y` is good for every `y < P(η_μ + 2)`**), `wuPast` (**`WcRead0 ⇒ wuX(u') ≤ otp(C ∩ θ_{k+2})`**);
* `wuSup` (**THE SUPPLY PAST `wcX`: `WcRead0 ⇒ υ_{μ+wuX(u')} ≤ Θ_μ(G') ≤ r(μ)`**, so every bound `B < ε_{u'+1}`
  has `υ_{μ+B} ≤ r(μ)`: `wuSup_lt`).

No new axiom.  New definition: `wuX` (an ordinal term).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- `wuX u = φ(1, u+1)` (the `(u+1)`-th `ε`-number). -/
noncomputable def wuX (u : Ordinal.{0}) : Ordinal.{0} := veblen 1 (u + 1)

theorem wuX_E (u : Ordinal.{0}) : InE (wuX u) := by
  unfold wuX InE
  have := veblen_veblen_of_lt (zero_lt_one : (0 : Ordinal.{0}) < 1) (u + 1)
  rwa [veblen_zero_apply] at this

theorem wuX_gt (u : Ordinal.{0}) : u < wuX u :=
  (lt_add_one u).trans_le ((isNormal_veblen 1).strictMono.le_apply)

theorem wuEN_le (u : Ordinal.{0}) : eN u ≤ wuX u := eN_le (wuX_gt u) (wuX_E u)

theorem wuX_one_lt (u : Ordinal.{0}) : 1 < wuX u := So.soOne_lt_E (wuX_E u)

theorem wuX_wcX (u : Ordinal.{0}) : Wc.wcX u < wuX u := by
  have hE := wuX_E u
  have h1 : ω ^ (u + 1) < wuX u := hE.opow_lt (hE.add_lt (wuX_gt u) (wuX_one_lt u))
  have h2 : ω ^ (u + 1) + 1 < wuX u := hE.add_lt h1 (wuX_one_lt u)
  exact hE.opow_lt h2

theorem wuX_lt_SC {s u : Ordinal.{0}} (hs : SC s) (hu : u < s) : wuX u < s :=
  hs.2 1 (Wc.wcSC_one hs) (u + 1) (hs.isPrincipal hu (Wc.wcSC_one hs))

theorem wuX_limit (u : Ordinal.{0}) : IsSuccLimit (wuX u) := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (lt_of_le_of_lt zero_le (wuX_gt u)).ne'
  rwa [wuX_E u] at h

section Pos

variable {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
  (hc : cdCode S μ = Ls.lsG S (k + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω)
include hR hc hω

omit hc hω in
/-- **Goodness below `P(η_μ + 2)`**: `η_μ + y` is good for every `y < P(η_μ + 1 + 1)`. -/
theorem wuGood {X : Ordinal.{0}} (hX : X ≤ Nm.Pv S (cdEta S μ + 1 + 1)) :
    ∀ y < X, Bt.Good S (cdEta S μ + y) := by
  obtain ⟨hg, -, -⟩ := Ra.raName hR
  set η := cdEta S μ with hηdef
  have hE : ∀ e, 1 < Nm.Pv S e := fun e => So.soOne_lt_E (Sl.slPv_E (S := S) e)
  intro y hy
  refine Rz.rz_good_shift hg ?_
  rcases lt_or_ge y 2 with h2 | h2
  · have h2le : (2 : Ordinal.{0}) ≤ Nm.Pv S (η + y) := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact Order.add_one_le_of_lt (hE _)
    exact h2.trans_le h2le
  · have hle : η + 1 + 1 ≤ η + y := by
      rw [add_assoc, one_add_one_eq_two]; exact (add_le_add_iff_left η).2 h2
    exact (hy.trans_le hX).trans_le (Nm.Pv_mono hle)

/-- `wuX(u') < P(η_μ + 2)`. -/
theorem wuX_lt_P : wuX (upsilon (μ + 1)) < Nm.Pv S (cdEta S μ + 1 + 1) := by
  obtain ⟨hg, -, -⟩ := Ra.raName hR
  set η := cdEta S μ with hηdef
  have hE : ∀ e, 1 < Nm.Pv S e := fun e => So.soOne_lt_E (Sl.slPv_E (S := S) e)
  have hg1 : Bt.Good S (η + 1) := Rz.rz_good_shift hg (hE _)
  have hu : upsilon (μ + 1) = Nm.Pv S (η + 1) := by
    rw [Wc.wcUps1 hR (k := k + 1) hc hω]
    show _ = S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ConjT.A_succ]
  rw [hu]
  exact wuX_lt_SC (Nm.Pv_SC S _) (Nm.Pv_lt_succ hg1)

/-- **`WcRead0 ⇒ φ(1, u'+1) ≤ otp(C ∩ θ_{k+2})`**: the code `φ(1, θ+1) < Ω₂` reads `φ(1, Θ_C(θ)+1)`. -/
theorem wuPast (hr : Wc.WcRead0 S μ) :
    wuX (upsilon (μ + 1)) ≤ cdOtp (Vy.vyC S (upsilon μ)) (Lc.lcTh S (k + 1 + 1)) := by
  have hX := Wc.wcX_pv hR (k := k + 1) hc hω
  obtain ⟨hZ, -⟩ := Le.leRho hR.1 hX
  set Z := upsilon μ with hZdef
  set At := Ld.ldAt S (Om ω + 1) Z with hAtdef
  have hAt : GxAt At := Ld.ldAt_GxAt _ _
  have hθ : GxCl Z At (ConjT.th S) :=
    GxCl.atom ⟨Om ω, ConjT.OmW_mem S _ _, lt_add_one _, rfl⟩
  have hZ1' : (1 : Ordinal.{0}) < Z := Wc.wcSC_one hZ
  have h1 : GxCl Z At 1 := GxCl.small hZ1'
  have hθ1 : GxCl Z At (ConjT.th S + 1) := GxCl.add hθ h1
  set m0 := veblen 1 (ConjT.th S + 1) with hm0
  have hm0C : GxCl Z At m0 := GxCl.phi h1 hθ1
  have hg1 : gxTh Z At 1 = 1 := gxTh_small hZ1'.le
  have hread : gxTh Z At m0 = wuX (gxTh Z At (ConjT.th S)) := by
    rw [hm0, gxTh_phi hZ hAt 1 h1 _ hθ1, hg1, gxTh_add hZ hAt hθ, hg1]; rfl
  have hle : wuX (upsilon (μ + 1)) ≤ gxTh Z At m0 := by
    rw [hread]
    exact (isNormal_veblen 1).monotone (add_le_add_left hr 1)
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hm0lt : m0 < Om (1 + 1) := wuX_lt_SC Ld.ldOm2_SC hθ2
  have hOm2 : Om (1 + 1 : Ordinal.{0}) < Lc.lcTh S (k + 1 + 1) := by
    have h := (psiS_bounds (S := S) (Om ω) ((k + 1 + 1 : ℕ) : Ordinal.{0})).1
    refine (Om_le_Om.2 ?_).trans_lt h
    have : ((1 + 1 : ℕ) : Ordinal.{0}) ≤ ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by
      exact_mod_cast (show 1 + 1 ≤ k + 1 + 1 by omega)
    simp
  refine Vy.vyOtp_of_map (Ru.ruInv Z At) (fun x hx => ?_) (fun x hx => ?_) (fun y x hyx hx => ?_)
  · exact Wc.wcCode_vyC (Ru.ruInv_spec (hx.trans_le hle)).1
  · exact ((Ru.ruInv_spec (hx.trans_le hle)).2.1.trans hm0lt).trans hOm2
  · exact Ru.ruInv_lt (hx.trans_le hle) hyx

/-- **THE SUPPLY PAST `Wc.wcX`**: `WcRead0 ⇒ υ_{μ+φ(1,u'+1)} ≤ Θ_μ(G') ≤ r(μ)`, `φ(1, u'+1) ≥ ε_{u'+1} > wcX(u')`. -/
theorem wuSup (hr : Wc.WcRead0 S μ) :
    eN (upsilon (μ + 1)) ≤ wuX (upsilon (μ + 1)) ∧ Wc.wcX (upsilon (μ + 1)) < wuX (upsilon (μ + 1)) ∧
      upsilon (μ + wuX (upsilon (μ + 1))) ≤ cdTheta S μ (Ls.lsG S (k + 1 + 1)) ∧
      upsilon (μ + wuX (upsilon (μ + 1))) ≤ cdR S μ := by
  have hu1 : upsilon (μ + 1) < Om 1 := by
    rw [Wc.wcUps1 hR (k := k + 1) hc hω]; exact psi_lt Low.InR_Om_one _
  have hXP := wuX_lt_P hR hc hω
  exact ⟨wuEN_le _, wuX_wcX _, Vy.vySup (k + 1) hR hc (wuX_limit _) (wuGood hR hXP.le)
    (wuX_lt_SC Ph.ph_SC_Om1 hu1).le (wuPast hR hc hω hr)⟩

/-- **Every bound below `ε_{u'+1}` is supplied**: `B < eN(u') ⇒ υ_{μ+B} ≤ r(μ)`. -/
theorem wuSup_lt (hr : Wc.WcRead0 S μ) {B : Ordinal.{0}} (hB : B ≤ wuX (upsilon (μ + 1))) :
    upsilon (μ + B) ≤ cdR S μ :=
  (upsilon_normal.strictMono.monotone (add_le_add_right hB μ)).trans (wuSup hR hc hω hr).2.2.2

end Pos

end Googology.Trans.PoR.InaccPsi.R2.Wu
