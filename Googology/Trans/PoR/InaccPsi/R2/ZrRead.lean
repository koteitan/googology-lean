import Googology.Trans.PoR.InaccPsi.R2.ZrTh

/-!
# Zr: the reading of the base code is short, `Θ_{l₀}(π_{Ω₂}) < δ_{l₀}` (skBCThPos)

At `A = Ω_ω + Ω₂`, `ρ = ψ_{Ω₁}(A)` (own), `H = Cl(A, ρ)`, `Θ(x) = otp(H ∩ x)`, `θ = ψ_{Ω₂}(Ω_ω)` with
`Θ(θ) = ψ_{Ω₁}(A + θ)`, `g(x) = ψ_{Ω₁}(A + θ + x)`, `F_0 = ρ`, `F_{j+1} = g(F_j)`, `K_j` the plateau iterates
(`K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + K_j)`):

* `zrPs_mono`, `zrPs_strict` (`g` is monotone, and strictly so at `x < y` once `x < g(y)`), `zrPs_gt_rho`;
* `zrF_lt_succ`, `zrF_infl` (**the inflation below the iterates**: `x < F_j ⇒ x < g(x)`; `g(x) ≥ x` fails in
  general, above a fixed point of `g`), `zrF_lt_Y` (`F_j < g(Ω₁)`);
* `zrInner` (**an atom `ψ_{Ω₂}(Ω_ω + c)` with `c < K_j` reads at most `g(Θ(c))`**, by induction on `c`),
  `zrOuter` (**`Θ(K_j) ≤ F_j`**, by induction on `j`, `Ls.lsOtp_least` at every step);
* `zrTh_Om2` (**`Θ(Ω₂) ≤ g(Ω₁) = ψ_{Ω₁}(A + θ + Ω₁)`**: every atom below `Ω₂` lies below some `K_j`);
* `zrY_lt` (`ψ_{Ω₁}(A + θ + Ω₁) < ψ_{Ω₁}(A + θ·(ω+1))`);
* `zrBCThPos` (**the skeleton leaf skBCThPos**: `Θ_{l₀}(m_{l₀}) < δ_{l₀}` at `l₀ = ι(Ω₂)`, no hypothesis).

No new axiom.  New definitions: the auxiliary maps `zrPs`, `zrF` (no statement of the skeleton depends on them).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Zr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Zo Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `g(x) = ψ_{Ω₁}(A + θ + x)`. -/
noncomputable def zrPs (S : InaccSeq.{0}) (A x : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (A + ConjT.th S + x) (Om 1)

/-- `F_0 = ρ`, `F_{j+1} = g(F_j)`. -/
noncomputable def zrF (S : InaccSeq.{0}) (A ρ : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => ρ
  | j + 1 => zrPs S A (zrF S A ρ j)

theorem zrTh_pos : (0 : Ordinal.{0}) < ConjT.th S :=
  (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

theorem zrTh_gt_Om1 : Om 1 < ConjT.th S := (psiS_bounds (S := S) _ 1).1

theorem zrPs_mono {A x y : Ordinal.{0}} (h : x ≤ y) : zrPs S A x ≤ zrPs S A y :=
  (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl h)).1

theorem zrHull_zero (C : Set Ordinal.{0}) : cdOtp C 0 = 0 :=
  le_antisymm (cdOtp_le_self _ 0) zero_le

theorem zr_dvd_Omw : ω ^ Om (1 + 1 : Ordinal.{0}) ∣ Om ω := by
  rw [← Zj.zjOmW_eq]
  exact opow_dvd_opow ω (Om_le_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast (natCast_lt_omega0 2).le))

theorem zrE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2

/-- An argument `e < Ω_ω + c` of an atom below `ψ_{Ω₂}(Ω_ω + c)`. -/
theorem zrArg_lt {e c : Ordinal.{0}} (hlt : S.psi e (Om (1 + 1)) < S.psi (Om ω + c) (Om (1 + 1))) :
    e < Om ω + c := by
  by_contra h
  exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 h)).1)

section Read

variable {A ρ : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hA : A = Om ω + Om (1 + 1))
  (hown : A ∈ S.CSet A ρ)

include hρ hA hown

theorem zrA_mem {a : Ordinal.{0}} (ha : A ≤ a) : A ∈ S.CSet a (S.psi a (Om 1)) := by
  have h : A ∈ S.CSet A (S.psi A (Om 1)) := by rw [hρ]; exact hown
  exact (psi_mono (S := S) Low.InR_Om_one ha).2 h

theorem zrOmw_lt : Om ω < A := by
  rw [hA]; exact lt_add_of_pos_right _ (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero))

theorem zrAθ_mem (y : Ordinal.{0}) : A + ConjT.th S ∈ S.CSet (A + ConjT.th S + y) (zrPs S A y) :=
  CSet.add_mem (zrA_mem hρ hA hown (le_self_add.trans le_self_add))
    (ConjT.th_mem (S := S) ((zrOmw_lt hρ hA hown).trans_le (le_self_add.trans le_self_add)))

theorem zrPs_strict {x y : Ordinal.{0}} (h : x < y) (hx : x < zrPs S A y) : zrPs S A x < zrPs S A y :=
  psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 h)
    (CSet.add_mem (zrAθ_mem hρ hA hown y) (CSet.of_lt hx))

theorem zrPs_gt_rho (x : Ordinal.{0}) : ρ < zrPs S A x := by
  rw [← hρ]
  refine psi_lt_psi_of_mem Low.InR_Om_one ?_ (zrA_mem hρ hA hown (le_self_add.trans le_self_add))
  exact (lt_add_of_pos_right A zrTh_pos).trans_le le_self_add

theorem zrRho_pos : 0 < ρ := hρ ▸ (SC_psi Low.InR_Om_one A).1

theorem zrF_lt_succ : ∀ j, zrF S A ρ j < zrF S A ρ (j + 1)
  | 0 => zrPs_gt_rho hρ hA hown _
  | j + 1 => zrPs_strict hρ hA hown (zrF_lt_succ j)
      ((zrF_lt_succ j).trans_le (zrPs_mono (zrF_lt_succ j).le))

theorem zrF_pos (j : ℕ) : 0 < zrF S A ρ j := by
  rcases j with _ | j
  · exact zrRho_pos hρ hA hown
  · exact (zrRho_pos hρ hA hown).trans (zrPs_gt_rho hρ hA hown _)

/-- **The inflation below the iterates**: `x < F_j ⇒ x < g(x)`. -/
theorem zrF_infl : ∀ j, ∀ x < zrF S A ρ j, x < zrPs S A x
  | 0, x, hx => hx.trans (zrPs_gt_rho hρ hA hown x)
  | j + 1, x, hx => by
    rcases lt_or_ge x (zrF S A ρ j) with h | h
    · exact zrF_infl j x h
    · exact hx.trans_le (zrPs_mono h)

theorem zrF_lt_Om1 (j : ℕ) : zrF S A ρ j < Om 1 := by
  rcases j with _ | j
  · rw [← hρ]; exact psi_lt Low.InR_Om_one _
  · exact psi_lt Low.InR_Om_one _

theorem zrF_lt_Y : ∀ j, zrF S A ρ j < zrPs S A (Om 1)
  | 0 => zrPs_gt_rho hρ hA hown _
  | j + 1 => zrPs_strict hρ hA hown (zrF_lt_Om1 hρ hA hown j) (zrF_lt_Y j)

variable (hθ : cdOtp (S.CSet A ρ) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1))

include hθ

theorem zrθ_eq : cdOtp (S.CSet A ρ) (ConjT.th S) = zrPs S A 0 := by
  rw [hθ]; unfold zrPs; rw [add_zero]

/-- **An atom `ψ_{Ω₂}(Ω_ω + c)`, `c < K_j`, reads at most `g(Θ(c))`** (given `Θ(K_j) ≤ F_j`). -/
theorem zrInner (j : ℕ) (hO : cdOtp (S.CSet A ρ) (zrK S j) ≤ zrF S A ρ j) :
    ∀ c, c ∈ S.CSet A ρ → c < zrK S j →
      cdOtp (S.CSet A ρ) (S.psi (Om ω + c) (Om (1 + 1))) ≤ zrPs S A (cdOtp (S.CSet A ρ) c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | _ c IH =>
  intro hc hcK
  refine Ls.lsOtp_least hρ (psi_lt (InR_Om_succ 1) _).le (SC_psi Low.InR_Om_one _)
    (zrPs_gt_rho hρ hA hown _) ?_
  rintro t ⟨e, he, heC, rfl⟩ hlt
  have he' : e < Om ω + c := zrArg_lt hlt
  have hΘcK : cdOtp (S.CSet A ρ) c < cdOtp (S.CSet A ρ) (zrK S j) := cdOtp_lt_of_mem hc hcK
  rcases le_or_gt e (Om ω) with h1 | h1
  · have htθ : S.psi e (Om (1 + 1)) ≤ ConjT.th S := (psi_mono (S := S) (InR_Om_succ 1) h1).1
    rcases eq_or_ne c 0 with rfl | hc0
    · have hlt' : S.psi e (Om (1 + 1)) < ConjT.th S := by
        have := hlt; rw [add_zero] at this; exact this
      have h2 := cdOtp_lt_of_mem (Ls.lsAt_mem ⟨e, he, heC, rfl⟩) hlt'
      rw [zrθ_eq hρ hA hown hθ] at h2
      rw [zrHull_zero _]
      exact h2
    · have hpos : 0 < cdOtp (S.CSet A ρ) c := by
        have := cdOtp_lt_of_mem (C := S.CSet A ρ) (CSet.zero_mem (S := S) A ρ) (pos_iff_ne_zero.2 hc0)
        rwa [zrHull_zero _] at this
      calc cdOtp (S.CSet A ρ) (S.psi e (Om (1 + 1))) ≤ cdOtp (S.CSet A ρ) (ConjT.th S) := cdOtp_mono _ htθ
        _ = zrPs S A 0 := zrθ_eq hρ hA hown hθ
        _ < zrPs S A (cdOtp (S.CSet A ρ) c) :=
            zrPs_strict hρ hA hown hpos (SC_psi Low.InR_Om_one _).1
  · obtain ⟨c', rfl⟩ := exists_add_of_le h1.le
    have hc'c : c' < c := (add_lt_add_iff_left _).1 he'
    have hc'2 : c' < ω ^ Om (1 + 1 : Ordinal.{0}) := by
      rw [zrE2]; exact (hc'c.trans hcK).trans (zrK_lt_Om2 j)
    have hc'C : c' ∈ S.CSet A ρ := Ls.lsTail _ heC (Om ω) c' zr_dvd_Omw hc'2 rfl
    have hIH := IH c' hc'c hc'C (hc'c.trans hcK)
    have hΘ' : cdOtp (S.CSet A ρ) c' < cdOtp (S.CSet A ρ) c := cdOtp_lt_of_mem hc'C hc'c
    have hinf : cdOtp (S.CSet A ρ) c' < zrPs S A (cdOtp (S.CSet A ρ) c') :=
      zrF_infl hρ hA hown j _ (hΘ'.trans (hΘcK.trans_le hO))
    exact hIH.trans_lt (zrPs_strict hρ hA hown hΘ' (hinf.trans_le (zrPs_mono hΘ'.le)))

variable (hΩ : cdOtp (S.CSet A ρ) (Om 1) = ρ)

include hΩ

/-- **`Θ(K_j) ≤ F_j`.** -/
theorem zrOuter : ∀ j, cdOtp (S.CSet A ρ) (zrK S j) ≤ zrF S A ρ j
  | 0 => hΩ.le
  | j + 1 => by
    have hO := zrOuter j
    refine Ls.lsOtp_least hρ (zrK_lt_Om2 _).le (SC_psi Low.InR_Om_one _) (zrPs_gt_rho hρ hA hown _) ?_
    rintro t ⟨e, he, heC, rfl⟩ hlt
    rw [zrK_succ] at hlt
    have he' : e < Om ω + zrK S j := zrArg_lt hlt
    rcases le_or_gt e (Om ω) with h1 | h1
    · calc cdOtp (S.CSet A ρ) (S.psi e (Om (1 + 1))) ≤ cdOtp (S.CSet A ρ) (ConjT.th S) :=
            cdOtp_mono _ (psi_mono (S := S) (InR_Om_succ 1) h1).1
        _ = zrPs S A 0 := zrθ_eq hρ hA hown hθ
        _ < zrPs S A (zrF S A ρ j) :=
            zrPs_strict hρ hA hown (zrF_pos hρ hA hown j) (SC_psi Low.InR_Om_one _).1
    · obtain ⟨c, rfl⟩ := exists_add_of_le h1.le
      have hcK : c < zrK S j := (add_lt_add_iff_left _).1 he'
      have hc2 : c < ω ^ Om (1 + 1 : Ordinal.{0}) := by rw [zrE2]; exact hcK.trans (zrK_lt_Om2 j)
      have hcC : c ∈ S.CSet A ρ := Ls.lsTail _ heC (Om ω) c zr_dvd_Omw hc2 rfl
      have hI := zrInner hρ hA hown hθ j hO c hcC hcK
      have hΘc : cdOtp (S.CSet A ρ) c < zrF S A ρ j := (cdOtp_lt_of_mem hcC hcK).trans_le hO
      exact hI.trans_lt (zrPs_strict hρ hA hown hΘc (hΘc.trans (zrF_lt_succ hρ hA hown j)))

/-- **`Θ(Ω₂) ≤ ψ_{Ω₁}(A + θ + Ω₁)`.** -/
theorem zrTh_Om2 : cdOtp (S.CSet A ρ) (Om (1 + 1)) ≤ zrPs S A (Om 1) := by
  refine Ls.lsOtp_least hρ le_rfl (SC_psi Low.InR_Om_one _) (zrPs_gt_rho hρ hA hown _) ?_
  intro t ht htlt
  have htC := Ls.lsAt_mem ht
  have hρle : ρ ≤ S.psi A (Om (1 + 1)) := by
    rw [← hρ]; exact ((psi_lt Low.InR_Om_one A).trans (psiS_bounds (S := S) A 1).1).le
  have hπ : t < S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) := by
    rw [← hA]; exact lt_psi_of_mem (InR_Om_succ 1) (CSet_mono le_rfl hρle htC) htlt
  obtain ⟨j, hj⟩ := zrK_sup hπ
  have hKC : zrK S j ∈ S.CSet A ρ :=
    zrK_mem j fun i _ => by rw [hA]; exact (add_lt_add_iff_left _).2 (zrK_lt_Om2 i)
  exact (cdOtp_lt_of_mem htC hj).trans_le
    ((zrOuter hρ hA hown hθ hΩ j).trans (zrF_lt_Y hρ hA hown j).le)

end Read

/-- `ψ_{Ω₁}(A + θ + Ω₁) < ψ_{Ω₁}(A + θ·(ω+1))` for an own `A > Ω_ω`. -/
theorem zrY_lt {A : Ordinal.{0}} (hown : A ∈ S.CSet A (S.psi A (Om 1))) (hA : Om ω < A) :
    zrPs S A (Om 1) < S.psi (A + ConjT.th S * (ω + 1)) (Om 1) := by
  have hθ1 : Om 1 < ConjT.th S := zrTh_gt_Om1
  have hlt : ConjT.th S + Om 1 < ConjT.th S * (ω + 1) := by
    rw [mul_add_one]
    calc ConjT.th S + Om 1 < ConjT.th S + ConjT.th S := (add_lt_add_iff_left _).2 hθ1
      _ ≤ ConjT.th S * ω + ConjT.th S := by
          refine add_le_add ?_ le_rfl
          calc ConjT.th S = ConjT.th S * 1 := (mul_one _).symm
            _ ≤ ConjT.th S * ω := mul_le_mul_left' one_lt_omega0.le _
  unfold zrPs
  refine psi_lt_psi_of_mem Low.InR_Om_one ?_ ?_
  · rw [add_assoc]; exact (add_lt_add_iff_left _).2 hlt
  · refine CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown)
      (ConjT.th_mem (S := S) (hA.trans_le le_self_add))) (CSet.Om_mem (CSet.one_mem _ _))

/-- **skBCThPos (the short branch)**: `Θ_{l₀}(m_{l₀}) < δ_{l₀}` at `l₀ = ι(Ω₂)`, with no hypothesis: `m_{l₀} = π_{Ω₂}`,
`Θ(π_{Ω₂}) = Θ(Ω₂) ≤ ψ_{Ω₁}(A + θ + Ω₁) < ψ_{Ω₁}(A + θ·(ω+1)) = υ_{l₀+ω+1}`, `A = Ω_ω + Ω₂`. -/
theorem zrBCThPos : cdTheta S (zoBase S) (cdCode S (zoBase S)) < cdDelta (zoBase S) := by
  have hri : IsRestartIdx (zoBase S) := zoBase_spec.1
  have hR : CdRange S (zoBase S) := zoBase_range
  have hAη : ConjT.Aη S (cdEta S (zoBase S)) = Om ω + Om (1 + 1) := zrBase_A
  have hρ : S.psi (Om ω + Om (1 + 1)) (Om 1) = upsilon (zoBase S) := by
    rw [zrBase_rho]
    show S.psi (Om ω + Om (1 + 1)) (Om 1) = S.psi (ConjT.Aη S (Om (1 + 1))) (Om 1)
    rw [zrA_Om2]
  have hm : upsilon (zoBase S) < cdMstar S := by
    rw [← zoTop_ups (S := S)]; exact upsilon_normal.strictMono zoBase_lt_top
  have hω : upsilon (zoBase S) < Nc.ncL S ω := hm.trans_le (cdMstar_le_L S ω)
  obtain ⟨-, -, hown0⟩ := Rc.rcOwn hri hω
  rw [hAη] at hown0
  have hown' : Om ω + Om (1 + 1) ∈ S.CSet (Om ω + Om (1 + 1)) (S.psi (Om ω + Om (1 + 1)) (Om 1)) := hown0
  have hown : Om ω + Om (1 + 1) ∈ S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
    rw [← hρ]; exact hown'
  have hHull : cdHull S (zoBase S) = S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
    unfold cdHull; rw [hAη]
  have hθg := Wl.wlThVal hri hm hown' hρ
  have hat : Ld.ldAtR S (zoBase S) = Ls.lsAt S (Om ω + Om (1 + 1)) (upsilon (zoBase S)) := by
    unfold Ld.ldAtR; rw [hAη]; ext s
    exact ⟨fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩, fun ⟨a, h1, h2, h3⟩ => ⟨a, h2, h1, h3⟩⟩
  have hθ : cdOtp (S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S))) (ConjT.th S) =
      S.psi (Om ω + Om (1 + 1) + ConjT.th S) (Om 1) := by
    rw [Ls.lsOtp_eq (m := ConjT.th S) hρ (show ConjT.th S < Om (1 + 1) from psi_lt (InR_Om_succ 1) _).le, ← hat]
    exact hθg
  have hΩ : cdOtp (S.CSet (Om ω + Om (1 + 1)) (upsilon (zoBase S))) (Om 1) = upsilon (zoBase S) := by
    have hpv : Pv S (cdEta S (zoBase S)) = upsilon (zoBase S) := by rw [zrBase_eta, zrBase_rho]
    have h := cdTheta_Om1 (S := S) hpv
    unfold cdTheta at h; rwa [hHull] at h
  have hmain := zrTh_Om2 hρ rfl hown hθ hΩ
  have hAw : Om ω < Om ω + Om (1 + 1) :=
    lt_add_of_pos_right _ (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero))
  have hY := zrY_lt hown' hAw
  have hγ : ω + 1 ≤ upsilon (zoBase S) := by
    have hSC : SC (upsilon (zoBase S)) := by rw [← hρ]; exact SC_psi Low.InR_Om_one _
    exact Order.add_one_le_of_lt (Lw.lw_omega_lt_SC hSC)
  have hu := Rg.rgUps_eq hR hγ
  rw [hAη] at hu
  have hδ : S.psi (Om ω + Om (1 + 1) + ConjT.th S * (ω + 1)) (Om 1) = cdDelta (zoBase S) := by
    unfold cdDelta; rw [add_assoc (zoBase S)]; exact hu.symm
  rw [zrBase_theta]
  unfold cdTheta
  rw [hHull]
  exact hmain.trans_lt (hY.trans_le hδ.le)

/-- **CapV at the base**: `r(l₀) = δ + Θ(π_{Ω₂}) < P(Ω₂ + Ω₂) ≤ cap(l₀)`, given UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)`
(for `ρ_{l₀} < ν_C`, which makes the points `δ + x` closed). -/
theorem zrBaseCapV
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ) :
    CdCapV S (zoBase S) := by
  have hri : IsRestartIdx (zoBase S) := zoBase_spec.1
  have hR : CdRange S (zoBase S) := zoBase_range
  have hν := zrNu hlow
  have hTh := zrBCThPos (S := S)
  have hK : ∀ x ≤ cdTheta S (zoBase S) (cdCode S (zoBase S)), cdDelta (zoBase S) + x ∈ cdK (zoBase S) :=
    fun x hx => Zh.zhDense hri hν (hx.trans_lt hTh)
  have hRr : cdR S (zoBase S) = cdDelta (zoBase S) + cdTheta S (zoBase S) (cdCode S (zoBase S)) :=
    cdk_interval hK _ le_rfl
  have hAη : ConjT.Aη S (cdEta S (zoBase S)) = Om ω + Om (1 + 1) := zrBase_A
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := zrE2
  have hInE2 : InE (Om (1 + 1 : Ordinal.{0})) := hE2
  have hρ2 : upsilon (zoBase S) < Om (1 + 1) := by
    rw [zrBase_rho]; exact (Pv_lt_Om1 S _).trans (Om_lt_Om.2 (lt_add_of_pos_right 1 zero_lt_one))
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  -- `X = ψ_{Ω₁}(A + Ω₂) = P(Ω₂ + Ω₂)`
  set X := S.psi (Om ω + Om (1 + 1) + Om (1 + 1)) (Om 1) with hX
  have hXSC : SC X := SC_psi Low.InR_Om_one _
  -- `δ < υ_{l₀+ρ} ≤ X`
  have hγ : upsilon (zoBase S) ≤ upsilon (zoBase S) := le_rfl
  have hu := Rg.rgUps_eq hR hγ
  rw [hAη] at hu
  have hρω : ω + 1 < upsilon (zoBase S) := by
    have hSC : SC (upsilon (zoBase S)) := by rw [zrBase_rho]; exact Pv_SC S _
    exact hSC.isSuccLimit.add_one_lt (Lw.lw_omega_lt_SC hSC)
  have hδu : cdDelta (zoBase S) < upsilon (zoBase S + upsilon (zoBase S)) := by
    unfold cdDelta; rw [add_assoc]
    exact upsilon_normal.strictMono ((add_lt_add_iff_left _).2 hρω)
  have huX : upsilon (zoBase S + upsilon (zoBase S)) ≤ X := by
    rw [hu, hX]
    refine (psi_mono (S := S) Low.InR_Om_one ?_).1
    exact (add_le_add le_rfl (InE.mul_lt hInE2 hθ2 hρ2).le)
  have hδX : cdDelta (zoBase S) < X := hδu.trans_le huX
  -- `X ≤ cap(l₀)`
  have hcap : X ≤ cdCapB S (zoBase S) := by
    unfold cdCapB
    rw [zrBase_eta]
    have h0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := (Om_pos (by
      rw [one_add_one_eq_two]; exact two_ne_zero)).ne'
    have hle : Om (1 + 1 : Ordinal.{0}) ≤ cdExp (Om (1 + 1)) := cdExp_max h0 (by rw [hE2])
    have hw : Om (1 + 1 : Ordinal.{0}) ≤ ω ^ cdExp (Om (1 + 1)) := by
      rw [← hE2]; exact opow_le_opow_right omega0_pos (hE2.symm ▸ hle)
    calc X = Pv S (Om (1 + 1) + Om (1 + 1)) := by
          rw [hX]; show _ = S.psi (ConjT.Aη S (Om (1 + 1) + Om (1 + 1))) (Om 1)
          unfold ConjT.Aη; rw [mul_add, zr_th_Om2, add_assoc]
      _ ≤ Pv S (Om (1 + 1) + ω ^ cdExp (Om (1 + 1))) := Pv_mono (add_le_add le_rfl hw)
  unfold CdCapV
  rw [hRr]
  exact (hXSC.isPrincipal hδX (hTh.trans hδX)).trans_le hcap

end Googology.Trans.PoR.InaccPsi.R2.Zr
