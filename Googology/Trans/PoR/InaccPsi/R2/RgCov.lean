import Googology.Trans.PoR.InaccPsi.R2.RgEmb
import Googology.Trans.PoR.InaccPsi.R2.RgNu

/-!
# The reading lower bound `υ_{μ+γ} ≤ Θ_μ(s)` is exactly a covering by the atom readings below `s`

`θ = ψ_{Ω₂}(Ω_ω)`, `A = A_{η_μ} = Ω_ω + θ·η_μ`, `ρ_μ = ψ_{Ω₁}(A)`, the hull `Cl(A, ρ_μ)`,
`Θ(m) = otp(Cl(A, ρ_μ) ∩ m)`, the atoms `Ls.lsAt S A ρ` (the `ψ_{Ω₂}(e)`, `e ∈ Cl(A, ρ) ∩ A`).  At a Range
restart with `ω^{Ω₁} ∣ η_μ` and `γ < ρ_μ`: `υ_{μ+γ} = P(η_μ + γ) = ψ_{Ω₁}(A + θ·γ)`.

* `RgCov S A ρ s D` (**the covering of the collapses `ψ_{Ω₁}(A + ζ)`, `ζ < D`, by the atom readings below
  `s`**, asked only at the members `ζ ∈ Cl(A + D, Θ(s))`): `ψ_{Ω₁}(A + ζ) ≤ ρ` or `≤ Θ(t)` for an atom `t < s`;
* `rgPsi_le_cover` (**`RgCov → ψ_{Ω₁}(A + D) ≤ Θ(s)`** for a strongly critical `s ∈ (Ω₁, Ω₂]`, `ω^g ∣ A`,
  `D ≤ ω^g`), `rgCover_of_psi_le` (**the converse**, `A` own), `rgPsi_le_iff_cover`: Ls.lsStrict_iff for
  every `D` and every `s`, not only `D = G_k`, `s = G_{k+1}`;
* `rgDvd_A` (`ω^{θ+Ω₁} ∣ A_η` when `ω^{Ω₁} ∣ η`), `rgD_le` (`θ·γ ≤ ω^{θ+Ω₁}` for `γ < Ω₁`),
  `rgUps_le_iff_cover` (**`υ_{μ+γ} ≤ Θ_μ(s)` ⇔ `RgCov` at `D = θ·γ`**, at a Range restart below `L(ω)`);
* `RgCoverAt S a` (**the covering form of the supply at `a`**: for every `γ < a` a Range restart `μ`,
  `γ < ρ_μ < a`, `ω^{Ω₁} ∣ η_μ`, and one strongly critical code `s ∈ (Ω₁, m_μ]` covering `D = θ·γ`),
  `rgReadAt_of_cover` (**`RgCoverAt → Rc.RcReadAt`**), `rgSupAt_of_cover` (**`→ Ra.RaSupAt`**),
  `rgCover_of_read` (**`Ra.RaSupRead S k` gives `RgCoverAt` at `m*` and every `L(n+1)`**: the form asks
  no more than the docs' reading statement);
* `rgRoad_cov` (**the road `rgRoad` with the supply at `m*` and every `L(n+1)` in the covering form**).

No new axiom.  New definitions (hypothesis names only): `RgCov`, `RgCoverAt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **The covering of `ψ_{Ω₁}(A + ζ)`, `ζ < D`, by the atom readings below `s`** (members only). -/
def RgCov (S : InaccSeq.{0}) (A ρ s D : Ordinal.{0}) : Prop :=
  ∀ ζ ∈ S.CSet (A + D) (cdOtp (S.CSet A ρ) s), ζ < D →
    S.psi (A + ζ) (Om 1) ≤ ρ ∨ ∃ t ∈ Ls.lsAt S A ρ, t < s ∧ S.psi (A + ζ) (Om 1) ≤ cdOtp (S.CSet A ρ) t

/-- **`RgCov → ψ_{Ω₁}(A + D) ≤ Θ(s)`.** -/
theorem rgPsi_le_cover {A ρ s D g : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs : SC s)
    (h1 : Om 1 < s) (h2 : s ≤ Om (1 + 1)) (hg : ω ^ g ∣ A) (hD : D ≤ ω ^ g) (h : RgCov S A ρ s D) :
    S.psi (A + D) (Om 1) ≤ cdOtp (S.CSet A ρ) s := by
  have hβ := Ls.lsOtp_SC hρ hs h1 h2
  have hρβ := Ls.lsOtp_gt hρ h1 h2
  refine Ls.lsPsi_le_mem hβ (by rw [hρ]; exact hρβ) hg hD fun ζ hζC hζ => ?_
  rcases h ζ hζC hζ with h' | ⟨t, ht, hts, hv⟩
  · exact h'.trans_lt hρβ
  · exact hv.trans_lt (Ls.lsOtp_atom_lt ht hts)

/-- **The converse**: with `A` own, `ψ_{Ω₁}(A + D) ≤ Θ(s)` gives `RgCov`. -/
theorem rgCover_of_psi_le {A ρ s D : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (h2 : s ≤ Om (1 + 1))
    (hown : A ∈ S.CSet A (S.psi A (Om 1))) (hle : S.psi (A + D) (Om 1) ≤ cdOtp (S.CSet A ρ) s) :
    RgCov S A ρ s D := by
  intro ζ hζC hζ
  have hvlt : S.psi (A + ζ) (Om 1) < cdOtp (S.CSet A ρ) s := by
    rcases hle.lt_or_eq with hlt | heq
    · exact ((psi_mono (S := S) Low.InR_Om_one
        ((add_lt_add_iff_left A).2 hζ).le).1).trans_lt hlt
    · have hm : A + ζ ∈ S.CSet (A + D) (S.psi (A + D) (Om 1)) := by
        refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) ?_
        rw [heq]; exact hζC
      rw [← heq]
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hζ) hm
  by_contra hno
  push Not at hno
  obtain ⟨h1', h2'⟩ := hno
  have hle' := Ls.lsOtp_least hρ h2 (SC_psi Low.InR_Om_one _) h1' fun t ht hts => h2' t ht hts
  exact absurd hvlt (not_lt.2 hle')

/-- **`ψ_{Ω₁}(A + D) ≤ Θ(s)` ⇔ `RgCov`** (`A` own, `s` strongly critical in `(Ω₁, Ω₂]`, `ω^g ∣ A`, `D ≤ ω^g`). -/
theorem rgPsi_le_iff_cover {A ρ s D g : Ordinal.{0}} (hρ : S.psi A (Om 1) = ρ) (hs : SC s)
    (h1 : Om 1 < s) (h2 : s ≤ Om (1 + 1)) (hg : ω ^ g ∣ A) (hD : D ≤ ω ^ g)
    (hown : A ∈ S.CSet A (S.psi A (Om 1))) :
    S.psi (A + D) (Om 1) ≤ cdOtp (S.CSet A ρ) s ↔ RgCov S A ρ s D :=
  ⟨rgCover_of_psi_le hρ h2 hown, rgPsi_le_cover hρ hs h1 h2 hg hD⟩

theorem rgTh_SC (S : InaccSeq.{0}) : SC (ConjT.th S) := SC_psi (InR_Om_succ 1) _

theorem rgTh_opow (S : InaccSeq.{0}) : ω ^ ConjT.th S = ConjT.th S :=
  Low.opow_eq_self_of_SC (rgTh_SC S)

/-- `ω^{θ+Ω₁} ∣ A_η` when `ω^{Ω₁} ∣ η`. -/
theorem rgDvd_A {η : Ordinal.{0}} (hd : ω ^ Om 1 ∣ η) : ω ^ (ConjT.th S + Om 1) ∣ ConjT.Aη S η := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have h1ω : Om 1 < Om (ω : Ordinal.{0}) := Om_lt_Om.2 one_lt_omega0
  have hle : ConjT.th S + Om 1 ≤ Om ω := (hSC.isPrincipal (Bt.th_lt_Om_omega S) h1ω).le
  unfold ConjT.Aη
  refine dvd_add ?_ ?_
  · rw [← hOw]; exact opow_dvd_opow ω hle
  · rw [opow_add, rgTh_opow]; exact mul_dvd_mul_left _ hd

/-- `θ·γ ≤ ω^{θ+Ω₁}` for `γ < Ω₁`. -/
theorem rgD_le {γ : Ordinal.{0}} (hγ : γ < Om 1) : ConjT.th S * γ ≤ ω ^ (ConjT.th S + Om 1) := by
  rw [opow_add, rgTh_opow]
  exact mul_le_mul_of_nonneg_left (hγ.le.trans (right_le_opow _ one_lt_omega0)) zero_le

/-- `υ_{μ+γ} = ψ_{Ω₁}(A_{η_μ} + θ·γ)` at a Range restart, `γ ≤ ρ_μ`. -/
theorem rgUps_eq {μ γ : Ordinal.{0}} (hR : CdRange S μ) (hγ : γ ≤ upsilon μ) :
    upsilon (μ + γ) = S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * γ) (Om 1) := by
  rw [Ra.raUps_shift hR hγ]
  show S.psi (ConjT.Aη S (cdEta S μ + γ)) (Om 1) = _
  rw [Ra.raA_add]

theorem rgGam_lt {μ γ : Ordinal.{0}} (hR : CdRange S μ) (hγ : γ < upsilon μ) : γ < Om 1 := by
  have := Nm.Pv_lt_Om1 S (cdEta S μ)
  rw [Ls.lsPv_range hR] at this
  exact hγ.trans this

/-- **`υ_{μ+γ} ≤ Θ_μ(s)` ⇔ `RgCov` at `D = θ·γ`**, at a Range restart `μ` below `L(ω)` with
`ω^{Ω₁} ∣ η_μ`, `γ < ρ_μ`, `s` strongly critical in `(Ω₁, Ω₂]`. -/
theorem rgUps_le_iff_cover {μ γ s : Ordinal.{0}} (hR : CdRange S μ) (hω : upsilon μ < Nc.ncL S ω)
    (hd : ω ^ Om 1 ∣ cdEta S μ) (hγ : γ < upsilon μ) (hs : SC s) (h1 : Om 1 < s)
    (h2 : s ≤ Om (1 + 1)) :
    upsilon (μ + γ) ≤ cdTheta S μ s ↔
      RgCov S (ConjT.Aη S (cdEta S μ)) (upsilon μ) s (ConjT.th S * γ) := by
  rw [rgUps_eq hR hγ.le]
  obtain ⟨-, -, hown⟩ := Rc.rcOwn hR.1 hω
  exact rgPsi_le_iff_cover (Ls.lsPv_range hR) hs h1 h2 (rgDvd_A hd) (rgD_le (rgGam_lt hR hγ)) hown

/-- **The covering form of the supply at `a`**: for every `γ < a`, a Range restart `μ` with `γ < ρ_μ < a`,
`ω^{Ω₁} ∣ η_μ`, and a strongly critical code `s ∈ (Ω₁, m_μ]` whose atoms cover `D = θ·γ`. -/
def RgCoverAt (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ω ^ Om 1 ∣ cdEta S μ ∧
    ∃ s, SC s ∧ Om 1 < s ∧ s ≤ cdCode S μ ∧
      RgCov S (ConjT.Aη S (cdEta S μ)) (upsilon μ) s (ConjT.th S * γ)

/-- **`RgCoverAt → Rc.RcReadAt`.** -/
theorem rgReadAt_of_cover {a : Ordinal.{0}} (h : RgCoverAt S a) : Rc.RcReadAt S a := by
  intro γ hγ
  obtain ⟨μ, hR, h1, h2, hd, s, hs, hs1, hsm, hc⟩ := h γ hγ
  refine ⟨μ, hR, h1, h2, hd, ?_⟩
  have hs2 : s ≤ Om (1 + 1) := (hsm.trans hR.2.2.2.le).trans (cdPp_lt_Om2 S).le
  rw [rgUps_eq hR h1.le]
  exact (rgPsi_le_cover (Ls.lsPv_range hR) hs hs1 hs2 (rgDvd_A hd) (rgD_le (rgGam_lt hR h1)) hc).trans
    (cdTheta_mono S μ hsm)

/-- **`RgCoverAt → Ra.RaSupAt`.** -/
theorem rgSupAt_of_cover {a : Ordinal.{0}} (h : RgCoverAt S a) : Ra.RaSupAt S a :=
  Rc.rcSupAt_of_readAt (rgReadAt_of_cover h)

/-- **`Ra.RaSupRead S k` gives `RgCoverAt` at `m*` and at every `L(n+1)`** (with `s = G_{k+1}`). -/
theorem rgCover_of_read {k : ℕ} (h : Ra.RaSupRead S k) :
    RgCoverAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, RgCoverAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  have key : ∀ μ γ, CdRange S μ → upsilon μ < Nc.ncL S ω → γ < upsilon μ →
      cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ω ^ Om 1 ∣ cdEta S μ ∧ ∃ s, SC s ∧ Om 1 < s ∧ s ≤ cdCode S μ ∧
        RgCov S (ConjT.Aη S (cdEta S μ)) (upsilon μ) s (ConjT.th S * γ) := by
    intro μ γ hR hω hγ hc
    have hd := Ls.lsDiv_of_code hc
    refine ⟨hd, Ls.lsG S (k + 1), Ls.lsG_SC _, Ls.lsG_Om1 _, by rw [hc]; exact le_self_add, ?_⟩
    refine (rgUps_le_iff_cover hR hω hd hγ (Ls.lsG_SC _) (Ls.lsG_Om1 _) (Ls.lsG_Om2 _)).1 ?_
    exact (upsilon_normal.strictMono.monotone (add_le_add le_rfl hγ.le)).trans (h μ hR hc)
  refine ⟨fun γ hγ => ?_, fun n γ hγ => ?_⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) k γ hγ
    exact ⟨μ, hR, h1, h2, key μ γ hR (h2.trans_le (Pp.ppL_mono zero_le)) h1 hc⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_L (S := S) n k γ hγ
    exact ⟨μ, hR, h1, h2, key μ γ hR (h2.trans (Pp.ppL_lt_omega n)) h1 hc⟩

/-- **The road with the supply at `m*` and every `L(n+1)` in the covering form** (`rgRoad`). -/
theorem rgRoad_cov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hc0 : RgCoverAt S (Nc.ncL S 0))
    (hcn : ∀ n : ℕ, RgCoverAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hpair : RgLwPair S)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rgRoad hU hO hL hV hVt hEQ htop (rgSupAt_of_cover hc0) (fun n => rgSupAt_of_cover (hcn n)) h0 hn
    hpair hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Rg
