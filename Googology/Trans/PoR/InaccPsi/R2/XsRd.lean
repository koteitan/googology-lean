import Googology.Trans.PoR.InaccPsi.R2.WrMid
import Googology.Trans.PoR.InaccPsi.R2.RqFam

/-!
# The readings above `M_W`: the bases `β_γ = Ω_ω + Ω₂·γ` and their blocks

`Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`), `A = A_{η_λ}` (own, `ψ_{Ω₁}(A) = ρ_λ`), `θ = ψ_{Ω₂}(Ω_ω)`,
`M_W = ψ_{Ω₂}(Ω_ω + Ω₂)`, `β_γ = Ω_ω + Ω₂·γ` (`xsB`), `F^β = ψ_{Ω₂}(β + Ω₂)` (`Ld.ldTop`).

* `XsOwn S γ` (`γ < ψ_{Ω₂}(β_γ)`), `xsK` (`K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(β_{K_j})`), `xsK_own` (**every `γ < K_j` is
  own**: the hypothesis of the readings is satisfiable on an initial segment of the codes that passes `M_W`);
* `xsB_own`, `xsB_dvd`, `xsB_hull`, `xsB_A` (the base data of `Ld.ldBlk_step` at `β_γ`);
* `xsA_win` (**in a window `Ω_ω + Ω₂·Ω₂ ≤ A`**);
* `xsBase` (**THE BASE READINGS ABOVE `θ`**: `Θ(ψ_{Ω₂}(Ω_ω + Ω₂·γ)) = ψ_{Ω₁}(A + θ + Ω₁·Θ γ)` for every code
  `γ < Ω₂` all of whose codes `γ' ≤ γ` are own; one induction on `γ`: `Wl.wlThVal` at `0`, `Ld.ldBlk_next` at
  successors, a direct cofinality argument at limits);
* `xsBlk` (**THE BLOCK LAW ABOVE `M_W`**: `Θ(ψ_{Ω₂}(Ω_ω + Ω₂·γ + c)) = ψ_{Ω₁}(A + θ + Ω₁·Θ γ + Θ c)` for every code
  `c < F^{β_γ}`), `xsMW` (`γ = 1`: `Θ(M_W) = ψ_{Ω₁}(A + θ + Ω₁)`, agreeing with `Wr.wrThMW`).

No new axiom.  New definitions: `xsB`, `XsOwn`, `xsK` (auxiliary).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-- The base `β_γ = Ω_ω + Ω₂·γ`. -/
noncomputable def xsB (γ : Ordinal.{0}) : Ordinal.{0} := Om ω + Om (1 + 1) * γ

/-- `γ` is own for its base: `γ < ψ_{Ω₂}(β_γ)`. -/
def XsOwn (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop := γ < S.psi (xsB γ) (Om (1 + 1))

/-- `K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(β_{K_j})`. -/
noncomputable def xsK (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => 1
  | j + 1 => S.psi (xsB (xsK S j)) (Om (1 + 1))

theorem xsB_zero : xsB 0 = Om ω := by unfold xsB; rw [mul_zero, add_zero]

theorem xsB_one : xsB 1 = Om ω + Om (1 + 1) := by unfold xsB; rw [mul_one]

theorem xsB_succ (γ : Ordinal.{0}) : xsB γ + Om (1 + 1) = xsB (γ + 1) := by
  unfold xsB; rw [mul_add_one, add_assoc]

theorem xsB_mono {γ γ' : Ordinal.{0}} (h : γ ≤ γ') : xsB γ ≤ xsB γ' :=
  (add_le_add_iff_left _).2 (mul_le_mul_right h _)

theorem xsB_lt {γ γ' : Ordinal.{0}} (h : γ < γ') : xsB γ < xsB γ' :=
  (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 h)

theorem xsW2W_lt : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om ω :=
  (Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW ldOm2_lt_OmW

theorem xsW2_eq : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = ω ^ (Om (1 + 1) + Om (1 + 1)) := by
  rw [opow_add, gg_SC_eps ldOm2_SC]

theorem xsW2_lt : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < Om ω := by
  rw [xsW2_eq]
  conv_rhs => rw [← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 xsW2W_lt

theorem xsW2_dvd : ω ^ (Om (1 + 1 : Ordinal.{0}) + Om (1 + 1)) ∣ Om ω := by
  conv_rhs => rw [← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
  exact opow_dvd_opow ω xsW2W_lt.le

theorem xsB_dvd (γ : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) ∣ xsB γ :=
  dvd_add rnOm2_dvd_OmW (dvd_mul_right _ _)

theorem xsOm1_mem (a b : Ordinal.{0}) : Om (1 : Ordinal.{0}) ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem a b)

theorem xsMulW_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : Om (1 + 1) * x ∈ S.CSet a b :=
  ldMulK_mem ldOm2_SC (mxOm2_mem a b) hx

theorem xsMulO_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : Om 1 * x ∈ S.CSet a b :=
  ldMulK_mem Ph.ph_SC_Om1 (xsOm1_mem a b) hx

theorem xsB_mem {a b γ : Ordinal.{0}} (hγ : γ ∈ S.CSet a b) : xsB γ ∈ S.CSet a b :=
  CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (xsMulW_mem hγ)

/-- The base `β_γ` is own for every offset `d`, when `γ` is own. -/
theorem xsB_own {γ : Ordinal.{0}} (h : XsOwn S γ) :
    ∀ d, d ≤ Om (1 + 1) → xsB γ ∈ S.CSet (xsB γ + d) (S.psi (xsB γ + d) (Om (1 + 1))) := fun _ _ =>
  xsB_mem (CSet.of_lt (h.trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1))

theorem xsB_A {γ A : Ordinal.{0}} (hγ2 : γ < Om (1 + 1)) (hAb : Om ω + Om (1 + 1) * Om (1 + 1) ≤ A) :
    xsB γ + Om (1 + 1) < A := by
  rw [xsB_succ]
  refine lt_of_lt_of_le ?_ hAb
  have h1 : γ + 1 < Om (1 + 1) := ldOm2_SC.isPrincipal hγ2 (gg_one_lt_of_SC ldOm2_SC)
  exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 h1)

/-! ## The own codes -/

theorem xsK_lt_Om2 : ∀ j, xsK S j < Om (1 + 1)
  | 0 => gg_one_lt_of_SC ldOm2_SC
  | _ + 1 => psi_lt (InR_Om_succ 1) _

/-- **Every `γ < K_j` is own.** -/
theorem xsK_own : ∀ j, ∀ γ, γ < xsK S j → XsOwn S γ
  | 0, γ, h => by
    have h0 : γ = 0 := Order.lt_one_iff.1 h
    subst h0
    unfold XsOwn; rw [xsB_zero]; exact (ConjT.SC_th S).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (xsK S j) with h' | h'
    · exact xsK_own j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) (xsB_mono h')).1

theorem xsK_one : xsK S 1 = rnMW S := by
  show S.psi (xsB 1) (Om (1 + 1)) = _
  rw [xsB_one]; rfl


/-! ## The window bound -/

/-- **`Ω_ω + Ω_ω ≤ A_{η_λ}`** at every restart with own `A_{η_λ}` and `P(Ω_ω) ≤ ρ_λ` (`η_λ < Ω_ω` would give
`ρ_λ = P(η_λ) < P(Ω_ω)`). -/
theorem xsA_ge {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (h0 : Pv S (Om ω) ≤ upsilon l) : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  rcases lt_or_ge (cdEta S l) (Om ω) with hη | hη
  · exfalso
    have hlt : ConjT.Aη S (cdEta S l) < ConjT.Aη S (Om ω) := by
      unfold ConjT.Aη; exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (Sf.sfTh_pos S)).2 hη)
    have h2 : Pv S (cdEta S l) < Pv S (Om ω) :=
      psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 hown)
    rw [hpv] at h2
    exact absurd (h2.trans_le h0) (lt_irrefl _)
  · unfold ConjT.Aη
    exact (add_le_add_iff_left _).2 (hη.trans (le_mul_right _ (Sf.sfTh_pos S)))

theorem xsAb_of {A : Ordinal.{0}} (h : Om ω + Om ω ≤ A) : Om ω + Om (1 + 1) * Om (1 + 1) ≤ A :=
  ((add_le_add_iff_left _).2 xsW2_lt.le).trans h

/-- `P(Ω_ω) = L(0) ≤ L(n+1)`. -/
theorem xsL0_le (n : ℕ) : Pv S (Om ω) ≤ Bc.bcC S n := by
  have h0 : Nc.ncL S ((0 : ℕ) : Ordinal.{0}) ≤ Bc.bcC S n := Qq.qqL_mono (S := S) (Nat.zero_le (n + 1))
  rwa [Nat.cast_zero, Lw.lw_L_eq, mul_zero, add_zero] at h0

/-- **In a window, `Ω_ω + Ω_ω ≤ A_{η_λ}`.** -/
theorem xsA_win {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l) := by
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  exact xsA_ge hl hX hown ((xsL0_le n).trans h1.le)

/-! ## The base readings -/

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAb : Om ω + Om (1 + 1) * Om (1 + 1) ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAb

theorem xsWA : Om ω < ConjT.Aη S (cdEta S l) + ConjT.th S := by
  unfold ConjT.Aη
  exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ (Sf.sfTh_pos S))

theorem xsAθ_mem (x : Ordinal.{0}) :
    ConjT.Aη S (cdEta S l) + ConjT.th S ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + x)
      (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + x) (Om 1)) :=
  CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown)
    (ConjT.th_mem (S := S) ((xsWA hl hX hown hAb).trans_le le_self_add))

/-- The image argument `A + θ + Ω₁·Θ γ` is own once its reading is the reading of `ψ_{Ω₂}(β_γ)`. -/
theorem xsOwnT {γ : Ordinal.{0}} (hγ : GxCl (upsilon l) (ldAtR S l) γ) (ho : XsOwn S γ)
    (hb : gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) :
    ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ ∈
      S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
  have ht : gxTh (upsilon l) (ldAtR S l) γ <
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) := by
    rw [← hb]; exact gxTh_lt hγ ho
  exact CSet.add_mem (xsAθ_mem hl hX hown hAb _) (xsMulO_mem (CSet.of_lt ht))

/-- **THE BASE READINGS ABOVE `θ`**: `Θ(ψ_{Ω₂}(Ω_ω + Ω₂·γ)) = ψ_{Ω₁}(A + θ + Ω₁·Θ γ)` for every code `γ < Ω₂` whose
codes `γ' ≤ γ` are own. -/
theorem xsBase : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
    (∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → XsOwn S γ') →
    gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ) (Om (1 + 1))) =
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  have hθ := Wl.wlThVal hl hX hown hρ
  have hW2 : (0 : Ordinal.{0}) < Om (1 + 1) * Om (1 + 1) := mul_pos ldOm2_SC.1 ldOm2_SC.1
  have hθat : ConjT.th S ∈ ldAtR S l :=
    ⟨Om ω, ConjT.OmW_mem (S := S) _ _, (lt_add_of_pos_right _ hW2).trans_le hAb, rfl⟩
  have hΩ0 : (0 : Ordinal.{0}) < Om 1 := Om_pos one_ne_zero
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγ2 hown'
  have hoγ := hown' γ hγ le_rfl
  have hβH : xsB γ ∈ cdHull S l := xsB_mem ((ldHull_iff hl hX hγ2).2 hγ)
  have hβA := xsB_A hγ2 hAb
  have hsat : S.psi (xsB γ) (Om (1 + 1)) ∈ ldAtR S l := ldBlk_base_atom hβH hβA
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ0, rfl⟩ | hlim
  · subst h0
    rw [xsB_zero, gxTh_zero, mul_zero, add_zero]
    exact hθ
  · rw [Order.succ_eq_add_one] at hγ hγ2 hown' IH ⊢
    have hγ02 : γ0 < Om (1 + 1) := (lt_add_one γ0).trans hγ2
    have hγ0c : GxCl (upsilon l) (ldAtR S l) γ0 := Rq.rqCode_pred hl hX hγ hγ2
    have hIH := IH γ0 (lt_add_one γ0) hγ0c hγ02 (fun γ' hγ' h' => hown' γ' hγ' (h'.trans le_self_add))
    have ho0 := hown' γ0 hγ0c le_self_add
    have hÂ := xsOwnT hl hX hown hAb hγ0c ho0 hIH
    have hnext := ldBlk_next hl hX (xsB_own ho0) (xsB_dvd γ0) (xsB_mem ((ldHull_iff hl hX hγ02).2 hγ0c))
      (xsB_A hγ02 hAb) hÂ hIH
    unfold ldTop at hnext
    rw [xsB_succ] at hnext
    rw [hnext, Rq.rqTh_succ hl hX hγ0c, mul_add_one, ← add_assoc]
  · have hγ0 : γ ≠ 0 := hlim.ne_bot
    obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsat
    have hWβ : Om ω < xsB γ := by
      have := xsB_lt (pos_iff_ne_zero.2 hγ0); rwa [xsB_zero] at this
    have hθs : ConjT.th S < S.psi (xsB γ) (Om (1 + 1)) :=
      psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) hWβ (ConjT.OmW_mem (S := S) _ _)
    -- the successor bases below `γ`
    have hstep : ∀ q, GxCl (upsilon l) (ldAtR S l) q → q < γ →
        gxTh (upsilon l) (ldAtR S l) (S.psi (xsB (q + 1)) (Om (1 + 1))) =
          S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * (gxTh (upsilon l) (ldAtR S l) q + 1)) (Om 1) ∧
        gxTh (upsilon l) (ldAtR S l) (S.psi (xsB (q + 1)) (Om (1 + 1))) <
          gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ) (Om (1 + 1))) ∧
        gxTh (upsilon l) (ldAtR S l) q + 1 < gxTh (upsilon l) (ldAtR S l) γ ∧
        gxTh (upsilon l) (ldAtR S l) q + 1 <
          S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * (gxTh (upsilon l) (ldAtR S l) q + 1)) (Om 1) := by
      intro q hq hqγ
      have hq1γ : q + 1 < γ := by
        have := hlim.succ_lt hqγ; rwa [Order.succ_eq_add_one] at this
      have hq12 : q + 1 < Om (1 + 1) := hq1γ.trans hγ2
      have hq1c : GxCl (upsilon l) (ldAtR S l) (q + 1) := Rq.rqCode_succ hl hX hq hq12
      have hIH := IH (q + 1) hq1γ hq1c hq12 (fun γ' hγ' h' => hown' γ' hγ' (h'.trans hq1γ.le))
      rw [Rq.rqTh_succ hl hX hq] at hIH
      have hq1H : xsB (q + 1) ∈ cdHull S l := xsB_mem ((ldHull_iff hl hX hq12).2 hq1c)
      have hat := ldBlk_base_atom hq1H (xsB_A hq12 hAb)
      have hlt : S.psi (xsB (q + 1)) (Om (1 + 1)) < S.psi (xsB γ) (Om (1 + 1)) :=
        psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) (xsB_lt hq1γ) (xsB_mem (CSet.of_lt (hq1γ.trans hoγ)))
      have hΘq := gxTh_lt hq1c hq1γ
      rw [Rq.rqTh_succ hl hX hq] at hΘq
      have ho1 : XsOwn S (q + 1) := hown' (q + 1) hq1c hq1γ.le
      have hΘo := gxTh_lt hq1c ho1
      rw [Rq.rqTh_succ hl hX hq, hIH] at hΘo
      exact ⟨hIH, hTs _ hat hlt, hΘq, hΘo⟩
    have hθΘ : gxTh (upsilon l) (ldAtR S l) (ConjT.th S) <
        gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ) (Om (1 + 1))) := hTs _ hθat hθs
    apply le_antisymm
    · -- the upper bound
      have hΘγ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
        have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hγ0)
        rwa [gxTh_zero] at this
      have hAθlt : S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S) (Om 1) <
          S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) :=
        psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right _ (mul_pos hΩ0 hΘγ0)) (xsAθ_mem hl hX hown hAb _)
      have hρθ : upsilon l < gxTh (upsilon l) (ldAtR S l) (ConjT.th S) :=
        (ldAtom_ge hρSC hρ1 hAt hθat).2.1
      refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρθ.trans (hθ ▸ hAθlt)) ?_
      intro t ht hts
      obtain ⟨a, ha, -, rfl⟩ := ht
      rcases lt_or_ge a (Om ω) with haW | haW
      · have h1 : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤
            gxTh (upsilon l) (ldAtR S l) (ConjT.th S) :=
          gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haW.le).1
        rw [hθ] at h1
        exact h1.trans_lt hAθlt
      · obtain ⟨d, rfl⟩ := exists_add_of_le haW
        have hdγ : d < Om (1 + 1) * γ := by
          by_contra hc
          push Not at hc
          exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 hc)).1)
        have hdP : d < ω ^ (Om (1 + 1) + Om (1 + 1)) := by
          rw [← xsW2_eq]; exact hdγ.trans ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hγ2)
        have hmod : (Om ω + d) % ω ^ (Om (1 + 1) + Om (1 + 1)) = d := by
          obtain ⟨k, hk⟩ := xsW2_dvd
          rw [hk, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdP]
        have hdmem : d ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
          have := leModP_mem (S := S) (Om (1 + 1) + Om (1 + 1)) ha; rwa [hmod] at this
        have hqmem : d / Om (1 + 1) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := by
          have := leDivOp_mem (S := S) (K := Om (1 + 1)) (dvd_refl _) hdmem hdP
          rwa [gg_SC_eps ldOm2_SC] at this
        have hqγ : d / Om (1 + 1) < γ := (Ordinal.div_lt ldOm2_SC.1.ne').2 hdγ
        have hq2 : d / Om (1 + 1) < Om (1 + 1) := hqγ.trans hγ2
        have hqc : GxCl (upsilon l) (ldAtR S l) (d / Om (1 + 1)) := (ldHull_iff hl hX hq2).1 hqmem
        obtain ⟨hIHq, -, hq1, -⟩ := hstep _ hqc hqγ
        have hd1 : d < Om (1 + 1) * (d / Om (1 + 1) + 1) := by
          have := Ordinal.lt_mul_succ_div d ldOm2_SC.1.ne'; rwa [Order.succ_eq_add_one] at this
        have hle : S.psi (Om ω + d) (Om (1 + 1)) ≤ S.psi (xsB (d / Om (1 + 1) + 1)) (Om (1 + 1)) :=
          (psi_mono (S := S) (InR_Om_succ 1) ((add_lt_add_iff_left _).2 hd1).le).1
        refine (gxTh_mono hle).trans_lt ?_
        rw [hIHq]
        have hlt' : ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * (gxTh (upsilon l) (ldAtR S l) (d / Om (1 + 1)) + 1) <
            ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ :=
          (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hΩ0).2 hq1)
        have hmem1 : gxTh (upsilon l) (ldAtR S l) (d / Om (1 + 1)) + 1 <
            S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) :=
          (hstep _ hqc hqγ).2.2.2.trans_le (psi_mono (S := S) Low.InR_Om_one hlt'.le).1
        exact psi_lt_psi_of_mem Low.InR_Om_one hlt'
          (CSet.add_mem (xsAθ_mem hl hX hown hAb _) (xsMulO_mem (CSet.of_lt hmem1)))
    · -- the lower bound
      refine ldPsi1_le hTSC fun e he _ => ?_
      rcases le_or_gt e (ConjT.Aη S (cdEta S l) + ConjT.th S) with h | h
      · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one h).1 ?_
        rw [← hθ]; exact hθΘ
      · obtain ⟨f, rfl⟩ := exists_add_of_le h.le
        have hf : f < Om 1 * gxTh (upsilon l) (ldAtR S l) γ := (add_lt_add_iff_left _).1 he
        have hz : f / Om 1 < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.div_lt hΩ0.ne').2 hf
        obtain ⟨q, hqc, hqγ, hqz⟩ := gxTh_onto hz
        obtain ⟨hIHq, hlt, -, -⟩ := hstep q hqc hqγ
        have hf1 : f < Om 1 * (gxTh (upsilon l) (ldAtR S l) q + 1) := by
          have := Ordinal.lt_mul_succ_div f hΩ0.ne'; rwa [Order.succ_eq_add_one, ← hqz] at this
        refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_lt_add_iff_left _).2 hf1).le).1 ?_
        rw [← hIHq]; exact hlt

/-- **THE BLOCK LAW ABOVE `M_W`**: `Θ(ψ_{Ω₂}(Ω_ω + Ω₂·γ + c)) = ψ_{Ω₁}(A + θ + Ω₁·Θ γ + Θ c)` for every code
`c < ψ_{Ω₂}(Ω_ω + Ω₂·(γ+1))`, for every code `γ < Ω₂` whose codes `γ' ≤ γ` are own. -/
theorem xsBlk {γ : Ordinal.{0}} (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγ2 : γ < Om (1 + 1))
    (hown' : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → XsOwn S γ') :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (xsB γ) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (xsB γ + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ +
          gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hb := xsBase hl hX hown hAb γ hγ hγ2 hown'
  have ho := hown' γ hγ le_rfl
  exact ldBlk_step hl hX (xsB_own ho) (xsB_dvd γ) (xsB_mem ((ldHull_iff hl hX hγ2).2 hγ)) (xsB_A hγ2 hAb)
    (xsOwnT hl hX hown hAb hγ ho hb) hb

/-- `γ = 1`: `Θ(M_W) = ψ_{Ω₁}(A + θ + Ω₁)` (agrees with `Wr.wrThMW`). -/
theorem xsMW : gxTh (upsilon l) (ldAtR S l) (rnMW S) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h12 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hK2 : (1 : Ordinal.{0}) < xsK S 2 :=
    (gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1
  have h := xsBase hl hX hown hAb 1 h1c h12 (fun γ' _ h' => xsK_own 2 γ' (h'.trans_lt hK2))
  rw [gxTh_small (gg_one_lt_of_SC hρSC).le, mul_one, xsB_one] at h
  exact h

end Read

end Googology.Trans.PoR.InaccPsi.R2.Xs
