import Googology.Trans.PoR.InaccPsi.R2.LdBlkW

/-!
# `MxEQth` split at `θ·ω`: below it only the reading moves (`Θ_λ(m_λ) < δ_λ`), above it EQ

`B_n = Bc.bcB S n`, `θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `ρ_λ = ψ_{Ω₁}(A_{η_λ})`, `δ_λ = υ_{λ+ω+1}`,
`Θ_λ(m) = otp(H_λ ∩ m)`, `r(λ) = k_λ(Θ_λ(m_λ))`, `F_ω = ψ_{Ω₂}(Ω₂·ω)` (`R2.LdBlkW`).

* `ldIota_add_le` (`ι(η + ζ) ≤ ι(η) + ζ`), `ldTheta_le_psi` (**`Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)` for every `m`**:
  `c ↦ ψ_{Ω₁}(A + c)` maps `H_λ ∩ m` strictly increasingly into it), `ldTheta_lt_delta` (**`Θ_λ(m) < δ_λ` for every
  `m ≤ θ·ω`**: `ψ_{Ω₁}(A + θ·ω) = υ_{ι(η_λ+ω)} ≤ υ_{λ+ω}`);
* `LdThMoveR S` (a hypothesis name): **the reading moves `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at the codes
  `F_ω ≤ m_λ ≤ θ·ω`**; `LdEQhi S`: `MxEQth` at the codes `m_λ > θ·ω`;
* `ldThMoveQ_of_R`, `ldEQth_of_R` (**`LdThMoveR` and `LdEQhi` give `LdThMoveQ` and `MxEQth`**, given
  `L(ω+1) ≤ ν_C`; on `(θ, θ·ω]` by `Mv.mvk_move`), `ldThMoveR_of`, `ldEQhi_of` (**`MxThMoveW` and `MxEQth` give
  `LdThMoveR` and `LdEQhi`**, so neither is stronger), `ldRoadR` (**the road**).

No new axiom.  New definitions: the hypothesis names `LdThMoveR`, `LdEQhi`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- `ι(η + ζ) ≤ ι(η) + ζ`. -/
theorem ldIota_add_le (η : Ordinal.{0}) : ∀ ζ : Ordinal.{0}, Bt.iota S (η + ζ) ≤ Bt.iota S η + ζ := by
  intro ζ
  induction ζ using Ordinal.limitRecOn with
  | zero => rw [add_zero, add_zero]
  | add_one ζ ih =>
    rw [← add_assoc, ← add_assoc]
    exact (Bt.iota_succ_le (η + ζ)).2.trans (add_le_add ih le_rfl)
  | limit ζ hζ ih =>
    rw [Bt.iota_limit (isSuccLimit_add η hζ)]
    refine ciSup_le' fun e => ?_
    rcases lt_or_ge e.1 η with h | h
    · exact (Bt.iota_mono η e.1 h.le).trans le_self_add
    · obtain ⟨ζ', hζ'⟩ := exists_add_of_le h
      have hζ'ζ : ζ' < ζ := by
        have := e.2
        rw [hζ'] at this
        exact (add_lt_add_iff_left η).1 this
      rw [hζ']
      exact (ih ζ' hζ'ζ).trans ((add_le_add_iff_left _).2 hζ'ζ.le)

/-- **`Θ_λ(m) ≤ ψ_{Ω₁}(A_{η_λ} + m)`** for every `m`. -/
theorem ldTheta_le_psi {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (m : Ordinal.{0}) : cdTheta S l m ≤ S.psi (ConjT.Aη S (cdEta S l) + m) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  unfold cdTheta cdHull
  rw [← hA, ← hρ]
  have hmem : ∀ c, c ∈ S.CSet A (S.psi A (Om 1)) → ∀ d, A ≤ d → A + c ∈ S.CSet d (S.psi d (Om 1)) := by
    intro c hc d hd
    exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hd).2 hown)
      (CSet_mono hd zero_le (mxHull_sub0 hc))
  refine mxOtp_le _ _ _ (fun c => S.psi (A + c) (Om 1)) ?_ ?_
  · intro c _ _ c' hc' hc'c
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hc'c) (hmem c' hc' _ le_self_add)
  · intro c hc hcm
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hcm) (hmem c hc _ le_self_add)

/-- **`Θ_λ(m) < δ_λ` for every `m ≤ θ·ω`.** -/
theorem ldTheta_lt_delta {l ηx m : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (hm : m ≤ ConjT.th S * ω) : cdTheta S l m < cdDelta l := by
  obtain ⟨-, hιl, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  refine (ldTheta_le_psi hl hX hown m).trans_lt ?_
  have hι : Bt.iota S (cdEta S l + ω) ≤ l + ω := by
    have := ldIota_add_le (S := S) (cdEta S l) ω
    rwa [hιl] at this
  have h1 : S.psi (ConjT.Aη S (cdEta S l) + m) (Om 1) ≤ upsilon (l + ω) := by
    calc S.psi (ConjT.Aη S (cdEta S l) + m) (Om 1)
          ≤ S.psi (ConjT.Aη S (cdEta S l + ω)) (Om 1) := by
            rw [Bt.A_add]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 hm)).1
      _ = upsilon (Bt.iota S (cdEta S l + ω)) := (Bt.ups_iota S _).symm
      _ ≤ upsilon (l + ω) := upsilon_normal.monotone hι
  exact h1.trans_lt (upsilon_normal.strictMono (lt_add_one _))

/-! ## The split of `MxEQth` -/

/-- **The reading moves at the codes `F_ω ≤ m_λ ≤ θ·ω`.** -/
def LdThMoveR (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ldFw S ≤ cdCode S l → cdCode S l ≤ ConjT.th S * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- `MxEQth` at the codes `m_λ > θ·ω`. -/
def LdEQhi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ConjT.th S * ω < cdCode S l → Bc.bcB S n (cdR S l) = cdR S l'

theorem ldTh_le_thw : ConjT.th S ≤ ConjT.th S * ω := le_mul_left _ omega0_pos

theorem ldTh_lt_thw : ConjT.th S < ConjT.th S * ω := by
  have h := (mul_lt_mul_iff_right₀ (sfTh_pos S)).2 one_lt_omega0
  rwa [mul_one] at h

theorem ldGam_lt_Fw : ggGam < ldFw S := by
  rw [mxGam_psi (S := S)]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (ldW2_eq ▸ opow_pos _ omega0_pos) (CSet.zero_mem _ _)

/-- The own argument at a restart of the range below `L(n+2)`. -/
theorem ldOwnA {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : upsilon l < Bc.bcC S (n + 1)) :
    upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) ∧
      ConjT.Aη S (cdEta S l) ∈
        S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  exact ⟨hX, sfOwn hg (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2⟩

/-- `LdThMoveR` gives `LdThMoveQ`. -/
theorem ldThMoveQ_of_R (h : LdThMoveR S) : LdThMoveQ S :=
  fun n l l' hR h1 hr hl' hB hm _ hθ hF => h n l l' hR h1 hr hl' hB hm hF (hθ.trans ldTh_le_thw)

/-- **`LdThMoveR` and `LdEQhi` give `MxEQth`** (given `L(ω+1) ≤ ν_C`). -/
theorem ldEQth_of_R (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : LdThMoveR S) (hhi : LdEQhi S) : MxEQth S := by
  intro n l l' hR h1 hr hl' hB hm hθ
  by_cases hw : cdCode S l ≤ ConjT.th S * ω
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
    obtain ⟨hX, hown⟩ := ldOwnA hR.1 h2
    have hΘδ := ldTheta_lt_delta hR.1 hX hown hw
    have hΘ := h n l l' hR h1 hr hl' hB hm ((ldFw_lt_th.trans hθ).le) hw
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ, hΘ]
  · exact hhi n l l' hR h1 hr hl' hB hm (not_le.1 hw)

/-- **`MxThMoveW` and `MxEQth` give `LdThMoveR`** (given `L(ω+1) ≤ ν_C`). -/
theorem ldThMoveR_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : MxThMoveW S) (hE : MxEQth S) : LdThMoveR S := by
  intro n l l' hR h1 hr hl' hB hm hF hw
  by_cases hθ : cdCode S l ≤ ConjT.th S
  · have he : ggGam < cdExp (cdEta S l) :=
      ldGam_lt_Fw.trans_le (hF.trans (cdCodeOf_le_exp S _))
    exact hW n l l' hR h1 hr hl' hB hm he hθ fun j => (ldKs_lt_Fw j).le.trans hF
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
    obtain ⟨hX, hown⟩ := ldOwnA hR.1 h2
    have hΘδ := ldTheta_lt_delta hR.1 hX hown hw
    have e1 := hE n l l' hR h1 hr hl' hB hm (not_le.1 hθ)
    change Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) at e1
    rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ] at e1
    exact (cdk_inj l').1 e1

/-- `MxEQth` gives `LdEQhi`. -/
theorem ldEQhi_of (hE : MxEQth S) : LdEQhi S :=
  fun n l l' hR h1 hr hl' hB hm hw => hE n l l' hR h1 hr hl' hB hm (ldTh_lt_thw.trans hw)

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LdThMoveR` and `L(ω+1) ≤ ν_C → LdEQhi`.** -/
theorem ldRoadR (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LdThMoveR S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LdEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad5 hU hO hL hV hN hlh (fun hν => ldThMoveW_of_Q (ldThMoveQ_of_R (hth hν)))
    (fun hν => ldEQth_of_R hν (hth hν) (hhi hν))

end Googology.Trans.PoR.InaccPsi.R2.Ld
