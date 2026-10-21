import Googology.Trans.PoR.InaccPsi.R2.MxGam

/-!
# `MxEQtop` split at `θ`: below `θ` only the reading moves; the bound `Θ_λ(θ) ≤ υ_{λ+1}`

`B_n = Bc.bcB S n`, `θ = ψ_{Ω₂}(Ω_ω)` (`ConjT.th`), `A_η = Ω_ω + θ·η`, `ρ_λ = υ_λ = ψ_{Ω₁}(A_{η_λ})`, the hull
`H_λ = Cl(A_{η_λ}, ρ_λ)` (`Cd.cdHull`), `Θ_λ(m) = otp(H_λ ∩ m)`, `δ_λ = υ_{λ+ω+1}`, `r(λ) = k_λ(Θ_λ(m_λ))`.

* `mxOtp_le` (the order type below `m` of a set with a strictly increasing map into `X` is `≤ X`);
* `mxHull_sub0` (**`Cl(A, ψ_{Ω₁}(A)) ⊆ Cl(A, 0)`**, from `Cl(A, 0) ∩ Ω₁ = ψ_{Ω₁}(A)`);
* `mxTheta_le_succ` (**`Θ_λ(θ) ≤ υ_{λ+1}`**: `c ↦ ψ_{Ω₁}(A_η + c)` maps `H_λ ∩ θ` strictly increasingly into
  `ψ_{Ω₁}(A_η + θ) = υ_{λ+1}`), `mxTheta_lt_delta` (**`Θ_λ(m_λ) < δ_λ` for every code `m_λ ≤ θ`**);
* `MxThMove S` (a hypothesis name: **the reading moves**, `B_n(Θ_λ(m_λ)) = Θ_{λ'}(m_{λ'})`, at the long codes with
  `Γ_{Ω₁+1} < e(η_λ)` and `m_λ ≤ θ`), `MxEQth S` (`MwEQtop` at the long codes `m_λ > θ`);
  `mxEQtop_read` (**`MxThMove` and `MxEQth` give `MxEQtop`**, given `L(ω+1) ≤ ν_C`), `mxThMove_of_mw`,
  `mxEQth_of_mw` (both follow from `MwEQtop`, so neither is stronger), `mxRoad3`.

No new axiom.  New definitions: the hypothesis names `MxThMove`, `MxEQth`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- The order type below `m` of a set `C` with a strictly increasing map `f` into `X` is at most `X`. -/
theorem mxOtp_le (C : Set Ordinal.{0}) (m X : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (hmono : ∀ c ∈ C, c < m → ∀ c' ∈ C, c' < c → f c' < f c) (hX : ∀ c ∈ C, c < m → f c < X) :
    cdOtp C m ≤ X := by
  have key : ∀ c, c ∈ C → c < m → cdOtp C c ≤ f c := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc hcm
    rw [cdOtp_eq]
    refine ciSup_le' fun c' => ?_
    split_ifs with h
    · exact Order.add_one_le_of_lt ((IH c'.1 c'.2 h (c'.2.trans hcm)).trans_lt (hmono c hc hcm c'.1 h c'.2))
    · exact zero_le
  rw [cdOtp_eq]
  refine ciSup_le' fun c => ?_
  split_ifs with h
  · exact Order.add_one_le_of_lt ((key c.1 h c.2).trans_lt (hX c.1 h c.2))
  · exact zero_le

/-- **`Cl(A, ψ_{Ω₁}(A)) ⊆ Cl(A, 0)`.** -/
theorem mxHull_sub0 {A x : Ordinal.{0}} (h : x ∈ S.CSet A (S.psi A (Om 1))) : x ∈ S.CSet A 0 := by
  induction h with
  | @small x hx =>
    have : x ∈ S.CSet A 0 ∩ Iio (Om 1) := by
      rw [CSet_inter_Om1]; exact hx
    exact this.1
  | zero => exact CSet.zero_mem _ _
  | inacc n => exact CSet.I_mem _ _ n
  | inaccW => exact CSet.Iw_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | @coll π e hπ _ _ ihπ ihe => exact CSet.psi_mem e.2 hπ ihπ ihe

/-- **`Θ_λ(θ) ≤ υ_{λ+1}`** at a restart `λ` with `υ_λ < L(n+2)`. -/
theorem mxTheta_le_succ {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) : cdTheta S l (ConjT.th S) ≤ upsilon (l + 1) := by
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  obtain ⟨hg, hιl, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  have hsucc : upsilon (l + 1) = S.psi (A + ConjT.th S) (Om 1) := by
    rw [← hιl, ← Bt.iota_good hg, Bt.ups_iota S (η + 1), ← ConjT.A_succ]
  rw [hsucc]
  unfold cdTheta cdHull
  rw [← hη_def, ← hA_def, ← hρ]
  have hmem : ∀ c, c ∈ S.CSet A (S.psi A (Om 1)) → ∀ d, A ≤ d →
      A + c ∈ S.CSet d (S.psi d (Om 1)) := by
    intro c hc d hd
    exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hd).2 hown)
      (CSet_mono hd zero_le (mxHull_sub0 hc))
  refine mxOtp_le _ _ _ (fun c => S.psi (A + c) (Om 1)) ?_ ?_
  · intro c _ _ c' hc' hc'c
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hc'c) (hmem c' hc' _ le_self_add)
  · intro c hc hcθ
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hcθ) (hmem c hc _ le_self_add)

/-- **`Θ_λ(m_λ) < δ_λ`** for every code `m_λ ≤ θ` (`υ_λ < L(n+2)`). -/
theorem mxTheta_lt_delta {n : ℕ} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (hθ : cdCode S l ≤ ConjT.th S) :
    cdTheta S l (cdCode S l) < cdDelta l := by
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  exact ((cdTheta_mono S l hθ).trans (mxTheta_le_succ hl h2)).trans_lt hu1

/-- **The reading moves** at the long codes with `Γ_{Ω₁+1} < e(η_λ)` and `m_λ ≤ θ`:
`B_n(Θ_λ(m_λ)) = Θ_{λ'}(m_{λ'})`. -/
def MxThMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l ≤ ConjT.th S →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- `MwEQtop` at the long codes `m_λ > θ`. -/
def MxEQth (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ConjT.th S < cdCode S l → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`MxThMove` and `MxEQth` give `MxEQtop`**, given `L(ω+1) ≤ ν_C`. -/
theorem mxEQtop_read (hν : Nc.ncL S (ω + 1) ≤ nuC) (h1 : MxThMove S) (h2 : MxEQth S) : MxEQtop S := by
  intro n l l' hR hc hr hl' hB hm he
  by_cases hθ : cdCode S l ≤ ConjT.th S
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hρ2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
    have hΘδ := mxTheta_lt_delta hR.1 hρ2 hθ
    have hΘ := h1 n l l' hR hc hr hl' hB hm he hθ
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← mvk_move hν hR.1 hl' hc hδr hB hΘδ, hΘ]
  · exact h2 n l l' hR hc hr hl' hB hm (not_le.1 hθ)

/-- `MwEQtop` gives `MxThMove` (given `L(ω+1) ≤ ν_C`; `k_{λ'}` is injective). -/
theorem mxThMove_of_mw (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : MwEQtop S) : MxThMove S := by
  intro n l l' hR hc hr hl' hB hm he hθ
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hρ2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hΘδ := mxTheta_lt_delta hR.1 hρ2 hθ
  have e1 := h n l l' hR hc hr hl' hB hm he.le
  change Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) at e1
  rw [← mvk_move hν hR.1 hl' hc hδr hB hΘδ] at e1
  exact (cdk_inj l').1 e1

/-- `MwEQtop` gives `MxEQth`. -/
theorem mxEQth_of_mw (h : MwEQtop S) : MxEQth S := by
  intro n l l' hR hc hr hl' hB hm hθ
  have hGθ : ggGam ≤ ConjT.th S := ggGam_le (ConjT.SC_th S) (psiS_bounds (S := S) (Om ω) 1).1
  exact h n l l' hR hc hr hl' hB hm (hGθ.trans (hθ.le.trans (cdCodeOf_le_exp S _)))

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → MxThMove` and `L(ω+1) ≤ ν_C → MxEQth`.** -/
theorem mxRoad3 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMove S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad2 hU hO hL hV hN hlh fun hν => mxEQtop_read hν (hth hν) (hhi hν)

end Googology.Trans.PoR.InaccPsi.R2.Mx
