import Googology.Trans.PoR.InaccPsi.R2.RnRoad

/-!
# `Θ_λ(m) < δ_λ` up to `M_W = ψ_{Ω₂}(Ω_ω + Ω₂)`, and `Lj.LjEQhi` split at `M_W`

`θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = ψ_{Ω₂}(Ω_ω + 1)` (`Lj.ljThP`), `M_W = ψ_{Ω₂}(Ω_ω + Ω₂) = Ld.ldTop S Ω_ω` (`rnMW`),
`A = A_{η_λ}`, `δ_λ = υ_{λ+ω+1}`, `r(λ) = k_λ(Θ_λ(m_λ))`.

* `rnTheta_at` (**`Θ_λ(ψ_{Ω₂}(Ω_ω + c)) ≤ ψ_{Ω₁}(A + θ + 1 + Θ_λ(c))`** for every code `c < M_W`: by induction on `c`
  with `Ld.ldAtom_le`; the atoms below are `≤ θ` (read `≤ ψ_{Ω₁}(A + θ)` by `Ld.ldTheta_le_psi`) or
  `ψ_{Ω₂}(Ω_ω + c')` with `c' < c` (`Ld.ldBlk_cls` at the base `Ω_ω`));
* `rnTheta_MW` (**`Θ_λ(M_W) ≤ ψ_{Ω₁}(A + θ + Ω₁)`**), `rnTheta_lt_delta` (**`Θ_λ(m) < δ_λ` for every `m ≤ M_W`**:
  `ψ_{Ω₁}(A + θ + Ω₁) ≤ ψ_{Ω₁}(A_{η_λ+2}) ≤ υ_{λ+2}`).  So on `[θ⁺, M_W]` (all exponent codes `≤ M_W` and the first
  π-code `ψ_{Ω₂}(Ω_ω + θ·Ω₂) = M_W`) EQ needs no closed point past `δ_λ`, no gap calculus;
* `RnThMoveM S` (a hypothesis name): **the reading moves at the codes `θ⁺ ≤ m_λ ≤ M_W`**; `RnEQhi2 S`: **EQ at the
  codes `m_λ > M_W`**; `rnLjEQhi_of` (**`RnThMoveM` and `RnEQhi2` give `Lj.LjEQhi`**, given `L(ω+1) ≤ ν_C`, by
  `Mv.mvk_move`), `rnThMoveM_of`, `rnEQhi2_of`, `rnLjEQhi_iff` (**`LjEQhi ⇔ RnThMoveM ∧ RnEQhi2`**);
* `rnRoadB` (**the road** with `RnAtMove`, `RnThMoveM`, `RnEQhi2`).

No new axiom.  New definitions: `rnMW`, the hypothesis names `RnThMoveM`, `RnEQhi2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

/-- `M_W = ψ_{Ω₂}(Ω_ω + Ω₂)`. -/
noncomputable def rnMW (S : InaccSeq.{0}) : Ordinal.{0} := ldTop S (Om ω)

theorem rnOmW_own : ∀ d, d ≤ Om (1 + 1) →
    Om (ω : Ordinal.{0}) ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) :=
  fun _ _ => ConjT.OmW_mem S _ _

theorem rnOm2_dvd_OmW : Om (1 + 1 : Ordinal.{0}) ∣ Om ω := by
  rw [← gg_SC_eps ldOm2_SC, ← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
  exact opow_dvd_opow ω ldOm2_lt_OmW.le

theorem rnThP_le_MW : ljThP S ≤ rnMW S :=
  (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2
    (Order.one_le_iff_pos.2 ldOm2_SC.1))).1

section Bound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))

include hl hX hown

/-- **`Θ_λ(ψ_{Ω₂}(Ω_ω + c)) ≤ ψ_{Ω₁}(A + θ + 1 + Θ_λ(c))`** for every code `c < M_W`. -/
theorem rnTheta_at : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < rnMW S →
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) ≤
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hWA : Om ω ≤ A := le_self_add
  have hWAθ : Om ω < A + ConjT.th S := hWA.trans_lt (lt_add_of_pos_right A (sfTh_pos S))
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcM
  set X := S.psi (A + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c) (Om 1) with hX_def
  have hmemA : ∀ x, A ≤ x → A ∈ S.CSet x (S.psi x (Om 1)) := fun x hx =>
    (psi_mono (S := S) Low.InR_Om_one hx).2 hown
  have hAθX : A + ConjT.th S ∈ S.CSet (A + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c) X :=
    CSet.add_mem (hmemA _ (le_self_add.trans (le_self_add.trans le_self_add)))
      (ConjT.th_mem S (hWAθ.trans_le (le_self_add.trans le_self_add)))
  have hAθ_lt : S.psi (A + ConjT.th S) (Om 1) < X :=
    psi_lt_psi_of_mem Low.InR_Om_one ((lt_add_one _).trans_le le_self_add) hAθX
  have hρX : upsilon l < X := by
    rw [← hρ]
    exact lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one le_self_add).1 hAθ_lt
  refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) hρX fun t ht hts => ?_
  have htM : t < rnMW S := hts.trans_le (psi_mono (S := S) (InR_Om_succ 1)
    ((add_le_add_iff_left _).2 (hcM.trans (ldTop_lt_Om2 _)).le)).1
  rcases ldBlk_cls hl hX rnOmW_own rnOm2_dvd_OmW ht htM with htθ | ⟨c', hc', hc'M, rfl⟩
  · have hθ2 : t ≤ Om (1 + 1) := (htθ.trans (psi_lt (InR_Om_succ 1) _).le)
    rw [← ldTheta hl hX hθ2]
    refine ((ldTheta_le_psi hl hX hown t).trans ?_).trans_lt hAθ_lt
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 htθ)).1
  · have hc'c : c' < c := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 h)).1)
    have IH' := IH c' hc'c hc' hc'M
    have hΘlt : gxTh (upsilon l) (ldAtR S l) c' < gxTh (upsilon l) (ldAtR S l) c := gxTh_lt hc' hc'c
    have hlt : A + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c' <
        A + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left _).2 hΘlt
    have hc's : c' < S.psi (Om ω + c') (Om (1 + 1)) := ldTop_gt rnOmW_own rnOm2_dvd_OmW hc'M
    have hΘc'X : gxTh (upsilon l) (ldAtR S l) c' < X :=
      ((gxTh_lt hc' hc's).trans_le IH').trans_le (psi_mono (S := S) Low.InR_Om_one hlt.le).1
    refine IH'.trans_lt (psi_lt_psi_of_mem Low.InR_Om_one hlt ?_)
    exact CSet.add_mem (CSet.add_mem hAθX (CSet.one_mem _ _)) (CSet.of_lt hΘc'X)

/-- **`Θ_λ(M_W) ≤ ψ_{Ω₁}(A + θ + Ω₁)`.** -/
theorem rnTheta_MW :
    gxTh (upsilon l) (ldAtR S l) (rnMW S) ≤ S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hWA : Om ω ≤ A := le_self_add
  have hWAθ : Om ω < A + ConjT.th S := hWA.trans_lt (lt_add_of_pos_right A (sfTh_pos S))
  set Y := S.psi (A + ConjT.th S + Om 1) (Om 1) with hY_def
  have hAθY : A + ConjT.th S ∈ S.CSet (A + ConjT.th S + Om 1) Y :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown)
      (ConjT.th_mem S (hWAθ.trans_le le_self_add))
  have hAθ_lt : S.psi (A + ConjT.th S) (Om 1) < Y :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right _ (Om_pos one_ne_zero)) hAθY
  have hρY : upsilon l < Y := by
    rw [← hρ]
    exact lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one le_self_add).1 hAθ_lt
  refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) hρY fun t ht hts => ?_
  rcases ldBlk_cls hl hX rnOmW_own rnOm2_dvd_OmW ht hts with htθ | ⟨c', hc', hc'M, rfl⟩
  · have hθ2 : t ≤ Om (1 + 1) := (htθ.trans (psi_lt (InR_Om_succ 1) _).le)
    rw [← ldTheta hl hX hθ2]
    refine ((ldTheta_le_psi hl hX hown t).trans ?_).trans_lt hAθ_lt
    exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 htθ)).1
  · have IH' := rnTheta_at hl hX hown c' hc' hc'M
    have hc's : c' < S.psi (Om ω + c') (Om (1 + 1)) := ldTop_gt rnOmW_own rnOm2_dvd_OmW hc'M
    have hΘc'1 : gxTh (upsilon l) (ldAtR S l) c' < Om 1 :=
      ((gxTh_lt hc' hc's).trans_le IH').trans (psi_lt Low.InR_Om_one _)
    have h1c : 1 + gxTh (upsilon l) (ldAtR S l) c' < Om 1 :=
      Ph.ph_SC_Om1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)) hΘc'1
    have hlt : A + ConjT.th S + 1 + gxTh (upsilon l) (ldAtR S l) c' < A + ConjT.th S + Om 1 := by
      rw [add_assoc (A + ConjT.th S)]; exact (add_lt_add_iff_left _).2 h1c
    have hΘc'Y : gxTh (upsilon l) (ldAtR S l) c' < Y :=
      ((gxTh_lt hc' hc's).trans_le IH').trans_le (psi_mono (S := S) Low.InR_Om_one hlt.le).1
    refine IH'.trans_lt (psi_lt_psi_of_mem Low.InR_Om_one hlt ?_)
    exact CSet.add_mem (CSet.add_mem (CSet_mono le_rfl le_rfl hAθY) (CSet.one_mem _ _)) (CSet.of_lt hΘc'Y)

/-- **`Θ_λ(m) < δ_λ` for every `m ≤ M_W`.** -/
theorem rnTheta_lt_delta {m : Ordinal.{0}} (hm : m ≤ rnMW S) : cdTheta S l m < cdDelta l := by
  obtain ⟨-, hιl, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have h1 : cdTheta S l m ≤ S.psi (A + ConjT.th S + Om 1) (Om 1) := by
    refine (cdTheta_mono S l hm).trans ?_
    rw [ldTheta hl hX (show rnMW S ≤ Om (1 + 1) from (ldTop_lt_Om2 _).le)]
    exact rnTheta_MW hl hX hown
  have h2 : S.psi (A + ConjT.th S + Om 1) (Om 1) ≤ upsilon (l + 2) := by
    have hι : Bt.iota S (cdEta S l + 2) ≤ l + 2 := by
      have := ldIota_add_le (S := S) (cdEta S l) 2
      rwa [hιl] at this
    calc S.psi (A + ConjT.th S + Om 1) (Om 1) ≤ S.psi (ConjT.Aη S (cdEta S l + 2)) (Om 1) := by
          rw [Bt.A_add, add_assoc]
          refine (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 ?_)).1
          rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
          exact (add_le_add_iff_left _).2 (psiS_bounds (S := S) _ 1).1.le
      _ = upsilon (Bt.iota S (cdEta S l + 2)) := (Bt.ups_iota S _).symm
      _ ≤ upsilon (l + 2) := upsilon_normal.monotone hι
  refine (h1.trans h2).trans_lt (upsilon_normal.strictMono ?_)
  calc l + 2 < l + ω := (add_lt_add_iff_left l).2 (by exact_mod_cast natCast_lt_omega0 2)
    _ < l + ω + 1 := lt_add_one _

end Bound

/-! ## `LjEQhi` split at `M_W` -/

/-- **The reading moves at the codes `θ⁺ ≤ m_λ ≤ M_W`.** -/
def RnThMoveM (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ljThP S ≤ cdCode S l → cdCode S l ≤ rnMW S →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **EQ at the codes `m_λ > M_W`.** -/
def RnEQhi2 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    rnMW S < cdCode S l → Bc.bcB S n (cdR S l) = cdR S l'

/-- `Θ_λ(m_λ) < δ_λ` at a range restart with `m_λ ≤ M_W` below `L(n+2)`. -/
theorem rnTheta_lt_delta_R {n : ℕ} {l : Ordinal.{0}} (hR : CdRange S l) (hr : cdR S l < Bc.bcC S (n + 1))
    (hK : cdCode S l ≤ rnMW S) : cdTheta S l (cdCode S l) < cdDelta l := by
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hR.1 h2
  exact rnTheta_lt_delta hR.1 hX hown hK

/-- **`RnThMoveM` and `RnEQhi2` give `LjEQhi`** (given `L(ω+1) ≤ ν_C`). -/
theorem rnLjEQhi_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hQ : RnThMoveM S) (hE : RnEQhi2 S) : LjEQhi S := by
  intro n l l' hR h1 hr hl' hB hm hP
  by_cases hM : cdCode S l ≤ rnMW S
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hΘδ := rnTheta_lt_delta_R hR hr hM
    have hΘ := hQ n l l' hR h1 hr hl' hB hm hP hM
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ, hΘ]
  · exact hE n l l' hR h1 hr hl' hB hm (not_le.1 hM)

/-- **`LjEQhi` gives `RnEQhi2`.** -/
theorem rnEQhi2_of (h : LjEQhi S) : RnEQhi2 S :=
  fun n l l' hR h1 hr hl' hB hm hM => h n l l' hR h1 hr hl' hB hm (rnThP_le_MW.trans hM.le)

/-- **`LjEQhi` gives `RnThMoveM`** (given `L(ω+1) ≤ ν_C`): `k_{λ'}` is injective. -/
theorem rnThMoveM_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : LjEQhi S) : RnThMoveM S := by
  intro n l l' hR h1 hr hl' hB hm hP hM
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hΘδ := rnTheta_lt_delta_R hR hr hM
  have hEQ := h n l l' hR h1 hr hl' hB hm hP
  change Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) at hEQ
  rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ] at hEQ
  exact (cdk_inj l').1 hEQ

/-- **`LjEQhi ⇔ RnThMoveM ∧ RnEQhi2`** (given `L(ω+1) ≤ ν_C`). -/
theorem rnLjEQhi_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : LjEQhi S ↔ RnThMoveM S ∧ RnEQhi2 S :=
  ⟨fun h => ⟨rnThMoveM_of hν h, rnEQhi2_of h⟩, fun h => rnLjEQhi_of hν h.1 h.2⟩

/-- **The road with `RnAtMove`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rnRoadB (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rnRoadA hU hO hL hV hN hlh hat (fun hν => rnLjEQhi_of hν (hM hν) (hhi hν))

end Googology.Trans.PoR.InaccPsi.R2.Rn
