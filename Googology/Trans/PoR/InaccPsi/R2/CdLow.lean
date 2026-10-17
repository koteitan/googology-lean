import Googology.Trans.PoR.InaccPsi.R2.CdEnum

/-!
# CAP-0, CAP-1, and the lower bound `L(ω) ≤ ν_C` (NU-LOW″)

`m* = ψ_{Ω₁}(Ω_ω·2) = P(Ω_ω)` (`cdMstar`), the end of level 1; level 2 is `[m*, ψ_{Ω₁}(Ω_ω·3))`.
The **cap** of a restart `λ` with name `η_λ = η₀ + ω^{e_λ}` (`e_λ = cdExp η_λ`) is the next restart at the
depth of the last exponent, `P(η_λ + ω^{e_λ})` (`cdCapB`).  For an infinite `e_λ < Ω₂` the code is
`m_λ = e_λ` and this is the bound `H(η_λ + ω^{m_λ})` of CAP♯ of the corrected calculus; for a finite `e_λ` the
docs' restart is short (its reach is below the next restart `H(η_λ + ω²) ≤ H(η_λ + ω^{e_λ})`); for a
π-code (`e_λ ≥ Ω₂`) it is weaker than CAP♯ (`π_η < Ω₂ ≤ e_λ`).  (At the code `1`, `e_λ = 2`, the bound
`H(η_λ + ω^{m_λ}) = H(η_λ + ω)` would lie below `δ_λ` wherever `ι(η_λ + ω) = λ + ω`.)

* `CdCapAt S λ`: every `≤₁`-successor of `ρ_λ` is below the cap ("`ρ_λ` is not self-crossing");
* `CdCAP0 S` (**CAP-0**): every restart `λ ≥ B₀` of level 1 (`ρ_λ < m*`) satisfies `CdCapAt`;
* `CdCAP1 S X` (**CAP-1**): every restart `λ ≥ B₀` of level 2 with `ρ_λ < X` and code `m_λ < P'`
  satisfies `CdCapAt`;
* `CdCapV S λ` (**the cap of the predicted value**): `k_λ(Θ_λ(m_λ)) <` the cap;
* `CdCODES1 S`: every restart `λ ≥ B₀` of level 1 has code `m_λ < P'` (proved: `cdCODES1`).

Main statements:

* `cdLow` (**NU-LOW″**): CAP-0 and CAP-1 below `L(ω)` give `L(ω) ≤ ν_C`.  Proof: if `ν_C < L(ω)`, the
  first non-standard pair `ρ_λ <₂ ν_C` (`Lb.lbFirst`) has `≤₁`-predecessors `ρ_μ ≤₁ ν_C`, restarts `μ ≥ B₀`,
  cofinal below `ρ_λ`.  Write the least `η` with `ι(η) = λ` as `η₀ + ω^e` with `ω^e ∣ η₀` (`cdExp_decomp`);
  for `μ ∈ (ι(η₀), λ)` the name `η_μ` lies in `(η₀, η₀ + ω^e)`, so `η_μ + ω^{e_μ} < η₀ + ω^e` (`cdWin`)
  and the cap of `μ` is at most `ρ_λ < ν_C`; at level 2 the window also forces `m_μ < P'`
  (`cd_l2_contra`).  So `ρ_μ ≤₁ ν_C` breaks the cap of `μ`;
* `cdCapAt_of_upper`: UPPER and the cap of the value give the cap at `λ`;
* `cdCode_lt_level1`, `cdCODES1`, `cdRange_level1`: every restart of level 1 has code `< P'`, so every
  restart `λ ≥ B₀` of level 1 is in the range of ENUM-REACH;
* `cdCode_lt_level2`, `cdRange_iff_level2`: a restart `λ ≥ B₀` with `m* ≤ ρ_λ < L(ω)` is in the range iff
  it is none of the `L(k)` (whose codes are `P'`, `R2.CdCodes`);
* `cdCAP_of_enum`, `cdLow_enum`: UPPER on `[B₀, L(ω+1))` and the cap of the values below `L(ω)` give
  CAP-0, CAP-1 below `L(ω)`, hence `L(ω) ≤ ν_C`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- `m* = ψ_{Ω₁}(Ω_ω·2) = P(Ω_ω)`. -/
noncomputable abbrev cdMstar (S : InaccSeq.{0}) : Ordinal.{0} := Pv S (Om ω)

/-- The cap `P(η_λ + ω^{e_λ})` of a restart (`e_λ` the last exponent of its name). -/
noncomputable def cdCapB (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} :=
  Pv S (cdEta S l + ω ^ cdExp (cdEta S l))

/-- `ρ_λ` is not self-crossing: every `≤₁`-successor of `ρ_λ` is below the cap. -/
def CdCapAt (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := ∀ g, le1 (upsilon l) g → g < cdCapB S l

/-- **CAP-0** (from `B₀`): every restart of level 1 is not self-crossing. -/
def CdCAP0 (S : InaccSeq.{0}) : Prop :=
  ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → CdCapAt S l

/-- **CAP-1** (from `B₀`, below `X`): every restart of level 2 with code `< P'` is not self-crossing. -/
def CdCAP1 (S : InaccSeq.{0}) (X : Ordinal.{0}) : Prop :=
  ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < X →
    cdCode S l < Nc.ncPp S → CdCapAt S l

/-- **The cap of the predicted value**: `k_λ(Θ_λ(m_λ)) < P(η_λ + ω^{e_λ})`. -/
def CdCapV (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := cdR S l < cdCapB S l

/-- The codes of level 1 (from `B₀`) are below `P'`. -/
def CdCODES1 (S : InaccSeq.{0}) : Prop :=
  ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → cdCode S l < Nc.ncPp S

variable {S : InaccSeq.{0}}

theorem cdPp_lt_Om2 (S : InaccSeq.{0}) : Nc.ncPp S < Om (1 + 1) := (psiS_bounds (S := S) _ 1).2

theorem cdMstar_le_L (S : InaccSeq.{0}) (ξ : Ordinal.{0}) : cdMstar S ≤ Nc.ncL S ξ := by
  rw [Lw.lw_L_eq S ξ]; exact Pv_mono le_self_add

/-- **No name of level 2 sits in a window with exponent `> P'` below `Ω_ω + P'·ω`.** -/
theorem cd_l2_contra {η0 e x : Ordinal.{0}} (hd : ω ^ e ∣ η0) (hx : Om ω ≤ x)
    (hx2 : x < η0 + ω ^ e) (htop : η0 + ω ^ e < Om ω + Nc.ncPp S * ω) (he : Nc.ncPp S < e) :
    False := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hPw : Nc.ncPp S * ω = ω ^ (Nc.ncPp S + 1) := by
    conv_lhs => rw [← Lw.lw_Pp_opow S]
    rw [← opow_succ, succ_eq_add_one]
  have hpe : ω ^ (Nc.ncPp S + 1) ≤ ω ^ e :=
    opow_le_opow_right omega0_pos (Order.add_one_le_of_lt he)
  rcases le_or_gt (Om ω) η0 with h | h
  · refine absurd htop (not_lt.2 ?_)
    rw [hPw]; exact add_le_add h hpe
  · have hOe : Om ω ≤ ω ^ e := by
      by_contra hlt
      push Not at hlt
      have h3 : η0 + ω ^ e < Om ω := hSC.isPrincipal h hlt
      exact absurd (hx.trans_lt (hx2.trans h3)) (lt_irrefl _)
    have hη00 : η0 = 0 := by
      by_contra hne
      exact absurd (le_of_dvd hne hd) (not_le.2 (h.trans_le hOe))
    subst hη00
    rw [zero_add] at hx2 htop
    have heO : Om ω ≤ e := by
      have h' : ω ^ Om (ω : Ordinal.{0}) ≤ ω ^ e := by rw [hOw]; exact hOe
      exact (opow_le_opow_iff_right one_lt_omega0).1 h'
    rcases eq_or_lt_of_le heO with heq | hlt
    · rw [← heq, hOw] at hx2; exact absurd hx (not_le.2 hx2)
    · have h1 : ω ^ (Om (ω : Ordinal.{0}) + 1) ≤ ω ^ e :=
        opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)
      rw [opow_add, opow_one, hOw] at h1
      have h12 : (1 + 1 : Ordinal.{0}) < ω := by
        rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
      have hPO : Nc.ncPp S + 1 < Om ω :=
        hSC.add_one_lt ((cdPp_lt_Om2 S).trans (Om_lt_Om.2 h12))
      have hPwO : Nc.ncPp S * ω < Om ω := by
        rw [hPw, ← hOw]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hPO
      have h2 : Om ω + Nc.ncPp S * ω < Om ω * ω :=
        calc Om ω + Nc.ncPp S * ω < Om ω + Om ω := (add_lt_add_iff_left _).2 hPwO
          _ = Om ω * 2 := (Ordinal.mul_two _).symm
          _ < Om ω * ω := by
            refine mul_lt_mul_of_pos_left ?_ (Om_pos omega0_ne_zero)
            exact_mod_cast natCast_lt_omega0 2
      exact absurd (htop.trans (h2.trans_le h1)) (lt_irrefl _)

/-- **NU-LOW″**: CAP-0 and CAP-1 below `L(ω)` give `L(ω) ≤ ν_C`. -/
theorem cdLow (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S ω)) : Nc.ncL S ω ≤ nuC := by
  by_contra hlt
  have hνL : nuC < Nc.ncL S ω := not_le.1 hlt
  obtain ⟨l, hl, -, hlν, -, -, -, hP, hW, -⟩ := Lb.lbFirst
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * ω) := hLeq ▸ (hlν.trans hνL)
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  -- the least `η` with `ι(η) = λ`
  have hne : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = l}, iota S η ≠ l := fun η h he =>
    (csInf_le' (s := {η | iota S η = l}) he).not_gt h
  generalize sInf {η | iota S η = l} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon l := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon l := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hl).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l := lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  -- a restart witness `ρ_μ ≤₁ ν_C` with `μ ∈ (ι(η₀), λ)`
  obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon (iota S η0)) (upsilon_normal.strictMono hν)
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  have hμX : upsilon μ < Nc.ncL S ω := (upsilon_normal.strictMono hμl).trans (hlν.trans hνL)
  obtain ⟨hg, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hpvμ : Pv S (cdEta S μ) = upsilon μ := by
    calc Pv S (cdEta S μ) = upsilon (iota S (cdEta S μ)) := (ups_iota S _).symm
      _ = upsilon μ := by rw [hιμ]
  have hx0 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) η0 _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) ηm h
    rw [hιμ, hηm] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨hxe, hxw⟩ := cdWin hdvd hx0 hxm
  -- the cap of `μ` is at most `ρ_λ`
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  -- the cap of `μ` applies
  have hcapμ : CdCapAt S μ := by
    rcases lt_or_ge (upsilon μ) (cdMstar S) with hlev | hlev
    · exact h0 μ hμ hBμ hlev
    · refine h1 μ hμ hBμ hlev hμX ?_
      have hx1 : Om ω ≤ cdEta S μ := by
        by_contra h
        push Not at h
        have h1' := Pv_lt_succ hg
        have h2' : Pv S (cdEta S μ + 1) ≤ Pv S (Om ω) := Pv_mono (Order.add_one_le_of_lt h)
        rw [hpvμ] at h1'
        exact absurd (h1'.trans_le h2') (not_lt.2 hlev)
      have htop : η0 + ω ^ e < Om ω + Nc.ncPp S * ω := by
        rw [← hdec]
        by_contra h
        push Not at h
        have h' := Pv_mono (S := S) h
        rw [hpvm] at h'
        exact absurd (hlT.trans_le h') (lt_irrefl _)
      have hxP : cdExp (cdEta S μ) < Nc.ncPp S := by
        by_contra h
        push Not at h
        exact cd_l2_contra hdvd hx1 hxm htop (lt_of_le_of_lt h hxe)
      show cdCodeOf S (cdEta S μ) < Nc.ncPp S
      rw [cdCodeOf_of_lt (hxP.trans (cdPp_lt_Om2 S))]
      exact (cdOff_le _).trans_lt hxP
  exact absurd ((hcapμ nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

/-- **The codes of level 1 are below `P'`**: a restart `λ ≠ 0` with `ρ_λ < m*` has `m_λ < P'`.  For a last
exponent `e < Ω₂` the principal summand `ω^e` of the good name `η_λ` lies in `Cl(A_η + 1, P(η)) ⊆
Cl(Ω_ω·2, P')` (`MQ_of_mem_CSet`), and `ω^e < Ω₂` gives `ω^e < ψ_{Ω₂}(Ω_ω·2) = P'`; a π-code
`ψ_{Ω₂}(A_η)` is at most `ψ_{Ω₂}(Ω_ω + Ω_{k+1}) < P'` (`Pp.ppC_lt`). -/
theorem cdCode_lt_level1 {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlev : upsilon l < cdMstar S) :
    cdCode S l < Nc.ncPp S := by
  obtain ⟨hg, -, hηω, -⟩ := cdEta_pv_spec (S := S) (η0 := Om ω) hl0 hlev
  unfold cdCode
  generalize cdEta S l = η at hg hηω
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  -- `θ·η < Ω_ω`
  have hthη : ConjT.th S * η < Om ω := by
    have hp := isPrincipal_mul_omega0_opow_opow (Om (ω : Ordinal.{0}))
    rw [hOw, hOw] at hp
    exact hp (th_lt_Om_omega S) hηω
  by_cases he : cdExp η < Om (1 + 1)
  · rw [cdCodeOf_of_lt he]
    refine lt_of_le_of_lt ((cdOff_le _).trans (right_le_opow _ one_lt_omega0)) ?_
    rcases eq_or_ne η 0 with h0 | hη0
    · -- `η = 0`: `ω^{cdExp 0} < Ω₂`, and every ordinal below `Ω₂` in the hull is below `P'`
      have hmem : ω ^ cdExp η ∈ S.CSet (Om ω + Om ω) (Nc.ncPp S) := by
        have : cdExp η = 0 := by
          rw [h0]; unfold cdExp
          have hu : {e : Ordinal.{0} | ω ^ e ∣ (0 : Ordinal.{0})} = Set.univ := by
            ext e; simp
          rw [hu]; exact csSup_of_not_bddAbove not_bddAbove_univ |>.trans (by simp)
        rw [this, opow_zero]; exact CSet.one_mem _ _
      have h2 : ω ^ cdExp η < Om (1 + 1) := by
        have hO2 : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by simp)
        rw [← Low.opow_eq_self_of_SC hO2]
        exact (opow_lt_opow_iff_right one_lt_omega0).2 he
      exact lt_psi_of_mem (InR_Om_succ 1) hmem h2
    · obtain ⟨η0, hdec, -⟩ := cdExp_decomp hη0
      have hcomp : Comp (cdExp η) η := ⟨η0, 0, opow_pos _ omega0_pos, by rw [add_zero]; exact hdec⟩
      have hLam : Pv S η ≤ S.Lam :=
        (Pv_lt_Om1 S η).le.trans ((Low.Om_one_le_I 0).trans (S.I_lt_Lam 0).le)
      have hQ := (MQ_of_mem_CSet (S := S) (e := ConjT.Aη S η + 1) (g := Pv S η) le_rfl le_rfl hLam hg).1
      have hmem0 : ω ^ cdExp η ∈ S.CSet (ConjT.Aη S η + 1) (Pv S η) := (hQ.1 _ hcomp).1
      have hA : ConjT.Aη S η + 1 ≤ Om ω + Om ω := by
        unfold ConjT.Aη
        rw [add_assoc]
        exact ((add_lt_add_iff_left _).2 (hSC.add_one_lt hthη)).le
      have hP : Pv S η ≤ Nc.ncPp S :=
        (Pv_lt_Om1 S η).le.trans (Lw.lw_Om1_lt_Pp S).le
      have hmem : ω ^ cdExp η ∈ S.CSet (Om ω + Om ω) (Nc.ncPp S) := CSet_mono hA hP hmem0
      have h2 : ω ^ cdExp η < Om (1 + 1) := by
        have hO2 : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by simp)
        rw [← Low.opow_eq_self_of_SC hO2]
        exact (opow_lt_opow_iff_right one_lt_omega0).2 he
      exact lt_psi_of_mem (InR_Om_succ 1) hmem h2
  · unfold cdCodeOf
    rw [if_neg he]
    obtain ⟨k, hk⟩ := Pp.ppLt_Om_omega hthη
    have hA : ConjT.Aη S η ≤ Om ω + Om ((k + 1 : ℕ) : Ordinal.{0}) := by
      unfold ConjT.Aη; exact (add_le_add_iff_left _).2 hk.le
    exact lt_of_le_of_lt (psi_mono (InR_Om_succ 1) hA).1 (Pp.ppC_lt (S := S) k)

/-- **The codes of level 2 below `L(ω)`**: a restart `λ ≠ 0` with `m* ≤ ρ_λ < L(ω)` that is not one of the
`L(k)` has `m_λ < P'`.  Its name is `Ω_ω + η'` with `η' < P'·ω = ω^{P'+1}`; if `ω^{P'}` divided it, then
`η' = P'·k` with `k < ω` and `ρ_λ = L(k)`. -/
theorem cdCode_lt_level2 {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlev : cdMstar S ≤ upsilon l)
    (hlX : upsilon l < Nc.ncL S ω) (hnot : ∀ k : ℕ, upsilon l ≠ Nc.ncL S (k : Ordinal.{0})) :
    cdCode S l < Nc.ncPp S := by
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  obtain ⟨hg, -, hηt, hpv⟩ := cdEta_pv_spec (S := S) (η0 := Om ω + Nc.ncPp S * ω) hl0 (hLeq ▸ hlX)
  have hx1 : Om ω ≤ cdEta S l := by
    by_contra h
    push Not at h
    have h1' := Pv_lt_succ hg
    have h2' : Pv S (cdEta S l + 1) ≤ Pv S (Om ω) := Pv_mono (Order.add_one_le_of_lt h)
    rw [hpv] at h1'
    exact absurd (h1'.trans_le h2') (not_lt.2 hlev)
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hη0 : cdEta S l ≠ 0 := (lt_of_lt_of_le (Om_pos omega0_ne_zero) hx1).ne'
  obtain ⟨η', hη'⟩ := exists_add_of_le hx1
  have hexp : cdExp (cdEta S l) < Nc.ncPp S := by
    by_contra h
    push Not at h
    have hd : ω ^ Nc.ncPp S ∣ cdEta S l := (opow_dvd_opow ω h).trans (cdExp_dvd hη0)
    have hdO : ω ^ Nc.ncPp S ∣ Om ω := by
      rw [← hOw]; exact opow_dvd_opow ω (cdPp_lt_Om_omega S).le
    rw [hη'] at hd
    obtain ⟨q, hq⟩ := (dvd_add_iff hdO).1 hd
    have hlt : η' < Nc.ncPp S * ω := by
      rw [hη'] at hηt; exact (add_lt_add_iff_left _).1 hηt
    have hPω : Nc.ncPp S * ω = ω ^ Nc.ncPp S * ω := by rw [Lw.lw_Pp_opow]
    rw [hq, hPω] at hlt
    have hqω : q < ω :=
      (isNormal_mul_right (opow_pos (Nc.ncPp S) omega0_pos)).strictMono.lt_iff_lt.1 hlt
    obtain ⟨k, rfl⟩ := lt_omega0.1 hqω
    apply hnot k
    rw [← hpv, hη', hq, Lw.lw_Pp_opow, Lw.lw_L_eq]
  unfold cdCode
  rw [cdCodeOf_of_lt (hexp.trans (cdPp_lt_Om2 S))]
  exact (cdOff_le _).trans_lt hexp

/-- **The range of ENUM-REACH at level 2 below `L(ω)`**: a restart `λ ≥ B₀` with `m* ≤ ρ_λ < L(ω)` is in
the range iff it is none of the `L(k)`. -/
theorem cdRange_iff_level2 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l)
    (hlev : cdMstar S ≤ upsilon l) (hlX : upsilon l < Nc.ncL S ω) :
    CdRange S l ↔ ∀ k : ℕ, upsilon l ≠ Nc.ncL S (k : Ordinal.{0}) := by
  constructor
  · rintro ⟨-, -, -, hc⟩ k hk
    rcases k with _ | k
    · rw [Nat.cast_zero] at hk
      rw [(cdCode_L0 hk).2] at hc; exact lt_irrefl _ hc
    · rw [cdCode_L k hk] at hc; exact lt_irrefl _ hc
  · intro hnot
    exact ⟨hl, hB, hlX.trans_le (Pp.ppL_mono le_self_add), cdCode_lt_level2 hl.1 hlev hlX hnot⟩

/-- **The range of ENUM-REACH at level 1**: every restart `λ ≥ B₀` with `ρ_λ < m*` is in the range. -/
theorem cdRange_level1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l)
    (hlev : upsilon l < cdMstar S) : CdRange S l :=
  ⟨hl, hB, hlev.trans_le (cdMstar_le_L S _), cdCode_lt_level1 hl.1 hlev⟩

/-- **`CdCODES1` holds.** -/
theorem cdCODES1 : CdCODES1 S := fun _ hl _ hlev => cdCode_lt_level1 hl.1 hlev

/-- **UPPER and the cap of the value give the cap.** -/
theorem cdCapAt_of_upper {l : Ordinal.{0}} (hU : CdUpper S l) (hV : CdCapV S l) : CdCapAt S l := by
  intro g hg
  by_contra hge
  push Not at hge
  exact hU (le1_of_le_of_le1 ((cdRho_lt_R S l).le.trans le_self_add)
    ((Order.add_one_le_of_lt hV).trans hge) hg)

/-- **UPPER and the cap of the values give CAP-0 and CAP-1 below `L(ω)`** (the level-1 codes are
below `P'` by `cdCODES1`). -/
theorem cdCAP_of_enum (hU : CdUPPER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) :
    CdCAP0 S ∧ CdCAP1 S (Nc.ncL S ω) := by
  have hωL : Nc.ncL S ω ≤ Nc.ncL S (ω + 1) := Pp.ppL_mono le_self_add
  refine ⟨fun l hl hB hlev => ?_, fun l hl hB _ hlX hcode => ?_⟩
  · have hlX : upsilon l < Nc.ncL S ω := hlev.trans_le (cdMstar_le_L S ω)
    have hr : CdRange S l := ⟨hl, hB, hlX.trans_le hωL, cdCODES1 l hl hB hlev⟩
    exact cdCapAt_of_upper (hU l hr) (hV l hr hlX)
  · have hr : CdRange S l := ⟨hl, hB, hlX.trans_le hωL, hcode⟩
    exact cdCapAt_of_upper (hU l hr) (hV l hr hlX)

/-- **`L(ω) ≤ ν_C` from UPPER** and the cap of the values below `L(ω)`. -/
theorem cdLow_enum (hU : CdUPPER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l) :
    Nc.ncL S ω ≤ nuC :=
  cdLow (cdCAP_of_enum hU hV).1 (cdCAP_of_enum hU hV).2

end Googology.Trans.PoR.InaccPsi.R2.Cd
