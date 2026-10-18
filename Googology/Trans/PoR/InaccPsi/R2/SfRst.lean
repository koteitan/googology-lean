import Googology.Trans.PoR.InaccPsi.R2.SfLast

/-!
# (S1) restarts go to restarts: `TpRstMove` is proved, hence `TpShift`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `ι` the index of Theorem GEN,
`L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)`, `c = Ω_ω + P'·ω`, `B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW`.
An ordinal `A` is *own* when `A ∈ Cl(A, ψ_{Ω₁}(A))`.  A restart index is a nonzero multiple of `ω²`.

* `sfNotRst_succ`, `sfNotRst_omega`, `sfRst_cases`: `ζ + 1` and `ζ + ω` are never restart indices, and a
  nonzero non-restart index is one of them;
* `sfTgt_pred` (**the target side**): for own `A_{η'}` with `c ≤ η'`, if `ι(η')` is not a restart
  index then `η' = g' + 1` or `η' = g' + ω` with `A_{g'}` own;
* `sfData` (**the source side**): at a good `η` with `L(n+1) ≤ P(η) < L(n+2)`, `A_η = α_{n+1} + |ρ|`
  with `ρ` the rest of the normal-form argument, `θ ∣ |ρ|`, `B_n(P(η)) = ψ_{Ω₁}(α_ω + |σ(ρ)|)` and
  `ψ^S_0(α_ω + σ(ρ))` a normal form;
* `sfSrc_pred` (**the predecessor reflects**): if `|σ(ρ)| = θ·x + θ·δ` (`δ = 1` or `δ = ω`) with
  `α_ω + θ·x` own, then `|ρ| = θ·y + θ·δ` with `α_{n+1} + θ·y` own.  (The last summand of `σ(ρ)` is
  `θ·δ`, so that of `ρ` is too; the rest `ρ₀` has `|σ(ρ₀)| + θ·δ = θ·x + θ·δ`, so `x = δ·u + k`;
  with `ρ₁ = ρ₀ + θ·k`, `ψ^S_0(α_ω + σ(ρ₁))` is the normal form of `ψ_{Ω₁}(α_ω + θ·x)`, and
  `Sf.sfRefl` makes `ψ^S_0(α_{n+1} + ρ₁)` a normal form);
* `sfRstMove` (**(S1) `TpRstMove S`, no hypothesis beyond Theorem GEN**): `B_n(υ_μ) = P(η')`; if
  `ι(η')` were not a restart, the predecessor `g'` of `η'` would reflect to a good `g` with
  `η = g + 1` or `η = g + ω`, so `ι(η) = ι(g) + 1` or `ι(g) + ω` would not be a restart;
* `sfShiftAll`: **`TpShift S`** (with (S2), (S3) of `Sf.sfPvStep`, `Sf.sfLimMove`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## Restart indices -/

theorem sfNotRst_succ (ζ : Ordinal.{0}) : ¬ IsRestartIdx (ζ + 1) := by
  intro h
  have hd : ω ∣ ζ + 1 := (dvd_mul_right ω ω).trans (ri_iff.1 h).2
  have hl : IsSuccPrelimit (ζ + 1) := isSuccPrelimit_iff_omega0_dvd.2 hd
  rw [← Order.succ_eq_add_one] at hl
  exact Order.not_isSuccPrelimit_succ ζ hl

theorem sfNotRst_omega (ζ : Ordinal.{0}) : ¬ IsRestartIdx (ζ + ω) := by
  intro h
  have hd := (ri_iff.1 h).2
  have hww : (ω : Ordinal.{0}) * ω ≠ 0 := Tp.tpWW_pos.ne'
  have hr : ζ % (ω * ω) < ω * ω := mod_lt ζ hww
  obtain ⟨c, hc, hrc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hr
  have h2 : ζ % (ω * ω) + ω < ω * ω := by
    obtain ⟨m, rfl⟩ := lt_omega0.1 hc
    calc ζ % (ω * ω) + ω ≤ ω * (m : Ordinal.{0}) + ω := add_le_add_left hrc.le _
      _ = ω * ((m + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
      _ < ω * ω := (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _)
  have e : ζ + ω = ω * ω * (ζ / (ω * ω)) + (ζ % (ω * ω) + ω) := by
    rw [← add_assoc, div_add_mod]
  have hm : (ζ + ω) % (ω * ω) = ζ % (ω * ω) + ω := by
    rw [e, mul_add_mod_self, mod_eq_of_lt h2]
  have h0 := dvd_iff_mod_eq_zero.1 hd
  rw [hm] at h0
  exact absurd h0 (lt_of_lt_of_le omega0_pos le_add_self).ne'

theorem sfRst_cases {ξ : Ordinal.{0}} (h0 : ξ ≠ 0) (hn : ¬ IsRestartIdx ξ) :
    (∃ ζ, ξ = ζ + 1) ∨ (∃ ζ, ξ = ζ + ω) := by
  have hww : (ω : Ordinal.{0}) * ω ≠ 0 := Tp.tpWW_pos.ne'
  have hr0 : ξ % (ω * ω) ≠ 0 := fun h => hn (ri_iff.2 ⟨h0, dvd_iff_mod_eq_zero.2 h⟩)
  obtain ⟨m, k, hmk⟩ := ConjT.decomp (mod_lt ξ hww)
  have e := div_add_mod ξ (ω * ω)
  cases k with
  | zero =>
    cases m with
    | zero => exact absurd (by simpa using hmk) hr0
    | succ m' =>
      right
      refine ⟨ω * ω * (ξ / (ω * ω)) + ω * (m' : Ordinal.{0}), ?_⟩
      calc ξ = ω * ω * (ξ / (ω * ω)) + ξ % (ω * ω) := e.symm
        _ = ω * ω * (ξ / (ω * ω)) + (ω * ((m' + 1 : ℕ) : Ordinal.{0}) + ((0 : ℕ) : Ordinal.{0})) := by
          rw [hmk]
        _ = ω * ω * (ξ / (ω * ω)) + ω * (m' : Ordinal.{0}) + ω := by
          rw [Nat.cast_zero, add_zero, Nat.cast_succ, mul_add_one, add_assoc]
  | succ k' =>
    left
    refine ⟨ω * ω * (ξ / (ω * ω)) + (ω * (m : Ordinal.{0}) + (k' : Ordinal.{0})), ?_⟩
    calc ξ = ω * ω * (ξ / (ω * ω)) + ξ % (ω * ω) := e.symm
      _ = ω * ω * (ξ / (ω * ω)) + (ω * (m : Ordinal.{0}) + ((k' + 1 : ℕ) : Ordinal.{0})) := by
        rw [hmk]
      _ = ω * ω * (ξ / (ω * ω)) + (ω * (m : Ordinal.{0}) + (k' : Ordinal.{0})) + 1 := by
        rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ← add_assoc]

/-- `y < Z`, `ω^e ∣ Z`, `z < ω^e` give `y + z < Z`. -/
theorem sfAdd_lt_of_dvd {y z Z e : Ordinal.{0}} (hy : y < Z) (hd : ω ^ e ∣ Z) (hz : z < ω ^ e) :
    y + z < Z := by
  obtain ⟨m, rfl⟩ := hd
  have hω : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
  have ey := div_add_mod y (ω ^ e)
  have hq : y / ω ^ e < m := by
    by_contra hh
    push Not at hh
    have h2 : ω ^ e * (y / ω ^ e) ≤ y := by
      conv_rhs => rw [← ey]
      exact le_self_add
    have : ω ^ e * m ≤ y := (mul_le_mul_right hh _).trans h2
    exact absurd hy (not_lt.2 this)
  calc y + z = ω ^ e * (y / ω ^ e) + (y % ω ^ e + z) := by rw [← add_assoc, ey]
    _ < ω ^ e * (y / ω ^ e) + ω ^ e :=
        (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e (mod_lt y hω) hz)
    _ = ω ^ e * (y / ω ^ e + 1) := by rw [mul_add_one]
    _ ≤ ω ^ e * m := mul_le_mul_right (Order.add_one_le_of_lt hq) _

/-! ## The target side -/

theorem sfOwn_lt_Lam {A : Ordinal.{0}} (h : A ∈ S.CSet A (S.psi A (Om 1))) : A < S.Lam :=
  lt_Lam_of_mem ((psi_lt Low.InR_Om_one A).le.trans (Om_lt_Lam one_lt_Lam).le) h

theorem sfOwn_omega {A : Ordinal.{0}} (h : A ∈ S.CSet A (S.psi A (Om 1))) (hA : Om ω ≤ A) :
    A + ConjT.th S * ω ∈ S.CSet (A + ConjT.th S * ω) (S.psi (A + ConjT.th S * ω) (Om 1)) := by
  have h1 := (psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + ConjT.th S * ω)).2 h
  refine CSet.add_mem h1 (ConjT.th_omega_mem S ?_)
  exact lt_of_le_of_lt hA (lt_add_of_pos_right _ (mul_pos (sfTh_pos S) omega0_pos))

/-- **The target side**: a non-restart index above `ι(c)` has a predecessor `g' + 1` or `g' + ω`. -/
theorem sfTgt_pred {η' : Ordinal.{0}}
    (hown : ConjT.Aη S η' ∈ S.CSet (ConjT.Aη S η') (S.psi (ConjT.Aη S η') (Om 1)))
    (hc : Om ω + Nc.ncPp S * ω ≤ η') (hnr : ¬ IsRestartIdx (Bt.iota S η')) :
    ∃ g', ConjT.Aη S g' ∈ S.CSet (ConjT.Aη S g') (S.psi (ConjT.Aη S g') (Om 1)) ∧
      (η' = g' + 1 ∨ η' = g' + ω) := by
  have hg' : Bt.Good S η' := sfGood_of_own hown
  have hL : Nc.ncL S ω ≤ Bt.iota S η' := by
    rw [← Lw.lw_iota_L_omega S]; exact Bt.iota_mono _ _ hc
  have hωL : (ω : Ordinal.{0}) < Nc.ncL S ω := Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω)
  have h0 : Bt.iota S η' ≠ 0 := (Order.one_le_iff_ne_zero.1 (Bt.one_le_iota η'))
  have hAL : ConjT.Aη S η' < S.Lam := sfOwn_lt_Lam hown
  rcases sfRst_cases h0 hnr with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
  · have h1 : 1 ≤ ζ := by
      by_contra hh
      push Not at hh
      have : ζ = 0 := Order.lt_one_iff.1 hh
      rw [this, zero_add] at hζ
      rw [hζ] at hL
      exact absurd (hL.trans_lt one_lt_omega0) (not_lt.2 hωL.le)
    obtain ⟨g, hgη, hgg, hgι⟩ := Cd.cd_good_name (S := S) h1 (by rw [hζ]; exact lt_add_one ζ)
    have hogA : ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1)) :=
      sfOwn hgg ((ConjT.A_mono S hgη.le).trans_lt hAL)
    have ho1 := sfOwn_th hogA (ConjT.OmW_le_A S g)
    rw [ConjT.A_succ] at ho1
    refine ⟨g, hogA, Or.inl ?_⟩
    refine (Cd.cd_good_inj hg' (sfGood_of_own ho1) ?_)
    rw [Bt.iota_good hgg, hgι, hζ]
  · have h1 : 1 ≤ ζ := by
      by_contra hh
      push Not at hh
      have : ζ = 0 := Order.lt_one_iff.1 hh
      rw [this, zero_add] at hζ
      rw [hζ] at hL
      exact absurd hL (not_le.2 hωL)
    obtain ⟨g, hgη, hgg, hgι⟩ := Cd.cd_good_name (S := S) h1
      (by rw [hζ]; exact lt_add_of_pos_right _ omega0_pos)
    have hogA : ConjT.Aη S g ∈ S.CSet (ConjT.Aη S g) (S.psi (ConjT.Aη S g) (Om 1)) :=
      sfOwn hgg ((ConjT.A_mono S hgη.le).trans_lt hAL)
    have hoω := sfOwn_omega hogA (ConjT.OmW_le_A S g)
    rw [← Bt.A_add] at hoω
    refine ⟨g, hogA, Or.inr ?_⟩
    refine (Cd.cd_good_inj hg' (sfGood_of_own hoω) ?_)
    rw [sfIota_omega hogA, hgι, hζ]

/-! ## The source side -/

/-- **The data of `P(η)` at a good `η` in the window.** -/
theorem sfData {n : ℕ} {η : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hhi : Pv S η < Bc.bcC S (n + 1)) :
    ∃ ρ : Term, bcD S ρ ∧ NF (bcApp (bcPre (n + 1)) ρ) ∧ val S ρ < ω ^ (Nc.ncPp S + 1) ∧
      ConjT.Aη S η = bcAlpha S (n + 1) + val S ρ ∧ ConjT.th S ∣ val S ρ ∧
      Bc.bcB S n (Pv S η) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW ρ)) (Om 1) ∧
      NF (psiS Term.zero (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW ρ))) := by
  have hAL : ConjT.Aη S η < S.Lam := (sfA_lt hhi).2
  have hown := sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := sfArg_le (sfOwn_alpha S n) hown hlo
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := hhi.trans hLw
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hN := hD.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  rw [hva] at hB0
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hdα : ConjT.th S ∣ bcAlpha S (n + 1) := by rw [sfAlpha_eq]; exact sfTh_dvd_A S _
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have ea : a = bcApp (bcPre (n + 1)) (bcDrop (n + 3) a) := by
    have := bcApp_of_prefix (prin_pre (n + 1)) hN.2.1 hpre; rwa [sfPre_len] at this
  refine ⟨bcDrop (n + 3) a, bcD_drop hDa (n + 3), ea ▸ hN.2.1, ?_, by rw [← hva, hvρ], ?_, hB0, ?_⟩
  · have h1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) < bcAlphaW S := hvρ ▸ hAW
    unfold bcAlpha bcAlphaW at h1
    rw [add_assoc] at h1
    exact lt_of_le_of_lt le_add_self ((add_lt_add_iff_left _).1 h1)
  · have := sfTh_dvd_A S η
    rw [← hva, hvρ] at this
    exact (dvd_add_iff hdα).1 this
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rwa [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN

/-! ## The predecessor reflects -/

/-- A principal summand of a chain below `P'·ω` is `≤ P'`. -/
theorem sfHead_le_Pp {r : Term} (hr : NF r) (h0 : r ≠ Term.zero)
    (hv : val S r < ω ^ (Nc.ncPp S + 1)) : cmp (head r) tPp ≠ .gt := by
  have hP := isPrin_head hr h0
  have hh : NF (head r) := hr.head
  have hle := prin_le_Pp S hh hP (lt_of_le_of_lt (val_head_le S hr) hv)
  intro hc
  have := (cmp_eq_compare S hh NF_tPp).symm.trans hc
  rw [compare_gt_iff_gt, val_tPp] at this
  exact absurd hle (not_le.2 this)

/-- The chain `α_{n+1} + r` is normal for a normal `r` below `P'·ω`. -/
theorem sfNF_pre (n : ℕ) {r : Term} (hr : NF r) (hv : val S r < ω ^ (Nc.ncPp S + 1)) :
    NF (bcApp (bcPre (n + 1)) r) := by
  refine NF_bcApp (bcNFL_pre (n + 1)) (by simp [bcPre]) ?_
  by_cases h0 : r = Term.zero
  · exact Or.inl h0
  · exact Or.inr ⟨hr, by rw [bcLast_pre]; exact sfHead_le_Pp hr h0 hv⟩

/-- The chain `α_ω + σ(r)` is normal for `r` in the domain below `P'·ω`. -/
theorem sfNF_preW (n : ℕ) {r : Term} (hD : bcD S r) (hv : val S r < ω ^ (Nc.ncPp S + 1)) :
    NF (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW r)) := by
  refine NF_bcApp bcNFL_preW (by simp [bcPreW]) ?_
  by_cases h0 : r = Term.zero
  · left; rw [h0, bcSig_zero]
  · right
    refine ⟨bc_NF (k := n) hD, ?_⟩
    rw [bcLast_preW, head_bcSig]
    have hhD : bcD S (head r) := bcD_sub hD (head_sub r)
    have hc := bc_cmp' (k := n) hhD (bcD_free NF_tWp bcFree_tWp)
    rw [bcSig_free bcFree_tWp, cmp_lt_tWp_of_le S hD.1.head (sfHead_le_Pp hD.1 h0 hv)] at hc
    rw [hc]; simp

/-- **The predecessor reflects.** -/
theorem sfSrc_pred {n : ℕ} {ρ e : Term} {δ g x : Ordinal.{0}} (hD : bcD S ρ)
    (hv : val S ρ < ω ^ (Nc.ncPp S + 1)) (he : NF e) (hef : bcFree e)
    (hev : val S e = ConjT.th S * δ) (hg : ConjT.th S * δ = ω ^ g)
    (hδk : ∀ u x : Ordinal.{0}, δ * u + δ = x + δ →
      ∃ k : ℕ, x = δ * u + k ∧ ConjT.th S * k + ConjT.th S * δ = ConjT.th S * δ)
    (hown : bcAlphaW S + ConjT.th S * x ∈ S.CSet (bcAlphaW S + ConjT.th S * x)
      (S.psi (bcAlphaW S + ConjT.th S * x) (Om 1)))
    (hσv : val S (bcSig (bcPre (n + 1)) bcPreW ρ) = ConjT.th S * x + ConjT.th S * δ) :
    ∃ y, bcAlpha S (n + 1) + ConjT.th S * y ∈ S.CSet (bcAlpha S (n + 1) + ConjT.th S * y)
      (S.psi (bcAlpha S (n + 1) + ConjT.th S * y) (Om 1)) ∧
      val S ρ = ConjT.th S * y + ConjT.th S * δ := by
  have hθ0 := sfTh_pos S
  have hδ0 : ConjT.th S * δ ≠ 0 := by rw [hg]; exact (opow_pos g omega0_pos).ne'
  have hρ0 : ρ ≠ Term.zero := by
    rintro rfl
    rw [bcSig_zero] at hσv
    exact hδ0 (by
      have : (0 : Ordinal.{0}) = ConjT.th S * x + ConjT.th S * δ := hσv
      exact (add_eq_zero_iff.1 this.symm).2)
  have hσN : NF (bcSig (bcPre (n + 1)) bcPreW ρ) := bc_NF (k := n) hD
  have hσ0 : bcSig (bcPre (n + 1)) bcPreW ρ ≠ Term.zero := bcSig_ne_zero hρ0
  -- the last summand
  have hl1 : val S (sfLast (bcSig (bcPre (n + 1)) bcPreW ρ)) = ω ^ g := sfLast_val hσN hσ0 (by rw [hσv, hg])
  have hDl : bcD S (sfLast ρ) := bcD_sub hD (sfLast_sub ρ)
  have hDe : bcD S e := bcD_free he hef
  have hl2 : val S (sfLast ρ) = val S e := by
    refine sfSig_val_inj (n := n) hDl hDe ?_
    rw [← sfLast_sig, hl1, bcSig_free hef, hev, hg]
  have hle : sfLast ρ = e := eq_of_val_eq S hDl.1 he hl2
  -- the rest
  set r0 := sfInit ρ with hr0
  have hNr0 : NF r0 := (sfInit_NF hD.1).1
  have hDr0 : bcD S r0 := ⟨hNr0, sfInit_args hD.2⟩
  have hvρ : val S ρ = val S r0 + val S e := by rw [sfInit_val hD.1, hle]
  have hdr0 : ω ^ g ∣ val S r0 := sfInit_dvd (S := S) hD.1 (by rw [hle, hev, hg])
  obtain ⟨hNa, hva, -⟩ := addNF_spec (S := S) hNr0 he
  have hρe : ρ = addNF r0 e := eq_of_val_eq S hD.1 hNa (by rw [hva, hvρ])
  have hσρ : val S (bcSig (bcPre (n + 1)) bcPreW ρ) = val S (bcSig (bcPre (n + 1)) bcPreW r0) + ConjT.th S * δ := by
    rw [hρe, bcSig_addNF (k := n) hDr0 hDe, bcSig_free hef,
      (addNF_spec (S := S) (bc_NF (k := n) hDr0) he).2.1, hev]
  obtain ⟨u, hu⟩ := sfSig_dvdG (n := n) he hef (hev.trans hg) hDr0 hdr0
  have hu' : val S (bcSig (bcPre (n + 1)) bcPreW r0) = ConjT.th S * (δ * u) := by rw [hu, ← hg, mul_assoc]
  have e1 : ConjT.th S * (δ * u + δ) = ConjT.th S * (x + δ) := by
    rw [mul_add, mul_add, ← hu', ← hσρ, hσv]
  obtain ⟨k, hxk, hkδ⟩ := hδk u x (sfMul_inj hθ0 e1)
  -- the candidate `ρ₁ = ρ₀ + θ·k`
  obtain ⟨hKN, hKf, hKv⟩ := sfThK_spec S k
  have hDK : bcD S (sfThK k) := bcD_free hKN hKf
  obtain ⟨hN1, hv1, -⟩ := addNF_spec (S := S) hNr0 hKN
  have hD1 : bcD S (addNF r0 (sfThK k)) := ⟨hN1, sfArgs_addNF hDr0.2 (bcArgsLt_of_free hKf)⟩
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (addNF r0 (sfThK k))) = ConjT.th S * x := by
    rw [bcSig_addNF (k := n) hDr0 hDK, bcSig_free hKf,
      (addNF_spec (S := S) (bc_NF (k := n) hDr0) hKN).2.1, hu', hKv, ← mul_add, hxk]
  have hv1' : val S (addNF r0 (sfThK k)) < ω ^ (Nc.ncPp S + 1) := by
    refine lt_of_le_of_lt ?_ hv
    rw [hv1, hKv, hvρ, hev]
    calc val S r0 + ConjT.th S * k ≤ val S r0 + ConjT.th S * k + ConjT.th S * δ := le_self_add
      _ = val S r0 + ConjT.th S * δ := by rw [add_assoc, hkδ]
  -- the target normal form
  have hB : bcAlphaW S + ConjT.th S * x < S.Lam := sfOwn_lt_Lam hown
  have hlt : S.psi (bcAlphaW S + ConjT.th S * x) (Om 1) <
      S.psi (bcAlphaW S + ConjT.th S * x + 1) (Om 1) := by
    have hm := (psi_mono (S := S) Low.InR_Om_one
      (le_self_add : bcAlphaW S + ConjT.th S * x ≤ bcAlphaW S + ConjT.th S * x + 1)).2 hown
    exact psi_lt_psi_of_mem Low.InR_Om_one (lt_add_one _) hm
  obtain ⟨hTN, hTv⟩ := bcNf_spec S (mem_of_lt_psi S hlt)
  obtain ⟨a'', ha'', hva''⟩ := sfNf_psi hown hTN hTv
  have hTW : NF (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW (addNF r0 (sfThK k)))) := sfNF_preW n hD1 hv1'
  have ea'' : a'' = bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW (addNF r0 (sfThK k))) := by
    refine eq_of_val_eq S (ha'' ▸ hTN).2.1 hTW ?_
    rw [hva'', val_bcApp_preW, hσ1]
  have hT : NF (psiS Term.zero (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW (addNF r0 (sfThK k))))) := by
    rw [← ea'', ← ha'']; exact hTN
  -- reflect
  have hR := sfRefl hD1 hv1' (sfNF_pre n hN1 hv1') hT
  have hsem : Sem S (psiS Term.zero (bcApp (bcPre (n + 1)) (addNF r0 (sfThK k)))) := sem_of_NF hR
  have hsem2 := hsem.2.2
  have hval : val S (bcApp (bcPre (n + 1)) (addNF r0 (sfThK k))) =
      bcAlpha S (n + 1) + val S (addNF r0 (sfThK k)) := by
    have := val_of_pre S (sfNF_pre n hN1 hv1') (isPrefixOf_bcApp (prin_pre (n + 1)) _)
    rwa [bcDrop_bcApp (prin_pre (n + 1))] at this
  rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
    hval] at hsem2
  have hθg : ConjT.th S ∣ ω ^ g := ⟨δ, hg.symm⟩
  obtain ⟨v, hv⟩ := hθg.trans hdr0
  have hr1 : val S (addNF r0 (sfThK k)) = ConjT.th S * (v + k) := by
    rw [hv1, hKv, hv, mul_add]
  refine ⟨v + k, by rw [← hr1]; exact hsem2, ?_⟩
  rw [hvρ, hev, hv, mul_add, add_assoc, hkδ]

/-! ## (S1) -/

theorem sfA_inj {η1 η2 : Ordinal.{0}} (h : ConjT.Aη S η1 = ConjT.Aη S η2) : η1 = η2 :=
  sfMul_inj (sfTh_pos S) (add_left_cancel h)

/-- `ω^{θ+2} ∣ α_ω`. -/
theorem sfDvd_alphaW (S : InaccSeq.{0}) : ω ^ (ConjT.th S + 2) ∣ bcAlphaW S := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have h2 : ConjT.th S + 2 ≤ Om ω := by
    have hl := hSC.isSuccLimit
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc]
    exact (hl.add_one_lt (hl.add_one_lt (sfTh_lt_OmW S))).le
  have hdO : ω ^ (ConjT.th S + 2) ∣ Om ω := by rw [← hOw]; exact opow_dvd_opow ω h2
  have h3 : ConjT.th S + 2 ≤ Nc.ncPp S + 1 := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc]
    simpa [Order.succ_eq_add_one] using Order.succ_le_succ (Order.add_one_le_of_lt (Nc.ncTh_lt_Pp S))
  unfold bcAlphaW
  exact dvd_add (dvd_add hdO hdO) (opow_dvd_opow ω h3)

/-- **(S1) `TpRstMove S` holds** (no hypothesis beyond Theorem GEN). -/
theorem sfRstMove : Tp.TpRstMove S := by
  intro n μ hμ hlo hhi
  have hL : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  have hι : μ < Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Cd.cd_lt_iota (hL ▸ hhi)
  have h1 : 1 ≤ μ := Order.one_le_iff_ne_zero.2 hμ.1
  obtain ⟨η, hg, hιη, hpη, -⟩ := Tp.tpUps_pv (S := S) h1 (Order.add_one_le_of_lt hι)
  rw [← hpη] at hlo hhi ⊢
  obtain ⟨ρ, hD, hNc, hv, hAη, hdρ, hB, hNT⟩ := sfData hg hlo hhi
  obtain ⟨ζ', hζ'⟩ := sfSig_dvd n hD hdρ
  set η' := Om ω + Nc.ncPp S * ω + ζ' with hη'
  have hAη' : ConjT.Aη S η' = bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW ρ) := by
    rw [hη', Bt.A_add, ← sfAlphaW_eq, hζ']
  have hown' : ConjT.Aη S η' ∈ S.CSet (ConjT.Aη S η') (S.psi (ConjT.Aη S η') (Om 1)) := by
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW (bcSig (bcPre (n + 1)) bcPreW ρ))) :=
      sem_of_NF hNT
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW, ← hAη'] at h2
    exact h2
  have hBη : Bc.bcB S n (Pv S η) = upsilon (Bt.iota S η') := by
    rw [hB, Bt.ups_iota S η', hAη']
  refine ⟨Bt.iota S η', ?_, hBη⟩
  by_contra hnr
  obtain ⟨g', hog', hcase⟩ := sfTgt_pred hown' le_self_add hnr
  -- from `η' = g' + δ` to the source
  have key : ∀ (δ : Ordinal.{0}) (e : Term) (gg : Ordinal.{0}), NF e → bcFree e →
      val S e = ConjT.th S * δ → ConjT.th S * δ = ω ^ gg → gg < ConjT.th S + 2 →
      (∀ u x : Ordinal.{0}, δ * u + δ = x + δ →
        ∃ k : ℕ, x = δ * u + k ∧ ConjT.th S * k + ConjT.th S * δ = ConjT.th S * δ) →
      η' = g' + δ → ∃ y, Bt.Good S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y) ∧
        η = Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y + δ := by
    intro δ e gg he hef hev hgg hgl hδk hη
    have hA : ConjT.Aη S η' = ConjT.Aη S g' + ConjT.th S * δ := by rw [hη, Bt.A_add]
    have hge : bcAlphaW S ≤ ConjT.Aη S g' := by
      by_contra hh
      push Not at hh
      have := sfAdd_lt_of_dvd hh (sfDvd_alphaW S)
        (show ConjT.th S * δ < ω ^ (ConjT.th S + 2) by
          rw [hgg]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hgl)
      rw [← hA, hAη'] at this
      exact absurd this (not_lt.2 le_self_add)
    obtain ⟨D, hDv⟩ := exists_add_of_le hge
    have hdD : ConjT.th S ∣ D := by
      have h1 := sfTh_dvd_A S g'
      rw [hDv] at h1
      exact (dvd_add_iff (by rw [sfAlphaW_eq]; exact sfTh_dvd_A S _)).1 h1
    obtain ⟨x, hx⟩ := hdD
    have hσv : val S (bcSig (bcPre (n + 1)) bcPreW ρ) = ConjT.th S * x + ConjT.th S * δ := by
      have := hA
      rw [hAη', hDv, hx, add_assoc] at this
      exact add_left_cancel this
    have hownx : bcAlphaW S + ConjT.th S * x ∈ S.CSet (bcAlphaW S + ConjT.th S * x)
        (S.psi (bcAlphaW S + ConjT.th S * x) (Om 1)) := by
      rw [← hx, ← hDv]; exact hog'
    obtain ⟨y, hoy, hvy⟩ := sfSrc_pred hD hv he hef hev hgg hδk hownx hσv
    have hAg : ConjT.Aη S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y) =
        bcAlpha S (n + 1) + ConjT.th S * y := by rw [Bt.A_add, ← sfAlpha_eq]
    refine ⟨y, sfGood_of_own (by rw [hAg]; exact hoy), ?_⟩
    refine sfA_inj (S := S) ?_
    rw [hAη, Bt.A_add, hAg, hvy, add_assoc]
  rcases hcase with hη | hη
  · obtain ⟨y, hgy, hηy⟩ := key 1 sfThT (ConjT.th S) sfThT_NF sfThT_free
      (by rw [sfThT_val, mul_one]) (by rw [mul_one, sfTh_opow])
      (lt_add_of_pos_right _ (by norm_num))
      (fun u x h => by
        rw [one_mul] at h
        have hs : Order.succ x = Order.succ u := by
          rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact h.symm
        have hx : x = u := Order.succ_eq_succ_iff.1 hs
        exact ⟨0, by rw [one_mul, Nat.cast_zero, add_zero]; exact hx, by simp⟩) hη
    have := Bt.iota_good hgy
    rw [← hηy, hιη] at this
    exact sfNotRst_succ _ (this ▸ hμ)
  · obtain ⟨y, hgy, hηy⟩ := key ω sfThW (ConjT.th S + 1) sfThW_NF sfThW_free (sfThW_val S)
      (by rw [opow_add, opow_one, sfTh_opow])
      ((add_lt_add_iff_left _).2 (by norm_num))
      (fun u x h => by
        have hle : ω * u ≤ x := by
          by_contra hh
          push Not at hh
          have h2 : x + ω ≤ ω * u := by
            refine le_of_forall_lt fun z hz => ?_
            rcases (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hz with ⟨d, hd, hzd⟩
            exact hzd.trans (sfAdd_lt_of_dvd (e := 1) hh (by rw [opow_one]; exact dvd_mul_right _ _)
              (by rwa [opow_one]))
          rw [← h] at h2
          exact absurd h2 (not_le.2 (lt_add_of_pos_right _ omega0_pos))
        obtain ⟨d, rfl⟩ := exists_add_of_le hle
        have hd : d < ω := by
          by_contra hh
          push Not at hh
          rw [add_assoc] at h
          have := add_left_cancel h
          have h3 : ω < d + ω := lt_of_lt_of_le (lt_add_of_pos_right _ omega0_pos)
            (add_le_add_left hh ω)
          rw [← this] at h3
          exact lt_irrefl _ h3
        obtain ⟨k, rfl⟩ := lt_omega0.1 hd
        exact ⟨k, rfl, by rw [← mul_add, natCast_add_omega0]⟩) hη
    have hown_g : ConjT.Aη S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y) ∈
        S.CSet (ConjT.Aη S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y))
          (S.psi (ConjT.Aη S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + y)) (Om 1)) := by
      refine sfOwn hgy (lt_of_le_of_lt (ConjT.A_mono S ?_) (sfA_lt hhi).2)
      rw [hηy]; exact le_self_add
    have := sfIota_omega hown_g
    rw [← hηy, hιη] at this
    exact sfNotRst_omega _ (this ▸ hμ)

/-- **`TpShift S` holds** (no hypothesis beyond Theorem GEN). -/
theorem sfShiftAll : Tp.TpShift S := sfShift sfRstMove

end Googology.Trans.PoR.InaccPsi.R2.Sf
