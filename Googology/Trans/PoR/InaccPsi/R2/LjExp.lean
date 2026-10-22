import Googology.Trans.PoR.InaccPsi.R2.MvExp
import Googology.Trans.PoR.InaccPsi.R2.MwInd

/-!
# The last exponent of the name moves by `B_n`, for every last exponent

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `η_λ` the name of a
restart `λ` (`Cd.cdEta`), `e = cdExp(η_λ)` its last exponent.  `Mv.mvExp_move` moves `e < θ`.  Here every `e` with a
normal form: for `e < θ·ω` the first summand of a normal form of `e` is at most `θ`, so `θ + nf(e)` is a normal form
and `ω^{θ+e} = φ(0, θ + nf(e))`; for `e ≥ θ·ω`, `θ + e = e` and `B_n e ≥ θ·ω`, and the last summand is `φ(0, nf(e))`,
or `e` itself when `e` is an `ε`-number (then `B_n e` is one too).

* `ljHead_le_th` (the first summand of a normal form of `0 < e < θ·ω` is at most `θ`), `ljLast_shape`;
* `ljB_th`, `ljB_thw` (`B_n θ = θ`, `B_n(θ·ω) = θ·ω`), `ljSigLast` (**the image of a last summand `ω^{θ+e}` is
  `ω^{θ + B_n e}`**, every `e ≠ 0`);
* `ljExp_move` (**`cdExp(η_{λ'}) = B_n(e)`** for every last exponent `e` with a normal form).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- `θ·ω = ω^{θ+1}`. -/
theorem ljThW_eq (S : InaccSeq.{0}) : ConjT.th S * ω = ω ^ (ConjT.th S + 1) := by
  rw [opow_add, opow_one, sfTh_opow S]

/-- `θ·ω` is additively principal. -/
theorem ljThW_prin (S : InaccSeq.{0}) : IsPrincipal (· + ·) (ConjT.th S * ω) := by
  rw [ljThW_eq S]; exact isPrincipal_add_omega0_opow _

/-- A nonzero additively principal number below `θ·ω` is at most `θ`. -/
theorem ljPrin_le_th {p : Ordinal.{0}} (hP : IsPrincipal (· + ·) p) (hp0 : p ≠ 0)
    (hp : p < ConjT.th S * ω) : p ≤ ConjT.th S := by
  obtain ⟨c, rfl⟩ := Googology.Notation.InaccPsi.exists_opow_of_principal hP hp0
  rw [ljThW_eq S] at hp
  have hc : c < ConjT.th S + 1 := (opow_lt_opow_iff_right one_lt_omega0).1 hp
  rw [← sfTh_opow S]
  exact opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 hc)

/-- **The first summand of a normal form of `0 < e < θ·ω` is at most `θ`.** -/
theorem ljHead_le_th {t : Term} (ht : NF t) (ht0 : t ≠ Term.zero) (hlt : val S t < ConjT.th S * ω) :
    val S (head t) ≤ ConjT.th S := by
  have hprin : (head t).isPrin = true := by
    cases t with
    | zero => exact absurd rfl ht0
    | add a b => exact ht.2.2.1
    | _ => rfl
  have hP := isPrincipal_val S (NF.head ht) hprin
  have hne : val S (head t) ≠ 0 := by
    cases t with
    | zero => exact absurd rfl ht0
    | add a b => exact val_ne_zero S ht.1 (by
        intro h; rw [h] at hprin; simp [isPrin, isSC] at hprin)
    | _ => exact val_ne_zero S ht ht0
  exact ljPrin_le_th hP hne ((Bc.val_head_le (S := S) ht).trans_lt hlt)

/-- **A normal form of `ω^{θ+e}`** (`0 < e < θ·ω`, `e` with a normal form) is `φ(0, θ + nf(e))`. -/
theorem ljLast_shape {p : Term} (hp : NF p) {e : Ordinal.{0}} (he0 : e ≠ 0)
    (heθ : e < ConjT.th S * ω) (hmem : e ∈ ⋃ a, S.CSet a 0) (hv : val S p = ω ^ (ConjT.th S + e)) :
    p = phi Term.zero (add sfThT (bcNf S e)) := by
  have hθ := sfTh_pos S
  -- `θ + e` is not an ε-number
  have hne : ω ^ (ConjT.th S + e) ≠ ConjT.th S + e := by
    intro h
    have h1 : ConjT.th S * ω ≤ ω ^ (ConjT.th S + e) := by
      rw [opow_add, sfTh_opow S]
      have hωe : (ω : Ordinal.{0}) ≤ ω ^ e := by
        have := (opow_le_opow_iff_right one_lt_omega0).2 (Order.one_le_iff_ne_zero.2 he0)
        rwa [opow_one] at this
      exact mul_le_mul_right hωe _
    have h2 : ConjT.th S + e < ConjT.th S * ω :=
      ljThW_prin S ((lt_mul_iff_one_lt_right hθ).2 one_lt_omega0) heθ
    rw [h] at h1
    exact absurd h2 (not_lt.2 h1)
  have hmemE : ∀ {v : Ordinal.{0}}, v = ω ^ (ConjT.th S + e) → ω ^ v = v → False := by
    intro v hv' hE
    rw [hv'] at hE
    exact hne ((opow_right_inj one_lt_omega0).1 hE)
  have hSC : ¬ SC (val S p) := fun hs => hmemE hv (Low.opow_eq_self_of_SC hs)
  -- the term of `θ + e`
  obtain ⟨hNe, hve⟩ := bcNf_spec S hmem
  have hne0 : bcNf S e ≠ Term.zero := fun h => he0 (by rw [← hve, h]; rfl)
  have hNY : NF (add sfThT (bcNf S e)) := by
    refine ⟨sfThT_NF, hNe, rfl, hne0, ?_⟩
    have hle : val S (head (bcNf S e)) ≤ val S sfThT := by
      rw [sfThT_val]; exact ljHead_le_th hNe hne0 (by rw [hve]; exact heθ)
    rw [cmp_eq_compare S (NF.head hNe) sfThT_NF]
    intro hgt
    exact absurd (compare_gt_iff_gt.1 hgt) (not_lt.2 hle)
  cases p with
  | zero => exact absurd hv (opow_pos (ConjT.th S + e) omega0_pos).ne
  | add a b =>
    exfalso
    have hI : Indec (val S (Term.add a b)) := by
      rw [hv]
      exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    have := isPrin_of_indec hp hI
    simp [isPrin, isSC] at this
  | inacc m => exact absurd (SC_val S hp rfl) hSC
  | inaccW => exact absurd (SC_val S hp rfl) hSC
  | om a => exact absurd (SC_val S hp rfl) hSC
  | psiS s a => exact absurd (SC_val S hp rfl) hSC
  | psiI m a => exact absurd (SC_val S hp rfl) hSC
  | phi c d =>
    by_cases hc : c = Term.zero
    · subst hc
      have hvd : val S d = ConjT.th S + e := by
        simp only [val, veblen_zero] at hv
        exact (opow_right_inj one_lt_omega0).1 hv
      have : d = add sfThT (bcNf S e) :=
        eq_of_val_eq S hp.2.1 hNY (by rw [hvd]; show _ = val S sfThT + val S (bcNf S e); rw [sfThT_val, hve])
      rw [this]
    · exfalso
      have hpos : 0 < val S c := pos_iff_ne_zero.2 (val_ne_zero S hp.1 hc)
      exact hmemE hv (Tp.tpVeblen_fix hpos)

/-! ## `B_n` on `θ`, `θ·ω`, and on the last summand `ω^{θ+e}` -/

/-- `θ ∈ MvD` and `B_n θ = θ`. -/
theorem ljB_th {n : ℕ} : Mv.MvD S (ConjT.th S) ∧ Bc.bcB S n (ConjT.th S) = ConjT.th S := by
  have h := sfThT_D (S := S)
  rw [← sfThT_val S]
  exact ⟨Mv.mvD_of_term h, by rw [Mv.mvB_term h, bcSig_free sfThT_free]⟩

/-- `θ·ω ∈ MvD` and `B_n(θ·ω) = θ·ω`. -/
theorem ljB_thw {n : ℕ} : Mv.MvD S (ConjT.th S * ω) ∧ Bc.bcB S n (ConjT.th S * ω) = ConjT.th S * ω := by
  obtain ⟨hDt, hBt⟩ := ljB_th (S := S) (n := n)
  have hD1 : Mv.MvD S (1 : Ordinal.{0}) :=
    Mv.mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDs, hBs⟩ := Mv.mvB_add (k := n) hDt hD1
  have hne : ω ^ (ConjT.th S + 1) ≠ ConjT.th S + 1 := by
    intro h
    have h1 : ConjT.th S + 1 < ConjT.th S * ω :=
      ljThW_prin S ((lt_mul_iff_one_lt_right (sfTh_pos S)).2 one_lt_omega0)
        (one_lt_omega0.trans ((lt_mul_iff_one_lt_right (sfTh_pos S)).2 one_lt_omega0 |>.trans_le' ?_))
    · rw [ljThW_eq S, h] at h1; exact lt_irrefl _ h1
    · exact (Lw.lw_omega_lt_SC (ConjT.SC_th S)).le
  obtain ⟨hDo, hBo⟩ := Mv.mvB_opow (k := n) hDs hne
  rw [ljThW_eq S]
  exact ⟨hDo, by rw [hBo, hBs, hBt, Mw.mwB_one]⟩

/-- **The image of the last summand**: if `p ∈ D` has the value `ω^{θ+e}` (`e ≠ 0`), then `σ_n(p)` has the value
`ω^{θ + B_n e}`. -/
theorem ljSigLast {n : ℕ} {p : Term} (hDp : bcD S p) {e : Ordinal.{0}} (he0 : e ≠ 0)
    (hmem : e ∈ ⋃ a, S.CSet a 0) (hv : val S p = ω ^ (ConjT.th S + e)) :
    val S (bcSig (bcPre (n + 1)) bcPreW p) = ω ^ (ConjT.th S + Bc.bcB S n e) := by
  by_cases heθ : e < ConjT.th S * ω
  · have hshape := ljLast_shape hDp.1 he0 heθ hmem hv
    rw [hshape, bcSig_phi, bcSig_zero, bcSig_add, bcSig_free sfThT_free]
    show veblen 0 (val S sfThT + val S (bcSig (bcPre (n + 1)) bcPreW (bcNf S e))) = _
    rw [veblen_zero, sfThT_val]
    rfl
  have hle : ConjT.th S * ω ≤ e := not_lt.1 heθ
  have hθlt : ConjT.th S < ω ^ (ConjT.th S + 1) := by
    rw [← ljThW_eq S]; exact (lt_mul_iff_one_lt_right (sfTh_pos S)).2 one_lt_omega0
  have hθe : ConjT.th S + e = e :=
    Ordinal.add_of_omega0_opow_le hθlt (by rw [← ljThW_eq S]; exact hle)
  obtain ⟨hDw, hBw⟩ := ljB_thw (S := S) (n := n)
  -- `θ·ω ≤ B_n e` for `e ∈ MvD`
  have hBge : ∀ (hDe : Mv.MvD S e), ConjT.th S * ω ≤ Bc.bcB S n e := fun hDe => by
    have := not_lt.2 hle
    rw [← Mv.mvB_lt_iff (k := n) hDe hDw, hBw] at this
    exact not_lt.1 this
  rw [hθe] at hv
  have hBθ : ∀ (hDe : Mv.MvD S e), ConjT.th S + Bc.bcB S n e = Bc.bcB S n e := fun hDe =>
    Ordinal.add_of_omega0_opow_le hθlt (by rw [← ljThW_eq S]; exact hBge hDe)
  have hσv : val S (bcSig (bcPre (n + 1)) bcPreW p) = Bc.bcB S n (val S p) := (Mv.mvB_term hDp).symm
  by_cases hE : ω ^ e = e
  · -- `e` is an `ε`-number: `p = φ(c, d)` with `c ≠ 0`
    rw [hE] at hv
    have hDe : Mv.MvD S e := hv ▸ Mv.mvD_of_term hDp
    have hBe : Bc.bcB S n e = val S (bcSig (bcPre (n + 1)) bcPreW p) := by rw [hσv, hv]
    have hfix : ω ^ val S (bcSig (bcPre (n + 1)) bcPreW p) = val S (bcSig (bcPre (n + 1)) bcPreW p) →
        Bc.bcB S n e = ω ^ Bc.bcB S n e := fun h => by rw [hBe]; exact h.symm
    have hSCσ : p.isSC = true → SC (val S (bcSig (bcPre (n + 1)) bcPreW p)) := fun h =>
      SC_val S (bc_NF (k := n) hDp) (by rw [isSC_bcSig]; exact h)
    rw [hBθ hDe, hσv, hv]
    cases p with
    | zero => exact absurd hv.symm he0
    | add a b =>
      exfalso
      have hI : Indec (val S (Term.add a b)) := by
        rw [hv, ← hE]
        exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
      have := isPrin_of_indec hDp.1 hI
      simp [isPrin, isSC] at this
    | inacc m => exact hfix (Low.opow_eq_self_of_SC (hSCσ rfl))
    | inaccW => exact hfix (Low.opow_eq_self_of_SC (hSCσ rfl))
    | om a => exact hfix (Low.opow_eq_self_of_SC (hSCσ rfl))
    | psiS s a => exact hfix (Low.opow_eq_self_of_SC (hSCσ rfl))
    | psiI m a => exact hfix (Low.opow_eq_self_of_SC (hSCσ rfl))
    | phi c d =>
      by_cases hc : c = Term.zero
      · exfalso
        subst hc
        have hd : val S d < val S (phi Term.zero d) := (cmp_lt_iff S hDp.1.2.1 hDp.1).1 hDp.1.2.2.2
        have hvd : val S (phi Term.zero d) = ω ^ val S d := by simp only [val, veblen_zero]
        rw [hvd] at hd hv
        have : val S d = e := by
          have h2 : ω ^ val S d = ω ^ e := by rw [hv, hE]
          exact (opow_right_inj one_lt_omega0).1 h2
        rw [this, hE] at hd
        exact lt_irrefl _ hd
      · have hDc : bcD S c := bcD_sub hDp (Or.inr (Or.inl (Or.inl rfl)))
        have hNc := bc_NF (k := n) hDc
        have hc0 : 0 < val S (bcSig (bcPre (n + 1)) bcPreW c) :=
          pos_iff_ne_zero.2 (val_ne_zero S hNc (bcSig_ne_zero hc))
        have hBv : Bc.bcB S n e = veblen (val S (bcSig (bcPre (n + 1)) bcPreW c))
            (val S (bcSig (bcPre (n + 1)) bcPreW d)) := by
          rw [← hv, Mv.mvB_term hDp, bcSig_phi]; rfl
        rw [hBv]; exact (Tp.tpVeblen_fix hc0).symm
  · -- `e` is not an `ε`-number: `p = φ(0, d)` with `|d| = e`
    have hnSC : ¬ SC (val S p) := fun h => by
      have h1 := Low.opow_eq_self_of_SC h
      rw [hv] at h1
      exact hE ((opow_right_inj one_lt_omega0).1 h1)
    cases p with
    | zero => exact absurd hv (opow_pos e omega0_pos).ne
    | add a b =>
      exfalso
      have hI : Indec (val S (Term.add a b)) := by
        rw [hv]
        exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
      have := isPrin_of_indec hDp.1 hI
      simp [isPrin, isSC] at this
    | inacc m => exact absurd (SC_val S hDp.1 rfl) hnSC
    | inaccW => exact absurd (SC_val S hDp.1 rfl) hnSC
    | om a => exact absurd (SC_val S hDp.1 rfl) hnSC
    | psiS s a => exact absurd (SC_val S hDp.1 rfl) hnSC
    | psiI m a => exact absurd (SC_val S hDp.1 rfl) hnSC
    | phi c d =>
      by_cases hc : c = Term.zero
      · subst hc
        have hvd : val S d = e := by
          simp only [val, veblen_zero] at hv
          exact (opow_right_inj one_lt_omega0).1 hv
        have hDd : bcD S d := bcD_sub hDp (Or.inr (Or.inr (Or.inl rfl)))
        have hDe : Mv.MvD S e := hvd ▸ Mv.mvD_of_term hDd
        rw [hBθ hDe, bcSig_phi, bcSig_zero]
        show veblen 0 (val S (bcSig (bcPre (n + 1)) bcPreW d)) = _
        rw [veblen_zero, ← Mv.mvB_term hDd, hvd]
      · exfalso
        have hpos : 0 < val S c := pos_iff_ne_zero.2 (val_ne_zero S hDp.1.1 hc)
        have h1 := Tp.tpVeblen_fix (d := val S d) hpos
        have h2 : val S (phi c d) = veblen (val S c) (val S d) := rfl
        rw [← h2, hv] at h1
        exact hE ((opow_right_inj one_lt_omega0).1 h1)

/-! ## The last exponent of the image name -/

/-- **The last exponent moves by `B_n`** (every last exponent `e` with a normal form; `Mv.mvExp_move` had `e < θ`). -/
theorem ljExp_move {n : ℕ} {l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1))
    (hmem : Cd.cdExp (Cd.cdEta S l) ∈ ⋃ a, S.CSet a 0) :
    ∃ η', Bt.Good S η' ∧ Bc.bcB S n (upsilon l) = upsilon (Bt.iota S η') ∧
      Cd.cdEta S (Bt.iota S η') = η' ∧
      Cd.cdExp η' = Bc.bcB S n (Cd.cdExp (Cd.cdEta S l)) := by
  have hL : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  obtain ⟨hg, -, -, hpv⟩ := Cd.cdEta_pv_spec (S := S) hl0 (hL ▸ h2)
  set η := Cd.cdEta S l with hη
  rw [← hpv] at h1 h2 ⊢
  obtain ⟨ρ, hD, -, -, hAη, hdρ, hB, hNT⟩ := sfData hg h1.le h2
  obtain ⟨ζ, hζ⟩ := hdρ
  obtain ⟨ζ', hζ'⟩ := sfSig_dvd n hD ⟨ζ, hζ⟩
  have hηe : η = Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + ζ := by
    refine sfA_inj (S := S) ?_
    rw [hAη, hζ, Bt.A_add, ← sfAlpha_eq]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [add_zero] at hηe
    have : Pv S η = Bc.bcC S n := by rw [hηe, ← Lw.lw_L_eq]; rfl
    exact absurd h1 (by rw [this]; exact lt_irrefl _)
  have hρ0 : ρ ≠ Term.zero := by
    rintro rfl
    have : ConjT.th S * ζ = 0 := by rw [← hζ]; rfl
    exact hζ0 ((mul_eq_zero.1 this).resolve_left (sfTh_pos S).ne')
  have hexp : Cd.cdExp η = Cd.cdExp ζ := by rw [hηe]; exact sfCdExp_add _ hζ0
  have hlast : val S (sfLast ρ) = ω ^ (ConjT.th S + Cd.cdExp ζ) := by
    have hd := Cd.cdExp_dvd (mul_ne_zero (sfTh_pos S).ne' hζ0)
    obtain ⟨Y, hY, -⟩ := Cd.cdExp_decomp (mul_ne_zero (sfTh_pos S).ne' hζ0)
    rw [sfCdExp_th S hζ0] at hY
    exact sfLast_val hD.1 hρ0 (by rw [hζ]; exact hY)
  have hlN : NF (sfLast ρ) := NF_of_sub (sfLast_sub ρ) hD.1
  have hσl : val S (sfLast (bcSig (bcPre (n + 1)) bcPreW ρ)) =
      ω ^ (ConjT.th S + Bc.bcB S n (Cd.cdExp ζ)) := by
    rcases eq_or_ne (Cd.cdExp ζ) 0 with h0 | h0
    · have hθv : val S (sfLast ρ) = val S sfThT := by
        rw [hlast, h0, add_zero, sfThT_val, sfTh_opow]
      have e1 := eq_of_val_eq S hlN sfThT_NF hθv
      rw [sfLast_sig, e1, bcSig_free sfThT_free, sfThT_val, h0, Bc.bcB_zero, add_zero, sfTh_opow]
    · rw [sfLast_sig]
      exact ljSigLast (n := n) (bcD_sub hD (sfLast_sub ρ)) h0 (hexp ▸ hmem) hlast
  have hσN := bc_NF (k := n) hD
  have hσ0 : bcSig (bcPre (n + 1)) bcPreW ρ ≠ Term.zero := bcSig_ne_zero hρ0
  have hζ'0 : ζ' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ'
    exact val_ne_zero S hσN hσ0 hζ'
  have hexp' : Cd.cdExp ζ' = Bc.bcB S n (Cd.cdExp ζ) := by
    have c1 := sfCdExp_last hσN hσl
    rw [hζ', sfCdExp_th S hζ'0] at c1
    exact add_left_cancel c1
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
  have hg' := sfGood_of_own hown'
  refine ⟨η', hg', ?_, Cd.cdEta_unique hg' rfl, ?_⟩
  · rw [hB, Bt.ups_iota S η', hAη']
  · rw [hη', sfCdExp_add _ hζ'0, hexp', hexp]

end Googology.Trans.PoR.InaccPsi.R2.Lj
