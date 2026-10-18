import Googology.Trans.PoR.InaccPsi.R2.MvDom

/-!
# The last exponent of the name moves by `B_n` beyond `L(ω)`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `η_λ` the name of a
restart `λ` (`Cd.cdEta`), `e = cdExp(η_λ)` its last exponent.  `Sf.sfExp_move` moves `e` for `e < L(ω)`; the same
proof works for every `e < θ` with a normal form (the bound `e < L(ω)` was used only to get `e < θ` and a normal
form of `e`).

* `mvLast_shape`: a normal form of `ω^{θ+e}` (`0 < e < θ`, `e` with a normal form) is `φ(0, θ + nf(e))`;
* `mvExp_move` (**`cdExp(η_{λ'}) = B_n(e)`**): at a restart `λ` with `c_n < ρ_λ < c_{n+1}`, `e < θ` with a normal
  form, the image name `η'` is good, `B_n ρ_λ = υ_{ι(η')}`, `cdEta(ι η') = η'` and `cdExp(η') = B_n(e)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- **A normal form of `ω^{θ+e}`** (`0 < e < θ`, `e` with a normal form) is `φ(0, θ + nf(e))`. -/
theorem mvLast_shape {p : Term} (hp : NF p) {e : Ordinal.{0}} (he0 : e ≠ 0)
    (heθ : e < ConjT.th S) (hmem : e ∈ ⋃ a, S.CSet a 0) (hv : val S p = ω ^ (ConjT.th S + e)) :
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
    have h2 : ConjT.th S + e < ConjT.th S * ω := by
      calc ConjT.th S + e < ConjT.th S + ConjT.th S := (add_lt_add_iff_left _).2 heθ
        _ = ConjT.th S * 2 := by
          rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        _ < ConjT.th S * ω := (mul_lt_mul_iff_right₀ hθ).2 (by exact_mod_cast natCast_lt_omega0 2)
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
    have := cmp_lt_of_val S hNe.head sfThT_NF
      (by rw [sfThT_val]; exact lt_of_le_of_lt (val_head_le S hNe) (by rw [hve]; exact heθ))
    rw [this]; simp
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

/-! ## The last exponent of the image name -/

/-- **The last exponent moves by `B_n`** (every last exponent `e < θ` with a normal form). -/
theorem mvExp_move {n : ℕ} {l : Ordinal.{0}} (hl0 : l ≠ 0) (h1 : Bc.bcC S n < upsilon l)
    (h2 : upsilon l < Bc.bcC S (n + 1)) (heθ : Cd.cdExp (Cd.cdEta S l) < ConjT.th S)
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
  -- the source name
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
  -- the last summand of `ρ`
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
    · have hshape := mvLast_shape hlN h0 (hexp ▸ heθ) (hexp ▸ hmem) hlast
      rw [sfLast_sig, hshape, bcSig_phi, bcSig_zero, bcSig_add, bcSig_free sfThT_free]
      show veblen 0 (val S sfThT + val S (bcSig (bcPre (n + 1)) bcPreW (bcNf S (Cd.cdExp ζ)))) = _
      rw [veblen_zero, sfThT_val]
      rfl
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
  -- the target name
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

end Googology.Trans.PoR.InaccPsi.R2.Mv
