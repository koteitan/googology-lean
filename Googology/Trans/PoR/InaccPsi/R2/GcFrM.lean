import Googology.Trans.PoR.InaccPsi.R2.GcFr

/-!
# THE FRONTIER LEMMA with the codes `m_λ` in place of the last exponents `e(η_λ)`

Past `ι(Ω₂)` the names have `e(η) ≥ Ω₂`, and there the code is the π-code `m_λ = π_{η_λ} = ψ_{Ω₂}(A_η) ≠ e(η_λ)`
(`cdCodeOf`).  Here THEOREM UNI and the frontier lemma of `R2.GcUni` / `R2.GcFr` restated with `m_λ`:

* `gc_V_lt_pi` (**`Γ_{Ω₁+ε₀} < π_η`** for every name `η`), `gc_code_ge` (**`e(η) ≥ Ω₂` ⇒ `m = π_η`, `m ≠ e(η)`,
  `Γ_{Ω₁+ε₀} < m`**), `gc_code_eq_exp` (**`m_F ≤ Γ_{Ω₁+ε₀}` ⇒ `m_F = e(η_F)`** at a named fixed point);
* `gcUniM` (**THEOREM UNI with codes**: `Θ_F(m_F) = O_X(F)` at every named fixed point with `m_F ≤ E`, `E ≤
  Γ_{Ω₁+ε₀}`, `GcPoly X E`), `gcFr_code` (**THE FRONTIER LEMMA with codes**: every named fixed frontier `λ` of a system
  with top code `T ≤ Γ_{Ω₁+ε₀}` has `T ≤ m_λ`);
* `gc_past_Om2` (**every named fixed `λ` with `e(η_λ) ≥ Ω₂` has `ι(Ω₂) ≤ λ`, `m_λ = π_{η_λ} ≠ e(η_λ)`,
  `m_λ > Γ_{Ω₁+ε₀}`**),
  `gc_frontier_lt_Om2` (**every frontier `Λ⁺(X) = ι(T·ω)` of such a system is below `ι(Ω₂)`**): the frontiers past
  `ι(Ω₂)` need systems with top codes `≥ π`-codes.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

theorem gc_two_ne : (1 + 1 : Ordinal.{0}) ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'

theorem gc_eps0_mem (a b : Ordinal.{0}) : (ε₀ : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem a b) (CSet.zero_mem a b)

theorem gc_eps0_lt_A (η : Ordinal.{0}) : ε₀ < ConjT.Aη S η := by
  have h1 : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  exact (gc_eps0_le_Om1.trans_lt h1).trans_le le_self_add

/-- **`Γ_{Ω₁+ε₀} < π_η = ψ_{Ω₂}(A_η)`** for every name `η`. -/
theorem gc_V_lt_pi (S : InaccSeq.{0}) (η : Ordinal.{0}) : gcV < cdPi S η := by
  rw [← gcV_psi S]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (gc_eps0_lt_A η) (gc_eps0_mem _ _)

/-- **Past `Ω₂` the code is the π-code**: `e(η) ≥ Ω₂` gives `m = π_η`, `m ≠ e(η)`, `Γ_{Ω₁+ε₀} < m`. -/
theorem gc_code_ge (S : InaccSeq.{0}) {η : Ordinal.{0}} (h : Om (1 + 1) ≤ cdExp η) :
    cdCodeOf S η = cdPi S η ∧ cdCodeOf S η ≠ cdExp η ∧ gcV < cdCodeOf S η := by
  have e : cdCodeOf S η = cdPi S η := if_neg (not_lt.2 h)
  refine ⟨e, ?_, ?_⟩
  · rw [e]; exact ((cdPi_lt S η).trans_le h).ne
  · rw [e]; exact gc_V_lt_pi S η

/-- **`m_F ≤ Γ_{Ω₁+ε₀}` gives `m_F = e(η_F)`** at a named fixed point. -/
theorem gc_code_eq_exp {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hm : cdCode S F ≤ gcV) : cdExp (cdEta S F) = cdCode S F := by
  rcases lt_or_ge (cdExp (cdEta S F)) (Om (1 + 1)) with h | h
  · have hFe := Fx.fxExp_fix hF hfix hX
    have hω : ω ≤ cdExp (cdEta S F) :=
      ((le_mul_left _ omega0_pos).trans (gg_ww_lt hF hfix).le).trans hFe
    unfold cdCode
    rw [cdCodeOf_of_lt h, cpOff_of_ge hω]
  · exact absurd hm (not_le.2 (gc_code_ge S h).2.2)

/-- **THEOREM UNI with codes**: `Θ_F(m_F) = O_X(F)` at every named fixed point `F` with `m_F ≤ E`, for every term
system `X` with `GcPoly X E`, `E ≤ Γ_{Ω₁+ε₀}`. -/
theorem gcUniM {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ gcV) (hP : GcPoly X E) {F ηx : Ordinal.{0}}
    (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) (hm : cdCode S F ≤ E) :
    cdTheta S F (cdCode S F) = xtOrec X F :=
  gcUniTh hE hP hF hfix hX (by rw [gc_code_eq_exp hF hfix hX (hm.trans hE)]; exact hm)

/-- **THE FRONTIER LEMMA with codes**: every named fixed frontier `λ` of a system `X` with `GcPoly X T`, top
`Θ_y(T)`, `T ≤ Γ_{Ω₁+ε₀}`, has `T ≤ m_λ` (for `e(η_λ) < Ω₂` this is `gcFr_exp`; for `e(η_λ) ≥ Ω₂`, `m_λ = π_{η_λ} >
Γ_{Ω₁+ε₀}`). -/
theorem gcFr_code {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ gcV) (hP : GcPoly X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y gcAt T) {l ηx : Ordinal.{0}} (hl : XtFr X l)
    (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) : T ≤ cdCode S l := by
  rcases lt_or_ge (cdExp (cdEta S l)) (Om (1 + 1)) with h | h
  · have he := gcFr_exp (S := S) hT hP htop hl hfix hX
    have hFe := Fx.fxExp_fix hl.1 hfix hX
    have hω : ω ≤ cdExp (cdEta S l) :=
      ((le_mul_left _ omega0_pos).trans (gg_ww_lt hl.1 hfix).le).trans hFe
    unfold cdCode
    rw [cdCodeOf_of_lt h, cpOff_of_ge hω]
    exact he
  · exact hT.trans (gc_code_ge S h).2.2.le

/-- **Past `ι(Ω₂)`**: every named fixed point `λ` with `e(η_λ) ≥ Ω₂` has `ι(Ω₂) ≤ λ`, `m_λ = π_{η_λ} ≠ e(η_λ)` and
`Γ_{Ω₁+ε₀} < m_λ`. -/
theorem gc_past_Om2 {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx)
    (h : Om (1 + 1) ≤ cdExp (cdEta S l)) :
    iota S (Om (1 + 1)) ≤ l ∧ cdCode S l = cdPi S (cdEta S l) ∧ cdCode S l ≠ cdExp (cdEta S l) ∧
      gcV < cdCode S l := by
  obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hη0 : cdEta S l ≠ 0 := gg_name_ne hl hfix hX
  have hdv := cdExp_dvd hη0
  have hΩ : Om (1 + 1 : Ordinal.{0}) = ω ^ Om (1 + 1) :=
    (Low.opow_eq_self_of_SC (SC_Om gc_two_ne)).symm
  have hle : Om (1 + 1) ≤ cdEta S l :=
    hΩ.le.trans ((opow_le_opow_right omega0_pos h).trans (le_of_dvd hη0 hdv))
  refine ⟨?_, (gc_code_ge S h).1, (gc_code_ge S h).2.1, (gc_code_ge S h).2.2⟩
  rw [← hι]
  exact iota_mono _ _ hle

/-- **Every frontier `Λ⁺(X) = ι(T·ω)` of a system with a top code `Ω₁ ≤ T ≤ Γ_{Ω₁+ε₀}` is below `ι(Ω₂)`.** -/
theorem gc_frontier_lt_Om2 {T : Ordinal.{0}} (hT : T ≤ gcV) (hTcl : ∀ Z, SC Z → GxCl Z gcAt (T * ω)) :
    iota S (T * ω) < iota S (Om (1 + 1)) := by
  refine cd_iota_lt_of_good (gc_good hTcl) ?_
  have hE : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC (SC_Om gc_two_ne)
  exact InE.mul_lt hE (hT.trans_lt (gcV_lt_Om2 S)) (omega0_lt_inE hE)

end Googology.Trans.PoR.InaccPsi.R2.Gc
