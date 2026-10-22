import Googology.Trans.PoR.InaccPsi.R2.GaTow

/-!
# How far the frontier method goes: every located frontier lies below `ι(Ω₂)`, and `P(Ω₂) < L(0)`

The frontier lemma (`R2.LgFr2.lgB1_eq2`, `R2.GaFr.gaB1_eq`) locates `Λ⁺(X) = ι(ω^T·ω)` from a top code `T` read by the
codes of the hull below `Ω₂` (at a named fixed point `F`, `m_F = e(η_F)` only while `e(η_F) < Ω₂`).  Here:

* `gaEnd_Om2` (**`ι(η) ≤ ι(Ω₂) < ι(Ω_ω)` and `P(η) ≤ P(Ω₂) < L(0) = P(Ω_ω)` for every name `η ≤ Ω₂`**);
* `gaEnd_front` (**every frontier located by `gaB1_eq` is below `ι(Ω₂)`, with `υ` below `P(Ω₂) < L(0)`**);
* `gaEnd_exp` (**a fixed point `F < ι(Ω₂)` has `e(η_F) < Ω₂`**; so `L(0) = υ_{ι(Ω_ω)}` is out of reach of every frontier
  lemma whose codes are last exponents below `Ω₂`: between `ι(Ω₂)` and `ι(Ω_ω)` the names have `e(η) ≥ Ω₂`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **`ι(η) ≤ ι(Ω₂) < ι(Ω_ω)` and `P(η) ≤ P(Ω₂) < L(0)` for every name `η ≤ Ω₂`.** -/
theorem gaEnd_Om2 {η : Ordinal.{0}} (hη : η ≤ Om (1 + 1)) :
    iota S η ≤ iota S (Om (1 + 1)) ∧ iota S (Om (1 + 1)) < iota S (Om ω) ∧
      Pv S η ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  ⟨iota_mono _ _ hη, cd_iota_lt_of_good (ga_Om2_good S) ph_Om2_lt_Omw, Pv_mono hη, ga_Pv_lt_L0 S le_rfl⟩

/-- **Every frontier located by the frontier lemma lies below `ι(Ω₂)`**, with `υ` below `P(Ω₂) < L(0)`. -/
theorem gaEnd_front {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ gaW) (hP : GaPoly X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y gaAt T) (hTcl : ∀ Z, SC Z → GxCl Z gaAt T)
    (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X < iota S (Om (1 + 1)) ∧ upsilon (xtB1 X) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  obtain ⟨h1, h2, -⟩ := gaB1_eq (S := S) hT hP htop hTcl hTO htopE hPk
  have hS2 := gg_SC_Om2
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC hS2
  have hT2 : T < Om (1 + 1) := hT.trans_lt (gaW_lt_Om2 S)
  have hlt : ω ^ T * ω < Om (1 + 1) :=
    InE.mul_lt hE2 (hE2 ▸ (opow_lt_opow_iff_right one_lt_omega0).2 hT2) (omega0_lt_inE hE2)
  have hcl : ∀ Z, SC Z → GxCl Z gaAt (ω ^ T * ω) := fun Z hZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact GxCl.opow hZ.1 (GxCl.add (hTcl Z hZ) (GxCl.small (gg_one_lt_of_SC hZ)))
  have hι : iota S (ω ^ T * ω) < iota S (Om (1 + 1)) := cd_iota_lt_of_good (ga_good hcl) hlt
  refine ⟨h1 ▸ hι, ?_, ga_Pv_lt_L0 S le_rfl⟩
  rw [h2, show Pv S (Om (1 + 1)) = upsilon (iota S (Om (1 + 1))) from (ups_iota S _).symm,
    show Pv S (ω ^ T * ω) = upsilon (iota S (ω ^ T * ω)) from (ups_iota S _).symm]
  exact upsilon_normal.strictMono hι

/-- **A named fixed point below `ι(Ω₂)` has `e(η_F) < Ω₂`.** -/
theorem gaEnd_exp {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (hlt : F < iota S (Om (1 + 1))) : cdExp (cdEta S F) < Om (1 + 1) := by
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC gg_SC_Om2
  have hw : Om (1 + 1 : Ordinal.{0}) * ω = ω ^ (Om (1 + 1) + 1) := by
    rw [opow_add, opow_one, hE2]
  have hle : F < iota S (ω ^ Om (1 + 1 : Ordinal.{0}) * ω) := by
    refine hlt.trans_le (iota_mono _ _ ?_)
    rw [hE2]; exact le_mul_of_one_le_right zero_le one_lt_omega0.le
  have h1 := phExp_le hF hfix hX hle
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
    obtain ⟨η0, hdec, -⟩ := cdExp_decomp (gg_name_ne hF hfix hX)
    have hge : Om (1 + 1 : Ordinal.{0}) ≤ cdEta S F := by
      rw [hdec, h, hE2]; exact le_add_self
    have := iota_mono (S := S) _ _ hge
    rw [hι] at this
    exact absurd hlt (not_lt.2 this)

end Googology.Trans.PoR.InaccPsi.R2.Ga
