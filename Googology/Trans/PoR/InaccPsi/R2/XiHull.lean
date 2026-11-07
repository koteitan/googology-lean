import Googology.Trans.PoR.InaccPsi.R2.XiImg
import Googology.Trans.PoR.InaccPsi.R2.CdCodes

/-!
# XiHull: BELOW `θ` THE HULL READING `Θ_λ` IS THE READING `R_{ρ_λ}`

A hull `Cl(A, ρ)` with `Ω_ω ≤ A`, `ρ ≤ Ω₁` strongly critical, `Cl(A, ρ) ∩ Ω₁ ⊆ ρ` and every ordinal below `ρ` of the
notation has below `θ` exactly the codes of `qtU` over `ρ` (THE HULL LEMMA `Zb.ZbAS.Ok.hull` one way; the atoms lie in
the hull, `Zb.ZbAS.Ok.mem`, the other way), i.e. `WDom S ρ` (`Xi.xi_dom_codes`).  So its order type function below
`θ` is `R_ρ` (`Xi.xiR_otp`).  For a restart `λ` with `ρ_λ = P(η_λ)` the hull of `λ` has `A = Ω_ω + θ·η_λ ≥ Ω_ω`:

* `xi_hull_iff` (**`c ∈ Cl(A, ρ) ↔ c ∈ WDom S ρ`** for `c < θ`), `xi_hull_otp` (**`otp(Cl(A, ρ) ∩ c) = R_ρ(c)`**);
* `xi_cdTheta` (**`Θ_λ(c) = R_{ρ_λ}(c)`** for every code `c < θ` visible at `ρ_λ`, when `ρ_λ = P(η_λ)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **Below `θ` the hull `Cl(A, ρ)` is `WDom S ρ`.** -/
theorem xi_hull_iff {A ρ : Ordinal.{0}} (hA : Om ω ≤ A) (hρS : SC ρ) (hρ1 : ρ < Om1)
    (hcnt : ∀ y ∈ S.CSet A ρ, y < Om 1 → y < ρ) (hnot : ∀ z < ρ, z ∈ ⋃ e, S.CSet e 0)
    {c : Ordinal.{0}} (hcθ : c < ConjT.th S) : c ∈ S.CSet A ρ ↔ WDom S ρ c := by
  have hρ1' : ρ ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hρ1.le
  rw [← xi_dom_codes hρS hρ1 hcθ]
  constructor
  · intro hc
    exact (Qt.qtU_ok S).hull A ρ hρS hρ1' hcnt c hc hcθ
  · intro hc
    clear hcθ
    induction hc with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs => exact (Qt.qtU_ok S).mem A ρ ρ _ hA hρS hρ1' le_rfl hnot hs
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The order type of the hull below a code `c < θ` visible at `ρ` is `R_ρ(c)`.** -/
theorem xi_hull_otp {A ρ : Ordinal.{0}} (hA : Om ω ≤ A) (hρS : SC ρ) (hρ1 : ρ < Om1)
    (hcnt : ∀ y ∈ S.CSet A ρ, y < Om 1 → y < ρ) (hnot : ∀ z < ρ, z ∈ ⋃ e, S.CSet e 0)
    {c : Ordinal.{0}} (hc : WDom S ρ c) (hcθ : c < ConjT.th S) :
    Cd.cdOtp (S.CSet A ρ) c = xiR ρ c := by
  rw [xiR_otp S (Low.opow_eq_self_of_SC hρS) hρ1 c hc]
  exact Gg.ggOtp_congr c fun d hd => xi_hull_iff hA hρS hρ1 hcnt hnot (hd.trans hcθ)

/-- **`Θ_λ(c) = R_{ρ_λ}(c)`** for a code `c < θ` visible at `ρ_λ = P(η_λ)` (`ρ_λ` strongly critical, every ordinal
below it of the notation). -/
theorem xi_cdTheta {l c : Ordinal.{0}} (hpv : Nm.Pv S (Cd.cdEta S l) = upsilon l) (hρS : SC (upsilon l))
    (hρ1 : upsilon l < Om1) (hnot : ∀ z < upsilon l, z ∈ ⋃ e, S.CSet e 0) (hc : WDom S (upsilon l) c)
    (hcθ : c < ConjT.th S) : Cd.cdTheta S l c = xiR (upsilon l) c := by
  have hA : Om ω ≤ ConjT.Aη S (Cd.cdEta S l) := le_self_add
  have hcnt : ∀ y ∈ Cd.cdHull S l, y < Om 1 → y < upsilon l := fun y hy hy1 => by
    rw [← hpv]
    unfold Cd.cdHull at hy
    rw [← hpv] at hy
    exact lt_psi_of_mem Low.InR_Om_one hy hy1
  unfold Cd.cdTheta
  exact xi_hull_otp hA hρS hρ1 hcnt hnot hc hcθ

end Googology.Trans.PoR.InaccPsi.R2.Xi
