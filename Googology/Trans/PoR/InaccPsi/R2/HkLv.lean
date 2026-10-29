import Googology.Trans.PoR.InaccPsi.R2.HjLim

/-!
# HkLv: THE LEVEL DATUM `Ω₁·M` READ AS `x·M`, FOR EVERY `1 ≤ M < ε₀`

`Ω₁·M` with `M < ε₀` is a finite sum of terms `Ω₁·ω^e = φ(0, Ω₁ + e)` (`e < ε₀`), so it lies in every hull
`C(a, b)` and is a code over every strongly critical `Z ≤ Ω₁` (`hk_mul_mem`, `hk_mul_code`).  Its reading is `x·M`;
Lemma EXACT `π_{σ,ρ}(ρ·M) = σ·M` is `Exact.pi_mul`, since `M < ε₀ ≤ σ` at every base `σ`.

* `hk_split` (`M = ω^{log M} + r`, `r < M`), `hk_om_opow` (`Ω₁·ω^e = φ(0, Ω₁ + e)`), `hk_mul_mem`, `hk_mul_code`;
* `hkLv M` (**THE LEVEL DATUM `Ω₁·M`**), `hkLv_L`, `hkLv_l`;
* cofinality of multiples along a cofinal sequence: `hk_mul_cof`, `hk_mul_cof1`.

No new axiom.  New definition: `hkLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **`M = ω^{log M} + r` with `r < M`** for `M ≠ 0`. -/
theorem hk_split {M : Ordinal.{0}} (h0 : M ≠ 0) :
    ω ^ log ω M + (M - ω ^ log ω M) = M ∧ M - ω ^ log ω M < M := by
  have hwd : ω ^ log ω M ≤ M := opow_log_le_self ω h0
  have hdr : ω ^ log ω M + (M - ω ^ log ω M) = M := Ordinal.add_sub_cancel_of_le hwd
  refine ⟨hdr, ?_⟩
  rcases (Ordinal.sub_le_self M (ω ^ log ω M)).lt_or_eq with hrd | hrd
  · exact hrd
  · exfalso
    have h1 : ω ^ log ω M + M = M := by
      conv_rhs => rw [← hdr]
      rw [hrd]
    have h2 := add_eq_right_iff_mul_omega0_le.1 h1
    rw [← opow_succ] at h2
    exact absurd (lt_opow_succ_log_self one_lt_omega0 M) (not_lt.2 h2)

/-- **`Ω₁·ω^e = φ(0, Ω₁ + e)`.** -/
theorem hk_om_opow (e : Ordinal.{0}) : (Om1 : Ordinal.{0}) * ω ^ e = veblen 0 (Om 1 + e) := by
  rw [veblen_zero_apply, opow_add, show ω ^ Om (1 : Ordinal.{0}) = Om 1 from hj_Om_E, Br.Om1_eq]

/-- **`Ω₁·M` lies in every hull `C(a, b)`** for `M < ε₀`. -/
theorem hk_mul_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) :
    ∀ M : Ordinal.{0}, M < ε₀ → (Om1 : Ordinal.{0}) * M ∈ S.CSet a b := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM
  rcases eq_or_ne M 0 with rfl | h0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨hdr, hrd⟩ := hk_split h0
  have hL : log ω M < M := gc_log_lt h0 hM
  have hw : (Om1 : Ordinal.{0}) * ω ^ log ω M ∈ S.CSet a b := by
    rw [hk_om_opow]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (gc_cst_mem a b _ (hL.trans hM)))
  rw [← hdr, mul_add]
  exact CSet.add_mem hw (IH _ hrd (hrd.trans hM))

/-- **`Ω₁·M` is a code over every strongly critical `Z ≤ Ω₁`** for `M < ε₀`. -/
theorem hk_mul_code {Z : Ordinal.{0}} (hZ : SC Z) :
    ∀ M : Ordinal.{0}, M < ε₀ → GxCl Z {gcG 0} ((Om1 : Ordinal.{0}) * M) := by
  have hZE : ε₀ ≤ Z := gc_eps0_le (Low.opow_eq_self_of_SC hZ)
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM
  rcases eq_or_ne M 0 with rfl | h0
  · rw [mul_zero]; exact GxCl.small hZ.1
  obtain ⟨hdr, hrd⟩ := hk_split h0
  have hL : log ω M < M := gc_log_lt h0 hM
  have hw : GxCl Z {gcG 0} ((Om1 : Ordinal.{0}) * ω ^ log ω M) := by
    rw [hk_om_opow]
    exact GxCl.phi (GxCl.small hZ.1) (GxCl.add GxCl.om (GxCl.small ((hL.trans hM).trans_le hZE)))
  rw [← hdr, mul_add]
  exact GxCl.add hw (IH _ hrd (hrd.trans hM))

theorem hk_lt_E {M x : Ordinal.{0}} (hM : M < ε₀) (hx : InE x) : M < x := hM.trans_le (gc_eps0_le hx)

/-- **THE LEVEL DATUM `Ω₁·M`, READ AS `x·M`**, for `1 ≤ M < ε₀`. -/
noncomputable def hkLv (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < ε₀) : HjLv where
  L := Om1 * M
  l := fun x => x * M
  q := M
  OL := le_mul_of_one_le_right' h1
  L_G := InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC 0)) (hg_Om1_lt_G 0)
    (hk_lt_E hM (Low.opow_eq_self_of_SC (gcG_SC 0)))
  L_eq := by rw [Br.Om1_eq]
  L_mem := fun S a b => hk_mul_mem S a b M hM
  L_code := fun _ hZ _ => hk_mul_code hZ M hM
  l_ge := fun _ => le_mul_of_one_le_right' h1
  l_lt := fun x hx hx1 => InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (lgG_facts hx hx1).2.1
    (hk_lt_E hM (lgG_facts hx hx1).2.2.2.1)
  l_pi := fun _ _ hB => pi_mul hB M (hk_lt_E hM hB.1)

theorem hkLv_L (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < ε₀) : (hkLv M h1 hM).L = Om1 * M := rfl

theorem hkLv_l (M : Ordinal.{0}) (h1 : 1 ≤ M) (hM : M < ε₀) (x : Ordinal.{0}) : (hkLv M h1 hM).l x = x * M := rfl

/-! ## Multiples along a cofinal sequence -/

/-- **`b < a·M` lies below `a·M_k`** for a sequence `M_k` cofinal in `M`. -/
theorem hk_mul_cof {a b M : Ordinal.{0}} {Ms : ℕ → Ordinal.{0}} (ha : 0 < a) (hcof : ∀ t, t < M → ∃ k, t < Ms k)
    (hb : b < a * M) : ∃ k, b < a * Ms k := by
  have hdiv : b / a < M := (lt_mul_iff_div_lt ha.ne').1 hb
  obtain ⟨k, hk⟩ := hcof _ hdiv
  refine ⟨k, (lt_mul_div_add b ha.ne').trans_le ?_⟩
  rw [← mul_add_one]
  exact mul_le_mul_left' (Order.add_one_le_of_lt hk) _

/-- **`b < a·M` gives `b + 1 < a·M_k`** for a strictly increasing sequence `M_k` cofinal in `M`. -/
theorem hk_mul_cof1 {a b M : Ordinal.{0}} {Ms : ℕ → Ordinal.{0}} (ha : 0 < a) (hmono : ∀ k, Ms k < Ms (k + 1))
    (hcof : ∀ t, t < M → ∃ k, t < Ms k) (hb : b < a * M) : ∃ k, b + 1 < a * Ms k := by
  obtain ⟨k, hk⟩ := hk_mul_cof ha hcof hb
  refine ⟨k + 1, ?_⟩
  calc b + 1 ≤ a * Ms k := Order.add_one_le_of_lt hk
  _ < a * Ms k + a := (lt_add_iff_pos_right _).2 ha
  _ = a * (Ms k + 1) := by rw [mul_add_one]
  _ ≤ a * Ms (k + 1) := mul_le_mul_left' (Order.add_one_le_of_lt (hmono k)) _

end Googology.Trans.PoR.InaccPsi.R2.Hk
