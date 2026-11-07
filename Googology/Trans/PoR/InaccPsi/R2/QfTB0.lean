import Googology.Trans.PoR.InaccPsi.R2.QfDict
import Googology.Trans.PoR.InaccPsi.R2.HeMul
import Googology.Trans.PoR.InaccPsi.R2.GlAt

/-!
# QfTB0: MEMBERSHIP IN `Tᵖ[σ]` THROUGH THE ADDITIVE COMPONENTS, AND THE PARTS OF A ϑ-TERM `ϑᵖ(Ω₁·a + r)`

`π = π_{σ,ρ}` for `υ`-points `σ < ρ` (`Bases σ ρ`).

* `qf_TB_mul_nat`, `qf_TB_of_comps` (**an ordinal is in `Tᵖ[σ]` once its additive components are**);
* `qf_comps_Om1_mul_add` (**`comps(Ω₁·a + r) = Ω₁·comps(a) ++ comps(r)`** for `r < Ω₁`);
* `qf_TB_of_Om1_mul_add` (**`Ω₁·a + r ∈ Tᵖ[σ]` gives `a, r ∈ Tᵖ[σ]`**, for countable `a`, from `R2.siTB_of_comps` and
  `R2.om1_opow_TB_all`), `qf_glA_TB_inv` (**the parts of a ϑ-term in `Tᵖ[σ]` are in `Tᵖ[σ]`**, `R2.vt_memTwo`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si

section Base

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem qf_TB_zero : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hB.1.pos

theorem qf_TB_mul_nat {x : Ordinal.{0}} (hx : x ∈ TB ρ σ) : ∀ n : ℕ, x * n ∈ TB ρ σ := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero]; exact qf_TB_zero hB
  | succ n ih => rw [Nat.cast_succ, mul_add_one]; exact (pi_add hB ih hx).1

/-- **An ordinal is in `Tᵖ[σ]` once its additive components are.** -/
theorem qf_TB_of_comps : ∀ x, (∀ p ∈ comps x, p ∈ TB ρ σ) → x ∈ TB ρ σ := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact qf_TB_zero hB
  obtain ⟨hdec, -, hkω, hr⟩ := si_dec hx0
  obtain ⟨k, hk⟩ := lt_omega0.1 hkω
  have hL : ω ^ log ω x ∈ TB ρ σ := hx _ (lead_comp hx0)
  have hrx : x % ω ^ log ω x < x := by
    refine hr.trans_le (opow_log_le_self ω hx0)
  have hrT : x % ω ^ log ω x ∈ TB ρ σ := IH _ hrx fun p hp => by
    apply hx; rw [si_comps_cons hx0]; exact List.mem_cons_of_mem _ hp
  rw [← hdec, hk]
  exact (pi_add hB (qf_TB_mul_nat hB hL k) hrT).1

end Base

/-- **`comps(Ω₁·a + r) = Ω₁·comps(a) ++ comps(r)`** for `r < Ω₁`. -/
theorem qf_comps_Om1_mul_add {r : Ordinal.{0}} (hr : r < Om1) :
    ∀ a, comps (Om1 * a + r) = (comps a).map (fun p => Om1 * p) ++ comps r := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [mul_zero, zero_add, si_comps_zero]; rfl
  have hO : (Om1 : Ordinal.{0}) = ω ^ Om (1 : Ordinal.{0}) := by rw [Bt.Om1_opow, rj_Om1]
  have hr' : r < ω ^ Om (1 : Ordinal.{0}) := by rw [← hO]; exact hr
  have hs0 : Om1 * a + r ≠ 0 := (lt_of_lt_of_le (mul_pos rj_Om1_pos (pos_iff_ne_zero.2 ha0)) le_self_add).ne'
  have hlog : log ω (Om1 * a + r) = Om (1 : Ordinal.{0}) + log ω a := by
    rw [hO]; exact log_opow_mul_add one_lt_omega0 ha0 hr'
  have hmod : (Om1 * a + r) % ω ^ log ω (Om1 * a + r) = Om1 * (a % ω ^ log ω a) + r := by
    rw [hlog, opow_add, ← hO]
    exact mul_add_mod_mul hr _ _
  have hlead : ω ^ log ω (Om1 * a + r) = Om1 * ω ^ log ω a := by rw [hlog, opow_add, ← hO]
  have ham : a % ω ^ log ω a < a := (mod_lt a (opow_pos _ omega0_pos).ne').trans_le (opow_log_le_self ω ha0)
  rw [si_comps_cons hs0, hmod, IH _ ham, hlead, si_comps_cons ha0]
  rfl

section Base2

variable {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
include hσ hρ hB

/-- **`Ω₁·a + r ∈ Tᵖ[σ]` gives `a, r ∈ Tᵖ[σ]`** (`a < Ω₁`, `r < Ω₁`). -/
theorem qf_TB_of_Om1_mul_add {a r : Ordinal.{0}} (ha1 : a < Om1) (hr : r < Om1) (ha0 : a ≠ 0)
    (h : Om1 * a + r ∈ TB ρ σ) : a ∈ TB ρ σ ∧ r ∈ TB ρ σ := by
  have hρs : ρ ≤ Om1 * a + r :=
    (hB.2.2.2.le.trans (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 ha0))).trans le_self_add
  have hc := qf_comps_Om1_mul_add hr a
  refine ⟨qf_TB_of_comps hB a fun p hp => ?_, siTB_of_comps hB h hρs fun p hp => by
    rw [hc]; exact List.mem_append_right _ hp⟩
  -- a component `p = ω^e` of `a`: `Ω₁·ω^e` is a component of `Ω₁·a + r`
  have hp0 := hp
  unfold comps at hp
  obtain ⟨⟨e, k⟩, hek, rfl⟩ := List.mem_map.1 hp
  have hmem : Om1 * ω ^ e ∈ comps (Om1 * a + r) := by
    rw [hc]; refine List.mem_append_left _ (List.mem_map.2 ⟨ω ^ e, ?_, rfl⟩)
    unfold comps; exact List.mem_map.2 ⟨⟨e, k⟩, hek, rfl⟩
  have hO : (Om1 : Ordinal.{0}) = ω ^ Om (1 : Ordinal.{0}) := by rw [Bt.Om1_opow, rj_Om1]
  have hcomp1 : comps (Om1 * ω ^ e) = [Om1 * ω ^ e] := by
    rw [hO, ← opow_add]; exact comps_opow _
  have hT : Om1 * ω ^ e ∈ TB ρ σ := siTB_of_comps hB h hρs fun q hq => by
    rw [hcomp1, List.mem_singleton] at hq; rw [hq]; exact hmem
  have he1 : e < Om1 := by
    have h1 : ω ^ e ≤ a := le_of_mem_comps hp0
    exact (right_le_opow e one_lt_omega0).trans_lt (h1.trans_lt ha1)
  have heE : ∀ x : Ordinal.{0}, InE x → Om1 < x → e < x := fun x _ hx => he1.trans hx
  have heT : e ∈ TB ρ σ := ((om1_opow_TB_all hB heE).1).1 hT
  exact (pi_opowZ hσ hρ hB heT he1).1

/-- **The parts of a ϑ-term in `Tᵖ[σ]` are in `Tᵖ[σ]`**: `ϑᵖ(Ω₁·a + r) ∈ Tᵖ[σ]` gives `a, r ∈ Tᵖ[σ]`. -/
theorem qf_glA_TB_inv {a r : Ordinal.{0}} (ha1 : 1 ≤ a) (haT : a ∈ Tset ρ) (haΩ : a < Om1) (hrT : r ∈ Tset ρ)
    (hr1 : r < Om1) (h : vt ρ (Om1 * a + r) ∈ TB ρ σ) : a ∈ TB ρ σ ∧ r ∈ TB ρ σ := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨hξT, hξ2, -⟩ := ul_facts hρE hρ1 ha1 haT haΩ hrT hr1
  obtain ⟨-, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hξT hξ2
  have hξTB : Om1 * a + r ∈ TB ρ σ := ⟨hξT, by rw [← hPar]; exact h.2⟩
  exact qf_TB_of_Om1_mul_add hσ hρ hB haΩ hr1 (lt_of_lt_of_le zero_lt_one ha1).ne' hξTB

end Base2

end Googology.Trans.PoR.InaccPsi.R2.Qf
