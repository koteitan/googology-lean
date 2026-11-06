import Googology.Trans.PoR.InaccPsi.R2.QcSt
import Googology.Trans.PoR.InaccPsi.R2.ZmRa

/-!
# QcNx: THE STEP `E ↦ ε_{E+1}` AND THE RAISED GATES FOR A DIGIT SYSTEM BELOW `B₂`

`Zm.ZmPx`, `Zm.ZmTc`, `Zm.ZmDS.step` and `Zm.ZmDS.raise` for `Qc.QDS`.  The codes are those of `Uc.UcCl`: closed under
`g ↦ ω^e·g` over every strongly critical `Z` (`qc_cl_opow_mul`, by the derivation of `g`: an additive principal
`g = ω^a` gives `ω^{e+a}`), and under `y ↦ y / ω^a`, `y ↦ y mod ω^a` over `Z ≤ Ω₁` (`qc_cl_divOp`, from
`Uc.ucDec`).  The new base reading `ε_{V(x)+1}` is below `gq σ x` for the non-closure witness `σ < Dv(x) + V(x)`, a
point of a generic level (`Qc.qcBd_gq`).

* `qc_cl_opow_fix`, `qc_cl_opow_mul_small`, `qc_cl_opow_veb`, `qc_cl_opow_mul_tl`, `qc_cl_opow_mul`, `qc_cl_divOp`;
* `QDS.E_cl`, `QDS.sG_cl` (**gate below `Z` ⇒ a code**), `QDS.sG_gate` (**a code over `Z ≤ Ω₁` has gate below `Z`**);
* `QDS.VN_lt`, `QDS.Vg`, `QDS.VN_pi`, `QDS.opow_pi`, `QDS.atom_pi`, `QDS.sR_pi` (**Lemma EXACT**), `QDS.sR_dig`;
* `QDS.q_facts`, `QDS.sR_tw`, `QDS.step` (**THE STEP**), `QDS.step_gc0`, `QDS.raise` (**the raised gates**).

No new axiom.  New definitions: `QDS.Vg`, `QDS.step`, `QDS.Gc0`, `QDS.rgt`, `QDS.raise`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zm

/-! ## The codes of `UcCl` under `g ↦ ω^e·g` and `y ↦ y / ω^a` -/

section Cl

variable {Z : Ordinal.{0}}

/-- `ω^e·a = ω^{e+a}` is a code for a code `a = ω^a`. -/
theorem qc_cl_opow_fix (hZ : 0 < Z) {e a : Ordinal.{0}} (he : UcCl Z e) (ha : UcCl Z a) (h : ω ^ a = a) :
    UcCl Z (ω ^ e * a) := by
  rw [show ω ^ e * a = ω ^ (e + a) by rw [opow_add, h]]
  exact UcCl.opow hZ (UcCl.add he ha)

theorem qc_cl_opow_mul_small (hZ : SC Z) {e : Ordinal.{0}} (he : UcCl Z e) : ∀ g, g < Z → UcCl Z (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact UcCl.zero hZ.1
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact UcCl.add (UcCl.opow hZ.1 (UcCl.add he (UcCl.small ((log_le_self ω g).trans_lt hg))))
    (IH _ (Ph.ph_sub_log_lt hg0) ((Ordinal.sub_le_self _ _).trans_lt hg))

theorem qc_cl_opow_veb (hZ : 0 < Z) {e a b : Ordinal.{0}} (he : UcCl Z e) (ha : UcCl Z a) (hb : UcCl Z b) :
    UcCl Z (ω ^ e * veblen a b) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply, ← opow_add]; exact UcCl.opow hZ (UcCl.add he hb)
  · have h : ω ^ veblen a b = veblen a b := by
      rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 ha0) b
    exact qc_cl_opow_fix hZ he (UcCl.phi ha hb) h

theorem qc_cl_opow_mul_tl (hZ : SC Z) {e : Ordinal.{0}} (he : UcCl Z e) {g : Ordinal.{0}} (hg : TlCl Z g) :
    UcCl Z (ω ^ e * g) := by
  induction hg with
  | small h => exact qc_cl_opow_mul_small hZ he _ h
  | om => exact qc_cl_opow_fix hZ.1 he UcCl.om Rj.rj_Om1_opow
  | add _ _ ihx ihy => rw [mul_add]; exact UcCl.add ihx ihy
  | @phi x y hx hy _ _ => exact qc_cl_opow_veb hZ.1 he (UcCl.tl hx) (UcCl.tl hy)
  | @atom β y hβ hy h1 _ _ =>
    exact qc_cl_opow_fix hZ.1 he (UcCl.tl (TlCl.atom hβ hy h1)) (Low.opow_eq_self_of_SC (rhF_SC β y))

/-- **`UcCl Z` is closed under `g ↦ ω^e·g`** for a code `e` (every strongly critical `Z`). -/
theorem qc_cl_opow_mul (hZ : SC Z) {e : Ordinal.{0}} (he : UcCl Z e) {g : Ordinal.{0}} (hg : UcCl Z g) :
    UcCl Z (ω ^ e * g) := by
  induction hg with
  | small h => exact qc_cl_opow_mul_small hZ he _ h
  | om => exact qc_cl_opow_fix hZ.1 he UcCl.om Rj.rj_Om1_opow
  | add _ _ ihx ihy => rw [mul_add]; exact UcCl.add ihx ihy
  | @phi x y hx hy _ _ => exact qc_cl_opow_veb hZ.1 he hx hy
  | tl h => exact qc_cl_opow_mul_tl hZ he h
  | @hatom γ y hγ hc hy hX _ _ =>
    exact qc_cl_opow_fix hZ.1 he (UcCl.hatom hγ hc hy hX) (Low.opow_eq_self_of_SC (ucH_SC γ y))

theorem qc_nat_cl (hZ : SC Z) (n : ℕ) : UcCl Z (n : Ordinal.{0}) :=
  UcCl.small ((natCast_lt_omega0 n).trans (omega0_lt_inE (gg_SC_eps hZ)))

/-- **Division by `ω^a`** over a strongly critical `Z ≤ Ω₁`. -/
theorem qc_cl_divOp (hZ : SC Z) (hZ1 : Z ≤ Om1) {a : Ordinal.{0}} (ha : UcCl Z a) :
    ∀ y, UcCl Z y → UcCl Z (y / ω ^ a) ∧ UcCl Z (y % ω ^ a) := by
  have hωa : ω ^ a ≠ 0 := (opow_pos _ omega0_pos).ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨UcCl.zero hZ.1, UcCl.zero hZ.1⟩
  obtain ⟨hsub, hlog⟩ := ucDec hZ hZ1 y hy
  set g := log ω y with hg
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  set y' := y % ω ^ g with hy'
  have hdec : ω ^ g * (n : Ordinal.{0}) + y' = y := by rw [← hn]; exact div_add_mod y _
  have hy'lt : y' < ω ^ g := Ordinal.mod_lt y (opow_pos _ omega0_pos).ne'
  have hlead : UcCl Z (ω ^ g * (n : Ordinal.{0})) := qc_cl_opow_mul hZ hlog (qc_nat_cl hZ n)
  have hy'C : UcCl Z y' := by
    have := hsub _ hlead (by rw [← hdec]; exact le_self_add)
    rwa [← hdec, Ordinal.add_sub_cancel] at this
  have hy'y : y' < y := hy'lt.trans_le (opow_log_le_self ω hy0)
  rcases lt_or_ge g a with hga | hag
  · have hya : y < ω ^ a := by
      calc y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
        _ ≤ ω ^ a := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hga)
    rw [Ordinal.div_eq_zero_of_lt hya, Ordinal.mod_eq_of_lt hya]
    exact ⟨UcCl.zero hZ.1, hy⟩
  · obtain ⟨h1, h2⟩ := IH y' hy'y hy'C
    have hgaC : UcCl Z (g - a) := (ucDec hZ hZ1 g hlog).1 a ha hag
    have e : y = ω ^ a * (ω ^ (g - a) * (n : Ordinal.{0})) + y' := by
      rw [← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le hag, hdec]
    rw [e, Ordinal.mul_add_div _ hωa, Ordinal.mul_add_mod_self]
    exact ⟨UcCl.add (qc_cl_opow_mul hZ hgaC (qc_nat_cl hZ n)) h1, h2⟩

end Cl

namespace QDS

variable (M : QDS)

/-! ## Codes and gates one level up -/

theorem E_cl {Z : Ordinal.{0}} (hZ : SC Z) (hEg : M.Eg < Z) : UcCl Z M.E := by
  rw [← M.E_eq]; exact UcCl.phi (UcCl.one hZ.1) (M.Ei_cl Z hZ hEg)

/-- **Gate below `Z` ⇒ a code of `UcCl Z`.** -/
theorem sG_cl {Z : Ordinal.{0}} (hZ : SC Z) : ∀ o, o < eN M.E → M.sG o < Z → UcCl Z o := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoN hg
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg; exact M.cl o Z hZ hoE hg
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  have hEgZ : M.Eg < Z := (M.sG_Eg _ hk0.ne').trans_lt g1
  have hkC := IH _ hko (hko.trans hoN) g1
  have hrC := IH _ hro (hro.trans hoN) g3
  have hdC := M.cl _ Z hZ hdE g2
  have hEk' : UcCl Z (M.E * log M.E o) := by
    have h := qc_cl_opow_mul hZ (M.E_cl hZ hEgZ) hkC
    rwa [show ω ^ M.E = M.E from M.E_E] at h
  have key : ∀ dd, UcCl Z dd → UcCl Z (M.E ^ log M.E o * dd) := fun dd hdd => by
    rw [zm_opow_eq M.E_E]; exact qc_cl_opow_mul hZ hEk' hdd
  rw [← hdec]
  exact UcCl.add (key _ hdC) hrC

/-- **A code of `UcCl Z` (`Z ≤ Ω₁` strongly critical) below `ε_{E+1}` has gate below `Z`.** -/
theorem sG_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hEgZ : M.Eg < Z) :
    ∀ o, o < eN M.E → UcCl Z o → M.sG o < Z := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoN hC
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE]; exact M.gate o Z hZ hZ1 hEgZ hoE hC
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  rw [M.sG_cnf hoE hoN]
  set k := log M.E o with hkdef
  set d := o / M.E ^ k with hddef
  set r := o % M.E ^ k with hrdef
  have hEC := M.E_cl hZ hEgZ
  have hEω : ω ^ M.E = M.E := M.E_E
  have hP : M.E ^ k = ω ^ (M.E * k) := zm_opow_eq M.E_E k
  have hlog : log ω o = M.E * k + log ω d := by
    rw [← hdec, hP]; exact log_opow_mul_add one_lt_omega0 hd0.ne' (hP ▸ hrk)
  have hlogC : UcCl Z (log ω o) := (ucDec hZ hZ1 o hC).2
  have hld : log ω d < M.E := (log_le_self ω d).trans_lt hdE
  have hkC : UcCl Z k := by
    have h := (qc_cl_divOp hZ hZ1 hEC (log ω o) hlogC).1
    rw [hlog, hEω, Ordinal.mul_add_div _ M.E_E.pos.ne', Ordinal.div_eq_zero_of_lt hld, add_zero] at h
    exact h
  have hPC : UcCl Z (M.E * k) := by
    have h := qc_cl_opow_mul hZ hEC hkC; rwa [hEω] at h
  obtain ⟨hdC, hrC⟩ := qc_cl_divOp hZ hZ1 hPC o hC
  rw [← hP, ← hdec, Ordinal.mul_add_div _ (opow_pos _ M.E_E.pos).ne', Ordinal.div_eq_zero_of_lt hrk,
    add_zero] at hdC
  rw [← hP, ← hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrk] at hrC
  exact max_lt (IH k hko (hko.trans hoN) hkC) (max_lt (M.gate d Z hZ hZ1 hEgZ hdE hdC) (IH r hro (hro.trans hoN) hrC))

/-! ## Lemma EXACT and the digit lemma one level up (as `Zm.ZmPx`) -/


theorem VN_lt (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) : eN (M.V x) < Om1 := by
  obtain ⟨hWT, hW1, he⟩ := M.W_T x hx hx1 hEg
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  rw [he]; exact (glA_facts hx hx1 le_rfl h1T h11 hWT hW1).2.2.1

theorem V_gtx (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) : x < M.V x :=
  (M.Dv_T x hx hx1 hEg).2.2.1.trans_le (M.V_T x hx hx1 hEg).2.2.1

theorem V_opow_eq (x a : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) :
    M.V x ^ a = ω ^ (M.V x * a) :=
  zm_opow_eq (M.V_T x hx hx1 hEg).2.1 a

open Classical in
/-- The base reading, replaced by `D` at and below the base gate (for `Te`). -/
noncomputable def Vg (x : Ordinal.{0}) : Ordinal.{0} := if M.Eg < x then M.V x else ywV 1 0 x

theorem Vg_facts (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) :
    InE (M.Vg x) ∧ x < M.Vg x ∧ eN (M.Vg x) < Om1 := by
  unfold Vg
  split_ifs with h
  · exact ⟨(M.V_T x hx hx1 h).2.1, M.V_gtx x hx hx1 h, M.VN_lt x hx hx1 h⟩
  · obtain ⟨hDT, hxD, hD1, hDE⟩ := zmD_facts hx hx1
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    refine ⟨hDE, hxD, ?_⟩
    rw [zmD_eN hx hx1]; exact (glA_facts hx hx1 le_rfl h1T h11 hDT hD1).2.2.1

theorem Vg_eq {x : Ordinal.{0}} (h : M.Eg < x) : M.Vg x = M.V x := by unfold Vg; rw [if_pos h]

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

theorem VN_pi (hEg : M.Eg < σ) : eN (M.V ρ) ∈ TB ρ σ ∧ R2.pi σ ρ (eN (M.V ρ)) = eN (M.V σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hEgρ : M.Eg < ρ := hEg.trans hB.2.2.1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨w1, w2⟩ := M.W_pi σ ρ hB hEg
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 w1 (M.W_T ρ hB.2.1 hρ1 hEgρ).2.1
  rw [o2, w2, ← (M.W_T ρ hB.2.1 hρ1 hEgρ).2.2, ← (M.W_T σ hB.1 hσ1 hEg).2.2] at h
  exact h

theorem Vg_pi (hEg : M.Eg < σ) :
    (M.Vg ρ ∈ TB ρ σ ∧ R2.pi σ ρ (M.Vg ρ) = M.Vg σ) ∧
      (eN (M.Vg ρ) ∈ TB ρ σ ∧ R2.pi σ ρ (eN (M.Vg ρ)) = eN (M.Vg σ)) := by
  rw [M.Vg_eq hEg, M.Vg_eq (hEg.trans hB.2.2.1)]
  exact ⟨M.V_pi σ ρ hB hEg, M.VN_pi hB hEg⟩

/-- **`π(ω^X) = ω^{π X}`** for `X ∈ Tᵖ[σ] ∩ [V(ρ), ε_{V(ρ)+1})`. -/
theorem opow_pi (hEg : M.Eg < σ) {X : Ordinal.{0}} (hX : X ∈ TB ρ σ) (hGX : M.V ρ ≤ X)
    (hXe : X < eN (M.V ρ)) : ω ^ X ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ X) = ω ^ (R2.pi σ ρ X) := by
  have hρ := M.Vg_eq (hEg.trans hB.2.2.1)
  rw [← hρ] at hGX hXe
  exact Te.te_opow_pi hB (fun x hx hx1 => (M.Vg_facts x hx hx1).1) (fun x hx hx1 => (M.Vg_facts x hx hx1).2.1)
    (fun x hx hx1 => (M.Vg_facts x hx hx1).2.2) (M.Vg_pi hB hEg).1 (M.Vg_pi hB hEg).2 hX hGX hXe

theorem atom_pi (hEg : M.Eg < σ) {β : Ordinal.{0}} (hβ : β ∈ TB ρ σ) (hβe : M.V ρ + β < eN (M.V ρ)) :
    ω ^ (M.V ρ + β) ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ (M.V ρ + β)) = ω ^ (M.V σ + R2.pi σ ρ β) := by
  have hρ := M.Vg_eq (hEg.trans hB.2.2.1)
  have hσ := M.Vg_eq hEg
  rw [← hρ] at hβe ⊢
  rw [← hσ]
  exact Te.te_atom_pi hB (fun x hx hx1 => (M.Vg_facts x hx hx1).1) (fun x hx hx1 => (M.Vg_facts x hx hx1).2.1)
    (fun x hx hx1 => (M.Vg_facts x hx hx1).2.2) (M.Vg_pi hB hEg).1 (M.Vg_pi hB hEg).2 hβ hβe

/-- **LEMMA EXACT FOR THE READINGS BELOW `ε_{E+1}`** (and for `V(ρ)·R(o)(ρ)`). -/
theorem sR_pi : ∀ o, o < eN M.E → M.sG o < σ →
    (M.sR o ρ ∈ TB ρ σ ∧ R2.pi σ ρ (M.sR o ρ) = M.sR o σ) ∧
    (M.V ρ * M.sR o ρ ∈ TB ρ σ ∧ R2.pi σ ρ (M.V ρ * M.sR o ρ) = M.V σ * M.sR o σ) := by
  have hρE := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoN hg
  have hgρ : M.sG o < ρ := hg.trans hB.2.2.1
  rcases eq_or_ne o 0 with rfl | ho0
  · have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hB.1.pos
    have h0pi : R2.pi σ ρ 0 = 0 := pi_lt hB hB.1.pos
    rw [M.sR_zero, M.sR_zero, mul_zero, mul_zero]
    exact ⟨⟨h0T, h0pi⟩, ⟨h0T, h0pi⟩⟩
  have hEg : M.Eg < σ := (M.sG_Eg o ho0).trans_lt hg
  have hVρE : InE (M.V ρ) := (M.V_T ρ hρE hρ1 (hEg.trans hB.2.2.1)).2.1
  have hVσE : InE (M.V σ) := (M.V_T σ hB.1 hσ1 hEg).2.1
  obtain ⟨v1, v2⟩ := M.V_pi σ ρ hB hEg
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg
    rw [M.sR_lt hoE, M.sR_lt hoE]
    refine ⟨M.ex σ ρ o hB hoE hg, ?_⟩
    have h := M.dig σ ρ o hB hoE hg (M.V ρ) (M.V σ) (fun β hβT hβ =>
      M.atom_pi hB hEg hβT ((inE_indec (eN_E _)).add_lt (lt_eN _) (hβ.trans (lt_eN _))))
    rw [show ω ^ M.V ρ = M.V ρ from hVρE, show ω ^ M.V σ = M.V σ from hVσE] at h
    exact h
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  rw [M.sR_cnf hoE hoN ρ, M.sR_cnf hoE hoN σ]
  set k := log M.E o
  set d := o / M.E ^ k
  set r := o % M.E ^ k
  obtain ⟨⟨k1, k2⟩, ⟨km1, km2⟩⟩ := IH k hko (hko.trans hoN) g1
  obtain ⟨⟨r1, r2⟩, ⟨rm1, rm2⟩⟩ := IH r hro (hro.trans hoN) g3
  have hSk := M.sR_main hρE hρ1 k (hko.trans hoN) (g1.trans hB.2.2.1)
  have ha0 : 0 < M.sR k ρ := hSk.2.1 hk0.ne'
  have haN : M.sR k ρ < eN (M.V ρ) := hSk.1
  have hVa : M.V ρ ≤ M.V ρ * M.sR k ρ := by
    have := mul_le_mul_right (one_le_iff_pos.2 ha0) (M.V ρ); rwa [mul_one] at this
  have hVaN : M.V ρ * M.sR k ρ < eN (M.V ρ) := mul_lt_inE (eN_E _) (lt_eN _) haN
  -- the atoms `ω^{Q + V·a + β}` for `Q = 0` and `Q = V`
  have hP : ∀ Q Q', Q ∈ TB ρ σ → R2.pi σ ρ Q = Q' → Q + M.V ρ * M.sR k ρ < eN (M.V ρ) →
      ∀ β, β ∈ TB ρ σ → β < M.V ρ →
        ω ^ (Q + M.V ρ * M.sR k ρ + β) ∈ TB ρ σ ∧
          R2.pi σ ρ (ω ^ (Q + M.V ρ * M.sR k ρ + β)) = ω ^ (Q' + M.V σ * M.sR k σ + R2.pi σ ρ β) :=
    fun Q Q' hQ hQ' hQN β hβT hβ => by
      obtain ⟨s1, s2⟩ := pi_add hB hQ km1
      obtain ⟨t1, t2⟩ := pi_add hB s1 hβT
      have hXN : Q + M.V ρ * M.sR k ρ + β < eN (M.V ρ) :=
        (inE_indec (eN_E _)).add_lt hQN (hβ.trans (lt_eN _))
      have hXV : M.V ρ ≤ Q + M.V ρ * M.sR k ρ + β := hVa.trans (le_add_self.trans le_self_add)
      obtain ⟨u1, u2⟩ := M.opow_pi hB hEg t1 hXV hXN
      exact ⟨u1, by rw [u2, t2, s2, hQ', km2]⟩
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hB.1.pos
  have h0pi : R2.pi σ ρ 0 = 0 := pi_lt hB hB.1.pos
  -- `V^a·R(d) = ω^{V·a}·R(d)`
  have hD1 := M.dig σ ρ d hB hdE g2 (0 + M.V ρ * M.sR k ρ) (0 + M.V σ * M.sR k σ)
    (hP 0 0 h0T h0pi (by rw [zero_add]; exact hVaN))
  rw [zero_add, zero_add] at hD1
  rw [M.V_opow_eq ρ _ hρE hρ1 (hEg.trans hB.2.2.1), M.V_opow_eq σ _ hB.1 hσ1 hEg]
  obtain ⟨p1, p2⟩ := pi_add hB hD1.1 r1
  refine ⟨⟨p1, by rw [p2, hD1.2, r2]⟩, ?_⟩
  -- `V·(V^a·R(d) + R(r)) = ω^{V + V·a}·R(d) + V·R(r)`
  have e : ∀ t, InE (M.V t) → M.V t * (ω ^ (M.V t * M.sR k t) * M.R d t + M.sR r t) =
      ω ^ (M.V t + M.V t * M.sR k t) * M.R d t + M.V t * M.sR r t := fun t ht => by
    rw [mul_add, ← mul_assoc, opow_add, show ω ^ M.V t = M.V t from ht]
  rw [e ρ hVρE, e σ hVσE]
  have hVVa : M.V ρ + M.V ρ * M.sR k ρ < eN (M.V ρ) := (inE_indec (eN_E _)).add_lt (lt_eN _) hVaN
  have hD2 := M.dig σ ρ d hB hdE g2 (M.V ρ + M.V ρ * M.sR k ρ) (M.V σ + M.V σ * M.sR k σ)
    (hP (M.V ρ) (M.V σ) v1 v2 hVVa)
  obtain ⟨q1, q2⟩ := pi_add hB hD2.1 rm1
  exact ⟨q1, by rw [q2, hD2.2, rm2]⟩

/-- **THE DIGIT LEMMA ONE LEVEL UP**: `π(ω^P·R(d)(ρ)) = ω^{P'}·R(d)(σ)` for the codes `d < ε_{E+1}`, once the atoms
`ω^{P+β}`, `β ∈ Tᵖ[σ]`, `β < ε_{V(ρ)+1}`, are exact. -/
theorem sR_dig : ∀ d, d < eN M.E → M.sG d < σ → ∀ P P' : Ordinal.{0},
    (∀ β, β ∈ TB ρ σ → β < eN (M.V ρ) →
      ω ^ (P + β) ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ (P + β)) = ω ^ (P' + R2.pi σ ρ β)) →
    ω ^ P * M.sR d ρ ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ P * M.sR d ρ) = ω ^ P' * M.sR d σ := by
  have hρE := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoN hg P P' hP
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg
    rw [M.sR_lt hoE, M.sR_lt hoE]
    exact M.dig σ ρ o hB hoE hg P P' (fun β hβT hβ => hP β hβT (hβ.trans (lt_eN _)))
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  rw [M.sR_cnf hoE hoN ρ, M.sR_cnf hoE hoN σ]
  set k := log M.E o
  set d := o / M.E ^ k
  set r := o % M.E ^ k
  have hEg : M.Eg < σ := (M.sG_Eg k hk0.ne').trans_lt g1
  obtain ⟨-, ⟨km1, km2⟩⟩ := M.sR_pi hB k (hko.trans hoN) g1
  have hSk := M.sR_main hρE hρ1 k (hko.trans hoN) (g1.trans hB.2.2.1)
  have hVaN : M.V ρ * M.sR k ρ < eN (M.V ρ) := mul_lt_inE (eN_E _) (lt_eN _) hSk.1
  have e : ∀ t Q, t = ρ ∨ t = σ → ω ^ Q * (M.V t ^ M.sR k t * M.R d t + M.sR r t) =
      ω ^ (Q + M.V t * M.sR k t) * M.R d t + ω ^ Q * M.sR r t := fun t Q ht => by
    have htE : InE t := by rcases ht with rfl | rfl; exacts [hρE, hB.1]
    have ht1 : t < Om1 := by rcases ht with rfl | rfl; exacts [hρ1, hσ1]
    have htg : M.Eg < t := by rcases ht with rfl | rfl; exacts [hEg.trans hB.2.2.1, hEg]
    rw [M.V_opow_eq t _ htE ht1 htg, mul_add, ← mul_assoc, ← opow_add]
  rw [e ρ P (Or.inl rfl), e σ P' (Or.inr rfl)]
  have hD := M.dig σ ρ d hB hdE g2 (P + M.V ρ * M.sR k ρ) (P' + M.V σ * M.sR k σ) (fun β hβT hβ => by
    obtain ⟨s1, s2⟩ := pi_add hB km1 hβT
    have h := hP _ s1 ((inE_indec (eN_E _)).add_lt hVaN (hβ.trans (lt_eN _)))
    rw [s2, km2, ← add_assoc, ← add_assoc] at h
    exact h)
  obtain ⟨r1, r2⟩ := IH r hro (hro.trans hoN) g3 P P' hP
  obtain ⟨p1, p2⟩ := pi_add hB hD.1 r1
  exact ⟨p1, by rw [p2, hD.2, r2]⟩

end Pi


/-! ## The step (as `Zm.ZmNx`) -/

/-- **The facts of a non-closure witness `σ < Dv(x) + V(x)`**: `gq σ x` is a fixed point of `φ(1, ·)`, below a
point of a generic level. -/
theorem q_facts {x σ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hEg : M.Eg < x) (hσT : σ ∈ Tset x)
    (hσ1 : σ < Om1) (hσV : σ < M.Dv x + M.V x) :
    veblen 1 (gq σ x) = gq σ x ∧ QcBd x (gq σ x) ∧ InE (gq σ x) := by
  obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hσT hσ1
  have hbd : QcBd x σ := qcBd_mono hσV.le (qcBd_add hx hx1 (M.Dv_T x hx hx1 hEg).2.2.2 (M.V_T x hx hx1 hEg).2.2.2)
  exact ⟨xk_fix hx hx1 hσT hσ1 le_rfl (lu_one_lt_E hqE), qcBd_gq hx hx1 hσT hbd, hqE⟩

/-- Cofinally many codes of gate `≤ max Eg 1`. -/
def Gc0 : Prop := ∀ c, c < M.E → ∃ c', c ≤ c' ∧ c' < M.E ∧ M.G c' ≤ max M.Eg 1


/-- **The tower of codes reads the tower of `V(x)`**, gate `≤ max Eg 1`. -/
theorem sR_tw (x : Ordinal.{0}) : ∀ n, M.sR (zmTw M.E n) x = zmTw (M.V x) n ∧ M.sG (zmTw M.E n) ≤ max M.Eg 1 := by
  have h1E : (1 : Ordinal.{0}) < M.E := M.one_lt_E
  have hR1 : M.sR 1 x = 1 := by rw [M.sR_lt h1E, M.R_one]
  intro n
  induction n with
  | zero =>
    have e : M.E = M.E ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
    have hv : M.E ^ (1 : Ordinal.{0}) * 1 + 0 < eN M.E := by rw [← e]; exact lt_eN _
    have hr : (0 : Ordinal.{0}) < M.E ^ (1 : Ordinal.{0}) := by rw [opow_one]; exact M.E_E.pos
    show M.sR M.E x = M.V x ∧ M.sG M.E ≤ max M.Eg 1
    rw [e, M.sR_eq zero_lt_one one_ne_zero h1E hr hv, M.sG_eq zero_lt_one one_ne_zero h1E hr hv, hR1,
      M.R_one, M.sR_zero, M.sG_lt h1E, M.sG_zero, opow_one, mul_one, add_zero]
    exact ⟨rfl, max_le M.G1 (max_le M.G1 zero_le)⟩
  | succ n ih =>
    have ht0 := zmTw_pos M.E_E n
    have e : zmTw M.E (n + 1) = M.E ^ zmTw M.E n * 1 + 0 := by
      show M.E ^ zmTw M.E n = _; rw [mul_one, add_zero]
    have hv : M.E ^ zmTw M.E n * 1 + 0 < eN M.E := by rw [← e]; exact zmTw_lt (E := M.E) (n + 1)
    have hr : (0 : Ordinal.{0}) < M.E ^ zmTw M.E n := opow_pos _ M.E_E.pos
    rw [e, M.sR_eq ht0 one_ne_zero h1E hr hv, M.sG_eq ht0 one_ne_zero h1E hr hv, ih.1, M.R_one, mul_one,
      M.sR_zero, add_zero, M.sG_zero]
    exact ⟨rfl, max_le ih.2 (max_le M.G1 zero_le)⟩

/-- **THE GENERIC STEP**: a digit system at the base `E` gives one at the base `ε_{E+1}`. -/
noncomputable def step : QDS where
  E := eN M.E
  Ei := M.Ei + 1
  V := fun x => eN (M.V x)
  W := fun x => M.W x + 1
  R := M.sR
  G := M.sG
  Eg := M.Eg
  B := M.B
  Dv := M.Dv
  E_eq := by rw [← M.E_eq, Go.go_eN_veb]
  BG_le := M.BG_le.trans (lt_eN _).le
  BG_B := M.BG_B
  B_le := M.B_le.trans (lt_eN _).le
  B_cl := M.B_cl
  Dv_T := M.Dv_T
  Dv_pi := M.Dv_pi
  E_X := by
    rw [← M.E_eq, Go.go_eN_veb]
    have hi : M.Ei + 1 < ucB := by
      have h := (right_le_veblen 1 M.Ei).trans_lt (M.E_eq ▸ M.E_X)
      exact (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC ucB_SC)).add_one_lt h
    exact ucB_SC.2 1 (gg_one_lt_of_SC ucB_SC) _ hi
  Ei_cl := fun Z hZ hEg => UcCl.add (M.Ei_cl Z hZ hEg) (UcCl.one hZ.1)
  nfx := fun y h1 h2 hΓ => by
    rcases le_or_gt y M.E with hy | hy
    · exact M.nfx y h1 hy hΓ
    refine absurd (zm_fix_of_gamma hΓ) ?_
    rcases h2.lt_or_eq with h3 | h3
    · intro hfix
      exact absurd (eN_le hy (zm_fix_E hfix)) (not_le.2 h3)
    · rw [h3]; exact zm_eN_nfix _
  Eg_le := fun c hc0 => M.sG_Eg c hc0
  V_T := fun x hx hx1 hEg => by
    obtain ⟨hVT, hVE, hDV, hVX⟩ := M.V_T x hx hx1 hEg
    obtain ⟨σ, hσT, hσ1, hσV, hVσ⟩ := M.Vq x hx hx1 hEg
    obtain ⟨hfix, hqX, -⟩ := M.q_facts hx hx1 hEg hσT hσ1 hσV
    obtain ⟨hWT, hW1, he⟩ := M.W_T x hx hx1 hEg
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    refine ⟨?_, eN_E _, hDV.trans (lt_eN _).le, qcBd_mono (zm_eN_lt_fix hVσ hfix).le hqX⟩
    rw [he]; exact (glA_facts hx hx1 le_rfl h1T h11 hWT hW1).1
  Vq := fun x hx hx1 hEg => by
    obtain ⟨σ, hσT, hσ1, hσV, hVσ⟩ := M.Vq x hx hx1 hEg
    obtain ⟨hfix, -, -⟩ := M.q_facts hx hx1 hEg hσT hσ1 hσV
    exact ⟨σ, hσT, hσ1, hσV.trans_le ((add_le_add_iff_left _).2 (lt_eN _).le), zm_eN_lt_fix hVσ hfix⟩
  W_T := fun x hx hx1 hEg => by
    obtain ⟨hWT, hW1, he⟩ := M.W_T x hx hx1 hEg
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hWT hW1
    refine ⟨hsT, hs1, ?_⟩
    show eN (eN (M.V x)) = glA 1 (M.W x + 1) x
    rw [he, glA_eN_one hx hx1 hWT hW1]
  V_pi := fun σ ρ hB hEg => M.VN_pi hB hEg
  W_pi := fun σ ρ hB hEg => by
    obtain ⟨w1, w2⟩ := M.W_pi σ ρ hB hEg
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB w1 o1
    exact ⟨s1, by rw [s2, w2, o2]⟩
  R0 := M.sR_zero
  G0 := M.sG_zero
  G1 := by rw [M.sG_lt M.one_lt_E]; exact M.G1
  lt := fun c x hx hx1 hc hg => (M.sR_main hx hx1 c hc hg).1
  pos := fun c x hx hx1 hc0 hc hg => (M.sR_main hx hx1 c hc hg).2.1 hc0
  mono := fun b c x hx hx1 hbc hc hgb hgc => (M.sR_main hx hx1 c hc hgc).2.2.2 b hbc hgb
  succ := M.sR_succ
  g_le := M.sG_le_succ
  g_succ := fun c Z hZ hEg hg => M.sG_succ_lt c Z hZ hEg hg
  lim := fun c x hx hx1 hl hc hg => M.sR_lim c x hx hx1 hl hc hg
  cof := fun c x hx hx1 hl hc hg ν hν => M.sR_cof c x hx hx1 hl hc hg ν hν
  nc := fun c x hx hx1 hl hc hg => by
    rcases lt_or_ge c M.E with hcE | hcE
    · rw [M.sR_lt hcE]; rw [M.sG_lt hcE] at hg; exact M.nc c x hx hx1 hl hcE hg
    have hc0 : c ≠ 0 := (lt_of_lt_of_le M.E_E.pos hcE).ne'
    have hEg : M.Eg < x := (M.sG_Eg c hc0).trans_lt hg
    obtain ⟨hVT, hVE, hDV, hVX⟩ := M.V_T x hx hx1 hEg
    obtain ⟨σ, hσT, hσ1, hσV, hVσ⟩ := M.Vq x hx hx1 hEg
    obtain ⟨hfix, -, hqE⟩ := M.q_facts hx hx1 hEg hσT hσ1 hσV
    obtain ⟨hlt, -, -, hmono⟩ := M.sR_main hx hx1 c hc hg
    have hVc : M.V x ≤ M.sR c x := by
      obtain ⟨e1, e2⟩ := M.sR_tw x 0
      rcases hcE.lt_or_eq with h | h
      · have h' := hmono M.E h (e2.trans_lt (max_lt hEg (lu_one_lt_E hx)))
        exact (e1.symm.trans_le h'.le)
      · rw [← h]; exact e1.symm.le
    exact ⟨σ, hσT, hσ1, hσV.trans_le ((add_le_add_iff_left _).2 hVc),
      (inE_indec hqE).add_lt (hDV.trans_lt hVσ) (hlt.trans (zm_eN_lt_fix hVσ hfix))⟩
  top := fun x hx hx1 hEg ν hν => by
    obtain ⟨n, hn⟩ := zmTw_cof (M.V_T x hx hx1 hEg).2.1 hν
    obtain ⟨e1, e2⟩ := M.sR_tw x n
    exact ⟨zmTw M.E n, zmTw_lt (E := M.E) n, e2.trans_lt (max_lt hEg (lu_one_lt_E hx)),
      by rw [e1]; exact hn.le⟩
  ex := fun σ ρ c hB hc hg => (M.sR_pi hB c hc hg).1
  dig := fun σ ρ d hB hd hg P P' hP => M.sR_dig hB d hd hg P P' hP
  cl := fun c Z hZ hc hg => M.sG_cl hZ c hc hg
  gate := fun c Z hZ hZ1 hEg hc h => M.sG_gate hZ hZ1 hEg c hc h

theorem step_E : M.step.E = eN M.E := rfl

theorem step_R : M.step.R = M.sR := rfl

theorem step_Eg : M.step.Eg = M.Eg := rfl

/-- **The step always has cofinally many codes of gate `≤ max Eg 1`** (the tower). -/
theorem step_gc0 : M.step.Gc0 := fun c hc => by
  obtain ⟨n, hn⟩ := zmTw_cof M.E_E hc
  exact ⟨zmTw M.E n, hn.le, zmTw_lt (E := M.E) n, (M.sR_tw 0 n).2⟩


/-! ## The raised gates (as `Zm.ZmRa`) -/

section Raise

variable (g : Ordinal.{0})

/-- The raised gate. -/
noncomputable def rgt (c : Ordinal.{0}) : Ordinal.{0} := if c = 0 then 0 else max g (M.G c)

theorem rgt_ne {c : Ordinal.{0}} (h : c ≠ 0) : M.rgt g c = max g (M.G c) := by unfold rgt; rw [if_neg h]

theorem rgt_zero : M.rgt g 0 = 0 := by unfold rgt; rw [if_pos rfl]

theorem G_le_rgt (c : Ordinal.{0}) : M.G c ≤ M.rgt g c := by
  rcases eq_or_ne c 0 with rfl | h
  · rw [rgt_zero, M.G0]
  · rw [M.rgt_ne g h]; exact le_max_right _ _

/-- From a raised gate below `x` (nonzero code): `g < x`. -/
theorem g_lt_of {c x : Ordinal.{0}} (h0 : c ≠ 0) (h : M.rgt g c < x) : g < x := by
  rw [M.rgt_ne g h0] at h; exact (le_max_left _ _).trans_lt h

theorem rgt_lt {c x : Ordinal.{0}} (hg : g < x) (h : M.G c < x) : M.rgt g c < x := by
  rcases eq_or_ne c 0 with rfl | h0
  · rw [rgt_zero]; exact (zero_le).trans_lt hg
  · rw [M.rgt_ne g h0]; exact max_lt hg h

/-- **THE RAISED SYSTEM**: gates `max g (G c)` (`c ≠ 0`), base gate `max Eg g`. -/
noncomputable def raise : QDS where
  E := M.E
  Ei := M.Ei
  V := M.V
  W := M.W
  R := M.R
  G := M.rgt g
  Eg := max M.Eg g
  B := M.B
  Dv := M.Dv
  E_eq := M.E_eq
  BG_le := M.BG_le
  BG_B := M.BG_B
  B_le := M.B_le
  B_cl := fun Z hZ h => M.B_cl Z hZ ((le_max_left _ _).trans_lt h)
  Dv_T := fun x hx hx1 h => M.Dv_T x hx hx1 ((le_max_left _ _).trans_lt h)
  Dv_pi := fun σ ρ hB h => M.Dv_pi σ ρ hB ((le_max_left _ _).trans_lt h)
  E_X := M.E_X
  Ei_cl := fun Z hZ h => M.Ei_cl Z hZ ((le_max_left _ _).trans_lt h)
  nfx := M.nfx
  Eg_le := fun c hc => by rw [M.rgt_ne g hc]; exact max_le_max (M.Eg_le c hc) le_rfl |>.trans_eq (max_comm _ _)
  V_T := fun x hx hx1 h => M.V_T x hx hx1 ((le_max_left _ _).trans_lt h)
  Vq := fun x hx hx1 h => M.Vq x hx hx1 ((le_max_left _ _).trans_lt h)
  W_T := fun x hx hx1 h => M.W_T x hx hx1 ((le_max_left _ _).trans_lt h)
  V_pi := fun σ ρ hB h => M.V_pi σ ρ hB ((le_max_left _ _).trans_lt h)
  W_pi := fun σ ρ hB h => M.W_pi σ ρ hB ((le_max_left _ _).trans_lt h)
  R0 := M.R0
  G0 := M.rgt_zero g
  G1 := by
    rw [M.rgt_ne g one_ne_zero]
    exact max_le ((le_max_right _ _).trans (le_max_left _ _)) (M.G1.trans (max_le_max (le_max_left _ _) le_rfl))
  lt := fun c x hx hx1 hc hg => M.lt c x hx hx1 hc ((M.G_le_rgt g c).trans_lt hg)
  pos := fun c x hx hx1 hc0 hc hg => M.pos c x hx hx1 hc0 hc ((M.G_le_rgt g c).trans_lt hg)
  mono := fun b c x hx hx1 hbc hc hgb hgc =>
    M.mono b c x hx hx1 hbc hc ((M.G_le_rgt g b).trans_lt hgb) ((M.G_le_rgt g c).trans_lt hgc)
  succ := M.succ
  g_le := fun c => by
    rcases eq_or_ne c 0 with rfl | h0
    · rw [rgt_zero]; exact zero_le
    · rw [M.rgt_ne g h0, M.rgt_ne g (by simp)]; exact max_le_max le_rfl (M.g_le c)
  g_succ := fun c Z hZ hEg hg => by
    have hgZ : g < Z := (le_max_right _ _).trans_lt hEg
    exact M.rgt_lt g hgZ (M.g_succ c Z hZ ((le_max_left _ _).trans_lt hEg) ((M.G_le_rgt g c).trans_lt hg))
  lim := fun c x hx hx1 hl hc hg => M.lim c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg)
  nc := fun c x hx hx1 hl hc hg => M.nc c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg)
  cof := fun c x hx hx1 hl hc hg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof c x hx hx1 hl hc ((M.G_le_rgt g c).trans_lt hg) ν hν
    exact ⟨b, hb, M.rgt_lt g (M.g_lt_of g hl.bot_lt.ne' hg) hgb, hνb⟩
  top := fun x hx hx1 hEg ν hν => by
    obtain ⟨b, hb, hgb, hνb⟩ := M.top x hx hx1 ((le_max_left _ _).trans_lt hEg) ν hν
    exact ⟨b, hb, M.rgt_lt g ((le_max_right _ _).trans_lt hEg) hgb, hνb⟩
  ex := fun σ ρ c hB hc hg => M.ex σ ρ c hB hc ((M.G_le_rgt g c).trans_lt hg)
  dig := fun σ ρ d hB hd hg P P' hP => M.dig σ ρ d hB hd ((M.G_le_rgt g d).trans_lt hg) P P' hP
  cl := fun c Z hZ hc hg => M.cl c Z hZ hc ((M.G_le_rgt g c).trans_lt hg)
  gate := fun c Z hZ hZ1 hEg hc h =>
    M.rgt_lt g ((le_max_right _ _).trans_lt hEg) (M.gate c Z hZ hZ1 ((le_max_left _ _).trans_lt hEg) hc h)

theorem raise_E : (M.raise g).E = M.E := rfl
theorem raise_R : (M.raise g).R = M.R := rfl
theorem raise_V : (M.raise g).V = M.V := rfl
theorem raise_Eg : (M.raise g).Eg = max M.Eg g := rfl
theorem raise_G {c : Ordinal.{0}} (h : c ≠ 0) : (M.raise g).G c = max g (M.G c) := M.rgt_ne g h

end Raise

end QDS

end Googology.Trans.PoR.InaccPsi.R2.Qc
