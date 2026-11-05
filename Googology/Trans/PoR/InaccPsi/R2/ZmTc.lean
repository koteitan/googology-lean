import Googology.Trans.PoR.InaccPsi.R2.ZmPx

/-!
# ZmTc: THE GENERIC STEP — THE CODES OF `TlCl` ARE EXACTLY THE CODES WITH GATE BELOW `Z`

* `zm_cl_divOp` (**the codes over a strongly critical `Z` are closed under `y ↦ y / ω^a` and `y ↦ y mod ω^a` for
  every code `a`**);
* `ZmDS.E_cl` (`E = φ(1, E_i)` is a code), `ZmDS.sG_cl` (**gate below `Z` ⇒ a code of `TlCl Z`**),
  `ZmDS.sG_gate` (**a code of `TlCl Z`, `Z ≤ Ω₁`, has gate below `Z`**: the exponent through `log_ω` and the
  division by `ω^E`, the digit and the rest through the division by `ω^{E·k}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk

theorem zm_nat_cl {Z : Ordinal.{0}} (hZ : SC Z) (n : ℕ) : TlCl Z (n : Ordinal.{0}) :=
  TlCl.small ((natCast_lt_omega0 n).trans (omega0_lt_inE (gg_SC_eps hZ)))

/-- **Division by `ω^a`**: the codes over a strongly critical `Z` are closed under `y ↦ y / ω^a` and
`y ↦ y mod ω^a` for every code `a`. -/
theorem zm_cl_divOp {Z : Ordinal.{0}} (hZ : SC Z) {a : Ordinal.{0}} (ha : TlCl Z a) :
    ∀ y, TlCl Z y → TlCl Z (y / ω ^ a) ∧ TlCl Z (y % ω ^ a) := by
  have hωa : ω ^ a ≠ 0 := (opow_pos _ omega0_pos).ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨TlCl.zero hZ.1, TlCl.zero hZ.1⟩
  obtain ⟨hsub, hlog⟩ := tlDec hZ y hy
  set g := log ω y with hg
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  set y' := y % ω ^ g with hy'
  have hdec : ω ^ g * (n : Ordinal.{0}) + y' = y := by rw [← hn]; exact div_add_mod y _
  have hy'lt : y' < ω ^ g := Ordinal.mod_lt y (opow_pos _ omega0_pos).ne'
  have hlead : TlCl Z (ω ^ g * (n : Ordinal.{0})) := tl_cl_opow_mul hZ hlog _ (zm_nat_cl hZ n)
  have hy'C : TlCl Z y' := by
    have := hsub _ hlead (by rw [← hdec]; exact le_self_add)
    rwa [← hdec, Ordinal.add_sub_cancel] at this
  have hy'y : y' < y := hy'lt.trans_le (opow_log_le_self ω hy0)
  rcases lt_or_ge g a with hga | hag
  · have hya : y < ω ^ a := by
      calc y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
        _ ≤ ω ^ a := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hga)
    rw [Ordinal.div_eq_zero_of_lt hya, Ordinal.mod_eq_of_lt hya]
    exact ⟨TlCl.zero hZ.1, hy⟩
  · obtain ⟨h1, h2⟩ := IH y' hy'y hy'C
    have hgaC : TlCl Z (g - a) := hsub' hsub hlog ha hag
    have e : y = ω ^ a * (ω ^ (g - a) * (n : Ordinal.{0})) + y' := by
      rw [← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le hag, hdec]
    rw [e, Ordinal.mul_add_div _ hωa, Ordinal.mul_add_mod_self]
    exact ⟨TlCl.add (tl_cl_opow_mul hZ hgaC _ (zm_nat_cl hZ n)) h1, h2⟩
where
  hsub' {g a : Ordinal.{0}} {y : Ordinal.{0}} (hsub : ∀ x, TlCl Z x → x ≤ y → TlCl Z (y - x)) (hlog : TlCl Z g)
      (ha : TlCl Z a) (hag : a ≤ g) : TlCl Z (g - a) :=
    (tlDec hZ g hlog).1 a ha hag

namespace ZmDS

variable (M : ZmDS)

theorem E_cl {Z : Ordinal.{0}} (hZ : SC Z) (hEg : M.Eg < Z) : TlCl Z M.E := by
  rw [← M.E_eq]; exact TlCl.phi (TlCl.one hZ.1) (M.Ei_cl Z hZ hEg)

/-- **Gate below `Z` ⇒ a code of `TlCl Z`.** -/
theorem sG_cl {Z : Ordinal.{0}} (hZ : SC Z) : ∀ o, o < eN M.E → M.sG o < Z → TlCl Z o := by
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
  have hEk' : TlCl Z (M.E * log M.E o) := by
    have h := tl_cl_opow_mul hZ (M.E_cl hZ hEgZ) _ hkC
    rwa [show ω ^ M.E = M.E from M.E_E] at h
  have key : ∀ dd, TlCl Z dd → TlCl Z (M.E ^ log M.E o * dd) := fun dd hdd => by
    rw [zm_opow_eq M.E_E]; exact tl_cl_opow_mul hZ hEk' dd hdd
  rw [← hdec]
  exact TlCl.add (key _ hdC) hrC

/-- **A code of `TlCl Z` (`Z ≤ Ω₁` strongly critical) below `ε_{E+1}` has gate below `Z`.** -/
theorem sG_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) (hEgZ : M.Eg < Z) :
    ∀ o, o < eN M.E → TlCl Z o → M.sG o < Z := by
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
  -- the exponent
  have hlog : log ω o = M.E * k + log ω d := by
    rw [← hdec, hP]; exact log_opow_mul_add one_lt_omega0 hd0.ne' (hP ▸ hrk)
  have hlogC : TlCl Z (log ω o) := (tlDec hZ o hC).2
  have hld : log ω d < M.E := (log_le_self ω d).trans_lt hdE
  have hkC : TlCl Z k := by
    have h := (zm_cl_divOp hZ hEC (log ω o) hlogC).1
    rw [hlog, hEω, Ordinal.mul_add_div _ M.E_E.pos.ne', Ordinal.div_eq_zero_of_lt hld, add_zero] at h
    exact h
  -- the digit and the rest
  have hPC : TlCl Z (M.E * k) := by
    have h := tl_cl_opow_mul hZ hEC _ hkC; rwa [hEω] at h
  obtain ⟨hdC, hrC⟩ := zm_cl_divOp hZ hPC o hC
  rw [← hP, ← hdec, Ordinal.mul_add_div _ (opow_pos _ M.E_E.pos).ne', Ordinal.div_eq_zero_of_lt hrk,
    add_zero] at hdC
  rw [← hP, ← hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrk] at hrC
  exact max_lt (IH k hko (hko.trans hoN) hkC) (max_lt (M.gate d Z hZ hZ1 hEgZ hdE hdC) (IH r hro (hro.trans hoN) hrC))

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
