import Googology.Trans.PoR.InaccPsi.R2.ZbE0

/-!
# ZgTl: EVERY `Yr` CODE `o < B_Γ` WITH GATE BELOW `Z` IS A CODE OF `TlCl Z`

The `TlCl` versions of `Gf.gfW_mem`, `Gi.gw_mulOm_mem`, `Gl.gl_mem`, `Yr.yr_mem`: the same inductions on the code,
using only the closure of `TlCl Z` under the ordinals below `Z`, `Ω₁`, `+`, `φ` and `Γ` above `Ω₁`
(`Tl.TlCl.gam`).  So the atom `Γ_{Ω₁+1+(B_Γ+1+o)}` is an atom of `Zb.zbU` over every strongly critical `Z` above
the gate `Yr.yrG o` (`zgAtom`).

* `zgMul`, `zgW`, `zgMulOm`, `zgGl`, `zgYr` (**`o < B_Γ`, `yrG o < Z` ⇒ `TlCl Z o`**), `zgAtom`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zg

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Hi
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Ga

variable {Z : Ordinal.{0}} (hZ : 0 < Z)
include hZ

theorem zgNat (n : ℕ) : TlCl Z (n : Ordinal.{0}) := by
  have := TlCl.mul_nat hZ (TlCl.one hZ) n
  rwa [one_mul] at this

/-- `ω^E · q` is a code for a code `E` and `q < Z`. -/
theorem zgMul {E : Ordinal.{0}} (hE : TlCl Z E) : ∀ q, q < Z → TlCl Z (ω ^ E * q) := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero]; exact TlCl.zero hZ
  set g := log ω q with hg
  set m := q / ω ^ g with hm
  set q' := q % ω ^ g with hq'
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * m + q' = q := Ordinal.div_add_mod q (ω ^ g)
  have hq'lt : q' < ω ^ g := Ordinal.mod_lt q hω0
  have hgle : ω ^ g ≤ q := opow_log_le_self ω hq0
  have hmω : m < ω := div_opow_log_lt q one_lt_omega0
  obtain ⟨j, hj⟩ := lt_omega0.1 hmω
  have hgb : g < Z := lt_of_le_of_lt (log_le_self ω q) hq
  have hP : TlCl Z (ω ^ (E + g)) := TlCl.opow hZ (TlCl.add hE (TlCl.small hgb))
  have e : ω ^ E * q = ω ^ (E + g) * (j : Ordinal.{0}) + ω ^ E * q' := by
    conv_lhs => rw [← hdm, hj, mul_add, ← mul_assoc]
    rw [← opow_add]
  rw [e]
  exact TlCl.add (TlCl.mul_nat hZ hP j) (IH q' (hq'lt.trans_le hgle) ((hq'lt.trans_le hgle).trans hq))

/-- **A code `c < ε_{Ω₁+1}` and `Ω₁·c` are codes of `TlCl Z` when the gate is below `Z`** (`Gf.gfW_mem`). -/
theorem zgW : ∀ c, c < gfE → gtc c < Z → TlCl Z c ∧ TlCl Z (Om1 * c) := by
  have hO : TlCl Z Om1 := TlCl.om
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcW hg
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [mul_zero]; exact ⟨TlCl.zero hZ, TlCl.zero hZ⟩
  obtain ⟨-, -, -, hdec, hrc, -⟩ := parts hc0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hc0 hcW
  have hlc := log_lt hc0 hcW
  set l := log Om1 c with hl
  set q := c / Om1 ^ l with hq
  set r := c % Om1 ^ l with hr
  obtain ⟨-, hlO⟩ := IH _ hlc (hlc.trans hcW) (gl.trans_lt hg)
  obtain ⟨hr1, hr2⟩ := IH _ hrc (hrc.trans hcW) (gr.trans_lt hg)
  have hqb := gq.trans_lt hg
  refine ⟨?_, ?_⟩
  · have e : c = ω ^ (Om1 * l) * q + r := by rw [← Om1_pow_eq, hdec]
    rw [e]
    exact TlCl.add (zgMul hZ hlO _ hqb) hr1
  · have e : Om1 * c = ω ^ (Om1 + Om1 * l) * q + Om1 * r := by
      rw [← mul_one_add, ← Om1_pow_eq, opow_one_add, mul_assoc, ← mul_add, hdec]
    rw [e]
    exact TlCl.add (zgMul hZ (TlCl.add hO hlO) _ hqb) hr2

/-- `ω^e·q` (`Gi.gw_mulOm_mem`). -/
theorem zgMulOm {e : Ordinal.{0}} (he : TlCl Z e) : ∀ q, q < gfE → gtc q < Z → TlCl Z (ω ^ e * q) := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hqW hg
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero]; exact TlCl.zero hZ
  obtain ⟨-, -, -, hdec, hrq, -⟩ := parts hq0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hq0 hqW
  have hlq := log_lt hq0 hqW
  obtain ⟨-, hlO⟩ := zgW hZ _ (hlq.trans hqW) (gl.trans_lt hg)
  have hr := IH _ hrq (hrq.trans hqW) (gr.trans_lt hg)
  have ee : ω ^ e * q = ω ^ (e + Om1 * log Om1 q) * (q / Om1 ^ log Om1 q) + ω ^ e * (q % Om1 ^ log Om1 q) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, opow_add, ← Om1_pow_eq]
  rw [ee]
  exact TlCl.add (zgMul hZ (TlCl.add he hlO) _ (gq.trans_lt hg)) hr

theorem zgY0 (α : Ordinal.{0}) : TlCl Z (glY0 α) := by
  unfold glY0
  split_ifs
  · exact TlCl.add TlCl.om (TlCl.one hZ)
  · exact TlCl.one hZ
  · exact TlCl.zero hZ

/-- **Every code `c < Γ_{Ω₁+1}` with gate below `Z`**, and `ω^e·c` (`Gl.gl_mem`). -/
theorem zgGl : ∀ c, c < gcG 0 → glG c < Z → TlCl Z c ∧ ∀ e, TlCl Z e → TlCl Z (ω ^ e * c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE] at hg
    exact ⟨(zgW hZ c hcE hg).1, fun e he => zgMulOm hZ he c hcE hg⟩
  have hnc := gl_idx_lt hcE hc
  have hlc := gl_lev_lt hcE hc
  obtain ⟨-, -, -, hce⟩ := gl_E_data hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := gl_parts_Q hcE hc hg
  set E := guE c with hEdef
  have hE : InE E := guE_E c
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hpart : ∀ p, p < c → glQ p < Z → (TlCl Z p ∧ ∀ e, TlCl Z e → TlCl Z (ω ^ e * p)) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨zgNat hZ m, fun e he => TlCl.mul_nat hZ (TlCl.opow hZ he) m⟩
    · have hQ : glQ p = glG p := by unfold glQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hQ ▸ hq)
  have hn := (hpart _ hnc ((glQE_le_I E).trans_lt q0n)).1
  have hl := (hpart _ hlc ((glQE_le_K E).trans_lt q0n)).1
  have hEm : TlCl Z E := by
    rw [← hce]
    unfold glPsi
    refine TlCl.phi hl ?_
    by_cases hF : glFw (glK E) (glI E)
    · rw [glLam_of hF]; exact TlCl.add hn (TlCl.one hZ)
    · rw [glLam_of_not hF]; exact TlCl.add (zgY0 hZ _) hn
  have hEk : TlCl Z (E * k) := by
    have := (hpart k hkc q0k).2 E hEm
    rwa [show ω ^ E = E from hE] at this
  have hd := hpart d hdc q0d
  have hrr := IH r hrc (hrc.trans hc) g0r
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  refine ⟨?_, fun e he => ?_⟩
  · rw [← hdec, hpow]
    exact TlCl.add (hd.2 _ hEk) hrr.1
  · rw [← hdec, hpow, mul_add, ← mul_assoc, ← opow_add]
    exact TlCl.add (hd.2 _ (TlCl.add he hEk)) (hrr.2 e he)

/-- **(1′) EVERY `Yr` CODE `o < B_Γ` WITH GATE BELOW `Z` IS A CODE OF `TlCl Z`** (`Yr.yr_mem`). -/
theorem zgYr : ∀ c, c < tfBG → yrG c < Z → TlCl Z c ∧ ∀ e, TlCl Z e → TlCl Z (ω ^ e * c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [yrG_low hcG] at hg
    exact zgGl hZ c hcG hg
  have hcE := yh_gfE_le hcG
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨q0n, q0k, q0d, g0r⟩ := yr_parts_Q hcG hg
  set E := guE c with hEdef
  have hE : InE E := guE_E c
  have hEc : E ≤ c := gl_E_le hcE
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hpart : ∀ p, p < c → yrQ p < Z → (TlCl Z p ∧ ∀ e, TlCl Z e → TlCl Z (ω ^ e * p)) := by
    intro p hpc hq
    by_cases hω : p < ω
    · obtain ⟨m, rfl⟩ := lt_omega0.1 hω
      exact ⟨zgNat hZ m, fun e he => TlCl.mul_nat hZ (TlCl.opow hZ he) m⟩
    · have hQ : yrQ p = yrG p := by unfold yrQ; rw [if_neg hω]
      exact IH p hpc (hpc.trans hc) (hQ ▸ hq)
  have hEm : TlCl Z E := by
    by_cases hA : YhAt E
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hA
      obtain ⟨hii, hie⟩ := yr_atom_idx hi (hEc.trans_lt hc)
      have hiq : yrQ i < Z := by
        rw [hi, yrQE_atom (hi ▸ hA) (by rw [yhJ_gcG]; exact hii), yhJ_gcG] at q0n; exact q0n
      have him := (hpart i (hie.trans_le hEc) hiq).1
      rw [hi, tf_gcG]
      refine TlCl.gam hZ (TlCl.add (TlCl.add TlCl.om (TlCl.one hZ)) him) ?_
      exact (lt_add_one _).trans_le le_self_add
    · have hce : yhPsi (yhK E) (yhI E) = E := (yh_E_data hcG hA).2.2.2
      rw [yrQE_psi hA] at q0n
      have hn := (hpart _ (yh_idx_lt hcG hA) ((le_max_right _ _).trans_lt q0n)).1
      have hl := (hpart _ (yh_lev_lt hcG hA) ((le_max_left _ _).trans_lt q0n)).1
      have hlam : ∀ η, TlCl Z η → TlCl Z (glLam (yhK E) η) := by
        intro η hη
        unfold glLam
        split_ifs
        · exact TlCl.add hη (TlCl.one hZ)
        · exact TlCl.add (zgY0 hZ _) hη
      rw [← hce]
      unfold yhPsi glPsi
      split_ifs
      · exact TlCl.phi hl (hlam _ (TlCl.add (TlCl.one hZ) hn))
      · exact TlCl.phi hl (hlam _ hn)
  have hEk : TlCl Z (E * k) := by
    have := (hpart k hkc q0k).2 E hEm
    rwa [show ω ^ E = E from hE] at this
  have hd := hpart d hdc q0d
  have hrr := IH r hrc (hrc.trans hc) g0r
  have hpow : E ^ k = ω ^ (E * k) := gu_pow_eq hE k
  refine ⟨?_, fun e he => ?_⟩
  · rw [← hdec, hpow]
    exact TlCl.add (hd.2 _ hEk) hrr.1
  · rw [← hdec, hpow, mul_add, ← mul_assoc, ← opow_add]
    exact TlCl.add (hd.2 _ (TlCl.add he hEk)) (hrr.2 e he)

end Googology.Trans.PoR.InaccPsi.R2.Zg
