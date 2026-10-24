import Googology.Trans.PoR.InaccPsi.R2.GkU6

/-!
# CODES BELOW `ζ_{Ω₁+1}`: Lemma EXACT at every pair of bases

* `gu_mulE` (**`E·k` is a code**, `E = ε_{Ω₁+n}`: `(E·k)(x) = ε_{x+n(x)}·k(x)`, gate at most `max(Q n, gate k)`),
  `gu_mulE_lt_pow` (`E·k < E^k`, `k ≥ 2`);
* `gu_base_pi` (`π(ε_{ρ+n(ρ)}) = ε_{σ+n(σ)}` and the same one pseudo-base up, by `pi_evAZ`);
* `gu_atom_pi` (**Lemma EXACT for the atom `ω^{B+δ}` above a pseudo-base `B`**: `ϑ^ρ(B+ξ) = ω^{B+1+ξ}` (`vt_ps`) and
  [W07a] Def 5.1 (`pi_vt`)), `gu_BK_pi` (`π(B·K) = B'·K'`);
* `gu_dig` (**`π(ω^P·d(ρ)) = ω^{P'}·d(σ)`** for every code `d` below the pseudo-base, once the atoms `ω^{P+β}`,
  `β < B`, are exact: the digits are themselves codes of lower brackets);
* `gu_pi` (**LEMMA EXACT for every code `c < ζ_{Ω₁+1}`** at every pair of bases `σ < ρ` above its gate; one
  induction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **`E·k` as a code** (`E = ε_{Ω₁+n}`, `1 ≤ k < ε_{E+1}`). -/
theorem gu_mulE {n : Ordinal.{0}} (hn1 : 1 ≤ n) (hnB : n < guB) : ∀ k, k ≠ 0 → k < eN (evA Om1 n) →
    evA Om1 n * k < evA Om1 (n + 1) ∧ evA Om1 n * k < guB ∧ guG (evA Om1 n * k) ≤ max (guQ n) (guG k) ∧
      ∀ x, InE x → guR (evA Om1 n * k) x = guA x (guR n x) * guR k x := by
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  have hEN : eN E = evA Om1 (n + 1) := by rw [hEdef, evA_add_one]
  have hNB : evA Om1 (n + 1) < guB := gu_evA_lt (guB_lim.add_one_lt hnB)
  intro k
  induction k using WellFoundedLT.induction with
  | ind k IH =>
  intro hk0 hkN
  have hv : E * k < evA Om1 (n + 1) := by rw [← hEN]; exact (eN_E E).mul_lt (lt_eN E) hkN
  refine ⟨hv, hv.trans hNB, ?_⟩
  rcases lt_or_ge k E with hkE | hkE
  · have e : E * k = E ^ (1 : Ordinal.{0}) * k + 0 := by rw [opow_one, add_zero]
    have hr : (0 : Ordinal.{0}) < E ^ (1 : Ordinal.{0}) := opow_pos _ hE.pos
    refine ⟨?_, fun x _ => ?_⟩
    · rw [e, guG_cnf hn1 one_ne_zero hk0 hkE hr (e ▸ hv) (e ▸ hv.trans hNB), guQ_one, guG_zero]
      simp only [zero_le, max_eq_left, max_eq_right]
      exact max_le (le_max_left _ _) ((guQ_le k).trans (le_max_right _ _))
    · rw [e, guR_cnf hn1 one_ne_zero hk0 hkE hr (e ▸ hv) (e ▸ hv.trans hNB), guR_one, opow_one, guR_zero,
        add_zero]
  have hkB : k < guB := hkN.trans (by rw [hEN]; exact hNB)
  obtain ⟨hNk, hEk, hgfk⟩ := gu_same hkE (hEN ▸ hkN) hn1
  obtain ⟨ha, hq0, hqE, hs, hdec, hak, hsk, -⟩ := gu_parts hgfk hkB
  rw [hEk] at ha hq0 hqE hs hdec hak hsk
  set a := log E k with hadef
  set q := k / E ^ a with hqdef
  set s := k % E ^ a with hsdef
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEs : E * s < E ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ hE.pos).2 hs
  have e : E * k = E ^ (1 + a) * q + E * s := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hsN : s < eN E := hsk.trans hkN
  have hgEs : guG (E * s) ≤ max (guQ n) (guG s) := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, mul_zero, guG_zero]; exact zero_le
    · exact (IH s hsk h0 hsN).2.2.1
  have hgk : guG k = max (max (guQ n) (guQ a)) (max (guQ q) (guG s)) := by
    rw [guG_dec hgfk hkB, hNk, hEk]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [e, guG_cnf hn1 h1a hq0 hqE hEs (e ▸ hv) (e ▸ hv.trans hNB), guQ_one_add, hgk]
    refine max_le (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_right _ _)))) (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      (hgEs.trans (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))))
  · rw [e, guR_cnf hn1 h1a hq0 hqE hEs (e ▸ hv) (e ▸ hv.trans hNB), guR_dec hgfk hkB, hNk, hEk]
    have hRs : guR (E * s) x = guA x (guR n x) * guR s x := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero, guR_zero, mul_zero]
      · exact (IH s hsk h0 hsN).2.2.2 x hx
    rw [hRs, guR_one_add hx (hak.trans hkB), opow_add, opow_one, mul_assoc, ← mul_add]

/-- `E·k < E^k` for every `2 ≤ k < ε_{E+1}` (`E·k` is not an `ε`-number). -/
theorem gu_mulE_lt_pow {E k : Ordinal.{0}} (hE : InE E) (hk : 1 < k) (hkN : k < eN E) : E * k < E ^ k := by
  rw [gu_pow_eq hE]
  rcases (right_le_opow (E * k) one_lt_omega0).lt_or_eq with h | h
  · exact h
  exfalso
  have hEk : InE (E * k) := h.symm
  have hlt : E < E * k := lt_mul_of_one_lt_right hE.pos hk
  exact absurd ((eN_le hlt hEk).trans_lt ((eN_E E).mul_lt (lt_eN E) hkN)) (lt_irrefl _)

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(ε_{ρ+n(ρ)}) = ε_{σ+n(σ)}`**, and one pseudo-base up, from Lemma EXACT for `n`. -/
theorem gu_base_pi {n : Ordinal.{0}} (hn1 : 1 ≤ n) (hnB : n < guB) (hgn : guG n < σ)
    (hex : guR n ρ ∈ TB ρ σ ∧ pi σ ρ (guR n ρ) = guR n σ) :
    guA ρ (guR n ρ) ∈ TB ρ σ ∧ pi σ ρ (guA ρ (guR n ρ)) = guA σ (guR n σ) ∧
      eN (guA ρ (guR n ρ)) ∈ TB ρ σ ∧ pi σ ρ (eN (guA ρ (guR n ρ))) = eN (guA σ (guR n σ)) := by
  have hσE := hB.1
  have hρE := hB.2.1
  have h1ρ := guR_pos' hρE (one_le_iff_ne_zero.1 hn1) hnB
  have h1σ := guR_pos' hσE (one_le_iff_ne_zero.1 hn1) hnB
  obtain ⟨hT, hp⟩ := hex
  have hZρ : guR n ρ < evZ ρ := guR_lt_evZ hρE n hnB (hgn.trans hB.2.2.1)
  have hZσ : guR n σ < evZ σ := guR_lt_evZ hσE n hnB hgn
  obtain ⟨a1, a2⟩ := pi_evAZ hB hT hZρ (by rw [hp]; exact hZσ)
  rw [hp] at a2
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB hT o1
  rw [hp, o2] at s2
  have hL : IsSuccLimit (evZ ρ) := ev_isSuccLimit_of_inE (evZ_E ρ)
  have hLσ : IsSuccLimit (evZ σ) := ev_isSuccLimit_of_inE (evZ_E σ)
  obtain ⟨b1, b2⟩ := pi_evAZ hB s1 (hL.add_one_lt hZρ) (by rw [s2]; exact hLσ.add_one_lt hZσ)
  rw [s2] at b2
  rw [guA_eq hρE h1ρ, guA_eq hσE h1σ, ← evA_add_one, ← evA_add_one]
  exact ⟨a1, a2, b1, b2⟩

/-- **Lemma EXACT for the atom `ω^{B+δ}`** above a pseudo-base `B ∈ Tᵖ[σ]` (`ρ < B`, `π(B) = B'`,
`π(ε_{B+1}) = ε_{B'+1}`), `δ ∈ Tᵖ[σ]`, `B + δ < ε_{B+1}`. -/
theorem gu_atom_pi {B B' δ : Ordinal.{0}} (hBE : InE B) (hB'E : InE B') (hρB : ρ < B) (hσB' : σ < B')
    (hBT : B ∈ TB ρ σ) (hpB : pi σ ρ B = B') (hNT : eN B ∈ TB ρ σ) (hpN : pi σ ρ (eN B) = eN B')
    (hNO : eN B < Om1) (hδ : δ ∈ TB ρ σ) (hBδ : B + δ < eN B) :
    ω ^ (B + δ) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (B + δ)) = ω ^ (B' + pi σ ρ δ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  have hmono := (pi_bijOn hB).2
  rcases eq_or_ne δ 0 with rfl | hδ0
  · rw [pi_lt hB hB.1.pos, add_zero, add_zero, show ω ^ B = B from hBE, show ω ^ B' = B' from hB'E]
    exact ⟨hBT, hpB⟩
  have hδ' : δ - 1 ∈ TB ρ σ ∧ 1 + pi σ ρ (δ - 1) = pi σ ρ δ := by
    have hb : 1 + (δ - 1) = δ := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hδ0)
    rcases lt_or_ge δ ω with hω | hω
    · have hδσ : δ < σ := hω.trans (omega0_lt_inE hB.1)
      have hδ'σ : δ - 1 < σ := lt_of_le_of_lt (sub_le_self δ 1) hδσ
      refine ⟨mem_TB_of_lt hB hδ'σ, ?_⟩
      rw [pi_lt hB hδ'σ, pi_lt hB hδσ, hb]
    · have e : δ - 1 = δ := by
        have h := Ordinal.add_sub_cancel 1 δ
        rw [one_add_of_omega0_le hω] at h
        exact h
      rw [e]
      refine ⟨hδ, one_add_of_omega0_le ?_⟩
      rcases lt_or_ge δ σ with hδσ | hσδ
      · rw [pi_lt hB hδσ]; exact hω
      · exact (omega0_lt_inE hB.1).le.trans (pi_ge hB hδ hσδ)
  set ξ := δ - 1 with hξdef
  obtain ⟨hξT, hπ1⟩ := hδ'
  have hb : 1 + ξ = δ := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hδ0)
  obtain ⟨hBξT, hpBξ⟩ := pi_add hB hBT hξT
  rw [hpB] at hpBξ
  obtain ⟨hBδT, hpBδ⟩ := pi_add hB hBT hδ
  rw [hpB] at hpBδ
  have hBξ1 : B + ξ < Om1 := lt_of_le_of_lt (add_le_add le_rfl (by rw [← hb]; exact le_add_self)) (hBδ.trans hNO)
  have hBδ' : B' + pi σ ρ δ < eN B' := by rw [← hpBδ, ← hpN]; exact hmono hBδT hNT hBδ
  have hN'O : eN B' < Om1 := by rw [← hpN, ← hpO]; exact hmono hNT hOT hNO
  have hv := vt_ps hB.2.1 hρ1 hBE hρB (by rw [add_assoc, hb]; exact hBδ) hBξ1
  rw [add_assoc, hb] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hBξT.1 hBξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hBξT.2⟩, ?_⟩
  have hB'ξ1 : B' + pi σ ρ ξ < Om1 :=
    lt_of_le_of_lt (add_le_add le_rfl (by rw [← hπ1]; exact le_add_self)) (hBδ'.trans hN'O)
  have hv' := vt_ps hB.1 hσ1 hB'E hσB' (by rw [add_assoc, hπ1]; exact hBδ') hB'ξ1
  rw [add_assoc, hπ1] at hv'
  rw [← hv, pi_vt hB hBξT hBξ1, hpBξ, hv']

/-- **`π(B·K) = B'·K'`** for the pseudo-base `B = ε_{ρ+m(ρ)}` and a code `κ` (finite: `pi_mul_nat`; infinite: the
code `E·κ`). -/
theorem gu_BK_pi {m κ : Ordinal.{0}} (hm1 : 1 ≤ m) (hmB : m < guB) (hgm : guG m < σ) (hκ0 : κ ≠ 0)
    (hκN : κ < eN (evA Om1 m)) (hexm : guR m ρ ∈ TB ρ σ ∧ pi σ ρ (guR m ρ) = guR m σ)
    (hexm2 : ω ≤ κ → guR (evA Om1 m * κ) ρ ∈ TB ρ σ ∧
      pi σ ρ (guR (evA Om1 m * κ) ρ) = guR (evA Om1 m * κ) σ) :
    guA ρ (guR m ρ) * guR κ ρ ∈ TB ρ σ ∧ pi σ ρ (guA ρ (guR m ρ) * guR κ ρ) = guA σ (guR m σ) * guR κ σ := by
  obtain ⟨a1, a2, -, -⟩ := gu_base_pi hB hm1 hmB hgm hexm
  rcases lt_or_ge κ ω with hω | hω
  · obtain ⟨j, rfl⟩ := lt_omega0.1 hω
    rw [guR_nat, guR_nat]
    exact pi_mul_nat hB a1 a2 j
  · obtain ⟨-, -, -, hR⟩ := gu_mulE hm1 hmB κ hκ0 hκN
    rw [← hR ρ hB.2.1, ← hR σ hB.1]
    exact hexm2 hω

/-- **The digits**: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` for every code `d` below `ε_{Ω₁+n}` with gate below `σ`, once the
atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < ε_{ρ+n(ρ)}`) are exact and Lemma EXACT holds below `ε_{Ω₁+n}`. -/
theorem gu_dig {n : Ordinal.{0}} (hn1 : 1 ≤ n) (hnB : n < guB) (hgn : guG n < σ)
    (hEX : ∀ j, j < evA Om1 n → guG j < σ → guR j ρ ∈ TB ρ σ ∧ pi σ ρ (guR j ρ) = guR j σ) :
    ∀ d, d < evA Om1 n → guG d < σ → ∀ P P' : Ordinal.{0},
      (∀ β, β ∈ TB ρ σ → β < guA ρ (guR n ρ) →
        ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
      ω ^ P * guR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * guR d ρ) = ω ^ P' * guR d σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hωσ := omega0_lt_inE hσE
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  have hBρ : eN ρ ≤ guA ρ (guR n ρ) := gu_eN_le_guA ρ (guR_pos' hρE (one_le_iff_ne_zero.1 hn1) hnB)
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdE hgd P P' hat
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [guR_zero, guR_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  rcases lt_or_ge d gfE with hdW | hdW
  · -- a code below `ε_{Ω₁+1}`: the normal form `Ω₁^l·q + r` of `R2.GfSub`
    have hgd' : gtc d < σ := by rw [guG_low hdW] at hgd; exact hgd
    obtain ⟨-, hqΩ, -, -, hrγ, -⟩ := parts hd0
    obtain ⟨gl, gq, gr⟩ := gtc_parts hd0 hdW
    have hrW : log Om1 d < gfE ∧ d % Om1 ^ log Om1 d < gfE := ⟨(log_lt hd0 hdW).trans hdW, hrγ.trans hdW⟩
    obtain ⟨h1, h2⟩ := IH _ hrγ (hrγ.trans hdE) (by rw [guG_low hrW.2]; exact gr.trans_lt hgd') P P' hat
    simp only [guR_low hrW.2] at h1 h2
    have hqσ : d / Om1 ^ log Om1 d < σ := gq.trans_lt hgd'
    have hcb : OT.CB (tcx (log Om1 d)) σ := cb_tcx hσE.pos _ (gl.trans_lt hgd')
    have edec : ∀ x Q : Ordinal.{0}, InE x → ω ^ Q * rdc d x =
        ω ^ (Q + OT.ev (tcx (log Om1 d)) x) * (d / Om1 ^ log Om1 d) + ω ^ Q * rdc (d % Om1 ^ log Om1 d) x := by
      intro x Q hx
      rw [rdc_dec hd0 hdW, mul_add, ← mul_assoc, pw_eq' hx, ← opow_add, ev_tcx hx]
    have hatom : ∀ z, z < σ → ω ^ (P + (OT.ev (tcx (log Om1 d)) ρ + z)) ∈ TB ρ σ ∧
        pi σ ρ (ω ^ (P + (OT.ev (tcx (log Om1 d)) ρ + z))) = ω ^ (P' + (OT.ev (tcx (log Om1 d)) σ + z)) := by
      intro z hz
      have hcb' : OT.CB (OT.add (tcx (log Om1 d)) (OT.k z)) σ := ⟨hcb, hz⟩
      obtain ⟨t1, t2⟩ := pi_ev hB _ hcb'
      simp only [OT.ev_add, OT.ev_k] at t1 t2
      have hlt : OT.ev (tcx (log Om1 d)) ρ + z < eN ρ := by
        have := ev_lt_eN (OT.CB_mono hcb' hB.2.2.1.le)
        simpa only [OT.ev_add, OT.ev_k] using this
      obtain ⟨t3, t4⟩ := hat _ t1 (hlt.trans_le hBρ)
      rw [t2] at t4
      exact ⟨t3, t4⟩
    have hmul : ∀ q', q' < σ → ω ^ (P + OT.ev (tcx (log Om1 d)) ρ) * q' ∈ TB ρ σ ∧
        pi σ ρ (ω ^ (P + OT.ev (tcx (log Om1 d)) ρ) * q') = ω ^ (P' + OT.ev (tcx (log Om1 d)) σ) * q' := by
      intro q'
      induction q' using WellFoundedLT.induction with
      | ind q' IHq =>
      intro hq'
      rcases eq_or_ne q' 0 with rfl | hq0
      · rw [mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
      obtain ⟨q'', hgs, -, hq''⟩ := lg_split hq0
      have hz : lg q' < σ := lt_of_le_of_lt (lg_le hq0) hq'
      obtain ⟨k1, k2⟩ := IHq q'' hq'' (hq''.trans hq')
      obtain ⟨k3, k4⟩ := hatom _ hz
      rw [hgs, mul_add, mul_add, ← opow_add, ← opow_add, add_assoc, add_assoc]
      obtain ⟨k5, k6⟩ := pi_add hB k1 k3
      exact ⟨k5, by rw [k6, k2, k4]⟩
    obtain ⟨m1, m2⟩ := hmul _ hqσ
    rw [guR_low hdW, guR_low hdW, edec ρ P hρE, edec σ P' hσE]
    obtain ⟨m3, m4⟩ := pi_add hB m1 h1
    exact ⟨m3, by rw [m4, m2, h2]⟩
  -- a code of a lower bracket
  have hdB : d < guB := hdE.trans (gu_evA_lt hnB)
  obtain ⟨hn1d, -, hdn, hnBd, hnlt⟩ := guN_spec hdW hdB
  obtain ⟨hk, hd0', -, -, hdec, hkd, hrd, hdd⟩ := gu_parts hdW hdB
  obtain ⟨g0n, g0k, g0d, g0r⟩ := gu_parts_g hωσ hdW hdB hgd
  have hlt : ∀ j, j < d → j < evA Om1 n := fun j hj => hj.trans hdE
  have hexn := hEX _ (hlt _ hnlt) g0n
  have hEdE : InE (guE d) := guE_E d
  have hkN : log (guE d) d < eN (guE d) := hkd.trans (by rw [guE, ← evA_add_one]; exact hdn)
  have hBK := gu_BK_pi hB hn1d hnBd g0n hk hkN hexn (fun hω => by
    have hk1 : 1 < log (guE d) d := lt_of_lt_of_le one_lt_omega0 hω
    have hEkd : guE d * log (guE d) d < d := (gu_mulE_lt_pow hEdE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0')).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, -, hg, -⟩ := gu_mulE hn1d hnBd _ hk hkN
    exact hEX _ (hlt _ hEkd) (hg.trans_lt (max_lt ((guQ_le _).trans_lt g0n) g0k)))
  have hlead : guA ρ (guR (guN d) ρ) * guR (log (guE d) d) ρ < guA ρ (guR n ρ) := by
    have h1 : guA ρ (guR (guN d) ρ) * guR (log (guE d) d) ρ ≤
        guA ρ (guR (guN d) ρ) ^ guR (log (guE d) d) ρ := by
      rw [gu_pow_eq (guA_E _ _)]; exact right_le_opow _ one_lt_omega0
    have h2 := (gu_lead hρE hdW hdB).1
    have h3 : guA ρ (guR (guN d) ρ) ^ guR (log (guE d) d) ρ ≤
        guA ρ (guR (guN d) ρ) ^ guR (log (guE d) d) ρ * guR (d / guE d ^ log (guE d) d) ρ :=
      le_mul_of_one_le_right' (guR_pos' hρE hd0' (hdd.trans hdB))
    exact (h1.trans (h3.trans h2)).trans_lt (guR_lt_base hρE hn1 hnB (hgn.trans hB.2.2.1) hdE (hgd.trans hB.2.2.1))
  have hat' : ∀ β, β ∈ TB ρ σ → β < guA ρ (guR n ρ) →
      ω ^ ((P + guA ρ (guR (guN d) ρ) * guR (log (guE d) d) ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + guA ρ (guR (guN d) ρ) * guR (log (guE d) d) ρ) + β)) =
        ω ^ ((P' + guA σ (guR (guN d) σ) * guR (log (guE d) d) σ) + pi σ ρ β) := by
    intro β hβ hβB
    obtain ⟨s1, s2⟩ := pi_add hB hBK.1 hβ
    have := hat _ s1 ((inE_indec (guA_E _ _)).add_lt hlead hβB)
    rw [s2, hBK.2] at this
    rw [add_assoc, add_assoc]; exact this
  obtain ⟨u1, u2⟩ := IH _ hdd (hlt _ hdd) g0d _ _ hat'
  obtain ⟨v1, v2⟩ := IH _ hrd (hlt _ hrd) g0r P P' hat
  have e : ∀ x Q : Ordinal.{0}, ω ^ Q * guR d x =
      ω ^ (Q + guA x (guR (guN d) x) * guR (log (guE d) d) x) * guR (d / guE d ^ log (guE d) d) x +
        ω ^ Q * guR (d % guE d ^ log (guE d) d) x := by
    intro x Q
    rw [guR_dec hdW hdB, mul_add, ← mul_assoc, gu_pow_eq (guA_E _ _), ← opow_add]
  rw [e ρ P, e σ P']
  obtain ⟨w1, w2⟩ := pi_add hB u1 v1
  exact ⟨w1, by rw [w2, u2, v2]⟩

/-- **LEMMA EXACT for every code `c < ζ_{Ω₁+1}`** at every pair of bases `σ < ρ` with the gate below `σ`:
`c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(c(ρ)) = c(σ)`. -/
theorem gu_pi : ∀ c, c < guB → guG c < σ → guR c ρ ∈ TB ρ σ ∧ pi σ ρ (guR c ρ) = guR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hωσ := omega0_lt_inE hσE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE] at hg
    rw [guR_low hcE, guR_low hcE]
    exact rdc_pi hB hcE hg
  obtain ⟨hn1, hnc', hcn, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gu_parts hcE hc
  obtain ⟨g0n, g0k, g0d, g0r⟩ := gu_parts_g hωσ hcE hc hg
  have hEcE : InE (guE c) := guE_E c
  have hcN' : c < eN (guE c) := by rw [guE, ← evA_add_one]; exact hcn
  have hkN : log (guE c) c < eN (guE c) := hkc.trans hcN'
  have hexn := IH _ hnc hnB g0n
  obtain ⟨b1, b2, b3, b4⟩ := gu_base_pi hB hn1 hnB g0n hexn
  have hBK := gu_BK_pi hB hn1 hnB g0n hk hkN hexn (fun hω => by
    have hk1 : 1 < log (guE c) c := lt_of_lt_of_le one_lt_omega0 hω
    have hEkc : guE c * log (guE c) c < c := (gu_mulE_lt_pow hEcE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, hB', hg', -⟩ := gu_mulE hn1 hnB _ hk hkN
    exact IH _ hEkc hB' (hg'.trans_lt (max_lt ((guQ_le _).trans_lt g0n) g0k)))
  set Bρ := guA ρ (guR (guN c) ρ) with hBρdef
  set Bσ := guA σ (guR (guN c) σ) with hBσdef
  have hBρE : InE Bρ := guA_E _ _
  have hBσE : InE Bσ := guA_E _ _
  have h1ρ : 1 ≤ guR (guN c) ρ := guR_pos' hρE (one_le_iff_ne_zero.1 hn1) hnB
  have h1σ : 1 ≤ guR (guN c) σ := guR_pos' hσE (one_le_iff_ne_zero.1 hn1) hnB
  have hρB : ρ < Bρ := (lt_eN ρ).trans_le (gu_eN_le_guA ρ h1ρ)
  have hσB : σ < Bσ := (lt_eN σ).trans_le (gu_eN_le_guA σ h1σ)
  have hBO : Bρ < Om1 := by
    rw [hBρdef, guA_eq hρE h1ρ]
    exact (evA_lt_evZ hρE (guR_lt_evZ hρE _ hnB (g0n.trans hB.2.2.1))).trans (evZ_lt_Om1 hρE hρ1)
  have hNO : eN Bρ < Om1 := eN_lt_Om1K hBO
  have hKN : guR (log (guE c) c) ρ < eN Bρ := by
    rcases lt_or_ge (log (guE c) c) (guE c) with hkE | hkE
    · exact (guR_lt_base hρE hn1 hnB (g0n.trans hB.2.2.1) hkE (g0k.trans hB.2.2.1)).trans (lt_eN _)
    · obtain ⟨hNk, -, hgfk⟩ := gu_same hkE (hkc.trans hcn) hn1
      have := guR_top hρE (hkc.trans hc) hgfk (g0k.trans hB.2.2.1)
      rwa [hNk, guA_succ ρ h1ρ] at this
  -- the atoms `ω^{B·K+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < Bρ → ω ^ (Bρ * guR (log (guE c) c) ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (Bρ * guR (log (guE c) c) ρ + β)) = ω ^ (Bσ * guR (log (guE c) c) σ + pi σ ρ β) := by
    intro β hβ hβB
    have hlt : Bρ * guR (log (guE c) c) ρ + β < eN Bρ :=
      (inE_indec (eN_E Bρ)).add_lt ((eN_E Bρ).mul_lt (lt_eN Bρ) hKN) (hβB.trans (lt_eN Bρ))
    rcases lt_or_ge (log (guE c) c) ω with hkω | hkω
    · obtain ⟨j, hj⟩ := lt_omega0.1 hkω
      obtain ⟨j0, rfl⟩ : ∃ j0 : ℕ, j = j0 + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hk (by rw [hj]; rfl))
      rw [hj, guR_nat, guR_nat]
      obtain ⟨m1, m2⟩ := pi_mul_nat hB b1 b2 j0
      obtain ⟨n1, n2⟩ := pi_add hB m1 hβ
      have hc1 : ((j0 + 1 : ℕ) : Ordinal.{0}) = 1 + (j0 : Ordinal.{0}) := by
        rw [Nat.add_comm]; push_cast; rfl
      have eρ : Bρ * ((j0 + 1 : ℕ) : Ordinal.{0}) + β = Bρ + (Bρ * (j0 : Ordinal.{0}) + β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      have eσ : Bσ * ((j0 + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β = Bσ + (Bσ * (j0 : Ordinal.{0}) + pi σ ρ β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      rw [hj, guR_nat] at hlt
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1 (by rw [← eρ]; exact hlt)
      rw [n2, m2] at a2
      rw [eρ, eσ]
      exact ⟨a1, a2⟩
    · have hKω : ω ≤ guR (log (guE c) c) ρ := gu_omega_le hρE hkω (hkc.trans hc)
      have hKω' : ω ≤ guR (log (guE c) c) σ := gu_omega_le hσE hkω (hkc.trans hc)
      have hab : ∀ X K : Ordinal.{0}, ω ≤ K → ∀ b, X * K + b = X + (X * K + b) := by
        intro X K hK b
        rw [← add_assoc]
        congr 1
        calc X * K = X * (1 + K) := by rw [one_add_of_omega0_le hK]
          _ = X + X * K := by rw [mul_add, mul_one]
      obtain ⟨n1, n2⟩ := pi_add hB hBK.1 hβ
      rw [hBK.2] at n2
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1
        (by rw [← hab _ _ hKω]; exact hlt)
      rw [n2] at a2
      rw [hab Bρ _ hKω β, hab Bσ _ hKω' (pi σ ρ β)]
      exact ⟨a1, a2⟩
  have hdig := gu_dig hB hn1 hnB g0n (fun j hj hgj => IH j (hj.trans_le hnc') (hj.trans (gu_evA_lt hnB)) hgj)
    _ hdE g0d _ _ hat
  obtain ⟨r1, r2⟩ := IH _ hrc (hrc.trans hc) g0r
  rw [guR_dec hcE hc, guR_dec hcE hc, gu_pow_eq hBρE, gu_pow_eq hBσE]
  obtain ⟨w1, w2⟩ := pi_add hB hdig.1 r1
  exact ⟨w1, by rw [w2, hdig.2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gk
