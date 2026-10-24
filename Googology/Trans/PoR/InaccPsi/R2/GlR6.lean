import Googology.Trans.PoR.InaccPsi.R2.GlR5

/-!
# CODES BELOW `Γ_{Ω₁+1}`: Lemma EXACT at every pair of bases

The atom of an `ε`-number code of level `α` is `ϑˣ(Ω₁·α(x) + η(x))`, so its base change is [W07a] Def 5.1
(`pi_vt_two`, with `π(Ω₁·β) = Ω₁·π(β)`: `π(ϑᵖ(Ω₁·β + t)) = ϑ^σ(Ω₁·π(β) + π(t))`), and so is the base change of the next
`ε`-number after it (`ϑᵖ(Ω₁ + t + 1)` at level `1`, `ϑᵖ(Ω₁ + a)` above a fixed point `a`; `R2.GlAt`).  The rest
is the argument of round 82 (`R2.GkU7`) with the pseudo-base `ε_{x+ν(x)}` replaced by the atom of any level.

* `gl_mulE` (**`e·κ` is a code**, `e` an `ε`-number code: `(e·κ)(x) = e(x)·κ(x)`, gate at most
  `max(QE e, gate κ)`);
* `gl_base_pi` (`π(e(ρ)) = e(σ)` and the same for the next `ε`-number), `gl_BK_pi` (`π(B·K) = B'·K'`);
* `gl_dig` (**`π(ω^P·d(ρ)) = ω^{P'}·d(σ)`** for every code `d` below an `ε`-number code, once the atoms are exact);
* `gl_pi` (**LEMMA EXACT for every code `c < Γ_{Ω₁+1}`** at every pair of bases `σ < ρ` above its gate; no
  `υ`-point hypothesis; one induction).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **`e·κ` as a code** (`e` an `ε`-number code, `1 ≤ κ < ε_{e+1}`). -/
theorem gl_mulE {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) : ∀ κ, κ ≠ 0 → κ < eN e →
    e * κ < eN e ∧ e * κ < gcG 0 ∧ glG (e * κ) ≤ max (glQE e) (glG κ) ∧
      ∀ x, InE x → x < Om1 → glG κ < x → glR (e * κ) x = glR e x * glR κ x := by
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have hNB : eN e ≤ gcG 0 := eN_le heB gl_G0_E
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
  intro hk0 hkN
  have hv : e * κ < eN e := (eN_E e).mul_lt (lt_eN e) hkN
  refine ⟨hv, hv.trans_le hNB, ?_⟩
  rcases lt_or_ge κ e with hkE | hkE
  · have e1 : e * κ = e ^ (1 : Ordinal.{0}) * κ + 0 := by rw [opow_one, add_zero]
    have hr : (0 : Ordinal.{0}) < e ^ (1 : Ordinal.{0}) := opow_pos _ he.pos
    refine ⟨?_, fun x _ _ _ => ?_⟩
    · rw [e1, glG_cnf he hOe one_ne_zero hk0 hkE hr (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), glQ_one, glG_zero]
      simp only [zero_le, max_eq_left, max_eq_right]
      exact max_le (le_max_left _ _) ((glQ_le κ).trans (le_max_right _ _))
    · rw [e1, glR_cnf he hOe one_ne_zero hk0 hkE hr (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), glR_one, opow_one,
        glR_zero, add_zero, ← glR_base he hOe heB]
  have hkB : κ < gcG 0 := hkN.trans_le hNB
  obtain ⟨hEk, hgfk⟩ := gl_same he hOe hkE hkN
  obtain ⟨ha, hq0, hqE, hs, hdec, hak, hsk, -⟩ := gl_parts hgfk
  rw [hEk] at ha hq0 hqE hs hdec hak hsk
  set a := log e κ with hadef
  set q := κ / e ^ a with hqdef
  set s := κ % e ^ a with hsdef
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEs : e * s < e ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ he.pos).2 hs
  have e1 : e * κ = e ^ (1 + a) * q + e * s := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hsN : s < eN e := hsk.trans hkN
  have hgEs : glG (e * s) ≤ max (glQE e) (glG s) := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, mul_zero, glG_zero]; exact zero_le
    · exact (IH s hsk h0 hsN).2.2.1
  have hgk : glG κ = max (max (glQE e) (glQ a)) (max (glQ q) (glG s)) := by
    rw [glG_dec hgfk hkB, hEk]
  refine ⟨?_, fun x hx hx1 hgx => ?_⟩
  · rw [e1, glG_cnf he hOe h1a hq0 hqE hEs (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), glQ_one_add, hgk]
    refine max_le (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_right _ _)))) (max_le ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
      (hgEs.trans (max_le (le_max_left _ _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))))))
  · have hωx := omega0_lt_inE hx
    obtain ⟨-, g1, -, g3⟩ := gl_parts_g hωx hgfk hkB hgx
    rw [hEk] at g1 g3
    rw [e1, glR_cnf he hOe h1a hq0 hqE hEs (e1 ▸ hv) (e1 ▸ hv.trans_le hNB), glR_dec hgfk hkB, hEk,
      ← glR_base he hOe heB]
    have hRs : glR (e * s) x = glR e x * glR s x := by
      rcases eq_or_ne s 0 with h0 | h0
      · rw [h0, mul_zero, glR_zero, mul_zero]
      · exact (IH s hsk h0 hsN).2.2.2 x hx hx1 g3
    rw [hRs, glR_one_add hx hx1 (hak.trans hkB) g1, opow_add, opow_one, mul_assoc, ← mul_add]

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(e(ρ)) = e(σ)`** for an `ε`-number code `e`, and the same for the next `ε`-number, from Lemma EXACT at its
level and its index. -/
theorem gl_base_pi {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < σ)
    (hexα : glR (glK e) ρ ∈ TB ρ σ ∧ pi σ ρ (glR (glK e) ρ) = glR (glK e) σ)
    (hex : glR (glI e) ρ ∈ TB ρ σ ∧ pi σ ρ (glR (glI e) ρ) = glR (glI e) σ) :
    glR e ρ ∈ TB ρ σ ∧ pi σ ρ (glR e ρ) = glR e σ ∧
      eN (glR e ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (glR e ρ)) = eN (glR e σ) := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨rρ, -, -, -, -, -, hkRρ, -, hk1ρ, -, hη1, -, -⟩ := gl_eps_read hρE hρ1 he hOe heB (hge.trans hB.2.2.1)
  obtain ⟨rσ, -, -, -, -, -, -, -, -, -, -, -, -⟩ := gl_eps_read hσE hσ1 he hOe heB hge
  obtain ⟨a1, a2⟩ := glA_pi hB hexα.1 hk1ρ hex.1 hη1
  obtain ⟨b1, b2⟩ := glA_eN_pi hB hkRρ hexα.1 hk1ρ hex.1 hη1
  rw [hex.2, hexα.2] at a2 b2
  rw [rρ, rσ]
  exact ⟨a1, a2, b1, b2⟩

/-- **`π(B·K) = B'·K'`** for the atom `B = e(ρ)` of an `ε`-number code and a code `κ` (finite: `pi_mul_nat`; infinite:
the code `e·κ`). -/
theorem gl_BK_pi {e κ : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < σ)
    (hκ0 : κ ≠ 0) (hκN : κ < eN e) (hgκ : glG κ < σ)
    (hexe : glR e ρ ∈ TB ρ σ ∧ pi σ ρ (glR e ρ) = glR e σ)
    (hexm2 : ω ≤ κ → glR (e * κ) ρ ∈ TB ρ σ ∧ pi σ ρ (glR (e * κ) ρ) = glR (e * κ) σ) :
    glR e ρ * glR κ ρ ∈ TB ρ σ ∧ pi σ ρ (glR e ρ * glR κ ρ) = glR e σ * glR κ σ := by
  rcases lt_or_ge κ ω with hω | hω
  · obtain ⟨j, rfl⟩ := lt_omega0.1 hω
    rw [glR_nat, glR_nat]
    exact pi_mul_nat hB hexe.1 hexe.2 j
  · obtain ⟨-, -, -, hR⟩ := gl_mulE he hOe heB κ hκ0 hκN
    rw [← hR ρ hB.2.1 hB.2.2.2 (hgκ.trans hB.2.2.1), ← hR σ hB.1 (hB.2.2.1.trans hB.2.2.2) hgκ]
    exact hexm2 hω

/-- **The digits**: `π(ω^P·d(ρ)) = ω^{P'}·d(σ)` for every code `d` below an `ε`-number code `e` with gate below `σ`,
once the atoms `ω^{P+β}` (`β ∈ Tᵖ[σ]`, `β < e(ρ)`) are exact and Lemma EXACT holds below `e`. -/
theorem gl_dig {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (hge : glG e < σ)
    (hEX : ∀ j, j < e → glG j < σ → glR j ρ ∈ TB ρ σ ∧ pi σ ρ (glR j ρ) = glR j σ) :
    ∀ d, d < e → glG d < σ → ∀ P P' : Ordinal.{0},
      (∀ β, β ∈ TB ρ σ → β < glR e ρ →
        ω ^ (P + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (P + β)) = ω ^ (P' + pi σ ρ β)) →
      ω ^ P * glR d ρ ∈ TB ρ σ ∧ pi σ ρ (ω ^ P * glR d ρ) = ω ^ P' * glR d σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  have hgeρ : glG e < ρ := hge.trans hB.2.2.1
  have hBρ : eN ρ ≤ glR e ρ := (gl_eps_read hρE hρ1 he hOe heB hgeρ).2.2.2.2.2.2.2.2.2.2.2.2
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hdE hgd P P' hat
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [glR_zero, glR_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  rcases lt_or_ge d gfE with hdW | hdW
  · -- a code below `ε_{Ω₁+1}`: the normal form `Ω₁^l·q + r` of `R2.GfSub`
    have hgd' : gtc d < σ := by rw [glG_low hdW] at hgd; exact hgd
    obtain ⟨-, hqΩ, -, -, hrγ, -⟩ := parts hd0
    obtain ⟨gl, gq, gr⟩ := gtc_parts hd0 hdW
    have hrW : log Om1 d < gfE ∧ d % Om1 ^ log Om1 d < gfE := ⟨(log_lt hd0 hdW).trans hdW, hrγ.trans hdW⟩
    obtain ⟨h1, h2⟩ := IH _ hrγ (hrγ.trans hdE) (by rw [glG_low hrW.2]; exact gr.trans_lt hgd') P P' hat
    simp only [glR_low hrW.2] at h1 h2
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
    rw [glR_low hdW, glR_low hdW, edec ρ P hρE, edec σ P' hσE]
    obtain ⟨m3, m4⟩ := pi_add hB m1 h1
    exact ⟨m3, by rw [m4, m2, h2]⟩
  -- a code of a lower bracket
  have hdB : d < gcG 0 := hdE.trans heB
  obtain ⟨hk, hd0', -, -, hdec, hkd, hrd, hdd⟩ := gl_parts hdW
  obtain ⟨g0n, g0k, g0d, g0r⟩ := gl_parts_g hωσ hdW hdB hgd
  have hlt : ∀ j, j < d → j < e := fun j hj => hj.trans hdE
  set ed := guE d with heddef
  have hEdE : InE ed := guE_E d
  have hOd : Om1 < ed := gl_Om1_lt_E hdW
  have hedd : ed ≤ d := gl_E_le hdW
  have hedB : ed < gcG 0 := hedd.trans_lt hdB
  have hged : glG ed < σ := gl_E_g hdW hdB hgd
  have hkN : log ed d < eN ed := hkd.trans (gl_lt_eN hdW)
  have hexe : glR ed ρ ∈ TB ρ σ ∧ pi σ ρ (glR ed ρ) = glR ed σ := by
    rcases hedd.lt_or_eq with h | h
    · exact hEX _ (hlt _ h) hged
    · have hgq : glQE ed < σ := by rw [glG_base hEdE hOd hedB] at hged; exact hged
      obtain ⟨b1, b2, -, -⟩ := gl_base_pi hB hEdE hOd hedB hged
        (hEX _ (hlt _ ((glData_spec hEdE hOd hedB).2.1.trans_le hedd))
          (glG_of_Q hωσ ((glQE_le_K ed).trans_lt hgq)))
        (hEX _ (hlt _ ((glData_spec hEdE hOd hedB).2.2.1.trans_le hedd))
          (glG_of_Q hωσ ((glQE_le_I ed).trans_lt hgq)))
      exact ⟨b1, b2⟩
  have hBK := gl_BK_pi hB hEdE hOd hedB hged hk hkN g0k hexe (fun hω => by
    have hk1 : 1 < log ed d := lt_of_lt_of_le one_lt_omega0 hω
    have hEkd : ed * log ed d < d := (gu_mulE_lt_pow hEdE hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0')).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, -, hg, -⟩ := gl_mulE hEdE hOd hedB _ hk hkN
    refine hEX _ (hlt _ hEkd) (hg.trans_lt (max_lt ?_ g0k))
    rw [glG_base hEdE hOd hedB] at hged; exact hged)
  have hgdρ : glG d < ρ := hgd.trans hB.2.2.1
  have hlead : glR ed ρ * glR (log ed d) ρ < glR e ρ := by
    have hEdρ := (gl_eps_read hρE hρ1 hEdE hOd hedB (hged.trans hB.2.2.1)).2.2.2.2.2.2.2.2.2.2.2.1
    have h1 : glR ed ρ * glR (log ed d) ρ ≤ glR ed ρ ^ glR (log ed d) ρ := by
      rw [gu_pow_eq hEdρ]; exact right_le_opow _ one_lt_omega0
    have h2 := (gl_lead hρE hρ1 hdW hdB hgdρ).1
    rw [← gl_At_eq hdW hdB] at h2
    have h3 : glR ed ρ ^ glR (log ed d) ρ ≤
        glR ed ρ ^ glR (log ed d) ρ * glR (d / ed ^ log ed d) ρ :=
      le_mul_of_one_le_right' (glR_pos' hρE hρ1 hd0' (hdd.trans hdB) (g0d.trans hB.2.2.1))
    exact (h1.trans (h3.trans h2)).trans_lt (glR_lt_eps hρE hρ1 he hOe heB hgeρ hdE hgdρ)
  have hat' : ∀ β, β ∈ TB ρ σ → β < glR e ρ →
      ω ^ ((P + glR ed ρ * glR (log ed d) ρ) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ ((P + glR ed ρ * glR (log ed d) ρ) + β)) =
        ω ^ ((P' + glR ed σ * glR (log ed d) σ) + pi σ ρ β) := by
    intro β hβ hβB
    obtain ⟨s1, s2⟩ := pi_add hB hBK.1 hβ
    have hRE := (gl_eps_read hρE hρ1 he hOe heB hgeρ).2.2.2.2.2.2.2.2.2.2.2.1
    have := hat _ s1 ((inE_indec hRE).add_lt hlead hβB)
    rw [s2, hBK.2] at this
    rw [add_assoc, add_assoc]; exact this
  obtain ⟨u1, u2⟩ := IH _ hdd (hlt _ hdd) g0d _ _ hat'
  obtain ⟨v1, v2⟩ := IH _ hrd (hlt _ hrd) g0r P P' hat
  have e1 : ∀ x Q : Ordinal.{0}, InE (glR ed x) → ω ^ Q * glR d x =
      ω ^ (Q + glR ed x * glR (log ed d) x) * glR (d / ed ^ log ed d) x +
        ω ^ Q * glR (d % ed ^ log ed d) x := by
    intro x Q hx
    rw [glR_dec hdW hdB, ← gl_At_eq hdW hdB, mul_add, ← mul_assoc, gu_pow_eq hx, ← opow_add]
  have hEdρ := (gl_eps_read hρE hρ1 hEdE hOd hedB (hged.trans hB.2.2.1)).2.2.2.2.2.2.2.2.2.2.2.1
  have hEdσ := (gl_eps_read hσE hσ1 hEdE hOd hedB hged).2.2.2.2.2.2.2.2.2.2.2.1
  rw [e1 ρ P hEdρ, e1 σ P' hEdσ]
  obtain ⟨w1, w2⟩ := pi_add hB u1 v1
  exact ⟨w1, by rw [w2, u2, v2]⟩

/-- **LEMMA EXACT for every code `c < Γ_{Ω₁+1}`** at every pair of bases `σ < ρ` with the gate below `σ`:
`c(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(c(ρ)) = c(σ)`. -/
theorem gl_pi : ∀ c, c < gcG 0 → glG c < σ → glR c ρ ∈ TB ρ σ ∧ pi σ ρ (glR c ρ) = glR c σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ := omega0_lt_inE hσE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [glG_low hcE] at hg
    rw [glR_low hcE, glR_low hcE]
    exact rdc_pi hB hcE hg
  by_cases hcI : InE c
  · have hOc : Om1 < c := Om1_lt_eW.trans_le hcE
    have hkc := (glData_spec hcI hOc hc).2.1
    have hηc := (glData_spec hcI hOc hc).2.2.1
    have hgq : glQE c < σ := by rw [glG_base hcI hOc hc] at hg; exact hg
    have hgη : glG (glI c) < σ := glG_of_Q hωσ ((glQE_le_I c).trans_lt hgq)
    have hgk : glG (glK c) < σ := glG_of_Q hωσ ((glQE_le_K c).trans_lt hgq)
    obtain ⟨b1, b2, -, -⟩ := gl_base_pi hB hcI hOc hc hg (IH _ hkc (hkc.trans hc) hgk) (IH _ hηc (hηc.trans hc) hgη)
    exact ⟨b1, b2⟩
  have hEc := gl_E_lt_self hcE hcI
  set e := guE c with hedef
  have he : InE e := guE_E c
  have hOe : Om1 < e := gl_Om1_lt_E hcE
  have heB : e < gcG 0 := hEc.trans hc
  have hge : glG e < σ := gl_E_g hcE hc hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  obtain ⟨g0n, g0k, g0d, g0r⟩ := gl_parts_g hωσ hcE hc hg
  have hcN' : c < eN e := gl_lt_eN hcE
  have hkN : log e c < eN e := hkc.trans hcN'
  have hηc : glI e < c := gl_idx_lt hcE hc
  have hkc' : glK e < c := gl_lev_lt hcE hc
  have g0l : glG (glK e) < σ := gl_parts_lev hωσ hcE hc hg
  obtain ⟨b1, b2, b3, b4⟩ := gl_base_pi hB he hOe heB hge (IH _ hkc' (hkc'.trans hc) g0l) (IH _ hηc (hηc.trans hc) g0n)
  have hBK := gl_BK_pi hB he hOe heB hge hk hkN g0k ⟨b1, b2⟩ (fun hω => by
    have hk1 : 1 < log e c := lt_of_lt_of_le one_lt_omega0 hω
    have hEkc : e * log e c < c := (gu_mulE_lt_pow he hk1 hkN).trans_le (by
      exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans (le_self_add.trans_eq hdec))
    obtain ⟨-, hB', hg', -⟩ := gl_mulE he hOe heB _ hk hkN
    refine IH _ hEkc hB' (hg'.trans_lt (max_lt ?_ g0k))
    rw [glG_base he hOe heB] at hge; exact hge)
  set Bρ := glR e ρ with hBρdef
  set Bσ := glR e σ with hBσdef
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBρE, hρB'⟩ := gl_eps_read hρE hρ1 he hOe heB (hge.trans hB.2.2.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hBσE, hσB'⟩ := gl_eps_read hσE hσ1 he hOe heB hge
  have hρB : ρ < Bρ := (lt_eN ρ).trans_le hρB'
  have hσB : σ < Bσ := (lt_eN σ).trans_le hσB'
  have hBO : Bρ < Om1 := (glR_T hρE hρ1 heB (hge.trans hB.2.2.1)).2
  have hNO : eN Bρ < Om1 := eN_lt_Om1K hBO
  have hKN : glR (log e c) ρ < eN Bρ := by
    rcases lt_or_ge (log e c) e with hkE | hkE
    · exact (glR_lt_eps hρE hρ1 he hOe heB (hge.trans hB.2.2.1) hkE (g0k.trans hB.2.2.1)).trans (lt_eN _)
    · obtain ⟨hEk, hgfk⟩ := gl_same he hOe hkE (hkc.trans hcN')
      have := glR_top hρE hρ1 (hkc.trans hc) hgfk (g0k.trans hB.2.2.1)
      rwa [hEk] at this
  -- the atoms `ω^{B·K+β}`
  have hat : ∀ β, β ∈ TB ρ σ → β < Bρ → ω ^ (Bρ * glR (log e c) ρ + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (Bρ * glR (log e c) ρ + β)) = ω ^ (Bσ * glR (log e c) σ + pi σ ρ β) := by
    intro β hβ hβB
    have hlt : Bρ * glR (log e c) ρ + β < eN Bρ :=
      (inE_indec (eN_E Bρ)).add_lt ((eN_E Bρ).mul_lt (lt_eN Bρ) hKN) (hβB.trans (lt_eN Bρ))
    rcases lt_or_ge (log e c) ω with hkω | hkω
    · obtain ⟨j, hj⟩ := lt_omega0.1 hkω
      obtain ⟨j0, rfl⟩ : ∃ j0 : ℕ, j = j0 + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hk (by rw [hj]; rfl))
      rw [hj, glR_nat, glR_nat]
      obtain ⟨m1, m2⟩ := pi_mul_nat hB b1 b2 j0
      obtain ⟨n1, n2⟩ := pi_add hB m1 hβ
      have hc1 : ((j0 + 1 : ℕ) : Ordinal.{0}) = 1 + (j0 : Ordinal.{0}) := by
        rw [Nat.add_comm]; push_cast; rfl
      have eρ : Bρ * ((j0 + 1 : ℕ) : Ordinal.{0}) + β = Bρ + (Bρ * (j0 : Ordinal.{0}) + β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      have eσ : Bσ * ((j0 + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β = Bσ + (Bσ * (j0 : Ordinal.{0}) + pi σ ρ β) := by
        rw [hc1, mul_add, mul_one, add_assoc]
      rw [hj, glR_nat] at hlt
      obtain ⟨a1, a2⟩ := gu_atom_pi hB hBρE hBσE hρB hσB b1 b2 b3 b4 hNO n1 (by rw [← eρ]; exact hlt)
      rw [n2, m2] at a2
      rw [eρ, eσ]
      exact ⟨a1, a2⟩
    · have hKω : ω ≤ glR (log e c) ρ := gl_omega_le hρE hρ1 hkω (hkc.trans hc) (g0k.trans hB.2.2.1)
      have hKω' : ω ≤ glR (log e c) σ := gl_omega_le hσE hσ1 hkω (hkc.trans hc) g0k
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
  have hdig := gl_dig hB he hOe heB hge (fun j hj hgj => IH j (hj.trans hEc) (hj.trans heB) hgj)
    _ hdE g0d _ _ hat
  obtain ⟨r1, r2⟩ := IH _ hrc (hrc.trans hc) g0r
  rw [glR_dec hcE hc, glR_dec hcE hc, ← gl_At_eq hcE hc, ← gl_At_eq hcE hc, gu_pow_eq hBρE, gu_pow_eq hBσE]
  obtain ⟨w1, w2⟩ := pi_add hB hdig.1 r1
  exact ⟨w1, by rw [w2, hdig.2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gl
