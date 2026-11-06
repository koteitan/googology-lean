import Googology.Trans.PoR.InaccPsi.R2.ZmCo

/-!
# ZmPx: THE GENERIC STEP — LEMMA EXACT AND THE DIGIT LEMMA ONE LEVEL UP

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161 (through `Te.te_opow_pi`,
`Te.te_atom_pi`, `Gl.glA_pi`, `pi_add`).

* `ZmDS.VN_pi` (`π(ε_{V(ρ)+1}) = ε_{V(σ)+1}`), `ZmDS.opow_pi` (**`π(ω^X) = ω^{π X}` for
  `X ∈ Tᵖ[σ] ∩ [V(ρ), ε_{V(ρ)+1})`**), `ZmDS.atom_pi`;
* `ZmDS.sR_pi` (**Lemma EXACT for the readings below `ε_{E+1}` and for `V(ρ)·R(o)(ρ)`, one induction**),
  `ZmDS.sR_dig` (**the digit lemma for the codes below `ε_{E+1}` with the atoms `ω^{P+β}`, `β < ε_{V(ρ)+1}`**).

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

namespace ZmDS

variable (M : ZmDS)

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

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
