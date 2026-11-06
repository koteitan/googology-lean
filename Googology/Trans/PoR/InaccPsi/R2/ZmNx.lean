import Googology.Trans.PoR.InaccPsi.R2.ZmTc

/-!
# ZmNx: THE GENERIC HEREDITARY STEP `E ↦ ε_{E+1}` AND ITS ITERATION — `ZbDirect S ε_{B_Γ+ω}`

* `zmTw` (the tower `E, E^E, …`), `zmTw_lt`, `zmTw_cof` (**cofinal in `ε_{E+1}`**);
* `ZmDS.sR_tw` (the tower of codes reads the tower of `V(x)`, gate `≤ 1`);
* `ZmDS.step` (**THE GENERIC STEP: a digit system at the base `E` gives one at the base `ε_{E+1}`**, codes
  `E^k·d + r`, reading `V(x)^{R(k)(x)}·R(d)(x) + R(r)(x)`, `V' = ε_{V+1}`, `W' = W + 1`);
* `zmCh n` (the digit system at the base `ε_{B_Γ+n}`), `zmCh_E`, `zmDirectN` (**`ZbDirect S ε_{B_Γ+n+1}`**),
  `zmDirectW` (**`ZbDirect S ε_{B_Γ+ω}`, UNCONDITIONAL**), `zmUVW` (**UPPER ∧ LOWER ∧ CapV at every range restart
  below `ι(Γ(B)·ω)`, every `B < ε_{B_Γ+ω}`, UNCONDITIONAL**).

No new axiom.  New definitions: `zmTw`, `ZmDS.step`, `zmCh`.
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

/-! ## The tower -/

/-- **The tower** `E, E^E, E^{E^E}, …`. -/
noncomputable def zmTw (E : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => E
  | n + 1 => E ^ zmTw E n

section Tw

variable {E : Ordinal.{0}} (hE : InE E)
include hE

theorem zmTw_pos : ∀ n, 0 < zmTw E n
  | 0 => hE.pos
  | n + 1 => opow_pos _ hE.pos

omit hE in
theorem zmTw_lt : ∀ n, zmTw E n < eN E
  | 0 => lt_eN E
  | n + 1 => zm_opow_lt (eN_E E) (lt_eN E) (zmTw_lt n)

theorem zmTw_iter : ∀ n : ℕ, (fun a => ω ^ a)^[n] (E + 1) ≤ zmTw E (n + 1)
  | 0 => by
    show E + 1 ≤ E ^ E
    have h1 : E < E ^ E := by
      have := (opow_lt_opow_iff_right (lu_one_lt_E hE)).2 (lu_one_lt_E hE); rwa [opow_one] at this
    exact (zm_opow_prin hE E h1 (lu_one_lt_E hE |>.trans h1)).le
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    show ω ^ ((fun a => ω ^ a)^[n] (E + 1)) ≤ E ^ zmTw E (n + 1)
    exact (opow_le_opow_right omega0_pos (zmTw_iter n)).trans
      (opow_le_opow_left _ (omega0_lt_inE hE).le)

/-- **The tower is cofinal in `ε_{E+1}`.** -/
theorem zmTw_cof {c : Ordinal.{0}} (hc : c < eN E) : ∃ n, c < zmTw E n := by
  unfold eN at hc
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (zmTw_iter hE n)⟩

end Tw

namespace ZmDS

variable (M : ZmDS)

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
noncomputable def step : ZmDS where
  E := eN M.E
  Ei := M.Ei + 1
  V := fun x => eN (M.V x)
  W := fun x => M.W x + 1
  R := M.sR
  G := M.sG
  Eg := M.Eg
  E_eq := by rw [← M.E_eq, Go.go_eN_veb]
  BG_le := M.BG_le.trans (lt_eN _).le
  E_X := by
    rw [← M.E_eq, Go.go_eN_veb]
    have hi : M.Ei + 1 < tlX := by
      have h := (right_le_veblen 1 M.Ei).trans_lt (M.E_eq ▸ M.E_X)
      exact (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC tlX_SC)).add_one_lt h
    exact tlX_SC.2 1 (gg_one_lt_of_SC tlX_SC) _ hi
  Ei_cl := fun Z hZ hEg => TlCl.add (M.Ei_cl Z hZ hEg) (TlCl.one hZ.1)
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
    obtain ⟨hVT, hVE, hDV, hVq⟩ := M.V_T x hx hx1 hEg
    obtain ⟨hWT, hW1, he⟩ := M.W_T x hx hx1 hEg
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    obtain ⟨-, -, -, hfix, -⟩ := zm_gq_facts hx hx1
    refine ⟨?_, eN_E _, hDV.trans (lt_eN _).le, zm_eN_lt_fix hVq hfix⟩
    rw [he]; exact (glA_facts hx hx1 le_rfl h1T h11 hWT hW1).1
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

end ZmDS

/-! ## The iteration -/

/-- **The digit system at the base `ε_{B_Γ+n}`.** -/
noncomputable def zmCh : ℕ → ZmDS
  | 0 => zmYr
  | n + 1 => (zmCh n).step

theorem zmCh_E : ∀ n : ℕ, (zmCh n).E = veblen 1 (tfBG + n)
  | 0 => by rw [Nat.cast_zero, add_zero, zm_BG_fix]; rfl
  | n + 1 => by
    show eN (zmCh n).E = _
    rw [zmCh_E n, Go.go_eN_veb, Nat.cast_succ, add_assoc]

theorem zmCh_Eg : ∀ n : ℕ, (zmCh n).Eg = 0
  | 0 => rfl
  | n + 1 => by show (zmCh n).Eg = 0; exact zmCh_Eg n

theorem zm_BG_lt_veb (n : ℕ) : tfBG < veblen 1 (tfBG + ((n + 1 : ℕ) : Ordinal.{0})) := by
  conv_lhs => rw [← zm_BG_fix]
  exact (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ (by exact_mod_cast Nat.succ_pos n))

/-- **`ZbDirect S ε_{B_Γ+n+1}`, UNCONDITIONAL.** -/
theorem zmDirectN (S : InaccSeq.{0}) (n : ℕ) : ZbDirect S (veblen 1 (tfBG + ((n + 1 : ℕ) : Ordinal.{0}))) := by
  have h := (zmCh (n + 1)).direct S (by rw [zmCh_E]; exact zm_BG_lt_veb n)
    (by rw [zmCh_Eg]; exact Td.tdK_SC.1) (zmCh n).step_gc0
  rwa [zmCh_E] at h

/-- **`ZbDirect S ε_{B_Γ+ω}`, UNCONDITIONAL.** -/
theorem zmDirectW (S : InaccSeq.{0}) : ZbDirect S (veblen 1 (tfBG + ω)) := by
  intro B hB1 hB2
  have hl : IsSuccLimit (tfBG + ω) := isSuccLimit_add _ isSuccLimit_omega0
  obtain ⟨c, hc, hBc⟩ := ((isNormal_veblen 1).lt_iff_exists_lt hl).1 hB2
  have hn : ∃ n : ℕ, c < tfBG + ((n + 1 : ℕ) : Ordinal.{0}) := by
    rcases lt_or_ge c tfBG with h | h
    · exact ⟨0, h.trans (lt_add_of_pos_right _ (by norm_num))⟩
    · obtain ⟨m, rfl⟩ := exists_add_of_le h
      obtain ⟨k, rfl⟩ := lt_omega0.1 ((add_lt_add_iff_left _).1 hc)
      exact ⟨k, (add_lt_add_iff_left _).2 (by exact_mod_cast Nat.lt_succ_self k)⟩
  obtain ⟨n, hn⟩ := hn
  exact zmDirectN S n B hB1 (hBc.trans ((isNormal_veblen 1).strictMono hn))

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < ε_{B_Γ+ω}`
(UNCONDITIONAL).** -/
theorem zmUVW (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < veblen 1 (tfBG + ω)) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zmDirectW S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zm
