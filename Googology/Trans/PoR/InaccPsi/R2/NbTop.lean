import Googology.Trans.PoR.InaccPsi.R2.NbCu

/-!
# Nb: THE TOP OF A STAGE — THE DIGIT SYSTEM AT THE NEXT PSEUDO-BASE `φ(2, p+1)`

`P = φ(2, p)`, `Z = φ(2, p+1) < X`, `M₀` the base of the chain (`Nb.NbBase`, `V₀(x) = φ(2, b(x))`).  The members
`NbGood c`, `c < Z` (`Nb.nbGood_all`), close up to a digit system at the base `Z` with `V(x) = W(x) = φ(2, b(x)+1)`,
the base of the next stage (`NbBase _ (p+1) (b+1)`), given that `Z` is a code above the base gate and Lemma EXACT for
`φ(2, b(ρ)+1)`.

* `nbHR_base`, `nbHG_base` (the reading `φ(1, V₀(x) + R(n))` and the gate of a bracket base `φ(1, P+n)`);
* `nbIt` (the codes `0, P, φ(1, P·2), …`), `nbIt_lt`, `nbIt_gate`, `nbIt_cof` (**their readings are cofinal in
  `φ(2, b(x)+1) = nfp φ(1, ·) (V₀(x)+1)`**);
* `zm_fix2_of_gamma`, `nbZ_nfixG`, `nbMI_spec'`, `nbTop_pick`;
* `nbTopDS` (**the digit system at `Z`**), `nbTop_base` (**`NbBase (nbTopDS …) (p+1) (b+1)`**).

No new axiom.  New definitions: `nbIt`, `nbTopDS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Nb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Xk

/-- A fixed point of `Γ` is a fixed point of `φ(2, ·)`. -/
theorem zm_fix2_of_gamma {y : Ordinal.{0}} (h : gamma y = y) : veblen 2 y = y := by
  have h2G : (2 : Ordinal.{0}) < gamma y := by
    have := (natCast_lt_omega0 2).trans (omega0_lt_inE (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC y)))
    exact_mod_cast this
  have hfix : veblen 2 (gamma y) = gamma y := by
    conv_lhs => rw [← veblen_gamma_zero y]
    rw [veblen_veblen_of_lt h2G, veblen_gamma_zero]
  rwa [h] at hfix

/-- **`φ(2, p+1)` is no fixed point of `Γ`.** -/
theorem nbZ_nfixG (p : Ordinal.{0}) : gamma (veblen 2 (p + 1)) ≠ veblen 2 (p + 1) := by
  intro h
  have h2 := zm_fix2_of_gamma h
  have e := (isNormal_veblen 2).strictMono.injective h2
  have hE : InE (p + 1) := by rw [← e]; exact zm_veb_pos_E two_ne_zero
  exact not_isSuccLimit_add_one p (ev_isSuccLimit_of_inE hE)

section Base

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
include hM₀

omit hM₀ in
theorem nbHR_one (x : Ordinal.{0}) : nbHR p M₀.R M₀.V 1 x = 1 := by
  rw [nbHR_lt (lu_one_lt_E (zm_fix_E (nb_fixP p))), show (1 : Ordinal.{0}) = 0 + 1 by simp, M₀.succ, M₀.R0,
    zero_add]

/-- **The reading of a bracket base**: `R(φ(1, P+n)) = φ(1, V₀(x) + R(n))`. -/
theorem nbHR_base {n : Ordinal.{0}} (hn : n < veblen 2 (p + 1)) (x : Ordinal.{0}) :
    nbHR p M₀.R M₀.V (veblen 1 (veblen 2 p + n)) x = veblen 1 (M₀.V x + nbHR p M₀.R M₀.V n x) := by
  set E := veblen 1 (veblen 2 p + n) with hEdef
  have hE : InE E := zm_veb_E _
  have hB : veblen 2 p ≤ E := le_self_add.trans (right_le_veblen _ _)
  have hEZ : E < veblen 2 (p + 1) := nb_veb_lt_Z hn
  have h2 : E < veblen 1 (veblen 2 p + (n + 1)) :=
    (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one n))
  have hN : nbN p E = n := nbN_eq le_rfl h2
  have hBE : nbBE p E = E := by rw [nbBE_eq le_rfl h2]
  have h1E : (1 : Ordinal.{0}) < E := lu_one_lt_E hE
  have hlog : log E E = 1 := by have h := log_opow h1E 1; rwa [opow_one] at h
  rw [nbHR_cnf hB hEZ x, hN, hBE, hlog, opow_one, Ordinal.div_self hE.pos.ne', Ordinal.mod_self,
    nbHR_one, nbHR_zero hM₀, opow_one, mul_one, add_zero]

/-- **The gate of a bracket base.** -/
theorem nbHG_base {n : Ordinal.{0}} (hn : n < veblen 2 (p + 1)) :
    nbHG p M₀.G (veblen 1 (veblen 2 p + n)) = max (nbHG p M₀.G n) (max (M₀.G 1) (max (M₀.G 1) 0)) := by
  set E := veblen 1 (veblen 2 p + n) with hEdef
  have hE : InE E := zm_veb_E _
  have hB : veblen 2 p ≤ E := le_self_add.trans (right_le_veblen _ _)
  have hEZ : E < veblen 2 (p + 1) := nb_veb_lt_Z hn
  have h2 : E < veblen 1 (veblen 2 p + (n + 1)) :=
    (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one n))
  have hN : nbN p E = n := nbN_eq le_rfl h2
  have hBE : nbBE p E = E := by rw [nbBE_eq le_rfl h2]
  have h1E : (1 : Ordinal.{0}) < E := lu_one_lt_E hE
  have h1P : (1 : Ordinal.{0}) < veblen 2 p := lu_one_lt_E (zm_fix_E (nb_fixP p))
  have hlog : log E E = 1 := by have h := log_opow h1E 1; rwa [opow_one] at h
  rw [nbHG_cnf hB hEZ, hN, hBE, hlog, opow_one, Ordinal.div_self hE.pos.ne', Ordinal.mod_self,
    nbHG_lt h1P, nbHG_zero hM₀]

end Base

/-- **The codes `0, P, φ(1, P·2), …`**: `c₀ = 0`, `c_{k+1} = φ(1, P + c_k)`. -/
noncomputable def nbIt (p : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | k + 1 => veblen 1 (veblen 2 p + nbIt p k)

theorem nbIt_lt (p : Ordinal.{0}) : ∀ k, nbIt p k < veblen 2 (p + 1)
  | 0 => (nbP_pos (p + 1))
  | k + 1 => nb_veb_lt_Z (nbIt_lt p k)

section It

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
include hM₀

theorem nbIt_gate : ∀ k, nbHG p M₀.G (nbIt p k) ≤ max M₀.Eg 1
  | 0 => by show nbHG p M₀.G 0 ≤ _; rw [nbHG_zero hM₀]; exact zero_le
  | k + 1 => by
    show nbHG p M₀.G (veblen 1 (veblen 2 p + nbIt p k)) ≤ _
    rw [nbHG_base hM₀ (nbIt_lt p k)]
    exact max_le (nbIt_gate k) (max_le M₀.G1 (max_le M₀.G1 zero_le))

theorem nbIt_read (x : Ordinal.{0}) (k : ℕ) :
    nbHR p M₀.R M₀.V (nbIt p (k + 1)) x = veblen 1 (M₀.V x + nbHR p M₀.R M₀.V (nbIt p k) x) :=
  nbHR_base hM₀ (nbIt_lt p k) x

/-- **The readings of the codes `c_k` are cofinal in `φ(2, b(x)+1)`.** -/
theorem nbIt_cof {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M₀.Eg < x) :
    ∀ ν, ν < veblen 2 (b x + 1) → ∃ k, ν < nbHR p M₀.R M₀.V (nbIt p k) x := by
  have hV := hM₀.V_eq x hx hx1 hgx
  have hV1 : (1 : Ordinal.{0}) ≤ M₀.V x := by rw [hV]; exact (lu_one_lt_E (zm_fix_E (nb_fixP _))).le
  have hnfp : veblen 2 (b x + 1) = nfp (veblen 1) (M₀.V x + 1) := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, veblen_add_one, deriv_add_one, ← veblen_add_one,
      show (1 : Ordinal.{0}) + 1 = 2 by norm_num, hV]
  have h1 : nbHR p M₀.R M₀.V (nbIt p 1) x = M₀.V x := by
    rw [nbIt_read hM₀ x 0]
    show veblen 1 (M₀.V x + nbHR p M₀.R M₀.V 0 x) = _
    rw [nbHR_zero hM₀, add_zero, hV, nb_fixP]
  have hit : ∀ n : ℕ, (veblen 1)^[n] (M₀.V x + 1) ≤ nbHR p M₀.R M₀.V (nbIt p (n + 2)) x := by
    intro n
    induction n with
    | zero =>
      show M₀.V x + 1 ≤ nbHR p M₀.R M₀.V (nbIt p (1 + 1)) x
      rw [nbIt_read hM₀ x 1, h1]
      exact (add_le_add le_rfl hV1).trans (right_le_veblen _ _)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show veblen 1 ((veblen 1)^[n] (M₀.V x + 1)) ≤ nbHR p M₀.R M₀.V (nbIt p (n + 2 + 1)) x
      rw [nbIt_read hM₀ x (n + 2)]
      exact (isNormal_veblen 1).strictMono.monotone (ih.trans le_add_self)
  intro ν hν
  rw [hnfp] at hν
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hν
  exact ⟨n + 2, hn.trans_le (hit n)⟩

end It

section Top

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
  (hZX : veblen 2 (p + 1) < tlX)
  (hZcl : ∀ Z, SC Z → M₀.Eg < Z → TlCl Z (veblen 2 (p + 1)))
  (hbπ : ∀ σ ρ, Bases σ ρ → M₀.Eg < σ →
    veblen 2 (b ρ + 1) ∈ TB ρ σ ∧ R2.pi σ ρ (veblen 2 (b ρ + 1)) = veblen 2 (b σ + 1))

include hM₀ in
theorem nbMI_spec' {c : Ordinal.{0}} (hc : c < veblen 2 (p + 1)) :
    nbMI p c < veblen 2 (p + 1) ∧ c < veblen 1 (veblen 2 p + nbMI p c) ∧
      (∀ Z, IsSuccLimit Z → M₀.Eg < Z → nbHG p M₀.G c < Z → nbEg M₀ p (nbMI p c) < Z) := by
  unfold nbMI
  split_ifs with hcB
  · refine ⟨nbP_pos (p + 1), by rw [add_zero, nb_fixP]; exact hcB, fun Z hZ hgZ _ => ?_⟩
    rw [nbEg_zero hM₀]; exact hgZ
  · have hcB' : veblen 2 p ≤ c := not_lt.1 hcB
    obtain ⟨b1, b2, b3⟩ := nb_bracket hcB' hc
    refine ⟨(ev_isSuccLimit_of_inE (nbZ_E p)).add_one_lt (b3.trans hc), b2, fun Z hZ hgZ hg => ?_⟩
    exact max_lt hgZ (nbHG_succ_lt hZ (fun o _ h => M₀.g_succ o Z hZ hgZ h) _ (b3.trans hc)
      ((nbHG_idx hcB' hc).trans_lt hg))

include hM₀ hZX in
theorem nbTop_pick {c : Ordinal.{0}} (hc : c < veblen 2 (p + 1)) :
    ∃ M : ZmDS, ∃ μ, μ < veblen 2 (p + 1) ∧ c < M.E ∧ M.E = veblen 1 (veblen 2 p + μ) ∧ M.Eg = nbEg M₀ p μ ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = veblen 1 (M₀.V x + nbHR p M₀.R M₀.V μ x)) ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x < veblen 2 (b x + 1)) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = nbHR p M₀.R M₀.V c' x) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (nbHG p M₀.G c')) ∧
      (∀ Z, IsSuccLimit Z → M₀.Eg < Z → nbHG p M₀.G c < Z → nbEg M₀ p μ < Z) := by
  obtain ⟨h1, h2, h3⟩ := nbMI_spec' hM₀ hc
  obtain ⟨M, hE, hEg, hV, hVb, hR, hGg⟩ := nbGood_all hM₀ hZX _ h1
  exact ⟨M, nbMI p c, h1, hE ▸ h2, hE, hEg, hV, hVb, hR, hGg, h3⟩

include hM₀ hZX hZcl hbπ

open Classical in
/-- **THE DIGIT SYSTEM AT THE NEXT PSEUDO-BASE `φ(2, p+1)`.** -/
noncomputable def nbTopDS : ZmDS where
  E := veblen 2 (p + 1)
  Ei := veblen 2 (p + 1)
  V := fun x => veblen 2 (b x + 1)
  W := fun x => veblen 2 (b x + 1)
  R := fun c x => if InE x ∧ x < Om1 ∧ c < veblen 2 (p + 1) then nbHR p M₀.R M₀.V c x else c
  G := fun c => if c < veblen 2 (p + 1) then (if c = 0 then 0 else max M₀.Eg (nbHG p M₀.G c)) else M₀.Eg
  Eg := M₀.Eg
  E_eq := nbZ_fix p
  BG_le := (M₀.BG_le.trans hM₀.E_eq.le).trans (nbP_lt_Z p).le
  E_X := hZX
  Ei_cl := hZcl
  nfx := fun y h1 h2 hΓ => by
    rcases h2.lt_or_eq with h3 | h3
    · obtain ⟨M, -, -, hyM, -, -, -, -, -, -, -⟩ := nbTop_pick hM₀ hZX h3
      exact M.nfx y h1 hyM.le hΓ
    · rw [h3] at hΓ; exact nbZ_nfixG p hΓ
  Eg_le := fun c hc0 => by
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  V_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, -, hDV₀, -⟩ := nb_V₀_facts hM₀ hx hx1 hgx
    have hVq := nb_top_lt_gq hM₀ hx hx1 hgx
    obtain ⟨-, hqT, hq1, -, -⟩ := zm_gq_facts hx hx1
    refine ⟨vz_T_down hx hx1 hqT hq1 hVq.le, zm_fix_E (nb_fixP _), ?_, hVq⟩
    rw [hM₀.V_eq x hx hx1 hgx] at hDV₀
    exact hDV₀.trans ((isNormal_veblen 2).strictMono (lt_add_one _)).le
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hxV₀, hDV₀, -⟩ := nb_V₀_facts hM₀ hx hx1 hgx
    have hVq := nb_top_lt_gq hM₀ hx hx1 hgx
    obtain ⟨-, hqT, hq1, -, -⟩ := zm_gq_facts hx hx1
    have hVT : veblen 2 (b x + 1) ∈ Tset x := vz_T_down hx hx1 hqT hq1 hVq.le
    have hV1 : veblen 2 (b x + 1) < Om1 := hVq.trans hq1
    refine ⟨hVT, hV1, ?_⟩
    have hV₀V : M₀.V x ≤ veblen 2 (b x + 1) := by
      rw [hM₀.V_eq x hx hx1 hgx]; exact ((isNormal_veblen 2).strictMono (lt_add_one _)).le
    have hxV : x < veblen 2 (b x + 1) := hxV₀.trans_le hV₀V
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have hna := Na.na_glA hx hx1 le_rfl h1T h11 hVT hV1 hxV ((lu_one_lt_E hx).trans hxV) (b := b x + 1)
      (by rw [one_add_one_eq_two]) 0 (by rw [add_zero]; exact hVT) (by rw [add_zero]; exact hV1)
      (by rw [add_zero, one_add_one_eq_two]; exact nbP_lt_Z _)
    rw [add_zero, add_zero] at hna
    show eN (veblen 2 (b x + 1)) = glA 1 (veblen 2 (b x + 1)) x
    rw [hna]
    conv_lhs => rw [← nb_fixP (b x + 1)]
    exact Go.go_eN_veb _
  V_pi := fun σ ρ hB hg => hbπ σ ρ hB hg
  W_pi := fun σ ρ hB hg => hbπ σ ρ hB hg
  R0 := fun x => by
    split_ifs
    · exact nbHR_zero hM₀ x
    · rfl
  G0 := by
    rw [if_pos (nbP_pos (p + 1)), if_pos rfl]
  G1 := by
    have h1 : (1 : Ordinal.{0}) < veblen 2 (p + 1) := lu_one_lt_E (nbZ_E p)
    have h1P : (1 : Ordinal.{0}) < veblen 2 p := lu_one_lt_E (zm_fix_E (nb_fixP p))
    show (if (1 : Ordinal.{0}) < veblen 2 (p + 1) then (if (1 : Ordinal.{0}) = 0 then 0 else
      max M₀.Eg (nbHG p M₀.G 1)) else M₀.Eg) ≤ max M₀.Eg 1
    rw [if_pos h1, if_neg one_ne_zero, nbHG_lt h1P]
    exact max_le (le_max_left _ _) M₀.G1
  lt := fun c x hx hx1 hc hg => by
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [nbHR_zero hM₀]; exact veblen_pos
    rw [if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hMx : M.Eg < x := by rw [hEg]; exact htr x hxl hg0 hgc
    have hGc : M.G c < x := nb_memG hGg hcM hMx (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact (M.lt c x hx hx1 hcM hGc).trans (hVb x hx hx1 hMx)
  pos := fun c x hx hx1 hc0 hc hg => by
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hGc : M.G c < x := nb_memG hGg hcM (by rw [hEg]; exact htr x hxl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.pos c x hx hx1 hc0 hcM hGc
  mono := fun b' c x hx hx1 hbc hc hgb hgc => by
    have hb := hbc.trans hc
    rw [if_pos ⟨hx, hx1, hb⟩, if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hb] at hgb
    rw [if_pos hc] at hgc
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hbc).ne'
    rw [if_neg hc0] at hgc
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgc
    have hgcc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hgc
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hMx : M.Eg < x := by rw [hEg]; exact htr x hxl hg0 hgcc
    have hbM := hbc.trans hcM
    have hGc : M.G c < x := nb_memG hGg hcM hMx (Or.inr hgcc)
    have hGb : M.G b' < x := by
      refine nb_memG hGg hbM hMx ?_
      rcases eq_or_ne b' 0 with h0 | h0
      · exact Or.inl h0
      · rw [if_neg h0] at hgb; exact Or.inr ((le_max_right _ _).trans_lt hgb)
    rw [← hR c hcM x hx hx1 hGc, ← hR b' hbM x hx hx1 hGb]
    exact M.mono b' c x hx hx1 hbc hcM hGb hGc
  succ := fun c x => by
    by_cases h : InE x ∧ x < Om1 ∧ c < veblen 2 (p + 1)
    · obtain ⟨hx, hx1, hc⟩ := h
      have hc1 : c + 1 < veblen 2 (p + 1) := (ev_isSuccLimit_of_inE (nbZ_E p)).add_one_lt hc
      rw [if_pos ⟨hx, hx1, hc1⟩, if_pos ⟨hx, hx1, hc⟩]
      exact nbHR_succ (fun o _ x => M₀.succ o x) c hc x
    · have h' : ¬ (InE x ∧ x < Om1 ∧ c + 1 < veblen 2 (p + 1)) := fun ⟨hx, hx1, hc1⟩ =>
        h ⟨hx, hx1, (lt_add_one c).trans hc1⟩
      rw [if_neg h, if_neg h']
  g_le := fun c => by
    by_cases hc : c < veblen 2 (p + 1)
    · have hc1 : c + 1 < veblen 2 (p + 1) := (ev_isSuccLimit_of_inE (nbZ_E p)).add_one_lt hc
      rw [if_pos hc, if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      split_ifs with h0
      · exact zero_le
      · exact max_le_max le_rfl (nbHG_le_succ (fun o _ => M₀.g_le o) c hc)
    · have hc1 : ¬ c + 1 < veblen 2 (p + 1) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc, if_neg hc1]
  g_succ := fun c Z hZ hgZ hg => by
    by_cases hc : c < veblen 2 (p + 1)
    · have hc1 : c + 1 < veblen 2 (p + 1) := (ev_isSuccLimit_of_inE (nbZ_E p)).add_one_lt hc
      rw [if_pos hc] at hg
      rw [if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      refine max_lt hgZ (nbHG_succ_lt hZ (fun o _ h => M₀.g_succ o Z hZ hgZ h) c hc ?_)
      rcases eq_or_ne c 0 with h0 | h0
      · rw [h0, nbHG_zero hM₀]; exact hZ.bot_lt
      · rw [if_neg h0] at hg; exact (le_max_right _ _).trans_lt hg
    · have hc1 : ¬ c + 1 < veblen 2 (p + 1) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc1]; exact hgZ
  lim := fun c x hx hx1 hlc hc hg => by
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hGc : M.G c < x := nb_memG hGg hcM (by rw [hEg]; exact htr x hxl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hlc hcM hGc
  cof := fun c x hx hx1 hlc hc hg ν hν => by
    rw [if_pos ⟨hx, hx1, hc⟩] at hν
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hMx : M.Eg < x := by rw [hEg]; exact htr x hxl hg0 hgc
    have hGc : M.G c < x := nb_memG hGg hcM hMx (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc] at hν
    obtain ⟨b', hb, hgb, hνb⟩ := M.cof c x hx hx1 hlc hcM hGc ν hν
    have hbM := hb.trans hcM
    have hbl := hb.trans hc
    refine ⟨b', hb, ?_, ?_⟩
    · rw [if_pos hbl]
      split_ifs with h0
      · exact hx.pos
      · rw [hGg b' hbM h0] at hgb; exact max_lt hg0 ((le_max_right _ _).trans_lt hgb)
    · rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b' hbM x hx hx1 hgb]; exact hνb
  top := fun x hx hx1 hgx ν hν => by
    obtain ⟨k, hk⟩ := nbIt_cof hM₀ hx hx1 hgx ν hν
    have hkZ := nbIt_lt p k
    refine ⟨nbIt p k, hkZ, ?_, ?_⟩
    · show (if nbIt p k < veblen 2 (p + 1) then
        (if nbIt p k = 0 then 0 else max M₀.Eg (nbHG p M₀.G (nbIt p k))) else M₀.Eg) < x
      rw [if_pos hkZ]
      split_ifs with h0
      · exact hx.pos
      · exact max_lt hgx ((nbIt_gate hM₀ k).trans_lt (max_lt hgx (lu_one_lt_E hx)))
    · show ν ≤ (if InE x ∧ x < Om1 ∧ nbIt p k < veblen 2 (p + 1) then nbHR p M₀.R M₀.V (nbIt p k) x else nbIt p k)
      rw [if_pos ⟨hx, hx1, hkZ⟩]; exact hk.le
  ex := fun σ ρ c hB hc hg => by
    change (if c < veblen 2 (p + 1) then
      (if c = 0 then 0 else max M₀.Eg (nbHG p M₀.G c)) else M₀.Eg) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show (if InE ρ ∧ ρ < Om1 ∧ c < veblen 2 (p + 1) then nbHR p M₀.R M₀.V c ρ else c) ∈ TB ρ σ ∧
      R2.pi σ ρ (if InE ρ ∧ ρ < Om1 ∧ c < veblen 2 (p + 1) then nbHR p M₀.R M₀.V c ρ else c) =
        (if InE σ ∧ σ < Om1 ∧ c < veblen 2 (p + 1) then nbHR p M₀.R M₀.V c σ else c)
    rw [if_pos ⟨hB.2.1, hρ1, hc⟩, if_pos ⟨hB.1, hσ1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [nbHR_zero hM₀, nbHR_zero hM₀]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hc0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hg0 : M₀.Eg < σ := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    have hGc : M.G c < σ := nb_memG hGg hcM (by rw [hEg]; exact htr σ hσl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
    exact M.ex σ ρ c hB hcM hGc
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d < veblen 2 (p + 1) then
      (if d = 0 then 0 else max M₀.Eg (nbHG p M₀.G d)) else M₀.Eg) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 2 (p + 1) then nbHR p M₀.R M₀.V d ρ else d) ∈ TB ρ σ ∧
      R2.pi σ ρ (ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 2 (p + 1) then nbHR p M₀.R M₀.V d ρ else d)) =
        ω ^ P' * (if InE σ ∧ σ < Om1 ∧ d < veblen 2 (p + 1) then nbHR p M₀.R M₀.V d σ else d)
    rw [if_pos ⟨hB.2.1, hρ1, hd⟩, if_pos ⟨hB.1, hσ1, hd⟩]
    rw [if_pos hd] at hg
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [nbHR_zero hM₀, nbHR_zero hM₀, mul_zero, mul_zero]
      exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hd0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hg0 : M₀.Eg < σ := (le_max_left _ _).trans_lt hg
    have hgd : nbHG p M₀.G d < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hdM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hd
    have hμσ := htr σ hσl hg0 hgd
    have hGd : M.G d < σ := nb_memG hGg hdM (by rw [hEg]; exact hμσ) (Or.inr hgd)
    rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
    refine M.dig σ ρ d hB hdM hGd P P' (fun β hβT hβ => hP β hβT (hβ.trans_le ?_))
    show M.V ρ ≤ veblen 2 (b ρ + 1)
    exact (hVb ρ hB.2.1 hρ1 (by rw [hEg]; exact hμσ.trans hB.2.2.1)).le
  cl := fun c Z hZ hc hg => by
    change (if c < veblen 2 (p + 1) then
      (if c = 0 then 0 else max M₀.Eg (nbHG p M₀.G c)) else M₀.Eg) < Z at hg
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · exact TlCl.zero hZ.1
    rw [if_neg hc0] at hg
    have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
    have hg0 : M₀.Eg < Z := (le_max_left _ _).trans_lt hg
    have hgc : nbHG p M₀.G c < Z := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbTop_pick hM₀ hZX hc
    exact M.cl c Z hZ hcM (nb_memG hGg hcM (by rw [hEg]; exact htr Z hZl hg0 hgc) (Or.inr hgc))
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c < veblen 2 (p + 1) then
      (if c = 0 then 0 else max M₀.Eg (nbHG p M₀.G c)) else M₀.Eg) < Z
    rw [if_pos hc]
    split_ifs with hc0
    · exact hZ.1
    · exact max_lt hgZ (nbHG_gate hM₀ hZ hZ1 hgZ c hc h)

/-- **The top of the stage is the base of the next stage.** -/
theorem nbTop_base : NbBase (nbTopDS hM₀ hZX hZcl hbπ) (p + 1) (fun x => b x + 1) :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

end Top

end Googology.Trans.PoR.InaccPsi.R2.Nb
