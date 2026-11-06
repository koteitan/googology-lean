import Googology.Trans.PoR.InaccPsi.R2.NbCi
import Googology.Trans.PoR.InaccPsi.R2.NaGV

/-!
# Nb: THE UNION AT A CODE-INDEX LIMIT ABOVE A PSEUDO-BASE AND THE CHAIN UP TO `φ(2, p+1)` (`Zm.ZmCu` over any `P`)

`P = φ(2, p)`, `Z_P = φ(2, p+1) < X`, `M₀` the base of the chain (`Nb.NbBase`, `V₀(x) = φ(2, b(x))`).  At a limit
index `λ < Z_P` the union `nbCU` has the base `φ(1, P+λ)`, the base gate `max g₀ (G λ)`, the base reading
`φ(1, V₀(x) + R(λ)(x))`; every field comes from the member at the index `nbMI c`.

* `nb_top_lt_gq` (`φ(2, b(x)+1) < gq(D(x)+1)`), `nbEg`, `nbHR_zero`, `nbMI`, `nbMI_spec`, `nbCu_pick`, `nb_memG`,
  `nbCu_l`;
* `nbCU` (**the union**), `nbGood_lim`, `nbGood_all` (**`NbGood c` for every `c < φ(2, p+1)`**).

No new axiom.  New definitions: `nbEg`, `nbMI`, `nbCU`.
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

/-- **The base gate of the member at the index `μ`.** -/
noncomputable def nbEg (M₀ : ZmDS) (p μ : Ordinal.{0}) : Ordinal.{0} := max M₀.Eg (nbHG p M₀.G μ)

open Classical in
/-- **The member index of a code**: `0` below `P`, else the index of its bracket plus one. -/
noncomputable def nbMI (p c : Ordinal.{0}) : Ordinal.{0} := if c < veblen 2 p then 0 else nbN p c + 1

section Base

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
include hM₀

theorem nbHR_zero (x : Ordinal.{0}) : nbHR p M₀.R M₀.V 0 x = 0 := by rw [nbHR_lt (nbP_pos p), M₀.R0]

theorem nbHG_zero : nbHG p M₀.G 0 = 0 := by rw [nbHG_lt (nbP_pos p), M₀.G0]

theorem nbEg_zero : nbEg M₀ p 0 = M₀.Eg := by unfold nbEg; rw [nbHG_zero hM₀, max_eq_left zero_le]

/-- **`φ(2, b(x)+1)` is below `gq(D(x)+1)`.** -/
theorem nb_top_lt_gq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M₀.Eg < x) :
    veblen 2 (b x + 1) < gq (ywV 1 0 x + 1) x := by
  obtain ⟨hDT1, hD11, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  obtain ⟨-, -, -, hVq⟩ := M₀.V_T x hx hx1 hgx
  rw [hM₀.V_eq x hx hx1 hgx] at hVq
  have hgE := (geq_facts hx hx1 hDT1 hD11).2.2.2.1
  have h2q : (2 : Ordinal.{0}) < gq (ywV 1 0 x + 1) x := by
    have := (natCast_lt_omega0 2).trans (omega0_lt_inE hgE)
    exact_mod_cast this
  have hfix := xk_fix hx hx1 hDT1 hD11 one_le_two h2q
  have hb1 : b x + 1 < gq (ywV 1 0 x + 1) x :=
    (ev_isSuccLimit_of_inE hgE).add_one_lt ((right_le_veblen 2 (b x)).trans_lt hVq)
  calc veblen 2 (b x + 1) < veblen 2 (gq (ywV 1 0 x + 1) x) := (isNormal_veblen 2).strictMono hb1
    _ = _ := hfix

theorem nb_T_of_top {x y : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M₀.Eg < x)
    (hy : y < veblen 2 (b x + 1)) : y ∈ Tset x ∧ y < Om1 := by
  obtain ⟨-, hqT, hq1, -, -⟩ := zm_gq_facts hx hx1
  have h := hy.trans (nb_top_lt_gq hM₀ hx hx1 hgx)
  exact ⟨vz_T_down hx hx1 hqT hq1 h.le, h.trans hq1⟩

theorem nb_V₀_facts {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : M₀.Eg < x) :
    M₀.V x ∈ Tset x ∧ M₀.V x < Om1 ∧ x < M₀.V x ∧ ywV 1 0 x ≤ M₀.V x ∧ M₀.V x < veblen 2 (b x + 1) := by
  obtain ⟨hVT, -, hDV, hVq⟩ := M₀.V_T x hx hx1 hgx
  obtain ⟨-, hxD, -, -⟩ := zmD_facts hx hx1
  have hVt : M₀.V x < veblen 2 (b x + 1) := by
    rw [hM₀.V_eq x hx hx1 hgx]; exact nbP_lt_Z (b x)
  exact ⟨hVT, (nb_T_of_top hM₀ hx hx1 hgx hVt).2, hxD.trans_le hDV, hDV, hVt⟩

end Base

section Union

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
  (hZX : veblen 2 (p + 1) < tlX)
  {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < veblen 2 (p + 1)) (hG : ∀ ν, ν < l → NbGood M₀ p b ν)

include hM₀ hl hlZ in
theorem nbMI_spec {c : Ordinal.{0}} (hc : c < veblen 1 (veblen 2 p + l)) :
    nbMI p c < l ∧ c < veblen 1 (veblen 2 p + nbMI p c) ∧
      (∀ Z, IsSuccLimit Z → M₀.Eg < Z → nbHG p M₀.G c < Z → nbEg M₀ p (nbMI p c) < Z) := by
  unfold nbMI
  split_ifs with hcB
  · refine ⟨hl.bot_lt, by rw [add_zero, nb_fixP]; exact hcB, fun Z hZ hgZ _ => ?_⟩
    rw [nbEg_zero hM₀]; exact hgZ
  · have hcB' : veblen 2 p ≤ c := not_lt.1 hcB
    have hcZ : c < veblen 2 (p + 1) := hc.trans (nb_veb_lt_Z hlZ)
    obtain ⟨b1, b2, b3⟩ := nb_bracket hcB' hcZ
    have hnl : nbN p c < l :=
      (add_lt_add_iff_left _).1 ((isNormal_veblen 1).strictMono.lt_iff_lt.1 (b1.trans_lt hc))
    refine ⟨hl.add_one_lt hnl, b2, fun Z hZ hgZ hg => ?_⟩
    exact max_lt hgZ (nbHG_succ_lt hZ (fun o _ h => M₀.g_succ o Z hZ hgZ h) _ (b3.trans hcZ)
      ((nbHG_idx hcB' hcZ).trans_lt hg))

include hM₀ hl hlZ hG in
/-- **The member for a code below `φ(1, P + λ)`.** -/
theorem nbCu_pick {c : Ordinal.{0}} (hc : c < veblen 1 (veblen 2 p + l)) :
    ∃ M : ZmDS, ∃ μ, μ < l ∧ c < M.E ∧ M.E = veblen 1 (veblen 2 p + μ) ∧ M.Eg = nbEg M₀ p μ ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = veblen 1 (M₀.V x + nbHR p M₀.R M₀.V μ x)) ∧
      (∀ x, InE x → x < Om1 → M.Eg < x → M.V x < veblen 2 (b x + 1)) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = nbHR p M₀.R M₀.V c' x) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (nbHG p M₀.G c')) ∧
      (∀ Z, IsSuccLimit Z → M₀.Eg < Z → nbHG p M₀.G c < Z → nbEg M₀ p μ < Z) := by
  obtain ⟨h1, h2, h3⟩ := nbMI_spec hM₀ hl hlZ hc
  obtain ⟨M, hE, hEg, hV, hVb, hR, hGg⟩ := hG _ h1
  exact ⟨M, nbMI p c, h1, hE ▸ h2, hE, hEg, hV, hVb, hR, hGg, h3⟩

omit hM₀ hZX hl hlZ hG in
/-- A member gate is below `x` when its base gate and the gate of the code are. -/
theorem nb_memG {M : ZmDS} {e c x : Ordinal.{0}} (hGg : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max e (nbHG p M₀.G c'))
    (hc : c < M.E) (he : e < x) (hcx : c = 0 ∨ nbHG p M₀.G c < x) : M.G c < x := by
  rcases eq_or_ne c 0 with rfl | h0
  · rw [M.G0]; exact (zero_le).trans_lt he
  · rw [hGg c hc h0]; rcases hcx with h | h
    · exact absurd h h0
    · exact max_lt he h

include hM₀ hl hlZ hG in
/-- **The reading of the index `λ`**: a limit, `V₀(x) + R(λ) < φ(2, b(x)+1)`, the order below it. -/
theorem nbCu_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgl : nbEg M₀ p l < x) :
    IsSuccLimit (nbHR p M₀.R M₀.V l x) ∧ M₀.V x + nbHR p M₀.R M₀.V l x < veblen 2 (b x + 1) ∧
      ∀ μ, μ < l → nbEg M₀ p μ < x → nbHR p M₀.R M₀.V μ x < nbHR p M₀.R M₀.V l x := by
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
  have hgl' : nbHG p M₀.G l < x := (le_max_right _ _).trans_lt hgl
  obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG (nb_idx_lt hlZ)
  have hμx := htr x hxl hg0 hgl'
  have hMx : M.Eg < x := hEg ▸ hμx
  have hGl : M.G l < x := nb_memG hGg hlM hMx (Or.inr hgl')
  have e := hR l hlM x hx hx1 hGl
  have hζE : InE (veblen 2 (b x + 1)) := zm_fix_E (nb_fixP _)
  have hDζ := (nb_V₀_facts hM₀ hx hx1 hg0).2.2.2.2
  refine ⟨?_, ?_, fun μ' hμ' hgμ' => ?_⟩
  · rw [← e]; exact M.lim l x hx hx1 hl hlM hGl
  · rw [← e]
    exact (inE_indec hζE).add_lt hDζ ((M.lt l x hx hx1 hlM hGl).trans (hVb x hx hx1 hMx))
  · have hμ'M : μ' < M.E := hμ'.trans hlM
    have hgμ'' : nbHG p M₀.G μ' < x := (le_max_right _ _).trans_lt hgμ'
    have hG' : M.G μ' < x := nb_memG hGg hμ'M hMx (Or.inr hgμ'')
    rw [← e, ← hR μ' hμ'M x hx hx1 hG']
    exact M.mono μ' l x hx hx1 hμ' hlM hG' hGl

end Union

section Union2

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
  (hZX : veblen 2 (p + 1) < tlX)
  {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < veblen 2 (p + 1)) (hG : ∀ ν, ν < l → NbGood M₀ p b ν)

include hM₀ hZX hl hlZ hG

open Classical in
/-- **THE UNION AT A CODE-INDEX LIMIT `λ < φ(2, p+1)`.** -/
noncomputable def nbCU : ZmDS where
  E := veblen 1 (veblen 2 p + l)
  Ei := veblen 2 p + l
  V := fun x => veblen 1 (M₀.V x + nbHR p M₀.R M₀.V l x)
  W := fun x => M₀.V x + (nbHR p M₀.R M₀.V l x + 1)
  R := fun c x => if InE x ∧ x < Om1 ∧ c < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V c x else c
  G := fun c => if c < veblen 1 (veblen 2 p + l) then
      (if c = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G c)) else nbEg M₀ p l
  Eg := nbEg M₀ p l
  E_eq := rfl
  BG_le := (M₀.BG_le.trans hM₀.E_eq.le).trans (le_self_add.trans (right_le_veblen _ _))
  E_X := (nb_veb_lt_Z hlZ).trans hZX
  Ei_cl := fun Z hZ hgZ => by
    have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
    have hg0 : M₀.Eg < Z := (le_max_left _ _).trans_lt hgZ
    have hgl : nbHG p M₀.G l < Z := (le_max_right _ _).trans_lt hgZ
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG (nb_idx_lt hlZ)
    have hGl : M.G l < Z := nb_memG hGg hlM (by rw [hEg]; exact htr Z hZl hg0 hgl) (Or.inr hgl)
    exact TlCl.add (nbP_cl hM₀ hZ hg0) (M.cl l Z hZ hlM hGl)
  nfx := fun y h1 h2 hΓ => by
    rcases h2.lt_or_eq with h3 | h3
    · obtain ⟨M, -, -, hyM, -, -, -, -, -, -, -⟩ := nbCu_pick hM₀ hl hlZ hG h3
      exact M.nfx y h1 hyM.le hΓ
    · refine absurd (zm_fix_of_gamma hΓ) ?_
      intro hfix
      rw [h3] at hfix
      have e := (isNormal_veblen 1).strictMono.injective hfix
      have hBl : veblen 2 p < veblen 2 p + l := lt_add_of_pos_right _ hl.bot_lt
      exact nb_noFix hBl ((inE_indec (nbZ_E p)).add_lt (nbP_lt_Z p) hlZ) e.symm.symm
  Eg_le := fun c hc0 => by
    beta_reduce
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  V_T := fun x hx hx1 hgl => by
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    obtain ⟨-, hDt, -⟩ := nbCu_l hM₀ hl hlZ hG hx hx1 hgl
    obtain ⟨-, -, -, hDV₀, -⟩ := nb_V₀_facts hM₀ hx hx1 hg0
    have hVζ : veblen 1 (M₀.V x + nbHR p M₀.R M₀.V l x) < veblen 2 (b x + 1) := by
      rw [← nb_fixP (b x + 1)]; exact (isNormal_veblen 1).strictMono hDt
    have hVq := hVζ.trans (nb_top_lt_gq hM₀ hx hx1 hg0)
    obtain ⟨-, hqT, hq1, -, -⟩ := zm_gq_facts hx hx1
    exact ⟨vz_T_down hx hx1 hqT hq1 hVq.le, zm_veb_E _,
      hDV₀.trans (le_self_add.trans (right_le_veblen _ _)), hVq⟩
  W_T := fun x hx hx1 hgl => by
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    obtain ⟨hlim, hDt, -⟩ := nbCu_l hM₀ hl hlZ hG hx hx1 hgl
    have hζE : InE (veblen 2 (b x + 1)) := zm_fix_E (nb_fixP _)
    have hDt1 : M₀.V x + (nbHR p M₀.R M₀.V l x + 1) < veblen 2 (b x + 1) := by
      rw [← add_assoc]; exact (ev_isSuccLimit_of_inE hζE).add_one_lt hDt
    obtain ⟨hT, h1⟩ := nb_T_of_top hM₀ hx hx1 hg0 hDt1
    refine ⟨hT, h1, ?_⟩
    have hω : ω ≤ nbHR p M₀.R M₀.V l x := omega0_le_of_isSuccLimit hlim
    have e : M₀.V x + 1 + (nbHR p M₀.R M₀.V l x + 1) = M₀.V x + nbHR p M₀.R M₀.V l x + 1 := by
      rw [add_assoc, ← add_assoc 1, one_add_of_omega0_le hω, ← add_assoc]
    obtain ⟨hV₀T, hV₀1, hxV₀, -, -⟩ := nb_V₀_facts hM₀ hx hx1 hg0
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have hna := Na.na_glA hx hx1 le_rfl h1T h11 hV₀T hV₀1 hxV₀ ((lu_one_lt_E hx).trans hxV₀) (b := b x)
      (by rw [one_add_one_eq_two]; exact (hM₀.V_eq x hx hx1 hg0).symm) _ hT h1
      (by rw [one_add_one_eq_two]; exact hDt1)
    show eN (veblen 1 (M₀.V x + nbHR p M₀.R M₀.V l x)) = _
    rw [Go.go_eN_veb, hna, e]
  V_pi := fun σ ρ hB hgl => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hglρ : nbEg M₀ p l < ρ := hgl.trans hB.2.2.1
    have hg0σ : M₀.Eg < σ := (le_max_left _ _).trans_lt hgl
    have hg0ρ : M₀.Eg < ρ := hg0σ.trans hB.2.2.1
    obtain ⟨hlimρ, hDtρ, -⟩ := nbCu_l hM₀ hl hlZ hG hB.2.1 hρ1 hglρ
    obtain ⟨hlimσ, hDtσ, -⟩ := nbCu_l hM₀ hl hlZ hG hB.1 hσ1 hgl
    have rep : ∀ t, InE t → t < Om1 → M₀.Eg < t → IsSuccLimit (nbHR p M₀.R M₀.V l t) →
        M₀.V t + nbHR p M₀.R M₀.V l t < veblen 2 (b t + 1) →
        veblen 1 (M₀.V t + nbHR p M₀.R M₀.V l t) = glA 1 (M₀.V t + nbHR p M₀.R M₀.V l t) t :=
      fun t ht ht1 hg0 hlim hDt => by
        obtain ⟨hV₀T, hV₀1, hxV₀, -, -⟩ := nb_V₀_facts hM₀ ht ht1 hg0
        obtain ⟨h1T, h11⟩ := gl_one_T ht ht1
        obtain ⟨hT, h1⟩ := nb_T_of_top hM₀ ht ht1 hg0 hDt
        rw [Na.na_glA ht ht1 le_rfl h1T h11 hV₀T hV₀1 hxV₀ ((lu_one_lt_E ht).trans hxV₀) (b := b t)
          (by rw [one_add_one_eq_two]; exact (hM₀.V_eq t ht ht1 hg0).symm) _ hT h1
          (by rw [one_add_one_eq_two]; exact hDt), add_assoc, one_add_of_omega0_le (omega0_le_of_isSuccLimit hlim)]
    show veblen 1 (M₀.V ρ + nbHR p M₀.R M₀.V l ρ) ∈ TB ρ σ ∧
      R2.pi σ ρ (veblen 1 (M₀.V ρ + nbHR p M₀.R M₀.V l ρ)) = veblen 1 (M₀.V σ + nbHR p M₀.R M₀.V l σ)
    rw [rep ρ hB.2.1 hρ1 hg0ρ hlimρ hDtρ, rep σ hB.1 hσ1 hg0σ hlimσ hDtσ]
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG (nb_idx_lt hlZ)
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgl' : nbHG p M₀.G l < σ := (le_max_right _ _).trans_lt hgl
    have hGl : M.G l < σ := nb_memG hGg hlM (by rw [hEg]; exact htr σ hσl hg0σ hgl') (Or.inr hgl')
    obtain ⟨e1, e2⟩ := M.ex σ ρ l hB hlM hGl
    rw [hR l hlM ρ hB.2.1 hρ1 (hGl.trans hB.2.2.1)] at e1 e2
    rw [hR l hlM σ hB.1 hσ1 hGl] at e2
    obtain ⟨d1, d2⟩ := M₀.V_pi σ ρ hB hg0σ
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (nb_T_of_top hM₀ hB.2.1 hρ1 hg0ρ hDtρ).2
    rw [o2, s2, d2, e2] at h
    exact h
  W_pi := fun σ ρ hB hgl => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hg0σ : M₀.Eg < σ := (le_max_left _ _).trans_lt hgl
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG (nb_idx_lt hlZ)
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgl' : nbHG p M₀.G l < σ := (le_max_right _ _).trans_lt hgl
    have hGl : M.G l < σ := nb_memG hGg hlM (by rw [hEg]; exact htr σ hσl hg0σ hgl') (Or.inr hgl')
    obtain ⟨e1, e2⟩ := M.ex σ ρ l hB hlM hGl
    rw [hR l hlM ρ hB.2.1 hρ1 (hGl.trans hB.2.2.1)] at e1 e2
    rw [hR l hlM σ hB.1 hσ1 hGl] at e2
    obtain ⟨d1, d2⟩ := M₀.V_pi σ ρ hB hg0σ
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB e1 o1
    obtain ⟨t1, t2⟩ := pi_add hB d1 s1
    exact ⟨t1, by rw [t2, d2, s2, e2, o2]⟩
  R0 := fun x => by
    beta_reduce
    split_ifs
    · exact nbHR_zero hM₀ x
    · rfl
  G0 := by
    beta_reduce
    rw [if_pos (zm_veb_E _).pos, if_pos rfl]
  G1 := by
    have h1 : (1 : Ordinal.{0}) < veblen 1 (veblen 2 p + l) := lu_one_lt_E (zm_veb_E _)
    have h1P : (1 : Ordinal.{0}) < veblen 2 p := lu_one_lt_E (zm_fix_E (nb_fixP p))
    show (if (1 : Ordinal.{0}) < veblen 1 (veblen 2 p + l) then (if (1 : Ordinal.{0}) = 0 then 0 else
      max (nbEg M₀ p l) (nbHG p M₀.G 1)) else nbEg M₀ p l) ≤ max (nbEg M₀ p l) 1
    rw [if_pos h1, if_neg one_ne_zero, nbHG_lt h1P]
    exact max_le (le_max_left _ _) (M₀.G1.trans (max_le_max (le_max_left _ _) le_rfl))
  lt := fun c x hx hx1 hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [nbHR_zero hM₀]; exact (zm_veb_E _).pos
    rw [if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : nbEg M₀ p l < x := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
    have hμx := htr x hxl hg0 hgc
    have hMx : M.Eg < x := by rw [hEg]; exact hμx
    have hGc : M.G c < x := nb_memG hGg hcM hMx (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    refine (M.lt c x hx hx1 hcM hGc).trans_le ?_
    rw [hV x hx hx1 hMx]
    exact (isNormal_veblen 1).strictMono.monotone (add_le_add le_rfl
      ((nbCu_l hM₀ hl hlZ hG hx hx1 hgl).2.2 μ hμl hμx).le)
  pos := fun c x hx hx1 hc0 hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : nbEg M₀ p l < x := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
    have hGc : M.G c < x := nb_memG hGg hcM (by rw [hEg]; exact htr x hxl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.pos c x hx hx1 hc0 hcM hGc
  mono := fun b' c x hx hx1 hbc hc hgb hgc => by
    beta_reduce at hgb hgc ⊢
    have hb := hbc.trans hc
    rw [if_pos ⟨hx, hx1, hb⟩, if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hb] at hgb
    rw [if_pos hc] at hgc
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hbc).ne'
    rw [if_neg hc0] at hgc
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : nbEg M₀ p l < x := (le_max_left _ _).trans_lt hgc
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    have hgcc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hgc
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
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
    beta_reduce
    by_cases h : InE x ∧ x < Om1 ∧ c < veblen 1 (veblen 2 p + l)
    · obtain ⟨hx, hx1, hc⟩ := h
      have hc1 : c + 1 < veblen 1 (veblen 2 p + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos ⟨hx, hx1, hc1⟩, if_pos ⟨hx, hx1, hc⟩]
      exact nbHR_succ (fun o _ x => M₀.succ o x) c (hc.trans (nb_veb_lt_Z hlZ)) x
    · have h' : ¬ (InE x ∧ x < Om1 ∧ c + 1 < veblen 1 (veblen 2 p + l)) := fun ⟨hx, hx1, hc1⟩ =>
        h ⟨hx, hx1, (lt_add_one c).trans hc1⟩
      rw [if_neg h, if_neg h']
  g_le := fun c => by
    beta_reduce
    by_cases hc : c < veblen 1 (veblen 2 p + l)
    · have hc1 : c + 1 < veblen 1 (veblen 2 p + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc, if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      split_ifs with h0
      · exact zero_le
      · exact max_le_max le_rfl (nbHG_le_succ (fun o _ => M₀.g_le o) c (hc.trans (nb_veb_lt_Z hlZ)))
    · have hc1 : ¬ c + 1 < veblen 1 (veblen 2 p + l) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc, if_neg hc1]
  g_succ := fun c Z hZ hgZ hg => by
    beta_reduce at hg ⊢
    have hg0Z : M₀.Eg < Z := (le_max_left _ _).trans_lt hgZ
    by_cases hc : c < veblen 1 (veblen 2 p + l)
    · have hc1 : c + 1 < veblen 1 (veblen 2 p + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc] at hg
      rw [if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      refine max_lt hgZ (nbHG_succ_lt hZ (fun o _ h => M₀.g_succ o Z hZ hg0Z h) c
        (hc.trans (nb_veb_lt_Z hlZ)) ?_)
      rcases eq_or_ne c 0 with h0 | h0
      · rw [h0, nbHG_zero hM₀]; exact hZ.bot_lt
      · rw [if_neg h0] at hg; exact (le_max_right _ _).trans_lt hg
    · have hc1 : ¬ c + 1 < veblen 1 (veblen 2 p + l) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc1]; exact hgZ
  lim := fun c x hx hx1 hlc hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : nbEg M₀ p l < x := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
    have hGc : M.G c < x := nb_memG hGg hcM (by rw [hEg]; exact htr x hxl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hlc hcM hGc
  cof := fun c x hx hx1 hlc hc hg ν hν => by
    beta_reduce at hg hν ⊢
    rw [if_pos ⟨hx, hx1, hc⟩] at hν
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : nbEg M₀ p l < x := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
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
      · rw [hGg b' hbM h0] at hgb; exact max_lt hgl ((le_max_right _ _).trans_lt hgb)
    · rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b' hbM x hx hx1 hgb]; exact hνb
  top := fun x hx hx1 hgl ν hν => by
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hg0 : M₀.Eg < x := (le_max_left _ _).trans_lt hgl
    obtain ⟨hlim, hDt, hmono⟩ := nbCu_l hM₀ hl hlZ hG hx hx1 hgl
    obtain ⟨y, hy, hνy⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hν
    have hmem : ∃ μ', μ' < l ∧ nbEg M₀ p μ' < x ∧
        ν < veblen 1 (M₀.V x + nbHR p M₀.R M₀.V μ' x) := by
      rcases lt_or_ge y (M₀.V x) with hyD | hyD
      · refine ⟨0, hl.bot_lt, by rw [nbEg_zero hM₀]; exact hg0, hνy.trans_le ?_⟩
        rw [nbHR_zero hM₀, add_zero]
        exact (isNormal_veblen 1).strictMono.monotone hyD.le
      · obtain ⟨s, rfl⟩ := exists_add_of_le hyD
        have hst : s < nbHR p M₀.R M₀.V l x := (add_lt_add_iff_left _).1 hy
        have hgl' : nbHG p M₀.G l < x := (le_max_right _ _).trans_lt hgl
        obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG (nb_idx_lt hlZ)
        have hMx : M.Eg < x := by rw [hEg]; exact htr x hxl hg0 hgl'
        have hGl : M.G l < x := nb_memG hGg hlM hMx (Or.inr hgl')
        rw [← hR l hlM x hx hx1 hGl] at hst
        obtain ⟨μ', hμ', hgμ', hsμ'⟩ := M.cof l x hx hx1 hl hlM hGl s hst
        have hμ'M := hμ'.trans hlM
        have hzμ' : nbEg M₀ p μ' < x := by
          rcases eq_or_ne μ' 0 with h0 | h0
          · rw [h0, nbEg_zero hM₀]; exact hg0
          · rw [hGg μ' hμ'M h0] at hgμ'
            exact max_lt hg0 ((le_max_right _ _).trans_lt hgμ')
        rw [hR μ' hμ'M x hx hx1 hgμ'] at hsμ'
        exact ⟨μ', hμ', hzμ', hνy.trans_le ((isNormal_veblen 1).strictMono.monotone
          (add_le_add le_rfl hsμ'))⟩
    obtain ⟨μ', hμ'l, hzμ', hνμ'⟩ := hmem
    obtain ⟨M, hE, hEg, hV, hVb, hR, hGg⟩ := hG μ' hμ'l
    have hMx : M.Eg < x := by rw [hEg]; exact hzμ'
    rw [← hV x hx hx1 hMx] at hνμ'
    obtain ⟨b', hbM, hgb, hνb⟩ := M.top x hx hx1 hMx ν hνμ'
    have hbl : b' < veblen 1 (veblen 2 p + l) :=
      hbM.trans_le (hE ▸ (isNormal_veblen 1).strictMono.monotone (add_le_add le_rfl hμ'l.le))
    refine ⟨b', hbl, ?_, ?_⟩
    · show (if b' < veblen 1 (veblen 2 p + l) then
        (if b' = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G b')) else nbEg M₀ p l) < x
      rw [if_pos hbl]
      split_ifs with h0
      · exact hx.pos
      · rw [hGg b' hbM h0] at hgb; exact max_lt hgl ((le_max_right _ _).trans_lt hgb)
    · show ν ≤ (if InE x ∧ x < Om1 ∧ b' < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V b' x else b')
      rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b' hbM x hx hx1 hgb]; exact hνb
  ex := fun σ ρ c hB hc hg => by
    change (if c < veblen 1 (veblen 2 p + l) then
      (if c = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G c)) else nbEg M₀ p l) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V c ρ else c) ∈ TB ρ σ ∧
      R2.pi σ ρ (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V c ρ else c) =
        (if InE σ ∧ σ < Om1 ∧ c < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V c σ else c)
    rw [if_pos ⟨hB.2.1, hρ1, hc⟩, if_pos ⟨hB.1, hσ1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [nbHR_zero hM₀, nbHR_zero hM₀]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hc0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgl : nbEg M₀ p l < σ := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < σ := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
    have hGc : M.G c < σ := nb_memG hGg hcM (by rw [hEg]; exact htr σ hσl hg0 hgc) (Or.inr hgc)
    rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
    exact M.ex σ ρ c hB hcM hGc
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d < veblen 1 (veblen 2 p + l) then
      (if d = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G d)) else nbEg M₀ p l) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V d ρ else d) ∈ TB ρ σ ∧
      R2.pi σ ρ (ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V d ρ else d)) =
        ω ^ P' * (if InE σ ∧ σ < Om1 ∧ d < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V d σ else d)
    rw [if_pos ⟨hB.2.1, hρ1, hd⟩, if_pos ⟨hB.1, hσ1, hd⟩]
    rw [if_pos hd] at hg
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [nbHR_zero hM₀, nbHR_zero hM₀, mul_zero, mul_zero]
      exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hd0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgl : nbEg M₀ p l < σ := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < σ := (le_max_left _ _).trans_lt hgl
    have hgd : nbHG p M₀.G d < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hdM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hd
    have hμσ := htr σ hσl hg0 hgd
    have hGd : M.G d < σ := nb_memG hGg hdM (by rw [hEg]; exact hμσ) (Or.inr hgd)
    rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
    refine M.dig σ ρ d hB hdM hGd P P' (fun β hβT hβ => hP β hβT (hβ.trans_le ?_))
    show M.V ρ ≤ veblen 1 (M₀.V ρ + nbHR p M₀.R M₀.V l ρ)
    rw [hV ρ hB.2.1 hρ1 (by rw [hEg]; exact hμσ.trans hB.2.2.1)]
    exact (isNormal_veblen 1).strictMono.monotone (add_le_add le_rfl
      ((nbCu_l hM₀ hl hlZ hG hB.2.1 hρ1 (hgl.trans hB.2.2.1)).2.2 μ hμl (hμσ.trans hB.2.2.1)).le)
  cl := fun c Z hZ hc hg => by
    change (if c < veblen 1 (veblen 2 p + l) then
      (if c = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G c)) else nbEg M₀ p l) < Z at hg
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · exact TlCl.zero hZ.1
    rw [if_neg hc0] at hg
    have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
    have hgl : nbEg M₀ p l < Z := (le_max_left _ _).trans_lt hg
    have hg0 : M₀.Eg < Z := (le_max_left _ _).trans_lt hgl
    have hgc : nbHG p M₀.G c < Z := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := nbCu_pick hM₀ hl hlZ hG hc
    exact M.cl c Z hZ hcM (nb_memG hGg hcM (by rw [hEg]; exact htr Z hZl hg0 hgc) (Or.inr hgc))
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c < veblen 1 (veblen 2 p + l) then
      (if c = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G c)) else nbEg M₀ p l) < Z
    rw [if_pos hc]
    split_ifs with hc0
    · exact hZ.1
    · exact max_lt hgZ (nbHG_gate hM₀ hZ hZ1 ((le_max_left _ _).trans_lt hgZ) c
        (hc.trans (nb_veb_lt_Z hlZ)) h)

open Classical in
theorem nbGood_lim : NbGood M₀ p b l := by
  refine ⟨nbCU hM₀ hZX hl hlZ hG, rfl, rfl, fun _ _ _ _ => rfl, fun x hx hx1 hgl => ?_,
    fun c hc x hx hx1 _ => ?_, fun c hc hc0 => ?_⟩
  · obtain ⟨-, hDt, -⟩ := nbCu_l hM₀ hl hlZ hG hx hx1 hgl
    show veblen 1 (M₀.V x + nbHR p M₀.R M₀.V l x) < _
    rw [← nb_fixP (b x + 1)]; exact (isNormal_veblen 1).strictMono hDt
  · have hc' : c < veblen 1 (veblen 2 p + l) := hc
    show (if InE x ∧ x < Om1 ∧ c < veblen 1 (veblen 2 p + l) then nbHR p M₀.R M₀.V c x else c) = _
    rw [if_pos ⟨hx, hx1, hc'⟩]
  · have hc' : c < veblen 1 (veblen 2 p + l) := hc
    show (if c < veblen 1 (veblen 2 p + l) then
      (if c = 0 then 0 else max (nbEg M₀ p l) (nbHG p M₀.G c)) else nbEg M₀ p l) = _
    rw [if_pos hc', if_neg hc0]
    rfl

end Union2

/-- **`NbGood c` FOR EVERY CODE INDEX `c < φ(2, p+1)`, ONE TRANSFINITE INDUCTION.** -/
theorem nbGood_all {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
    (hZX : veblen 2 (p + 1) < tlX) : ∀ c, c < veblen 2 (p + 1) → NbGood M₀ p b c := by
  intro c
  induction c using Ordinal.limitRecOn with
  | zero => exact fun _ => nbGood_zero hM₀
  | add_one n ih => exact fun h => nbGood_succ hM₀ h (ih ((lt_add_one n).trans h))
  | limit l hl ih => exact fun h => nbGood_lim hM₀ hZX hl h (fun ν hν => ih ν hν (hν.trans h))

end Googology.Trans.PoR.InaccPsi.R2.Nb
