import Googology.Trans.PoR.InaccPsi.R2.ZmCi

/-!
# ZmCu: THE UNION AT A CODE-INDEX LIMIT AND THE CHAIN UP TO `ζ_{B_Γ+1}` — `ZbDirect S ζ_{B_Γ+1}`

At a limit code index `λ < ζ_{B_Γ+1}` the union `zmCU` has the base `φ(1, B_Γ+λ)`, the base gate `G(λ)`, the base
reading `φ(1, D(x) + R(λ)(x))`; every field comes from the member at the index `zmMI c` (`0` below `B_Γ`, else the
index of the bracket of `c` plus one), whose gate is below every limit above the gate of `c`.  One transfinite
induction over the code indices gives `ZmGood2 c` for every `c < ζ_{B_Γ+1}`.

* `zmMI`, `zmMI_spec`, `zmCU` (**the union**), `zmGood2_lim`, `zmGood2_all` (**every code index below
  `ζ_{B_Γ+1}`**);
* `zm_Z_nfp`, `zmIt`, `zmIt_cof`, `zmIt_gate`, `zmDirectZ` (**`ZbDirect S ζ_{B_Γ+1}`, UNCONDITIONAL**), `zmUVZ`.

No new axiom.  New definitions: `zmMI`, `zmCU`, `zmIt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Lu

open Classical in
/-- **The member index of a code**: `0` below `B_Γ`, else the index of its bracket plus one. -/
noncomputable def zmMI (c : Ordinal.{0}) : Ordinal.{0} := if c < tfBG then 0 else zmN c + 1

section Union2

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < zmZ) (hG : ∀ ν, ν < l → ZmGood2 ν)

include hl hlZ in
theorem zmMI_spec {c : Ordinal.{0}} (hc : c < veblen 1 (tfBG + l)) :
    zmMI c < l ∧ c < veblen 1 (tfBG + zmMI c) ∧ (∀ Z, IsSuccLimit Z → zmHG c < Z → zmHG (zmMI c) < Z) := by
  unfold zmMI
  split_ifs with hcB
  · refine ⟨hl.bot_lt, by rw [add_zero, zm_BG_fix]; exact hcB, fun Z hZ _ => ?_⟩
    rw [zmHG_zero]; exact hZ.bot_lt
  · have hcB' : tfBG ≤ c := not_lt.1 hcB
    have hcZ : c < zmZ := hc.trans (zm_veb_lt_Z hlZ)
    obtain ⟨b1, b2, b3⟩ := zm_bracket hcB' hcZ
    have hnl : zmN c < l :=
      (add_lt_add_iff_left _).1 ((isNormal_veblen 1).strictMono.lt_iff_lt.1 (b1.trans_lt hc))
    refine ⟨hl.add_one_lt hnl, b2, fun Z hZ hg => ?_⟩
    exact zmHG_succ_lt _ (b3.trans hcZ) Z hZ ((zmHG_idx hcB' hcZ).trans_lt hg)

include hl hlZ hG in
/-- **The member for a code below `φ(1, B_Γ + λ)`.** -/
theorem zmCu_pick {c : Ordinal.{0}} (hc : c < veblen 1 (tfBG + l)) :
    ∃ M : ZmDS, ∃ μ, μ < l ∧ c < M.E ∧ M.E = veblen 1 (tfBG + μ) ∧ M.Eg = zmHG μ ∧
      (∀ x, InE x → x < Om1 → zmHG μ < x → M.V x = veblen 1 (ywV 1 0 x + zmHR μ x)) ∧
      (∀ x, InE x → x < Om1 → zmHG μ < x → M.V x < veblen 2 (ywV 1 0 x + 1)) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = zmHR c' x) ∧
      (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max (zmHG μ) (zmHG c')) ∧
      (∀ Z, IsSuccLimit Z → zmHG c < Z → zmHG μ < Z) := by
  obtain ⟨h1, h2, h3⟩ := zmMI_spec hl hlZ hc
  obtain ⟨M, hE, hEg, hV, hVb, hR, hGg⟩ := hG _ h1
  exact ⟨M, zmMI c, h1, hE ▸ h2, hE, hEg, hV, hVb, hR, hGg, h3⟩

omit hl hlZ hG in
/-- A member gate is below `x` when the gates of the member index and of the code are. -/
theorem zm_memG {M : ZmDS} {μ b x : Ordinal.{0}} (hGg : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max (zmHG μ) (zmHG c'))
    (hb : b < M.E) (hμ : zmHG μ < x) (hbx : b = 0 ∨ zmHG b < x) : M.G b < x := by
  rcases eq_or_ne b 0 with rfl | h0
  · rw [M.G0]; exact (zero_le).trans_lt hμ
  · rw [hGg b hb h0]; rcases hbx with h | h
    · exact absurd h h0
    · exact max_lt hμ h

include hl hlZ hG in
/-- **The reading of the index `λ`**: a limit below `ζ_{D(x)+1} − D(x)`, Lemma EXACT, the order below it. -/
theorem zmCu_l {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgl : zmHG l < x) :
    IsSuccLimit (zmHR l x) ∧ ywV 1 0 x + zmHR l x < veblen 2 (ywV 1 0 x + 1) ∧
      ∀ μ, μ < l → zmHG μ < x → zmHR μ x < zmHR l x := by
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG (zm_idx_lt hlZ)
  have hμx := htr x hxl hgl
  have hGl : M.G l < x := zm_memG hGg hlM hμx (Or.inr hgl)
  have e := hR l hlM x hx hx1 hGl
  have hζE : InE (veblen 2 (ywV 1 0 x + 1)) := zm_fix_E (zm_veb2_fix _)
  have hDζ : ywV 1 0 x < veblen 2 (ywV 1 0 x + 1) := by
    conv_lhs => rw [← zmD_fix2 hx hx1]
    exact (isNormal_veblen 2).strictMono (lt_add_one _)
  refine ⟨?_, ?_, fun μ' hμ' hgμ' => ?_⟩
  · rw [← e]; exact M.lim l x hx hx1 hl hlM hGl
  · rw [← e]
    exact (inE_indec hζE).add_lt hDζ ((M.lt l x hx hx1 hlM hGl).trans (hVb x hx hx1 hμx))
  · have hμ'M : μ' < M.E := hμ'.trans hlM
    have hG' : M.G μ' < x := zm_memG hGg hμ'M hμx (Or.inr hgμ')
    rw [← e, ← hR μ' hμ'M x hx hx1 hG']
    exact M.mono μ' l x hx hx1 hμ' hlM hG' hGl

open Classical in
/-- **THE UNION AT A CODE-INDEX LIMIT `λ < ζ_{B_Γ+1}`.** -/
noncomputable def zmCU : ZmDS where
  E := veblen 1 (tfBG + l)
  Ei := tfBG + l
  V := fun x => veblen 1 (ywV 1 0 x + zmHR l x)
  W := fun x => ywV 1 0 x + (zmHR l x + 1)
  R := fun c x => if InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l) then zmHR c x else c
  G := fun c => if c < veblen 1 (tfBG + l) then (if c = 0 then 0 else max (zmHG l) (zmHG c)) else zmHG l
  Eg := zmHG l
  E_eq := rfl
  BG_le := le_self_add.trans (right_le_veblen _ _)
  E_X := (zm_veb_lt_Z hlZ).trans zmZ_lt_X
  Ei_cl := fun Z hZ hgZ => by
    have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG (zm_idx_lt hlZ)
    have hGl : M.G l < Z := zm_memG hGg hlM (htr Z hZl hgZ) (Or.inr hgZ)
    exact TlCl.add (zbBG_tl hZ.1) (M.cl l Z hZ hlM hGl)
  nfx := fun y h1 h2 hΓ => by
    rcases h2.lt_or_eq with h3 | h3
    · obtain ⟨M, -, -, hyM, -, -, -, -, -, -, -⟩ := zmCu_pick hl hlZ hG h3
      exact M.nfx y h1 hyM.le hΓ
    · refine absurd (zm_fix_of_gamma hΓ) ?_
      intro hfix
      rw [h3] at hfix
      have e := (isNormal_veblen 1).strictMono.injective hfix
      have hBl : tfBG < tfBG + l := lt_add_of_pos_right _ hl.bot_lt
      exact zm_noFix hBl ((inE_indec zmZ_E).add_lt zm_BG_lt_Z hlZ) e.symm.symm
  Eg_le := fun c hc0 => by
    beta_reduce
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  V_T := fun x hx hx1 hgl => by
    obtain ⟨-, hDt, -⟩ := zmCu_l hl hlZ hG hx hx1 hgl
    obtain ⟨-, hqT, hq1, hqfix, -⟩ := zm_gq_facts hx hx1
    have hVζ : veblen 1 (ywV 1 0 x + zmHR l x) < veblen 2 (ywV 1 0 x + 1) := by
      rw [← zm_veb2_fix (ywV 1 0 x + 1)]; exact (isNormal_veblen 1).strictMono hDt
    have hVq := hVζ.trans (zm_zeta_lt_gq hx hx1)
    refine ⟨vz_T_down hx hx1 hqT hq1 hVq.le, zm_veb_E _, ?_, hVq⟩
    calc ywV 1 0 x = veblen 1 (ywV 1 0 x) := (zmD_fix hx hx1).symm
      _ ≤ veblen 1 (ywV 1 0 x + zmHR l x) := (isNormal_veblen 1).strictMono.monotone le_self_add
  W_T := fun x hx hx1 hgl => by
    obtain ⟨hlim, hDt, -⟩ := zmCu_l hl hlZ hG hx hx1 hgl
    have hζE : InE (veblen 2 (ywV 1 0 x + 1)) := zm_fix_E (zm_veb2_fix _)
    have hDt1 : ywV 1 0 x + (zmHR l x + 1) < veblen 2 (ywV 1 0 x + 1) := by
      rw [← add_assoc]; exact (ev_isSuccLimit_of_inE hζE).add_one_lt hDt
    obtain ⟨hT, h1⟩ := zmDZ_T hx hx1 hDt1
    refine ⟨hT, h1, ?_⟩
    have hω : ω ≤ zmHR l x := omega0_le_of_isSuccLimit hlim
    have e : ywV 1 0 x + 1 + (zmHR l x + 1) = ywV 1 0 x + zmHR l x + 1 := by
      rw [add_assoc, ← add_assoc 1, one_add_of_omega0_le hω, ← add_assoc]
    show eN (veblen 1 (ywV 1 0 x + zmHR l x)) = _
    rw [Go.go_eN_veb, zm_glA_veb2 hx hx1 _ hDt1, e]
  V_pi := fun σ ρ hB hgl => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hglρ : zmHG l < ρ := hgl.trans hB.2.2.1
    obtain ⟨hlimρ, hDtρ, -⟩ := zmCu_l hl hlZ hG hB.2.1 hρ1 hglρ
    obtain ⟨hlimσ, hDtσ, -⟩ := zmCu_l hl hlZ hG hB.1 hσ1 hgl
    have rep : ∀ t, InE t → t < Om1 → IsSuccLimit (zmHR l t) →
        ywV 1 0 t + zmHR l t < veblen 2 (ywV 1 0 t + 1) →
        veblen 1 (ywV 1 0 t + zmHR l t) = glA 1 (ywV 1 0 t + zmHR l t) t := fun t ht ht1 hlim hDt => by
      rw [zm_glA_veb2 ht ht1 _ hDt, add_assoc, one_add_of_omega0_le (omega0_le_of_isSuccLimit hlim)]
    show veblen 1 (ywV 1 0 ρ + zmHR l ρ) ∈ TB ρ σ ∧
      R2.pi σ ρ (veblen 1 (ywV 1 0 ρ + zmHR l ρ)) = veblen 1 (ywV 1 0 σ + zmHR l σ)
    rw [rep ρ hB.2.1 hρ1 hlimρ hDtρ, rep σ hB.1 hσ1 hlimσ hDtσ]
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG (zm_idx_lt hlZ)
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hGl : M.G l < σ := zm_memG hGg hlM (htr σ hσl hgl) (Or.inr hgl)
    obtain ⟨e1, e2⟩ := M.ex σ ρ l hB hlM hGl
    rw [hR l hlM ρ hB.2.1 hρ1 (hGl.trans hB.2.2.1)] at e1 e2
    rw [hR l hlM σ hB.1 hσ1 hGl] at e2
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (zmDZ_T hB.2.1 hρ1 hDtρ).2
    rw [o2, s2, d2, e2] at h
    exact h
  W_pi := fun σ ρ hB hgl => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG (zm_idx_lt hlZ)
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hGl : M.G l < σ := zm_memG hGg hlM (htr σ hσl hgl) (Or.inr hgl)
    obtain ⟨e1, e2⟩ := M.ex σ ρ l hB hlM hGl
    rw [hR l hlM ρ hB.2.1 hρ1 (hGl.trans hB.2.2.1)] at e1 e2
    rw [hR l hlM σ hB.1 hσ1 hGl] at e2
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB e1 o1
    obtain ⟨t1, t2⟩ := pi_add hB d1 s1
    exact ⟨t1, by rw [t2, d2, s2, e2, o2]⟩
  R0 := fun x => by
    beta_reduce
    split_ifs
    · exact zmHR_zero x
    · rfl
  G0 := by
    beta_reduce
    rw [if_pos (zm_veb_E _).pos, if_pos rfl]
  G1 := by
    have h1 : (1 : Ordinal.{0}) < veblen 1 (tfBG + l) := lu_one_lt_E (zm_veb_E _)
    show (if (1 : Ordinal.{0}) < veblen 1 (tfBG + l) then (if (1 : Ordinal.{0}) = 0 then 0 else
      max (zmHG l) (zmHG 1)) else zmHG l) ≤ max (zmHG l) 1
    rw [if_pos h1, if_neg one_ne_zero, zmHG_lt (gg_one_lt_of_SC tfBG_SC)]
    have h2 : yrG (1 : Ordinal.{0}) ≤ 1 := by
      have h1 : yrG ((1 : ℕ) : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) := by
        rw [yrG_low (Yh.yh_nat_lt_G 1), glG_nat]
      simpa using h1.le
    exact max_le_max le_rfl h2
  lt := fun c x hx hx1 hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zmHR_zero]; exact (zm_veb_E _).pos
    rw [if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : zmHG l < x := (le_max_left _ _).trans_lt hg
    have hgc : zmHG c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hμx := htr x hxl hgc
    have hGc : M.G c < x := zm_memG hGg hcM hμx (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    refine (M.lt c x hx hx1 hcM hGc).trans_le ?_
    rw [hV x hx hx1 hμx]
    exact (isNormal_veblen 1).strictMono.monotone (add_le_add_right
      ((zmCu_l hl hlZ hG hx hx1 hgl).2.2 μ hμl hμx).le _)
  pos := fun c x hx hx1 hc0 hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg hc0] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgc : zmHG c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hGc : M.G c < x := zm_memG hGg hcM (htr x hxl hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.pos c x hx hx1 hc0 hcM hGc
  mono := fun b c x hx hx1 hbc hc hgb hgc => by
    beta_reduce at hgb hgc ⊢
    have hb := hbc.trans hc
    rw [if_pos ⟨hx, hx1, hb⟩, if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hb] at hgb
    rw [if_pos hc] at hgc
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hbc).ne'
    rw [if_neg hc0] at hgc
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgcc : zmHG c < x := (le_max_right _ _).trans_lt hgc
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hμx := htr x hxl hgcc
    have hbM := hbc.trans hcM
    have hGc : M.G c < x := zm_memG hGg hcM hμx (Or.inr hgcc)
    have hGb : M.G b < x := by
      refine zm_memG hGg hbM hμx ?_
      rcases eq_or_ne b 0 with h0 | h0
      · exact Or.inl h0
      · rw [if_neg h0] at hgb; exact Or.inr ((le_max_right _ _).trans_lt hgb)
    rw [← hR c hcM x hx hx1 hGc, ← hR b hbM x hx hx1 hGb]
    exact M.mono b c x hx hx1 hbc hcM hGb hGc
  succ := fun c x => by
    beta_reduce
    by_cases h : InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l)
    · obtain ⟨hx, hx1, hc⟩ := h
      have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos ⟨hx, hx1, hc1⟩, if_pos ⟨hx, hx1, hc⟩]
      exact zmHR_succ c (hc.trans (zm_veb_lt_Z hlZ)) x
    · have h' : ¬ (InE x ∧ x < Om1 ∧ c + 1 < veblen 1 (tfBG + l)) := fun ⟨hx, hx1, hc1⟩ =>
        h ⟨hx, hx1, (lt_add_one c).trans hc1⟩
      rw [if_neg h, if_neg h']
  g_le := fun c => by
    beta_reduce
    by_cases hc : c < veblen 1 (tfBG + l)
    · have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc, if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      split_ifs with h0
      · exact zero_le
      · exact max_le_max le_rfl (zmHG_le_succ c (hc.trans (zm_veb_lt_Z hlZ)))
    · have hc1 : ¬ c + 1 < veblen 1 (tfBG + l) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc, if_neg hc1]
  g_succ := fun c Z hZ hgZ hg => by
    beta_reduce at hg ⊢
    by_cases hc : c < veblen 1 (tfBG + l)
    · have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc] at hg
      rw [if_pos hc1, if_neg (lt_of_le_of_lt zero_le (lt_add_one c)).ne']
      refine max_lt hgZ (zmHG_succ_lt c (hc.trans (zm_veb_lt_Z hlZ)) Z hZ ?_)
      rcases eq_or_ne c 0 with h0 | h0
      · rw [h0, zmHG_zero]; exact hZ.bot_lt
      · rw [if_neg h0] at hg; exact (le_max_right _ _).trans_lt hg
    · have hc1 : ¬ c + 1 < veblen 1 (tfBG + l) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc1]; exact hgZ
  lim := fun c x hx hx1 hlc hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos ⟨hx, hx1, hc⟩]
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgc : zmHG c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hGc : M.G c < x := zm_memG hGg hcM (htr x hxl hgc) (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc]
    exact M.lim c x hx hx1 hlc hcM hGc
  cof := fun c x hx hx1 hlc hc hg ν hν => by
    beta_reduce at hg hν ⊢
    rw [if_pos ⟨hx, hx1, hc⟩] at hν
    rw [if_pos hc, if_neg (show c ≠ 0 from hlc.bot_lt.ne')] at hg
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hgl : zmHG l < x := (le_max_left _ _).trans_lt hg
    have hgc : zmHG c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hμx := htr x hxl hgc
    have hGc : M.G c < x := zm_memG hGg hcM hμx (Or.inr hgc)
    rw [← hR c hcM x hx hx1 hGc] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof c x hx hx1 hlc hcM hGc ν hν
    have hbM := hb.trans hcM
    have hbl := hb.trans hc
    refine ⟨b, hb, ?_, ?_⟩
    · rw [if_pos hbl]
      split_ifs with h0
      · exact hx.pos
      · rw [hGg b hbM h0] at hgb; exact max_lt hgl ((le_max_right _ _).trans_lt hgb)
    · rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b hbM x hx hx1 hgb]; exact hνb
  top := fun x hx hx1 hgl ν hν => by
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    obtain ⟨hlim, hDt, hmono⟩ := zmCu_l hl hlZ hG hx hx1 hgl
    obtain ⟨y, hy, hνy⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hν
    -- a member below the base reading
    have hmem : ∃ μ', μ' < l ∧ zmHG μ' < x ∧ ν < veblen 1 (ywV 1 0 x + zmHR μ' x) := by
      rcases lt_or_ge y (ywV 1 0 x) with hyD | hyD
      · refine ⟨0, hl.bot_lt, by rw [zmHG_zero]; exact hx.pos, hνy.trans_le ?_⟩
        rw [zmHR_zero, add_zero]
        exact (isNormal_veblen 1).strictMono.monotone hyD.le
      · obtain ⟨s, rfl⟩ := exists_add_of_le hyD
        have hst : s < zmHR l x := (add_lt_add_iff_left _).1 hy
        obtain ⟨M, μ, hμl, hlM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG (zm_idx_lt hlZ)
        have hGl : M.G l < x := zm_memG hGg hlM (htr x hxl hgl) (Or.inr hgl)
        rw [← hR l hlM x hx hx1 hGl] at hst
        obtain ⟨μ', hμ', hgμ', hsμ'⟩ := M.cof l x hx hx1 hl hlM hGl s hst
        have hμ'M := hμ'.trans hlM
        have hzμ' : zmHG μ' < x := by
          rcases eq_or_ne μ' 0 with h0 | h0
          · rw [h0, zmHG_zero]; exact hx.pos
          · rw [hGg μ' hμ'M h0] at hgμ'; exact (le_max_right _ _).trans_lt hgμ'
        rw [hR μ' hμ'M x hx hx1 hgμ'] at hsμ'
        exact ⟨μ', hμ', hzμ', hνy.trans_le ((isNormal_veblen 1).strictMono.monotone
          (add_le_add_right hsμ' _))⟩
    obtain ⟨μ', hμ'l, hzμ', hνμ'⟩ := hmem
    obtain ⟨M, hE, hEg, hV, hVb, hR, hGg⟩ := hG μ' hμ'l
    rw [← hV x hx hx1 hzμ'] at hνμ'
    obtain ⟨b, hbM, hgb, hνb⟩ := M.top x hx hx1 (by rw [hEg]; exact hzμ') ν hνμ'
    have hbl : b < veblen 1 (tfBG + l) :=
      hbM.trans_le (hE ▸ (isNormal_veblen 1).strictMono.monotone (add_le_add_right hμ'l.le _))
    refine ⟨b, hbl, ?_, ?_⟩
    · show (if b < veblen 1 (tfBG + l) then (if b = 0 then 0 else max (zmHG l) (zmHG b)) else zmHG l) < x
      rw [if_pos hbl]
      split_ifs with h0
      · exact hx.pos
      · rw [hGg b hbM h0] at hgb; exact max_lt hgl ((le_max_right _ _).trans_lt hgb)
    · show ν ≤ (if InE x ∧ x < Om1 ∧ b < veblen 1 (tfBG + l) then zmHR b x else b)
      rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b hbM x hx hx1 hgb]; exact hνb
  ex := fun σ ρ c hB hc hg => by
    change (if c < veblen 1 (tfBG + l) then (if c = 0 then 0 else max (zmHG l) (zmHG c)) else zmHG l) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (tfBG + l) then zmHR c ρ else c) ∈ TB ρ σ ∧
      R2.pi σ ρ (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (tfBG + l) then zmHR c ρ else c) =
        (if InE σ ∧ σ < Om1 ∧ c < veblen 1 (tfBG + l) then zmHR c σ else c)
    rw [if_pos ⟨hB.2.1, hρ1, hc⟩, if_pos ⟨hB.1, hσ1, hc⟩]
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zmHR_zero, zmHR_zero]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hc0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgc : zmHG c < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    have hGc : M.G c < σ := zm_memG hGg hcM (htr σ hσl hgc) (Or.inr hgc)
    rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
    exact M.ex σ ρ c hB hcM hGc
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d < veblen 1 (tfBG + l) then (if d = 0 then 0 else max (zmHG l) (zmHG d)) else zmHG l) < σ at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (tfBG + l) then zmHR d ρ else d) ∈ TB ρ σ ∧
      R2.pi σ ρ (ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (tfBG + l) then zmHR d ρ else d)) =
        ω ^ P' * (if InE σ ∧ σ < Om1 ∧ d < veblen 1 (tfBG + l) then zmHR d σ else d)
    rw [if_pos ⟨hB.2.1, hρ1, hd⟩, if_pos ⟨hB.1, hσ1, hd⟩]
    rw [if_pos hd] at hg
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [zmHR_zero, zmHR_zero, mul_zero, mul_zero]; exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
    rw [if_neg hd0] at hg
    have hσl : IsSuccLimit σ := ev_isSuccLimit_of_inE hB.1
    have hgl : zmHG l < σ := (le_max_left _ _).trans_lt hg
    have hgd : zmHG d < σ := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hdM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hd
    have hμσ := htr σ hσl hgd
    have hGd : M.G d < σ := zm_memG hGg hdM hμσ (Or.inr hgd)
    rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
    refine M.dig σ ρ d hB hdM hGd P P' (fun β hβT hβ => hP β hβT (hβ.trans_le ?_))
    show M.V ρ ≤ veblen 1 (ywV 1 0 ρ + zmHR l ρ)
    rw [hV ρ hB.2.1 hρ1 (hμσ.trans hB.2.2.1)]
    exact (isNormal_veblen 1).strictMono.monotone (add_le_add_right
      ((zmCu_l hl hlZ hG hB.2.1 hρ1 (hgl.trans hB.2.2.1)).2.2 μ hμl (hμσ.trans hB.2.2.1)).le _)
  cl := fun c Z hZ hc hg => by
    change (if c < veblen 1 (tfBG + l) then (if c = 0 then 0 else max (zmHG l) (zmHG c)) else zmHG l) < Z at hg
    rw [if_pos hc] at hg
    rcases eq_or_ne c 0 with rfl | hc0
    · exact TlCl.zero hZ.1
    rw [if_neg hc0] at hg
    have hZl : IsSuccLimit Z := ev_isSuccLimit_of_inE (gg_SC_eps hZ)
    have hgc : zmHG c < Z := (le_max_right _ _).trans_lt hg
    obtain ⟨M, μ, hμl, hcM, hE, hEg, hV, hVb, hR, hGg, htr⟩ := zmCu_pick hl hlZ hG hc
    exact M.cl c Z hZ hcM (zm_memG hGg hcM (htr Z hZl hgc) (Or.inr hgc))
  gate := fun c Z hZ hZ1 hgZ hc h => by
    show (if c < veblen 1 (tfBG + l) then (if c = 0 then 0 else max (zmHG l) (zmHG c)) else zmHG l) < Z
    rw [if_pos hc]
    split_ifs with hc0
    · exact hZ.1
    · exact max_lt hgZ (zmHG_gate hZ hZ1 c (hc.trans (zm_veb_lt_Z hlZ)) h)

include hl hlZ hG in
open Classical in
theorem zmGood2_lim : ZmGood2 l := by
  refine ⟨zmCU hl hlZ hG, rfl, rfl, fun _ _ _ _ => rfl, fun x hx hx1 hgl => ?_, fun c hc x hx hx1 _ => ?_,
    fun c hc hc0 => ?_⟩
  · obtain ⟨-, hDt, -⟩ := zmCu_l hl hlZ hG hx hx1 hgl
    show veblen 1 (ywV 1 0 x + zmHR l x) < _
    rw [← zm_veb2_fix (ywV 1 0 x + 1)]; exact (isNormal_veblen 1).strictMono hDt
  · have hc' : c < veblen 1 (tfBG + l) := hc
    show (if InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l) then zmHR c x else c) = _
    rw [if_pos ⟨hx, hx1, hc'⟩]
  · have hc' : c < veblen 1 (tfBG + l) := hc
    show (if c < veblen 1 (tfBG + l) then (if c = 0 then 0 else max (zmHG l) (zmHG c)) else zmHG l) = _
    rw [if_pos hc', if_neg hc0]

end Union2

/-- **`ZmGood2 c` FOR EVERY CODE INDEX `c < ζ_{B_Γ+1}`, ONE TRANSFINITE INDUCTION.** -/
theorem zmGood2_all : ∀ c, c < zmZ → ZmGood2 c := by
  intro c
  induction c using Ordinal.limitRecOn with
  | zero => exact fun _ => zmGood2_zero
  | add_one n ih => exact fun h => zmGood2_succ h (ih ((lt_add_one n).trans h))
  | limit l hl ih => exact fun h => zmGood2_lim hl h (fun ν hν => ih ν hν (hν.trans h))

end Googology.Trans.PoR.InaccPsi.R2.Zm
