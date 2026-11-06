import Googology.Trans.PoR.InaccPsi.R2.ZmGl

/-!
# ZmLm: THE CHAIN OVER EVERY CONSTANT INDEX `ν < ε₀` — ONE TRANSFINITE INDUCTION, `ZbDirect S ε_{B_Γ+ε₀}`

`ZmGood ν`: a digit system at the base `φ(1, B_Γ + ν)` with base reading `φ(1, D(x) + ν)` whose readings and gates
are the global ones (`Zm.zmGR`, `Zm.zmGG`).  `ZmGood 0` is `Zm.zmYr`; `ZmGood ν ⇒ ZmGood (ν+1)` is the generic step
`ZmDS.step`; at a limit `λ < ε₀` the union `zmU` (readings and gates global, every field from a member below `λ`).

* `zmGood_zero`, `zmGood_succ` (**the step**), `zm_lim_idx`, `zmU` (**the union at a limit index**), `zmGood_lim`,
  `zmGood_all` (**`ZmGood ν` for every `ν < ε₀`, one transfinite induction**);
* `zmDirectE0` (**`ZbDirect S ε_{B_Γ+ε₀}`, UNCONDITIONAL**), `zmUVE0` (**UPPER ∧ LOWER ∧ CapV at every range restart
  below `ι(Γ(B)·ω)`, every `B < ε_{B_Γ+ε₀}`, UNCONDITIONAL**).

No new axiom.  New definitions: `ZmGood`, `zmU`.
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

/-- **The digit system of the chain at the index `ν`**: base `φ(1, B_Γ+ν)`, base reading `φ(1, D(x)+ν)`, the global
readings and gates. -/
def ZmGood (ν : Ordinal.{0}) : Prop :=
  ∃ M : ZmDS, M.E = veblen 1 (tfBG + ν) ∧ (∀ x, InE x → x < Om1 → M.V x = zmV ν x) ∧
    (∀ c, c < M.E → ∀ x, InE x → x < Om1 → M.R c x = zmGR c x) ∧ (∀ c, c < M.E → M.G c = zmGG c) ∧ M.Eg = 0

theorem zmGood_zero : ZmGood 0 := by
  refine ⟨zmYr, ?_, fun x hx hx1 => ?_, fun c hc x _ _ => (zmGR_lt hc x).symm, fun c hc => (zmGG_lt hc).symm, rfl⟩
  · show tfBG = _; rw [add_zero, zm_BG_fix]
  · show ywV 1 0 x = _; unfold zmV; rw [add_zero, zmD_fix hx hx1]

/-- **The step**: `ZmGood ν ⇒ ZmGood (ν+1)`. -/
theorem zmGood_succ {ν : Ordinal.{0}} (h : ZmGood ν) : ZmGood (ν + 1) := by
  obtain ⟨M, hE, hV, hR, hG, hEg⟩ := h
  have hEN : eN M.E = veblen 1 (tfBG + (ν + 1)) := by rw [hE, Go.go_eN_veb, add_assoc]
  refine ⟨M.step, hEN, fun x hx hx1 => ?_, ?_, ?_, hEg⟩
  · show eN (M.V x) = _
    rw [hV x hx hx1]; unfold zmV; rw [Go.go_eN_veb, add_assoc]
  · intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc x hx hx1
    have IH' : ∀ y, y < c → y < eN M.E → ∀ x, InE x → x < Om1 → M.sR y x = zmGR y x := IH
    change c < eN M.E at hc
    show M.sR c x = zmGR c x
    rcases lt_or_ge c M.E with hcE | hcE
    · rw [M.sR_lt hcE, hR c hcE x hx hx1]
    have h1 : veblen 1 (tfBG + ν) ≤ c := hE ▸ hcE
    have h2 : c < veblen 1 (tfBG + (ν + 1)) := hEN ▸ hc
    obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
    obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
    rw [M.sR_cnf hcE hc x, zmGR_cnf h1 h2 x, ← hE, hV x hx hx1, IH' _ hko (hko.trans hc) x hx hx1,
      IH' _ hro (hro.trans hc) x hx hx1, hR _ hdE x hx hx1]
  · intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc
    have IH' : ∀ y, y < c → y < eN M.E → M.sG y = zmGG y := IH
    change c < eN M.E at hc
    show M.sG c = zmGG c
    rcases lt_or_ge c M.E with hcE | hcE
    · rw [M.sG_lt hcE, hG c hcE]
    have h1 : veblen 1 (tfBG + ν) ≤ c := hE ▸ hcE
    have h2 : c < veblen 1 (tfBG + (ν + 1)) := hEN ▸ hc
    obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
    obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
    rw [M.sG_cnf hcE hc, zmGG_cnf h1 h2, ← hE, IH' _ hko (hko.trans hc), IH' _ hro (hro.trans hc), hG _ hdE]

/-- A code below `φ(1, B_Γ + λ)` (`λ` a limit) is below some `φ(1, B_Γ + ν)`, `ν < λ`. -/
theorem zm_lim_idx {l c : Ordinal.{0}} (hl : IsSuccLimit l) (hc : c < veblen 1 (tfBG + l)) :
    ∃ ν, ν < l ∧ c < veblen 1 (tfBG + ν) := by
  obtain ⟨c', hc', hcc'⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
  rcases lt_or_ge c' tfBG with h | h
  · refine ⟨0, hl.bot_lt, hcc'.trans ((isNormal_veblen 1).strictMono ?_)⟩
    rw [add_zero]; exact h
  · obtain ⟨μ, rfl⟩ := exists_add_of_le h
    exact ⟨μ, (add_lt_add_iff_left _).1 hc', hcc'⟩

section Union

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlε : l < ε₀) (hG : ∀ ν, ν < l → ZmGood ν)
include hl hG

/-- **A member of the chain containing a code below `φ(1, B_Γ + λ)`.** -/
theorem zmU_pick {c : Ordinal.{0}} (hc : c < veblen 1 (tfBG + l)) :
    ∃ M : ZmDS, ∃ ν, ν < l ∧ c < M.E ∧ M.E = veblen 1 (tfBG + ν) ∧
      (∀ x, InE x → x < Om1 → M.V x = zmV ν x) ∧
      (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.R c' x = zmGR c' x) ∧ (∀ c', c' < M.E → M.G c' = zmGG c') ∧
      M.Eg = 0 := by
  obtain ⟨ν, hν, hcν⟩ := zm_lim_idx hl hc
  obtain ⟨M, hE, hV, hR, hGg, hEg⟩ := hG ν hν
  exact ⟨M, ν, hν, hE ▸ hcν, hE, hV, hR, hGg, hEg⟩

omit hG in
theorem zmV_lt_lim {ν x : Ordinal.{0}} (hν : ν < l) : zmV ν x < zmV l x :=
  (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hν)

omit hl hG in
theorem zmV_lim_facts (hl0 : 0 < l) (hlε : l < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    zmV l x ∈ Tset x ∧ InE (zmV l x) ∧ ywV 1 0 x < zmV l x ∧ zmV l x < gq (ywV 1 0 x + 1) x := by
  obtain ⟨hDq, hqT, hq1, hqfix, -⟩ := zm_gq_facts hx hx1
  obtain ⟨-, hxD, -, hDE⟩ := zmD_facts hx hx1
  have hqE := zm_fix_E hqfix
  have hlD : l < ywV 1 0 x := hlε.trans_le ((gc_eps0_le hx).trans hxD.le)
  have hDl : ywV 1 0 x + l < gq (ywV 1 0 x + 1) x := (inE_indec hqE).add_lt hDq (hlD.trans hDq)
  have hVq : zmV l x < gq (ywV 1 0 x + 1) x := by
    unfold zmV
    calc veblen 1 (ywV 1 0 x + l) < veblen 1 (gq (ywV 1 0 x + 1) x) := (isNormal_veblen 1).strictMono hDl
      _ = _ := hqfix
  refine ⟨vz_T_down hx hx1 hqT hq1 hVq.le, zm_veb_E _, ?_, hVq⟩
  unfold zmV
  calc ywV 1 0 x = veblen 1 (ywV 1 0 x) := (zmD_fix hx hx1).symm
    _ < veblen 1 (ywV 1 0 x + l) := (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ hl0)

open Classical in
/-- **THE UNION AT A LIMIT INDEX `λ < ε₀`.** -/
noncomputable def zmU : ZmDS where
  E := veblen 1 (tfBG + l)
  Ei := tfBG + l
  V := zmV l
  W := fun x => ywV 1 0 x + (l + 1)
  R := fun c x => if InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l) then zmGR c x else c
  G := fun c => if c < veblen 1 (tfBG + l) then zmGG c else 0
  Eg := 0
  E_eq := rfl
  BG_le := le_self_add.trans (right_le_veblen _ _)
  E_X := by
    have h1 : l < tlX := hlε.trans_le (gc_eps0_le (Low.opow_eq_self_of_SC tlX_SC))
    exact tlX_SC.2 1 (gg_one_lt_of_SC tlX_SC) _ ((inE_indec (Low.opow_eq_self_of_SC tlX_SC)).add_lt tl_BG_lt_X h1)
  Ei_cl := fun Z hZ _ => TlCl.add (zbBG_tl hZ.1) (TlCl.small (hlε.trans_le (gc_eps0_le (gg_SC_eps hZ))))
  nfx := fun y h1 h2 hΓ => by
    rcases h2.lt_or_eq with h3 | h3
    · obtain ⟨M, -, -, hyM, -, -, -, -, -⟩ := zmU_pick hl hG h3
      exact M.nfx y h1 hyM.le hΓ
    · refine absurd (zm_fix_of_gamma hΓ) ?_
      intro hfix
      rw [h3] at hfix
      have e := (isNormal_veblen 1).strictMono.injective hfix
      have hE := zm_veb_E (tfBG + l)
      rw [e] at hE
      have hBl : tfBG < tfBG + l := lt_add_of_pos_right _ hl.bot_lt
      have h4 : tfBG + tfBG < tfBG + l := (inE_indec hE).add_lt hBl hBl
      have hlB : l < tfBG := hlε.trans_le (gc_eps0_le (Low.opow_eq_self_of_SC tfBG_SC))
      exact absurd ((add_lt_add_iff_left _).1 h4) (not_lt.2 hlB.le)
  Eg_le := fun _ _ => zero_le
  V_T := fun x hx hx1 _ => by
    obtain ⟨h1, h2, h3, h4⟩ := zmV_lim_facts hl.bot_lt hlε hx hx1
    exact ⟨h1, h2, h3.le, h4.trans (zm_gq_X hx hx1)⟩
  Vq := fun x hx hx1 _ => by
    obtain ⟨h1, h2, h3, h4⟩ := zmV_lim_facts hl.bot_lt hlε hx hx1
    exact zm_Vq_of hx hx1 h3.le h4 h2
  W_T := fun x hx hx1 _ => by
    have hl1 : l + 1 < ε₀ := gc_eps0_lim.add_one_lt hlε
    obtain ⟨hT, h1⟩ := zmDt_T hx hx1 hl1
    refine ⟨hT, h1, ?_⟩
    have hωl : ω ≤ l := omega0_le_of_isSuccLimit hl
    show eN (zmV l x) = _
    unfold zmV
    have e : ywV 1 0 x + 1 + (l + 1) = ywV 1 0 x + l + 1 := by
      rw [add_assoc, ← add_assoc 1 l 1, one_add_of_omega0_le hωl, ← add_assoc]
    rw [Go.go_eN_veb, zm_glA_veb hx hx1 _ hl1, e]
  V_pi := fun σ ρ hB _ => zmV_pi hB hlε
  W_pi := fun σ ρ hB _ => by
    have hl1 : l + 1 < σ := (ev_isSuccLimit_of_inE hB.1).add_one_lt (hlε.trans_le (gc_eps0_le hB.1))
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨s1, s2⟩ := pi_add hB d1 (mem_TB_of_lt hB hl1)
    exact ⟨s1, by rw [s2, d2, pi_lt hB hl1]⟩
  R0 := fun x => by
    split_ifs
    · rw [zmGR_lt tfBG_SC.1, yrR_zero]
    · rfl
  G0 := by rw [if_pos (zm_veb_E _).pos, zmGG_lt tfBG_SC.1, yrG_zero]
  G1 := by
    have h1 : (1 : Ordinal.{0}) < veblen 1 (tfBG + l) := lu_one_lt_E (zm_veb_E _)
    rw [if_pos h1, zmGG_lt (gg_one_lt_of_SC tfBG_SC)]; exact zmYr.G1
  lt := fun c x hx hx1 hc hg => by
    beta_reduce at hg ⊢
    rw [if_pos hc] at hg
    rw [if_pos ⟨hx, hx1, hc⟩]
    obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM x hx hx1]; rw [← hGg c hcM] at hg
    exact ((M.lt c x hx hx1 hcM hg).trans_eq (hV x hx hx1)).trans (zmV_lt_lim hl hν)
  pos := fun c x hx hx1 hc0 hc hg => by
    beta_reduce at *
    rw [if_pos hc] at hg
    rw [if_pos ⟨hx, hx1, hc⟩]
    obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM x hx hx1]; rw [← hGg c hcM] at hg
    exact M.pos c x hx hx1 hc0 hcM hg
  mono := fun b c x hx hx1 hbc hc hgb hgc => by
    beta_reduce at *
    have hb := hbc.trans hc
    rw [if_pos hb] at hgb; rw [if_pos hc] at hgc
    rw [if_pos ⟨hx, hx1, hb⟩, if_pos ⟨hx, hx1, hc⟩]
    obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    have hbM := hbc.trans hcM
    rw [← hR c hcM x hx hx1, ← hR b hbM x hx hx1]; rw [← hGg c hcM] at hgc; rw [← hGg b hbM] at hgb
    exact M.mono b c x hx hx1 hbc hcM hgb hgc
  succ := fun c x => by
    beta_reduce at *
    by_cases h : InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l)
    · obtain ⟨hx, hx1, hc⟩ := h
      have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos ⟨hx, hx1, hc1⟩, if_pos ⟨hx, hx1, hc⟩]
      obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
      have hc1M : c + 1 < M.E := M.E_lim.add_one_lt hcM
      rw [← hR c hcM x hx hx1, ← hR _ hc1M x hx hx1, M.succ]
    · have h' : ¬ (InE x ∧ x < Om1 ∧ c + 1 < veblen 1 (tfBG + l)) := fun ⟨hx, hx1, hc1⟩ =>
        h ⟨hx, hx1, (lt_add_one c).trans hc1⟩
      rw [if_neg h, if_neg h']
  g_le := fun c => by
    beta_reduce at *
    by_cases hc : c < veblen 1 (tfBG + l)
    · have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc, if_pos hc1]
      obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
      rw [← hGg c hcM, ← hGg _ (M.E_lim.add_one_lt hcM)]; exact M.g_le c
    · rw [if_neg hc]; exact zero_le
  g_succ := fun c Z hZ hEgZ hg => by
    beta_reduce at *
    by_cases hc : c < veblen 1 (tfBG + l)
    · have hc1 : c + 1 < veblen 1 (tfBG + l) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt hc
      rw [if_pos hc] at hg; rw [if_pos hc1]
      obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
      rw [← hGg c hcM] at hg; rw [← hGg _ (M.E_lim.add_one_lt hcM)]
      exact M.g_succ c Z hZ (by rw [hEgM]; exact hZ.bot_lt) hg
    · have hc1 : ¬ c + 1 < veblen 1 (tfBG + l) := fun h => hc ((lt_add_one c).trans h)
      rw [if_neg hc1]; exact hZ.bot_lt
  lim := fun c x hx hx1 hlc hc hg => by
    beta_reduce at *
    rw [if_pos hc] at hg
    rw [if_pos ⟨hx, hx1, hc⟩]
    obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM x hx hx1]; rw [← hGg c hcM] at hg
    exact M.lim c x hx hx1 hlc hcM hg
  nc := fun c x hx hx1 hlc hc hg => by
    beta_reduce at *
    rw [if_pos hc] at hg
    rw [if_pos ⟨hx, hx1, hc⟩]
    obtain ⟨M, ν, hν, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM x hx hx1]; rw [← hGg c hcM] at hg
    exact M.nc c x hx hx1 hlc hcM hg
  cof := fun c x hx hx1 hlc hc hg ν hν => by
    beta_reduce at *
    rw [if_pos hc] at hg
    rw [if_pos ⟨hx, hx1, hc⟩] at hν
    obtain ⟨M, μ, hμ, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM x hx hx1] at hν; rw [← hGg c hcM] at hg
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof c x hx hx1 hlc hcM hg ν hν
    have hbM := hb.trans hcM
    have hbl := hb.trans hc
    refine ⟨b, hb, ?_, ?_⟩
    · show (if b < veblen 1 (tfBG + l) then zmGG b else 0) < x
      rw [if_pos hbl, ← hGg b hbM]; exact hgb
    · show ν ≤ (if InE x ∧ x < Om1 ∧ b < veblen 1 (tfBG + l) then zmGR b x else b)
      rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b hbM x hx hx1]; exact hνb
  top := fun x hx hx1 _ ν hν => by
    have hDl : IsSuccLimit (ywV 1 0 x + l) := isSuccLimit_add _ hl
    obtain ⟨c', hc', hνc'⟩ := ((isNormal_veblen 1).lt_iff_exists_lt hDl).1 hν
    have hμ : ∃ μ, μ < l ∧ ν < zmV μ x := by
      rcases lt_or_ge c' (ywV 1 0 x) with h | h
      · refine ⟨0, hl.bot_lt, hνc'.trans ((isNormal_veblen 1).strictMono ?_)⟩
        rw [add_zero]; exact h
      · obtain ⟨μ, rfl⟩ := exists_add_of_le h
        exact ⟨μ, (add_lt_add_iff_left _).1 hc', hνc'⟩
    obtain ⟨μ, hμl, hνμ⟩ := hμ
    obtain ⟨M, hE, hV, hR, hGg, hEgM⟩ := hG μ hμl
    rw [← hV x hx hx1] at hνμ
    obtain ⟨b, hbM, hgb, hνb⟩ := M.top x hx hx1 (by rw [hEgM]; exact hx.pos) ν hνμ
    have hbl : b < veblen 1 (tfBG + l) :=
      hbM.trans_le (hE ▸ (isNormal_veblen 1).strictMono.monotone (add_le_add_right hμl.le _))
    refine ⟨b, hbl, ?_, ?_⟩
    · show (if b < veblen 1 (tfBG + l) then zmGG b else 0) < x
      rw [if_pos hbl, ← hGg b hbM]; exact hgb
    · show ν ≤ (if InE x ∧ x < Om1 ∧ b < veblen 1 (tfBG + l) then zmGR b x else b)
      rw [if_pos ⟨hx, hx1, hbl⟩, ← hR b hbM x hx hx1]; exact hνb
  ex := fun σ ρ c hB hc hg => by
    change (if c < veblen 1 (tfBG + l) then zmGG c else 0) < σ at hg
    rw [if_pos hc] at hg
    show (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (tfBG + l) then zmGR c ρ else c) ∈ TB ρ σ ∧
      R2.pi σ ρ (if InE ρ ∧ ρ < Om1 ∧ c < veblen 1 (tfBG + l) then zmGR c ρ else c) =
        (if InE σ ∧ σ < Om1 ∧ c < veblen 1 (tfBG + l) then zmGR c σ else c)
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    rw [if_pos ⟨hB.2.1, hρ1, hc⟩, if_pos ⟨hB.1, hσ1, hc⟩]
    obtain ⟨M, μ, hμ, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hR c hcM ρ hB.2.1 hρ1, ← hR c hcM σ hB.1 hσ1]; rw [← hGg c hcM] at hg
    exact M.ex σ ρ c hB hcM hg
  dig := fun σ ρ d hB hd hg P P' hP => by
    change (if d < veblen 1 (tfBG + l) then zmGG d else 0) < σ at hg
    rw [if_pos hd] at hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    show ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (tfBG + l) then zmGR d ρ else d) ∈ TB ρ σ ∧
      R2.pi σ ρ (ω ^ P * (if InE ρ ∧ ρ < Om1 ∧ d < veblen 1 (tfBG + l) then zmGR d ρ else d)) =
        ω ^ P' * (if InE σ ∧ σ < Om1 ∧ d < veblen 1 (tfBG + l) then zmGR d σ else d)
    rw [if_pos ⟨hB.2.1, hρ1, hd⟩, if_pos ⟨hB.1, hσ1, hd⟩]
    obtain ⟨M, μ, hμ, hdM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hd
    rw [← hR d hdM ρ hB.2.1 hρ1, ← hR d hdM σ hB.1 hσ1]; rw [← hGg d hdM] at hg
    exact M.dig σ ρ d hB hdM hg P P' (fun β hβT hβ => hP β hβT
      (hβ.trans_eq (hV ρ hB.2.1 hρ1) |>.trans (zmV_lt_lim hl hμ)))
  cl := fun c Z hZ hc hg => by
    change (if c < veblen 1 (tfBG + l) then zmGG c else 0) < Z at hg
    rw [if_pos hc] at hg
    obtain ⟨M, μ, hμ, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hGg c hcM] at hg
    exact M.cl c Z hZ hcM hg
  gate := fun c Z hZ hZ1 hEgZ hc h => by
    show (if c < veblen 1 (tfBG + l) then zmGG c else 0) < Z
    rw [if_pos hc]
    obtain ⟨M, μ, hμ, hcM, -, hV, hR, hGg, hEgM⟩ := zmU_pick hl hG hc
    rw [← hGg c hcM]; exact M.gate c Z hZ hZ1 (by rw [hEgM]; exact hZ.1) hcM h

include hlε in
open Classical in
theorem zmGood_lim : ZmGood l := by
  refine ⟨zmU hl hlε hG, rfl, fun _ _ _ => rfl, fun c hc x hx hx1 => ?_, fun c hc => ?_, rfl⟩
  · have hc' : c < veblen 1 (tfBG + l) := hc
    show (if InE x ∧ x < Om1 ∧ c < veblen 1 (tfBG + l) then zmGR c x else c) = _
    rw [if_pos ⟨hx, hx1, hc'⟩]
  · have hc' : c < veblen 1 (tfBG + l) := hc
    show (if c < veblen 1 (tfBG + l) then zmGG c else 0) = _
    rw [if_pos hc']

end Union

/-- **`ZmGood ν` FOR EVERY `ν < ε₀`, ONE TRANSFINITE INDUCTION.** -/
theorem zmGood_all : ∀ ν, ν < ε₀ → ZmGood ν := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => exact fun _ => zmGood_zero
  | add_one ν ih => exact fun h => zmGood_succ (ih ((lt_add_one ν).trans h))
  | limit l hl ih => exact fun h => zmGood_lim hl h (fun ν hν => ih ν hν (hν.trans h))

/-- **`ZbDirect S ε_{B_Γ+ε₀}`, UNCONDITIONAL.** -/
theorem zmDirectE0 (S : InaccSeq.{0}) : ZbDirect S (veblen 1 (tfBG + ε₀)) := by
  intro B hB1 hB2
  obtain ⟨ν, hν, hBν⟩ := zm_lim_idx gc_eps0_lim hB2
  obtain ⟨M, hE, -, -, -, hEg⟩ := zmGood_all ν hν
  have hBM : B < M.step.E := by
    show B < eN M.E
    rw [hE]; exact hBν.trans (lt_eN _)
  have hGM : tfBG < M.step.E := by
    show tfBG < eN M.E
    rw [hE]; exact (le_self_add.trans (right_le_veblen _ _)).trans_lt (lt_eN _)
  exact M.step.direct S hGM (by show M.Eg < _; rw [hEg]; exact Td.tdK_SC.1) M.step_gc0 B hB1 hBM

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < ε_{B_Γ+ε₀}`
(UNCONDITIONAL).** -/
theorem zmUVE0 (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < veblen 1 (tfBG + ε₀)) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zmDirectE0 S) l hr B hB hl

end Googology.Trans.PoR.InaccPsi.R2.Zm
