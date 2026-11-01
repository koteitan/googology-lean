import Googology.Trans.PoR.InaccPsi.R2.XkBase

/-!
# XkImg: LEMMA IMG BELOW `gq (c+1) ρ = Γ_{ρ+2+c}` FROM LEMMA IMG UP TO THE BASE ATOM `gq c ρ`

`He.he_img_G1` gives Lemma IMG below `Γ_{ρ+2} = gq 1 ρ` through the level induction `He.he_DI`, whose statements carry
the bound `gq 1 ρ`.  Here the step past a base atom is proved directly, for every index `c ∈ Tᵖ ∩ Ω₁`, with no level
induction: every `ε`-number `e ∈ (gq c ρ, gq (c+1) ρ)` is `ϑᵖ(Ω₁·q + t)` (`Xk.xk_rep`), and Lemma IMG at `e` follows
from Lemma IMG below `e` by the reach test going down (`He.he_img_down`) with
`E' = max(gq c ρ, q + 1, P, R)`: `P` the largest fixed point of `φ(q, ·)` below `e` (so every `ε`-number in `(E', e)`
has level `q' ≤ q`), `R` the previous point of level `q` (`t` a successor), `ϑᵖ(Ω₁·q + c')` (`t = c' + ω^z` with
`t < ϑᵖ(Ω₁·q + σ)` for some `σ < t`, so `ζ_t = z`), or `t` itself (`t` closed under `σ ↦ ϑᵖ(Ω₁·q + σ)`, so every
point of level `q` below `e` is at most `t`); the reaches come from `He.he_lhq`.

* `xk_succT`, `xkI_atom` (**Lemma IMG at the base atom `gq (1+α) ρ`** for `1 + α < ε₀`, from the top witness of the
  tower layer `(Gc.gcB α).K`), `xkImg_step` (**THE STEP: Lemma IMG below `gq c ρ` and at `gq c ρ` give it below
  `gq (c+1) ρ`**, every `c ∈ Tᵖ ∩ Ω₁`), `xkImg_nat` (**Lemma IMG below `gq (n+1) ρ = Γ_{ρ+2+n}` for every `n : ℕ`**;
  `n = 0` is `He.he_img_G1`), `xkL1Img` (**Lemma IMG below `gq 2 ρ = Γ_{ρ+3}`**: the skeleton leaf `skL1Img`),
  `xkImg_cst` (**Lemma IMG below `gq c ρ = Γ_{ρ+1+c}` for every constant `1 ≤ c < ε₀`**), `xkPkg_nat`, `xkPkg_cst`
  (Lemma IMG (gated) for a specified function below `gq (n+1) ρ`, below `gq c ρ`; `n = 0` is `He.he_pkg_G1`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xk

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.He
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Hb
  Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gj
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

/-- `c + 1 ∈ Tˣ ∩ Ω₁` for `c ∈ Tˣ ∩ Ω₁`. -/
theorem xk_succT {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hcT : c ∈ Tset x) (hc1 : c < Om1) :
    c + 1 ∈ Tset x ∧ c + 1 < Om1 := by
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hcT hc1
  exact ⟨vz_T_down hx hx1 hGT hG1 (Order.add_one_le_of_lt (gmq_gt hx hx1 hcT hc1)), gl_Om1_lim.add_one_lt hc1⟩

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT THE BASE ATOM `gq (1+α) ρ = Γ_{ρ+2+α}`** (`1 + α < ε₀`): the top witness of the tower layer
`(Gc.gcB α).K`, whose top is `gq (1+α)` (`Gc.gcB_E`), and `π(gq (1+α) ρ) = gq (1+α) (f ρ)` (`Gb.gq_pi`). -/
theorem xkI_atom {α : Ordinal.{0}} (hα : 1 + α < ε₀) : GnI ρ δ (gq (1 + α) ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set L := (gcB α).K with hL
  have hcst := gc_cst hα
  have hE : ∀ x, InE x → x < Om1 → L.sys.top x = gq (1 + α) x := by
    intro x hx hx1
    rw [L.top_eq x hx hx1, gcB_E hα hx hx1]
    exact (gq_facts hx hx1 (hcst x hx)).2.2.2.1
  obtain ⟨W, Z, hw, hTW, hI⟩ := L.top_wit ρ τ δ h
  rw [hE ρ hρE hρ1] at hTW
  obtain ⟨hT, -, h1, -, -⟩ := gq_facts hρE hρ1 (hcst ρ hρE)
  refine gnI_mk h hw (Finset.mem_union_left _ hTW) hT h1 (fun A f hW hZ C => ?_)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have hle := (hI A f hW hZ' C).2
  rw [hE _ hyE hy1, hE ρ hρE hρ1] at hle
  rw [(gq_pi (h.img_bases C) (hcst _ hyE)).2]
  exact hle

/-- **THE STEP PAST A BASE ATOM**: Lemma IMG below `gq c ρ` and at `gq c ρ` give Lemma IMG below `gq (c+1) ρ`, for
every `c ∈ Tᵖ ∩ Ω₁`. -/
theorem xkImg_step {c : Ordinal.{0}} (hcT : c ∈ Tset ρ) (hc1 : c < Om1) (H1 : ∀ v, v < gq c ρ → GnI ρ δ v)
    (H2 : GnI ρ δ (gq c ρ)) : ∀ v, v < gq (c + 1) ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hc1T, hc1'⟩ := xk_succT hρE hρ1 hcT hc1
  obtain ⟨-, hρG, -, -, -⟩ := geq_facts hρE hρ1 hcT hc1
  refine gnImg_of_eps h (fun v hv => xkT hρE hρ1 hc1T hc1' hv) (fun e he _ heB IHe => ?_)
  rcases le_or_gt e (gq c ρ) with hle | hgt
  · rcases hle.lt_or_eq with hlt | heq
    · exact H1 e hlt
    · rw [heq]; exact H2
  obtain ⟨q, t, hq1, hqT, hqΩ, htT, ht1, hev⟩ := xk_rep hρE hρ1 hcT hc1 he hgt heB
  subst hev
  obtain ⟨-, -, -, hE, hqe, hte⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  -- the fixed points of `φ(q, ·)` below `e`
  have hPq : ∃ P0, P0 < glA q t ρ ∧ ∀ u, LuP (q + 1) u → u < glA q t ρ → u ≤ P0 := by
    by_cases hz : veblen (q + 1) 0 ≤ glA q t ρ
    · obtain ⟨a, ha1, ha2⟩ := hb_floor (q + 1) (j0 := 0) hz
      refine ⟨veblen (q + 1) a, lt_of_le_of_ne ha1 (fun e' =>
        glA_notP hρE hρ1 hq1 hqT hqΩ htT ht1 (by rw [← e']; exact ⟨a, rfl⟩)), fun u hu hue => ?_⟩
      obtain ⟨j, rfl⟩ := hu
      have hj : j < a + 1 := (veblen_lt_veblen_iff_right).1 (hue.trans ha2)
      exact (isNormal_veblen _).monotone (Order.lt_add_one_iff.1 hj)
    · push Not at hz
      refine ⟨0, hE.pos, fun u hu hue => ?_⟩
      exfalso
      obtain ⟨j, rfl⟩ := hu
      exact absurd (hue.trans hz) (not_lt.2 ((isNormal_veblen _).monotone zero_le))
  -- the earlier points of level `q`
  have hRq : ∃ R0, R0 < glA q t ρ ∧ ∀ t', t' ∈ Tset ρ → t' < Om1 → t' < t → R0 < glA q t' ρ →
      luZeta ρ q t' < luZeta ρ q t := by
    rcases zero_or_succ_or_isSuccLimit t with ht0 | ⟨s, hs⟩ | hlim
    · refine ⟨0, hE.pos, fun t' _ _ ht' _ => ?_⟩
      exact absurd ht' (by rw [ht0]; exact not_lt.2 zero_le)
    · have hts : t = s + 1 := by rw [← hs, succ_eq_add_one]
      have hst : s < t := by rw [hts]; exact lt_add_one s
      obtain ⟨hsT, hs1⟩ : s ∈ Tset ρ ∧ s < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hst.le, hst.trans ht1⟩
      refine ⟨glA q s ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hsT htT ht1 hst, fun t' ht'T ht'1 ht' hR => ?_⟩
      exfalso
      have hst' : t' ≤ s := by rw [hts] at ht'; exact Order.lt_add_one_iff.1 ht'
      have := (glA_le_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 hsT hs1).2 hst'
      exact absurd hR (not_lt.2 this)
    · by_cases hcl : ∃ σ, σ < t ∧ t < vt ρ (Om1 * q + σ)
      · have hz : luZeta ρ q t = lg t := by unfold luZeta; rw [if_pos hcl]
        have ht0 : t ≠ 0 := hlim.bot_lt.ne'
        obtain ⟨c', hcs, -, hc't⟩ := lg_split ht0
        obtain ⟨hc'T, hc'1⟩ : c' ∈ Tset ρ ∧ c' < Om1 := ⟨vz_T_down hρE hρ1 htT ht1 hc't.le, hc't.trans ht1⟩
        refine ⟨glA q c' ρ, glA_lt_of hρE hρ1 hq1 hqT hqΩ hc'T htT ht1 hc't, fun t' ht'T ht'1 ht' hR => ?_⟩
        have hc't' : c' < t' := (glA_lt_iff hρE hρ1 hq1 hqT hqΩ hc'T hc'1 ht'T ht'1).1 hR
        rw [hz]
        set z := lg t with hzdef
        obtain ⟨δ', hδ'⟩ : ∃ δ', t' = c' + δ' := ⟨t' - c', (Ordinal.add_sub_cancel_of_le hc't'.le).symm⟩
        have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc't'.ne'
        have hδlt : δ' < ω ^ z := by
          have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact ht'
          exact (add_lt_add_iff_left _).1 this
        have hlgd : lg t' < z := by
          rw [hδ', gz_lg_add _ hδ0]
          by_contra hge; push Not at hge
          obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
          have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
          have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
          exact absurd hδlt (not_lt.2 (h1.trans h2))
        exact lu_zeta_le_lg.trans_lt hlgd
      · push Not at hcl
        refine ⟨t, hte, fun t' _ _ ht' hR => ?_⟩
        exact absurd (hcl t' ht') (not_le.2 hR)
  obtain ⟨P0, hP0e, hP0⟩ := hPq
  obtain ⟨R0, hR0e, hR0⟩ := hRq
  set E' := max (max (gq c ρ) (q + 1)) (max P0 R0) with hE'def
  have hGE' : gq c ρ ≤ E' := (le_max_left _ _).trans (le_max_left _ _)
  have hqE' : q < E' := (lt_add_one q).trans_le ((le_max_right _ _).trans (le_max_left _ _))
  have hPE' : P0 ≤ E' := (le_max_left _ _).trans (le_max_right _ _)
  have hRE' : R0 ≤ E' := (le_max_right _ _).trans (le_max_right _ _)
  have hE'e : E' < glA q t ρ :=
    max_lt (max_lt hgt ((ev_isSuccLimit_of_inE hE).add_one_lt hqe)) (max_lt hP0e hR0e)
  refine he_img_down h hq1 hqT hqΩ htT ht1 (hρG.trans_le hGE') hqE' hE'e (fun u hu hE'u hue => ?_) IHe
  have hGu : gq c ρ < u := hGE'.trans_lt hE'u
  obtain ⟨q', t', hq'1, hq'T, hq'Ω, ht'T, ht'1, hu'⟩ := xk_rep hρE hρ1 hcT hc1 hu hGu (hue.trans heB)
  have hq'q : q' ≤ q := by
    by_contra hlt
    push Not at hlt
    have hP : LuP (q + 1) u := by
      rw [← hu']
      exact (gq_veb_level hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1 le_add_self).2 (Order.add_one_le_of_lt hlt)
    exact absurd (hE'u.trans_le' (hP0 u hP hue |>.trans hPE')) (lt_irrefl _)
  obtain ⟨H1', H2', -⟩ := he_lhq hρE hρ1 hq'1 hq'T hq'Ω ht'T ht'1
  rw [hu'] at H1' H2'
  refine ⟨q', _, hq'q, H1', H2', fun e' => ?_⟩
  subst e'
  have ht't : t' < t := by
    rw [← hu'] at hue
    exact (glA_lt_iff hρE hρ1 hq1 hqT hqΩ ht'T ht'1 htT ht1).1 hue
  exact hR0 t' ht'T ht'1 ht't (hRE'.trans_lt (hu' ▸ hE'u))

/-- **LEMMA IMG BELOW `gq (n+1) ρ = Γ_{ρ+2+n}` FOR EVERY `n : ℕ`** (`n = 0`: `He.he_img_G1`). -/
theorem xkImg_nat : ∀ n : ℕ, ∀ v, v < gq ((n : Ordinal.{0}) + 1) ρ → GnI ρ δ v := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, zero_add]; exact he_img_G1 h
  | succ n IH =>
    have hρE := h.ρE
    have hρ1 := h.ρ1
    have hnc : GqCst ((n : Ordinal.{0}) + 1) := by
      have := gqCst_nat (n + 1); rwa [Nat.cast_add, Nat.cast_one] at this
    obtain ⟨hcT, hc1⟩ := gq_cst hρE hρ1 (hnc ρ hρE)
    have hα : 1 + (n : Ordinal.{0}) < ε₀ := by
      rw [← Nat.cast_one, ← Nat.cast_add]; exact natCast_lt_epsilon _ 0
    have hat : GnI ρ δ (gq ((n : Ordinal.{0}) + 1) ρ) := by
      have := xkI_atom h hα
      rwa [show (1 : Ordinal.{0}) + (n : Ordinal.{0}) = (n : Ordinal.{0}) + 1 by
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]] at this
    have H := xkImg_step h hcT hc1 IH hat
    rwa [show ((n + 1 : ℕ) : Ordinal.{0}) = (n : Ordinal.{0}) + 1 by push_cast; rfl]

/-- **LEMMA IMG BELOW `gq c ρ = Γ_{ρ+1+c}` FOR EVERY CONSTANT `1 ≤ c < ε₀`** (one transfinite induction on `c`:
`c = 1` is `He.he_img_G1`, successors by `xkImg_step` with the atom `xkI_atom`, limits by `Gc.gc_lt_lim_iff`). -/
theorem xkImg_cst : ∀ c : Ordinal.{0}, 1 ≤ c → c < ε₀ → ∀ v, v < gq c ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hε : ∀ c : Ordinal.{0}, c < ε₀ → c < ρ := fun c hc => gc_cst hc ρ hρE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc1 hcε
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlim
  · exact absurd (h0 ▸ hc1) (not_le.2 zero_lt_one)
  · have hcc : c = c' + 1 := by rw [← hc', succ_eq_add_one]
    have hc'c : c' < c := by rw [hcc]; exact lt_add_one c'
    have hc'ε : c' < ε₀ := hc'c.trans hcε
    rcases eq_or_ne c' 0 with h0 | h0
    · subst h0; rw [hcc, zero_add]; exact he_img_G1 h
    have h1c' : 1 ≤ c' := one_le_iff_ne_zero.2 h0
    obtain ⟨hcT, hcΩ⟩ := gq_cst hρE hρ1 (hε c' hc'ε)
    have hα : 1 + (c' - 1) = c' := Ordinal.add_sub_cancel_of_le h1c'
    have hat : GnI ρ δ (gq c' ρ) := by
      have := xkI_atom h (α := c' - 1) (by rw [hα]; exact hc'ε)
      rwa [hα] at this
    rw [hcc]
    exact xkImg_step h hcT hcΩ (IH c' hc'c h1c' hc'ε) hat
  · intro v hv
    obtain ⟨ν, hνc, hvν⟩ := gc_lt_lim_iff hρE hρ1 hlim (hε c hcε) v hv
    have hm : max ν 1 < c := max_lt hνc ((omega0_le_of_isSuccLimit hlim).trans_lt' one_lt_omega0)
    exact IH (max ν 1) hm (le_max_right _ _) (hm.trans hcε) v
      (hvν.trans_le (gq_mono hρE hρ1 (hε _ (hm.trans hcε)) (le_max_left _ _)))

/-- **LEMMA IMG BELOW `Γ_{ρ+3} = gq 2 ρ`** (the skeleton leaf `skL1Img`). -/
theorem xkL1Img : ∀ v, v < gq 2 ρ → GnI ρ δ v := by
  have H := xkImg_nat h 1
  rwa [show ((1 : ℕ) : Ordinal.{0}) + 1 = 2 by norm_num] at H

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `gq (n+1) ρ`** (`n = 0`: `He.he_pkg_G1`). -/
theorem xkPkg_nat (n : ℕ) {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < gq ((n : Ordinal.{0}) + 1) ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (xkImg_nat h n _ hT) hex

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `gq c ρ`**, every constant `1 ≤ c < ε₀`. -/
theorem xkPkg_cst {c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcε : c < ε₀) {g : Ordinal.{0}} {C : Finset Ordinal.{0}}
    {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ) (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < gq c ρ) (hex : GjEx g C T) :
    GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (xkImg_cst h c hc1 hcε _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Xk
