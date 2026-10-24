import Googology.Trans.PoR.InaccPsi.R2.SvTop

/-!
# `B_n` and `π_{σ,τ}` on the Veblen codes `[Ω₁, M)`, under the base-change facts as one hypothesis package

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `π = pi σ τ`, `Tᵗ[σ] = TB τ σ`, `Se.SeComm S n σ τ z` (`B_n z ∈
T^{τ'}[σ']`, `π_{σ',τ'}(B_n z) = B_n(π z)`), `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`.  `Si.siUncE` proves `SeComm` on the
codes `[Ω₁, E₁)` from the cited `Ω₁·ω^b ∈ Tᵗ[σ] ⇔ b ∈ Tᵗ[σ]`, `π(Ω₁·ω^b) = Ω₁·ω^{π b}` (`b < E₁`).  On the Veblen codes
`[E₁, Γ_{Ω₁+1})` two more facts are expected ([W07a] Def 5.1, third clause, through the terms `ϑ₁(⋯)` of the `ε`-numbers
and of the `ω^g`); they are **not** cited here:

* `SvCitPi M` (**the base-change facts below `M`**: `eps` (`φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]` and `π(φ(a, c)) = φ(π a, π
  c)` for an `ε`-number `Ω₁ < φ(a, c) < M` in normal form), `opow` (`ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]` and `π(ω^g) = ω^{π g}`
  for `E₁ ≤ g`, `ω^g ≠ g`, `ω^g < M`)), `svCitPi_E` (`SvCitPi E₁` holds);
* `svUncG` (**`SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, M)` with `ssDat ξ ≤ D < c_{n+1}`**, from `SeComm` at the
  countable `w ≤ D` and `SvCitPi M`, `M ≤ Γ_{Ω₁+1}` closed under `B_n` on the codes over `c_{n+1}`; also `B_n ξ`, `π ξ <
  Γ_{Ω₁+1}` and `π ξ` a code over `c_{n+1}`: the induction of `Si.siUncE` with one more case, the `ε`-numbers).

No new axiom.  New definition: the hypothesis package `SvCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si

variable {S : InaccSeq.{0}}

/-- **The base-change facts on the Veblen codes below `M`** ([W07a] Def 5.1; not cited here): a hypothesis package. -/
structure SvCitPi (M : Ordinal.{0}) : Prop where
  /-- an `ε`-number `φ(a, c)` in normal form -/
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → Om1 < veblen a c →
    veblen a c < M → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  /-- a power `ω^g`, `g ≥ E₁` not an `ε`-number -/
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → ggE ≤ g → ω ^ g ≠ g → ω ^ g < M →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- `SvCitPi E₁` holds: no `ε`-number in `(Ω₁, E₁)` and no `ω^g < E₁` with `g ≥ E₁`. -/
theorem svCitPi_E : SvCitPi ggE where
  eps := by
    intro σ τ a c _ ha _ _ h1 hE
    have hEps : ω ^ veblen a c = veblen a c := gg_veblen_eps (one_le_iff_ne_zero.1 ha)
    exact absurd (ggE_le hEps (by rw [← rj_Om1]; exact h1)) (not_le.2 hE)
  opow := by
    intro σ τ g _ hg _ hM
    exact absurd ((hg.trans (right_le_opow _ one_lt_omega0)).trans_lt hM) (lt_irrefl _)

/-- The data of a component: `ssDat (log_ω ξ)`, `ssDat (ξ mod ω^{log ξ}) ≤ ssDat ξ` for a non-`ε`
`ξ ∈ (Ω₁, Γ_{Ω₁+1})`. -/
theorem sv_dat_cnf {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < ggGam) (hE : ω ^ ξ ≠ ξ) :
    ssDat (log ω ξ) ≤ ssDat ξ ∧ ssDat (ξ % ω ^ log ω ξ) ≤ ssDat ξ := by
  rw [ssDat_eq_cnf h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- The data of the arguments: `ssDat a`, `ssDat c ≤ ssDat ξ` for an `ε`-number `ξ = φ(a, c) ∈ (Ω₁, Γ_{Ω₁+1})`. -/
theorem sv_dat_phi {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < ggGam) (hE : ω ^ ξ = ξ) :
    ssDat (invVeblen₁ ξ) ≤ ssDat ξ ∧ ssDat (invVeblen₂ ξ) ≤ ssDat ξ := by
  rw [ssDat_eq_phi h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- **`SeComm` on the Veblen codes `[Ω₁, M)`** under `SvCitPi M`. -/
theorem svUncG {M : Ordinal.{0}} (hP : SvCitPi M) (hMG : M ≤ ggGam)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → GgCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < M → ssDat ξ ≤ D →
      Bc.bcB S n ξ < ggGam ∧ pi σ τ ξ < ggGam ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hGs : SC (ggGam : Ordinal.{0}) := ggGam_spec.1
  have hEG : (ggE : Ordinal.{0}) < ggGam := Ss.ss_E_lt_Gam
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ pi σ τ w < ggGam ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), hπ1.trans ss_Om1_lt_Gam, GgCl.small hπc,
      Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξM hξD
  have hξG : ξ < ggGam := hξM.trans_le hMG
  have hξcl : GgCl (Bc.bcC S (n + 1)) ξ := ss_code hc0 ξ hξG (hξD.trans_lt hDc)
  have hBξG : Bc.bcB S n ξ < ggGam := ssB_lt_Gam hξcl
  have hDξ := (Rk.rkB_cl (n := n) hcL ξ hξcl).1
  -- facts at a smaller code `b ∈ Tᵗ[σ]` with `ssDat b ≤ D`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → ssDat b ≤ D →
      Mv.MvD S b ∧ pi σ τ b < ggGam ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧ Mv.MvD S (pi σ τ b) ∧
        Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbD
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 (by rw [← ssDat_small hb1]; exact hbD)
    · obtain ⟨-, a3, a4, a7⟩ := IH b hbξ hbT hb1 (hbξ.trans hξM) hbD
      have hbcl : GgCl (Bc.bcC S (n + 1)) b := ss_code hc0 b (hbξ.trans hξG) (hbD.trans_lt hDc)
      exact ⟨(Rk.rkB_cl (n := n) hcL b hbcl).1, a3, a4, (Rk.rkB_cl (n := n) hcL _ a4).1, a7⟩
  rcases lt_or_ge ξ ggE with hξE | hξE
  · -- below `E₁`: `Si.siUncE`
    have hrD : rjDat ξ ≤ D := by rw [← ssDat_eq_rj ξ hξE]; exact hξD
    obtain ⟨-, a2, a3, a4⟩ := siUncE (n := n) h hτc hDc hH ξ hξ hξ1 hξE hrD
    exact ⟨hBξG, a2.trans hEG, a3, a4⟩
  have hξ1' : Om1 < ξ := rj_Om1_lt_E.trans_le hξE
  by_cases hEps : ω ^ ξ = ξ
  · -- an `ε`-number `ξ = φ(a, c)`
    set a := invVeblen₁ ξ with hadef
    set c := invVeblen₂ ξ with hcdef
    have haξ : a < ξ := ss_inv1_lt hξ1' hξG
    have hcξ : c < ξ := ss_inv2_lt hEps
    have hev : veblen a c = ξ := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hEps]
    have ha0 : a ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ c = ω ^ ξ := by rw [hev, hEps]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hcξ.ne
    obtain ⟨haD, hcD⟩ := sv_dat_phi hξ1' hξG hEps
    have hepsξ := hP.eps h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
      (by rw [hev]; exact hξ1') (by rw [hev]; exact hξM)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hξ
    have hπξ : pi σ τ ξ = veblen (pi σ τ a) (pi σ τ c) := hepsξ.2 haT hcT
    obtain ⟨hDa, hπaG, hπacl, hDπa, haC⟩ := hsub a haξ haT (haD.trans hξD)
    obtain ⟨hDc', hπcG, hπccl, hDπc, hcC⟩ := hsub c hcξ hcT (hcD.trans hξD)
    -- `B_n ξ = φ(B_n a, B_n c)`
    obtain ⟨-, hBξ⟩ := Mw.mwB_phi (k := n) hDa hDc' (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    rw [hev] at hBξ
    have hBa : Bc.bcB S n a < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDa hDξ).2 haξ
    have hBc : Bc.bcB S n c < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDc' hDξ).2 hcξ
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (lt_of_le_of_lt zero_le hcL)
    have hBa0 : Bc.bcB S n a ≠ 0 := by
      intro e
      have h1 := (Mv.mvB_lt_iff (k := n) hD0 hDa).2 (pos_iff_ne_zero.2 ha0)
      rw [Bc.bcB_zero, e] at h1
      exact lt_irrefl _ h1
    obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
    rw [← rj_Om1] at hDO hBO
    have hOB : Om1 < Bc.bcB S n ξ := by
      have := (Mv.mvB_lt_iff (k := n) hDO hDξ).2 hξ1'; rwa [hBO] at this
    have hBξM : Bc.bcB S n ξ < M := hMB n ξ hξM hξcl
    have heps' := hP.eps hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBξ]; exact hBa) (by rw [← hBξ]; exact hBc)
      (by rw [← hBξ]; exact hOB) (by rw [← hBξ]; exact hBξM)
    rw [← hBξ] at heps'
    -- `π ξ = φ(π a, π c)` in normal form (`π` is injective)
    have hπinj : ∀ y ∈ TB τ σ, pi σ τ y = pi σ τ ξ → y = ξ := fun y hy he => (pi_bijOn h).1.injOn hy hξ he
    have hπa : pi σ τ a < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => haξ.ne (hπinj a haT e)
      rw [hπξ]; exact left_le_veblen _ _
    have hπc : pi σ τ c < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => hcξ.ne (hπinj c hcT e)
      rw [hπξ]; exact right_le_veblen _ _
    rw [hπξ] at hπa hπc
    obtain ⟨-, hBπ⟩ := Mw.mwB_phi (k := n) hDπa hDπc hπa hπc
    refine ⟨hBξG, by rw [hπξ]; exact hGs.2 _ hπaG _ hπcG, by rw [hπξ]; exact GgCl.phi hπacl hπccl, ?_, ?_⟩
    · exact heps'.1.2 ⟨haC.1, hcC.1⟩
    · rw [heps'.2 haC.1 hcC.1, haC.2, hcC.2, hπξ, hBπ]
  · -- a non-`ε` code `ξ = ω^g·k + r`, `g ≥ E₁`
    have hξ0 : ξ ≠ 0 := (rj_Om1_pos.trans hξ1').ne'
    have hτξ : τ ≤ ξ := h.2.2.2.le.trans hξ1'.le
    obtain ⟨hdec, -, -, -⟩ := si_dec hξ0
    have hcξ := si_comps_cons hξ0
    set g := log ω ξ with hgdef
    set r := ξ % ω ^ g with hrdef
    have hgE : ggE ≤ g := le_log_of_opow_le one_lt_omega0 (by rw [Rk.rk_E_inE]; exact hξE)
    have hgξ : g < ξ := ss_log_lt hξ0 hEps
    obtain ⟨hgD, hrD⟩ := sv_dat_cnf hξ1' hξG hEps
    have hrξ : r < ξ := rj_mod_lt hξ0
    have hpTB : ω ^ g ∈ TB τ σ := by
      refine siTB_of_comps h hξ hτξ fun p hp => ?_
      have hg0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
      rw [si_comps_cons hg0, log_opow one_lt_omega0, Ordinal.mod_self, si_comps_zero] at hp
      rw [List.mem_singleton.1 hp, hcξ]; exact List.mem_cons_self
    have hrTB : r ∈ TB τ σ := siTB_of_comps h hξ hτξ fun p hp => by
      rw [hcξ]; exact List.mem_cons_of_mem _ hp
    have hpξ : ω ^ g ≤ ξ := opow_log_le_self ω hξ0
    -- the facts at `ω^g`
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < ggGam ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧
        Mv.MvD S (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · -- `ω^g = g` an `ε`-number below `ξ`
        have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT (hgD.trans hξD)
      · obtain ⟨hiff, hπp⟩ := hP.opow h hgE hgE' (hpξ.trans_lt hξM)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hπgcl, hDπg, hgC⟩ := hsub g hgξ hgT (hgD.trans hξD)
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hgcl : GgCl (Bc.bcC S (n + 1)) g := ss_code hc0 g (hgξ.trans hξG) ((hgD.trans hξD).trans_lt hDc)
        have hpcl : GgCl (Bc.bcC S (n + 1)) (ω ^ g) := GgCl.opow hc0 hgcl
        have hBgE : ggE ≤ Bc.bcB S n g := sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpM : ω ^ Bc.bcB S n g < M := by rw [← hBp]; exact hMB n _ (hpξ.trans_lt hξM) hpcl
        obtain ⟨hiff', hπp'⟩ := hP.opow hB' hBgE hBgne hBpM
        refine ⟨hDp, by rw [hπp hgT]; exact sv_Gam_inE.opow_lt hπgG, by rw [hπp hgT]; exact GgCl.opow hc0 hπgcl,
          by rw [hπp hgT]; exact hDπp, ?_, ?_⟩
        · rw [hBp]; exact hiff'.2 hgC.1
        · rw [hBp, hπp' hgC.1, hgC.2, hπp hgT, hBπp]
    obtain ⟨hDp', hπpG, hπpcl, hDπp', hpC⟩ := hpF
    -- the multiples `ω^g·j`
    have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (Lw.lw_L_SC S ω).1
    have hmul : ∀ j : ℕ, ω ^ g * j ∈ TB τ σ ∧ pi σ τ (ω ^ g * j) = pi σ τ (ω ^ g) * j ∧
        Mv.MvD S (ω ^ g * j) ∧ Mv.MvD S (pi σ τ (ω ^ g) * j) ∧ Se.SeComm S n σ τ (ω ^ g * j) := by
      intro j
      induction j with
      | zero =>
        simp only [Nat.cast_zero, mul_zero]
        have h0T := mem_TB_of_lt h h0σ
        exact ⟨h0T, pi_lt h h0σ, hD0, hD0, hH 0 h0T rj_Om1_pos zero_le⟩
      | succ j ih =>
        obtain ⟨hT, hπ, hD, hDπ, hC⟩ := ih
        rw [Nat.cast_succ, mul_add_one, mul_add_one]
        obtain ⟨hsT, hsπ⟩ := pi_add h hT hpTB
        refine ⟨hsT, by rw [hsπ, hπ], (Mv.mvB_add (k := n) hD hDp').1, (Mv.mvB_add (k := n) hDπ hDπp').1, ?_⟩
        exact siComm_add h hτc hT hpTB hD hDp' (by rw [hπ]; exact hDπ) hDπp' hC hpC
    -- the remainder
    obtain ⟨hDr, hπrG, hπrcl, hDπr, hrC⟩ := hsub r hrξ hrTB (hrD.trans hξD)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
    have hξk : ω ^ g * (k : Ordinal.{0}) + r = ξ := by rw [← hk]; exact hdec
    obtain ⟨hkT, hkπ, hkD, hkDπ, hkC⟩ := hmul k
    have hπξ : pi σ τ ξ = pi σ τ (ω ^ g) * k + pi σ τ r := by
      conv_lhs => rw [← hξk]
      rw [(pi_add h hkT hrTB).2, hkπ]
    have hωG : (ω : Ordinal.{0}) < ggGam := omega0_lt_inE sv_Gam_inE
    refine ⟨hBξG, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact sv_Gam_inE.add_lt (sv_Gam_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact GgCl.add (GgCl.mul_nat hc0 hπpcl k) hπrcl
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Sv
