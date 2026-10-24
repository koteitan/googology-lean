import Googology.Trans.PoR.InaccPsi.R2.TcTop

/-!
# `B_n` and `π_{σ,τ}` on the codes `[Ω₁, M)` (`M ≤ Γ'`), under the base-change facts at `[Γ_{Ω₁+1}, M)` as a package

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `π = pi σ τ`, `Tᵗ[σ] = TB τ σ`, `Se.SeComm S n σ τ z`,
`E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `Γ' = lgGam'`.  `R2.CitedSy` cites the base-change facts on the Veblen codes
below `Γ_{Ω₁+1}` (`Sv.SvCitPi Γ_{Ω₁+1}`, `Sy.syCitPi`).  On the codes `[Γ_{Ω₁+1}, Γ')` (Veblen normal forms with the
atom `Γ_{Ω₁+1}`) three facts are needed; this module states them as one package (cited in `R2.CitedTc`):

* `TcCitPi M` (**the base-change facts on `[Γ_{Ω₁+1}, M)`**: `gam` (`Γ_{Ω₁+1} ∈ Tᵗ[σ]` and `π(Γ_{Ω₁+1}) = Γ_{Ω₁+1}`
  when `Γ_{Ω₁+1} < M`), `eps` (`φ(a, c) ∈ Tᵗ[σ] ⇔ a, c ∈ Tᵗ[σ]` and `π(φ(a, c)) = φ(π a, π c)` for an `ε`-number
  `Γ_{Ω₁+1} < φ(a, c) < M` in normal form), `opow` (`ω^g ∈ Tᵗ[σ] ⇔ g ∈ Tᵗ[σ]` and `π(ω^g) = ω^{π g}` for `E₁ ≤ g`,
  `ω^g ≠ g`, `Γ_{Ω₁+1} < ω^g < M`)), `tcCitPi_G` (`TcCitPi Γ_{Ω₁+1}` holds), `tc_gam_TB`, `tc_eps_TB`, `tc_opow_TB`
  (the facts on all of `(Ω₁, M)`, below `Γ_{Ω₁+1}` from `Sy.syCitPi`);
* `tcUncG` (**`SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, M)` with `tcDat ξ ≤ D < c_{n+1}`**, from `SeComm` at the
  countable `w ≤ D`, `TcCitPi M`, `M ≤ Γ'` closed under `B_n` on the codes over `c_{n+1}`; also `B_n ξ`, `π ξ < Γ'` and
  `π ξ` a code over `c_{n+1}`: the induction of `Sv.svUncG` with one more case, the atom).

No new axiom.  New definition: the hypothesis package `TcCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si

variable {S : InaccSeq.{0}}

/-- **The base-change facts on the codes `[Γ_{Ω₁+1}, M)`** ([W07a] Def 5.1): a hypothesis package. -/
structure TcCitPi (M : Ordinal.{0}) : Prop where
  /-- the atom `Γ_{Ω₁+1} = ϑ₁(Ω₂²)` -/
  gam : ∀ {σ τ : Ordinal.{0}}, Bases σ τ → ggGam < M → ggGam ∈ TB τ σ ∧ pi σ τ ggGam = ggGam
  /-- an `ε`-number `φ(a, c)` in normal form -/
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → ggGam < veblen a c →
    veblen a c < M → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  /-- a power `ω^g`, `g ≥ E₁` not an `ε`-number -/
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → ggE ≤ g → ω ^ g ≠ g → ggGam < ω ^ g → ω ^ g < M →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- `TcCitPi Γ_{Ω₁+1}` holds (nothing in `[Γ_{Ω₁+1}, Γ_{Ω₁+1})`). -/
theorem tcCitPi_G : TcCitPi ggGam where
  gam _ h := absurd h (lt_irrefl _)
  eps _ _ _ _ h1 h2 := absurd (h1.trans h2) (lt_irrefl _)
  opow _ _ _ h1 h2 := absurd (h1.trans h2) (lt_irrefl _)

section API

variable {M : Ordinal.{0}} (hP : TcCitPi M)
include hP

/-- The atom `Γ_{Ω₁+1}`. -/
theorem tc_gam_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) (hM : ggGam < M) :
    ggGam ∈ TB τ σ ∧ pi σ τ ggGam = ggGam := hP.gam h hM

/-- **An `ε`-number `Ω₁ < φ(a, c) < M` in normal form** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem tc_eps_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (hav : a < veblen a c)
    (hcv : c < veblen a c) (h1 : Om1 < veblen a c) (hM : veblen a c < M) :
    (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c)) := by
  rcases lt_trichotomy (veblen a c) ggGam with hl | he | hg
  · exact Sy.syCitPi.eps h ha hav hcv h1 hl
  · exfalso
    have := ggGam_spec.1.2 a (by rw [← he]; exact hav) c (by rw [← he]; exact hcv)
    rw [he] at this; exact lt_irrefl _ this
  · exact hP.eps h ha hav hcv hg hM

/-- **A power `ω^g < M`, `g ≥ E₁` not an `ε`-number** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem tc_opow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : ggE ≤ g) (hne : ω ^ g ≠ g) (hM : ω ^ g < M) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) := by
  rcases lt_trichotomy (ω ^ g) ggGam with hl | he | hg'
  · exact Sy.syCitPi.opow h hg hne hl
  · exfalso
    have hgl : g < ω ^ g := lt_of_le_of_ne (right_le_opow g one_lt_omega0) (Ne.symm hne)
    have h2 : ω ^ g < ggGam := Sv.sv_Gam_inE.opow_lt (by rw [← he]; exact hgl)
    rw [he] at h2; exact lt_irrefl _ h2
  · exact hP.opow h hg hne hg' hM

end API

/-- The data of a component: `tcDat (log_ω ξ)`, `tcDat (ξ mod ω^{log ξ}) ≤ tcDat ξ` for a non-`ε` `ξ ∈ (Ω₁, Γ')`. -/
theorem tc_dat_cnf {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < lgGam') (hE : ω ^ ξ ≠ ξ) :
    tcDat (log ω ξ) ≤ tcDat ξ ∧ tcDat (ξ % ω ^ log ω ξ) ≤ tcDat ξ := by
  rw [tcDat_eq_cnf h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- The data of the arguments of an `ε`-number `ξ = φ(a, c) ∈ (Ω₁, Γ')`, `ξ ≠ Γ_{Ω₁+1}`. -/
theorem tc_dat_phi {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < lgGam') (hG : ξ ≠ ggGam) (hE : ω ^ ξ = ξ) :
    tcDat (invVeblen₁ ξ) ≤ tcDat ξ ∧ tcDat (invVeblen₂ ξ) ≤ tcDat ξ := by
  rw [tcDat_eq_phi h1 h2 hG hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- **`SeComm` on the Veblen codes `[Ω₁, M)`** under `SvCitPi M`. -/
theorem tcUncG {M : Ordinal.{0}} (hP : TcCitPi M) (hMG : M ≤ lgGam')
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → LgCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < M → tcDat ξ ≤ D →
      Bc.bcB S n ξ < lgGam' ∧ pi σ τ ξ < lgGam' ∧ LgCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hGs : SC (lgGam' : Ordinal.{0}) := tc_SC_G'
  have hEG : (ggE : Ordinal.{0}) < lgGam' := Ss.ss_E_lt_Gam.trans tc_Gam_lt_G'
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ pi σ τ w < lgGam' ∧ LgCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), hπ1.trans tc_Om1_lt_G', LgCl.small hπc,
      Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξM hξD
  have hξG : ξ < lgGam' := hξM.trans_le hMG
  have hξcl : LgCl (Bc.bcC S (n + 1)) ξ := tc_code hc0 ξ hξG (hξD.trans_lt hDc)
  have hBξG : Bc.bcB S n ξ < lgGam' := tcB_lt_G' hξcl hξG
  have hDξ := (tcB_cl (n := n) hcL ξ hξcl).1
  -- facts at a smaller code `b ∈ Tᵗ[σ]` with `ssDat b ≤ D`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → tcDat b ≤ D →
      Mv.MvD S b ∧ pi σ τ b < lgGam' ∧ LgCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧ Mv.MvD S (pi σ τ b) ∧
        Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbD
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 (by rw [← tcDat_small hb1]; exact hbD)
    · obtain ⟨-, a3, a4, a7⟩ := IH b hbξ hbT hb1 (hbξ.trans hξM) hbD
      have hbcl : LgCl (Bc.bcC S (n + 1)) b := tc_code hc0 b (hbξ.trans hξG) (hbD.trans_lt hDc)
      exact ⟨(tcB_cl (n := n) hcL b hbcl).1, a3, a4, (tcB_cl (n := n) hcL _ a4).1, a7⟩
  rcases lt_or_ge ξ ggE with hξE | hξE
  · -- below `E₁`: `Si.siUncE`
    have hrD : rjDat ξ ≤ D := by
      rw [← ssDat_eq_rj ξ hξE, ← tcDat_eq_ss ξ (hξE.trans Ss.ss_E_lt_Gam)]; exact hξD
    obtain ⟨-, a2, a3, a4⟩ := siUncE (n := n) h hτc hDc hH ξ hξ hξ1 hξE hrD
    exact ⟨hBξG, a2.trans hEG, lgCl_of_GgCl a3, a4⟩
  have hξ1' : Om1 < ξ := rj_Om1_lt_E.trans_le hξE
  by_cases hGξ : ξ = ggGam
  · -- the atom `Γ_{Ω₁+1}`
    subst hGξ
    have hgB := tc_gam_TB hP (Se.seBases_img h hτc) hξM
    have hgA := tc_gam_TB hP h hξM
    refine ⟨hBξG, by rw [hgA.2]; exact tc_Gam_lt_G', by rw [hgA.2]; exact LgCl.gam, ?_, ?_⟩
    · rw [Mx.mxB_gam]; exact hgB.1
    · rw [Mx.mxB_gam, hgB.2, hgA.2, Mx.mxB_gam]
  by_cases hEps : ω ^ ξ = ξ
  · -- an `ε`-number `ξ = φ(a, c)`
    set a := invVeblen₁ ξ with hadef
    set c := invVeblen₂ ξ with hcdef
    have haξ : a < ξ := tc_inv1_lt hξ1' hξG hGξ
    have hcξ : c < ξ := ss_inv2_lt hEps
    have hev : veblen a c = ξ := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hEps]
    have ha0 : a ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ c = ω ^ ξ := by rw [hev, hEps]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hcξ.ne
    obtain ⟨haD, hcD⟩ := tc_dat_phi hξ1' hξG hGξ hEps
    have hepsξ := tc_eps_TB hP h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
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
    have heps' := tc_eps_TB hP hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBξ]; exact hBa) (by rw [← hBξ]; exact hBc)
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
    refine ⟨hBξG, by rw [hπξ]; exact hGs.2 _ hπaG _ hπcG, by rw [hπξ]; exact LgCl.phi hπacl hπccl, ?_, ?_⟩
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
    obtain ⟨hgD, hrD⟩ := tc_dat_cnf hξ1' hξG hEps
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
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < lgGam' ∧ LgCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧
        Mv.MvD S (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · -- `ω^g = g` an `ε`-number below `ξ`
        have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT (hgD.trans hξD)
      · obtain ⟨hiff, hπp⟩ := tc_opow_TB hP h hgE hgE' (hpξ.trans_lt hξM)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hπgcl, hDπg, hgC⟩ := hsub g hgξ hgT (hgD.trans hξD)
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hgcl : LgCl (Bc.bcC S (n + 1)) g := tc_code hc0 g (hgξ.trans hξG) ((hgD.trans hξD).trans_lt hDc)
        have hpcl : LgCl (Bc.bcC S (n + 1)) (ω ^ g) := LgCl.opow hc0 hgcl
        have hBgE : ggE ≤ Bc.bcB S n g := Sv.sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpM : ω ^ Bc.bcB S n g < M := by rw [← hBp]; exact hMB n _ (hpξ.trans_lt hξM) hpcl
        obtain ⟨hiff', hπp'⟩ := tc_opow_TB hP hB' hBgE hBgne hBpM
        refine ⟨hDp, by rw [hπp hgT]; exact tc_G'_inE.opow_lt hπgG, by rw [hπp hgT]; exact LgCl.opow hc0 hπgcl,
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
    have hωG : (ω : Ordinal.{0}) < lgGam' := omega0_lt_inE tc_G'_inE
    refine ⟨hBξG, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact tc_G'_inE.add_lt (tc_G'_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact LgCl.add (LgCl.mul_nat hc0 hπpcl k) hπrcl
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Tc
