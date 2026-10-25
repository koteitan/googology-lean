import Googology.Trans.PoR.InaccPsi.R2.TzTop
import Googology.Trans.PoR.InaccPsi.R2.TlCit

/-!
# `π` on the codes below `X` and the commutation `B_n ∘ π = π' ∘ B_n` there

`π = pi σ τ`, `B_n = Bc.bcB S n`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `X = Tl.tlX`, `F_β = Rh.rhF β`
(the atoms `F_β(y)`, `y < F_β(y)`, of the codes `Tl.TlCl`).  The proof of `R2.TiPi` with every atom below `X`, the
package `Tl.TlCitPi M` (`Tl.tlCitPi`: it holds at `M = X`, from `R2.CitedTl`) and the move `Tw.twB_atom`:

* `tz_eps_TB`, `tz_opow_TB` (the `ε`-numbers and the powers `ω^g` under `TlCitPi M`), `tz_dat_cnf`, `tz_dat_phi`;
* `tzUnc_atom` (**the atom step**: `π(F_β(y)) = F_{π β}(π y)` and `SeComm` at `F_β(y)` from `SeComm` at `β`, `y`);
* `tzUncG` (**`Se.SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, M)`, `M ≤ X`**, from `SeComm` at the countable terms
  `≤ D`; the new case is the atom `ξ = F_β(y)`: level `0` through `y = Ω₁ + 1 + c` (the data of `ξ` is that of `c`),
  level `β ≥ 1` through `β` and `y`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tz

open Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ts

variable {S : InaccSeq.{0}}

section API

variable {M : Ordinal.{0}} (hP : TlCitPi M)
include hP

/-- **An `ε`-number `Ω₁ < φ(a, c) < M` in normal form** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem tz_eps_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (hav : a < veblen a c)
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
theorem tz_opow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : ggE ≤ g) (hne : ω ^ g ≠ g) (hM : ω ^ g < M) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) := by
  rcases lt_trichotomy (ω ^ g) ggGam with hl | he | hg'
  · exact Sy.syCitPi.opow h hg hne hl
  · exfalso
    have hgl : g < ω ^ g := lt_of_le_of_ne (right_le_opow g one_lt_omega0) (Ne.symm hne)
    have h2 : ω ^ g < ggGam := Sv.sv_Gam_inE.opow_lt (by rw [← he]; exact hgl)
    rw [he] at h2; exact lt_irrefl _ h2
  · exact hP.opow h hg hne hg' hM

end API

/-- The data of a component: `tlDat (log_ω ξ)`, `tlDat (ξ mod ω^{log ξ}) ≤ tlDat ξ` for a non-`ε` `ξ ∈ (Ω₁, B_Γ)`. -/
theorem tz_dat_cnf {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < tlX) (hE : ω ^ ξ ≠ ξ) :
    tlDat (log ω ξ) ≤ tlDat ξ ∧ tlDat (ξ % ω ^ log ω ξ) ≤ tlDat ξ := by
  rw [tlDat_cnf h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- The data of the arguments of an `ε`-number `ξ = φ(a, c) ∈ (Ω₁, B_Γ)` that is not an atom. -/
theorem tz_dat_phi {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < tlX) (hE : ω ^ ξ = ξ) (hI : invVeblen₁ ξ < ξ) :
    tlDat (invVeblen₁ ξ) ≤ tlDat ξ ∧ tlDat (invVeblen₂ ξ) ≤ tlDat ξ := by
  rw [tlDat_phi h1 h2 hE hI]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- **The atom step**: for an atom `ξ = F_β(y)` (`y < ξ`, `Ω₁ < ξ < M`) in `Tᵗ[σ]` with `β`, `y`, `π β`, `π y` codes
over `c_{n+1}` and `SeComm` at `β` and `y`: `π ξ = F_{π β}(π y)` is a code below `X`, and `SeComm` holds at `ξ`. -/
theorem tzUnc_atom {M : Ordinal.{0}} (hP : TlCitPi M) {n : ℕ} {σ τ β y : Ordinal.{0}} (h : Bases σ τ)
    (hτc : τ < Bc.bcC S (n + 1)) (h1 : Om1 < rhF β y) (hyF : y < rhF β y) (hM : rhF β y < M)
    (hBM : Bc.bcB S n (rhF β y) < M) (hβT : β ∈ TB τ σ) (hyT : y ∈ TB τ σ)
    (hβcl : TlCl (Bc.bcC S (n + 1)) β) (hycl : TlCl (Bc.bcC S (n + 1)) y)
    (hπβcl : TlCl (Bc.bcC S (n + 1)) (pi σ τ β)) (hπycl : TlCl (Bc.bcC S (n + 1)) (pi σ τ y))
    (hβC : Se.SeComm S n σ τ β) (hyC : Se.SeComm S n σ τ y) :
    pi σ τ (rhF β y) = rhF (pi σ τ β) (pi σ τ y) ∧ pi σ τ (rhF β y) < tlX ∧
      TlCl (Bc.bcC S (n + 1)) (pi σ τ (rhF β y)) ∧ Se.SeComm S n σ τ (rhF β y) := by
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by
    rw [rj_Om1]; exact ((Se.seC_lt_L n).trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  obtain ⟨hA1, hA2⟩ := hP.atom h h1 hM hyF
  have hπξ := hA2 hβT hyT
  have hξT := hA1.2 ⟨hβT, hyT⟩
  have hmono := (pi_bijOn h).2
  have hπy : pi σ τ y < rhF (pi σ τ β) (pi σ τ y) := by rw [← hπξ]; exact hmono hyT hξT hyF
  have hπ1 : Om1 < rhF (pi σ τ β) (pi σ τ y) := by
    rw [← hπξ]; have := hmono (pi_Om1 h).1 hξT h1; rwa [(pi_Om1 h).2] at this
  have hπX : rhF (pi σ τ β) (pi σ τ y) < tlX := by
    have := (rhF_lt (pi σ τ β)).2 (tw_cl_lt hc1 hπycl); rwa [ts_X_fix (tw_cl_lt hc1 hπβcl)] at this
  obtain ⟨hDξ, hBξ, -⟩ := twB_atom (n := n) hβcl hycl hyF h1
  obtain ⟨-, hBπξ, -⟩ := twB_atom (n := n) hπβcl hπycl hπy hπ1
  have hDy := (twB_cl (n := n) hycl).1
  have hBy : Bc.bcB S n y < Bc.bcB S n (rhF β y) := (Mv.mvB_lt_iff hDy hDξ).2 hyF
  obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
  rw [← rj_Om1] at hDO hBO
  have hB1 : Om1 < Bc.bcB S n (rhF β y) := by
    have := (Mv.mvB_lt_iff (k := n) hDO hDξ).2 h1; rwa [hBO] at this
  rw [hBξ] at hBy hB1 hBM
  obtain ⟨hB1', hB2'⟩ := hP.atom (Se.seBases_img h hτc) hB1 hBM hBy
  refine ⟨hπξ, by rw [hπξ]; exact hπX, by rw [hπξ]; exact TlCl.atom hπβcl hπycl hπ1, ?_, ?_⟩
  · rw [hBξ]; exact hB1'.2 ⟨hβC.1, hyC.1⟩
  · rw [hBξ, hB2' hβC.1 hyC.1, hβC.2, hyC.2, hπξ, hBπξ]

/-- **`SeComm` on the Veblen codes `[Ω₁, M)`** under `TlCitPi M`. -/
theorem tzUncG {M : Ordinal.{0}} (hP : TlCitPi M) (hMG : M ≤ tlX)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → TlCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < M → tlDat ξ ≤ D →
      Bc.bcB S n ξ < tlX ∧ pi σ τ ξ < tlX ∧ TlCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hGs : SC (tlX : Ordinal.{0}) := tlX_SC
  have hEG : (ggE : Ordinal.{0}) < tlX := Ss.ss_E_lt_Gam.trans tz_gg_lt_X
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ pi σ τ w < tlX ∧ TlCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), hπ1.trans tlX_gt, TlCl.small hπc,
      Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξM hξD
  have hξG : ξ < tlX := hξM.trans_le hMG
  have hξcl : TlCl (Bc.bcC S (n + 1)) ξ := tl_code hc0 ξ hξG (hξD.trans_lt hDc)
  have hBξG : Bc.bcB S n ξ < tlX := twB_lt_X hξcl
  have hDξ := (twB_cl (n := n) hξcl).1
  -- facts at a smaller code `b ∈ Tᵗ[σ]` with `ssDat b ≤ D`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → tlDat b ≤ D →
      Mv.MvD S b ∧ pi σ τ b < tlX ∧ TlCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧ Mv.MvD S (pi σ τ b) ∧
        Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbD
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 (by rw [← tlDat_small hb1]; exact hbD)
    · obtain ⟨-, a3, a4, a7⟩ := IH b hbξ hbT hb1 (hbξ.trans hξM) hbD
      have hbcl : TlCl (Bc.bcC S (n + 1)) b := tl_code hc0 b (hbξ.trans hξG) (hbD.trans_lt hDc)
      exact ⟨(twB_cl (n := n) hbcl).1, a3, a4, (twB_cl (n := n) a4).1, a7⟩
  rcases lt_or_ge ξ ggE with hξE | hξE
  · -- below `E₁`: `Si.siUncE`
    have hrD : rjDat ξ ≤ D := by
      rw [← ssDat_eq_rj ξ hξE, ← tfDat_eq_ss ξ (hξE.trans Ss.ss_E_lt_Gam),
        ← tlDat_eq_tf ξ ((hξE.trans Ss.ss_E_lt_Gam).trans tf_gg_lt_BG)]; exact hξD
    obtain ⟨-, a2, a3, a4⟩ := siUncE (n := n) h hτc hDc hH ξ hξ hξ1 hξE hrD
    exact ⟨hBξG, a2.trans hEG, tlCl_of_tf hc0 (tfCl_of_lg hc0 (lgCl_of_GgCl a3)), a4⟩
  have hξ1' : Om1 < ξ := rj_Om1_lt_E.trans_le hξE
  by_cases hEps : ω ^ ξ = ξ
  · by_cases hI : invVeblen₁ ξ < ξ
    swap
    · -- an atom `ξ = F_β(y)`, `y < ξ`
      have hSC : SC ξ := tl_SC_of hξ1' hI
      obtain ⟨hnf, hyξ, hβξ⟩ := tl_nf hSC hξ1' hξG
      generalize hβdef : tlLev ξ = β at hnf hyξ hβξ
      generalize hydef : tlI β ξ = y at hnf hyξ
      have hyF : y < rhF β y := by rw [hnf]; exact hyξ
      have h1F : Om1 < rhF β y := by rw [hnf]; exact hξ1'
      have hMF : rhF β y < M := by rw [hnf]; exact hξM
      have hXF : rhF β y < tlX := by rw [hnf]; exact hξG
      have hBMF : Bc.bcB S n (rhF β y) < M := by rw [hnf]; exact hMB n ξ hξM hξcl
      have hξT' : rhF β y ∈ TB τ σ := by rw [hnf]; exact hξ
      obtain ⟨hβT, hyT⟩ := (hP.atom h h1F hMF hyF).1.1 hξT'
      have hcode : ∀ b, b < ξ → tlDat b ≤ D → TlCl (Bc.bcC S (n + 1)) b := fun b hb hbD =>
        tl_code hc0 b (hb.trans hξG) (hbD.trans_lt hDc)
      rcases eq_or_ne β 0 with hβ0 | hβ0
      · -- level `0`: `ξ = Γ_y`, `y = Ω₁ + 1 + c`, `tlDat ξ = tlDat c`
        subst hβ0
        rw [rhF_zero] at hyF h1F hXF
        have h1 : Om1 < y := tf_Om1_lt_gamma.1 h1F
        set c := y - (Om1 + 1) with hcdef
        have hyc : Om1 + 1 + c = y := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)
        have hcy : c ≤ y := by rw [← hyc]; exact le_add_self
        have hcξ : c < ξ := hcy.trans_lt hyξ
        have hdc : tlDat c = tlDat ξ := by
          have e := tlDat_gamma h1 hyF hXF; rw [rhF_zero] at hnf; rw [← hnf]; exact e.symm
        have hτy : τ ≤ y := h.2.2.2.le.trans h1.le
        have hcT : c ∈ TB τ σ := siTB_of_comps h hyT hτy fun p hp => by rw [← hyc]; exact ti_comps_sub c p hp
        obtain ⟨hDcc, hπcG, hπccl, hDπc, hcC⟩ := hsub c hcξ hcT (hdc.le.trans hξD)
        have hccl : TlCl (Bc.bcC S (n + 1)) c := hcode c hcξ (hdc.le.trans hξD)
        obtain ⟨hOT, hOπ⟩ := tf_Om1_succ_TB h
        obtain ⟨hOT', hOπ'⟩ := tf_Om1_succ_TB hB'
        obtain ⟨hDO1, hBO1⟩ := tiB_Om1_succ (S := S) (n := n)
        have hOC : Se.SeComm S n σ τ (Om1 + 1) := by
          refine ⟨by rw [hBO1]; exact hOT', by rw [hBO1, hOπ', hOπ, hBO1]⟩
        have hyC : Se.SeComm S n σ τ y := by
          rw [← hyc]
          exact siComm_add h hτc hOT hcT hDO1 hDcc (by rw [hOπ]; exact hDO1) hDπc hOC hcC
        obtain ⟨-, hπy⟩ := pi_add h hOT hcT
        rw [hOπ, hyc] at hπy
        have hO1c : TlCl (Bc.bcC S (n + 1)) (Om1 + 1) := TlCl.add TlCl.om (TlCl.one hc0)
        have hycl : TlCl (Bc.bcC S (n + 1)) y := by rw [← hyc]; exact TlCl.add hO1c hccl
        have hπycl : TlCl (Bc.bcC S (n + 1)) (pi σ τ y) := by rw [hπy]; exact TlCl.add hO1c hπccl
        have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
        have h0T : (0 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt h h0σ
        have hπ0 : pi σ τ 0 = 0 := pi_lt h h0σ
        have h0C : Se.SeComm S n σ τ 0 := hH 0 h0T rj_Om1_pos zero_le
        have h0cl : TlCl (Bc.bcC S (n + 1)) 0 := TlCl.zero hc0
        have hF0 : ∀ z, rhF 0 z = gamma z := fun z => by rw [rhF_zero]
        obtain ⟨-, a2, a3, a4⟩ := tzUnc_atom hP h hτc (by rw [hF0]; exact h1F) (by rw [hF0]; exact hyF)
          (by rw [hnf]; exact hξM) (by rw [hnf]; exact hMB n ξ hξM hξcl) h0T hyT h0cl hycl
          (by rw [hπ0]; exact h0cl) hπycl h0C hyC
        rw [hnf] at a2 a3 a4
        exact ⟨hBξG, a2, a3, a4⟩
      · -- level `β ≥ 1`: `tlDat ξ = max(tlDat β, tlDat y)`
        have hdat : tlDat ξ = max (tlDat β) (tlDat y) := by rw [← hnf]; exact tlDat_F hβ0 h1F hXF hyF
        have hβD : tlDat β ≤ D := (le_max_left _ _).trans (hdat ▸ hξD)
        have hyD : tlDat y ≤ D := (le_max_right _ _).trans (hdat ▸ hξD)
        obtain ⟨-, -, hπβcl, -, hβC⟩ := hsub β hβξ hβT hβD
        obtain ⟨-, -, hπycl, -, hyC⟩ := hsub y hyξ hyT hyD
        obtain ⟨-, a2, a3, a4⟩ := tzUnc_atom hP h hτc h1F hyF hMF hBMF hβT hyT (hcode β hβξ hβD) (hcode y hyξ hyD)
          hπβcl hπycl hβC hyC
        rw [hnf] at a2 a3 a4
        exact ⟨hBξG, a2, a3, a4⟩
    -- an `ε`-number `ξ = φ(a, c)`
    set a := invVeblen₁ ξ with hadef
    set c := invVeblen₂ ξ with hcdef
    have haξ : a < ξ := hI
    have hcξ : c < ξ := ss_inv2_lt hEps
    have hev : veblen a c = ξ := by rw [hadef, hcdef, veblen_invVeblen₁_invVeblen₂, hEps]
    have ha0 : a ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ c = ω ^ ξ := by rw [hev, hEps]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hcξ.ne
    obtain ⟨haD, hcD⟩ := tz_dat_phi hξ1' hξG hEps hI
    have hepsξ := tz_eps_TB hP h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
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
    have heps' := tz_eps_TB hP hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBξ]; exact hBa) (by rw [← hBξ]; exact hBc)
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
    refine ⟨hBξG, by rw [hπξ]; exact hGs.2 _ hπaG _ hπcG, by rw [hπξ]; exact TlCl.phi hπacl hπccl, ?_, ?_⟩
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
    obtain ⟨hgD, hrD⟩ := tz_dat_cnf hξ1' hξG hEps
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
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < tlX ∧ TlCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧
        Mv.MvD S (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · -- `ω^g = g` an `ε`-number below `ξ`
        have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT (hgD.trans hξD)
      · obtain ⟨hiff, hπp⟩ := tz_opow_TB hP h hgE hgE' (hpξ.trans_lt hξM)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hπgcl, hDπg, hgC⟩ := hsub g hgξ hgT (hgD.trans hξD)
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hgcl : TlCl (Bc.bcC S (n + 1)) g := tl_code hc0 g (hgξ.trans hξG) ((hgD.trans hξD).trans_lt hDc)
        have hpcl : TlCl (Bc.bcC S (n + 1)) (ω ^ g) := TlCl.opow hc0 hgcl
        have hBgE : ggE ≤ Bc.bcB S n g := Sv.sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpM : ω ^ Bc.bcB S n g < M := by rw [← hBp]; exact hMB n _ (hpξ.trans_lt hξM) hpcl
        obtain ⟨hiff', hπp'⟩ := tz_opow_TB hP hB' hBgE hBgne hBpM
        refine ⟨hDp, by rw [hπp hgT]; exact tl_X_inE.opow_lt hπgG, by rw [hπp hgT]; exact TlCl.opow hc0 hπgcl,
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
    have hωG : (ω : Ordinal.{0}) < tlX := omega0_lt_inE tl_X_inE
    refine ⟨hBξG, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact tl_X_inE.add_lt (tl_X_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact TlCl.add (TlCl.mul_nat hc0 hπpcl k) hπrcl
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Tz
