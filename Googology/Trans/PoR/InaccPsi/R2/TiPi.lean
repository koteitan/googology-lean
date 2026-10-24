import Googology.Trans.PoR.InaccPsi.R2.TiTop

/-!
# `π` on the codes below `B_Γ` and the commutation `B_n ∘ π = π' ∘ B_n` there

`π = pi σ τ`, `B_n = Bc.bcB S n`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `B_Γ = Tf.tfBG`, `Γ_ν = gamma ν`
(an atom `ψ_{Ω₂}(c)`, `ν = Ω₁ + 1 + c`, `R2.TfPsi`).  The proof of `R2.TcPi` with every atom below `B_Γ`:

* `TiCitPi M` (**[W07a] Def 5.1 on the codes `[Γ_{Ω₁+1}, M)`**, a package: `gam` (every atom `Γ_ν < M`: `Γ_ν ∈ Tᵗ[σ] ↔
  ν ∈ Tᵗ[σ]`, `π(Γ_ν) = Γ_{π ν}`), `eps` (`φ(a, c)` in normal form), `opow` (`ω^g`, `g ≥ E₁`)), `tiCitPi` (**`TiCitPi
  B_Γ` holds**, from `tfGam_TB`, `tfPhi_TB`, `tfOpow_TB` of `R2.CitedTf`), `ti_gam_TB`, `ti_eps_TB`, `ti_opow_TB`;
* `ti_dat_cnf`, `ti_dat_phi`, `ti_comps_fin`, `ti_comps_one_add`, `ti_comps_Om1`, `ti_comps_sub` (**every additive
  component of `c` is one of `Ω₁ + 1 + c`**, so `ν ∈ Tᵗ[σ]` gives `c ∈ Tᵗ[σ]`);
* `tiUncG` (**`Se.SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, M)`, `M ≤ B_Γ`**, from `SeComm` at the countable terms `≤ D`;
  the new case is the atom `ξ = Γ_ν`: `π ξ = Γ_{Ω₁+1+π c}`, `B_n ξ = Γ_{Ω₁+1+B_n c}`, `Ti.tiB_gamma`).

No new axiom.  New definition: the package `TiCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si

variable {S : InaccSeq.{0}}

/-- **The base-change facts on the codes `[Γ_{Ω₁+1}, M)`** ([W07a] Def 5.1): a hypothesis package (every atom
`Γ_ν = ψ_{Ω₂}(ν − (Ω₁ + 1))` below `M`, the `ε`-numbers `φ(a, c)` and the powers `ω^g`). -/
structure TiCitPi (M : Ordinal.{0}) : Prop where
  /-- an atom `Γ_ν`, `ν > Ω₁` -/
  gam : ∀ {σ τ ν : Ordinal.{0}}, Bases σ τ → Om1 < ν → gamma ν < M →
    (gamma ν ∈ TB τ σ ↔ ν ∈ TB τ σ) ∧ (ν ∈ TB τ σ → pi σ τ (gamma ν) = gamma (pi σ τ ν))
  /-- an `ε`-number `φ(a, c)` in normal form -/
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → ggGam < veblen a c →
    veblen a c < M → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  /-- a power `ω^g`, `g ≥ E₁` not an `ε`-number -/
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → ggE ≤ g → ω ^ g ≠ g → ggGam < ω ^ g → ω ^ g < M →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

/-- **`TiCitPi B_Γ`**, from `R2.CitedTf` (`tfGam_TB`, `tfPhi_TB`, `tfOpow_TB`). -/
theorem tiCitPi : TiCitPi tfBG where
  gam h h1 hB := tfGam_TB h h1 hB
  eps h h1 h2 h3 h4 h5 := tfPhi_TB h h1 h2 h3 (ss_Om1_lt_Gam.trans h4) h5
  opow h h1 h2 _ h4 := tfOpow_TB h h1 h2 h4

section API

variable {M : Ordinal.{0}} (hP : TiCitPi M)
include hP

/-- An atom `Γ_ν < M`. -/
theorem ti_gam_TB {σ τ ν : Ordinal.{0}} (h : Bases σ τ) (h1 : Om1 < ν) (hM : gamma ν < M) :
    (gamma ν ∈ TB τ σ ↔ ν ∈ TB τ σ) ∧ (ν ∈ TB τ σ → pi σ τ (gamma ν) = gamma (pi σ τ ν)) := hP.gam h h1 hM

/-- **An `ε`-number `Ω₁ < φ(a, c) < M` in normal form** (below `Γ_{Ω₁+1}` from `Sy.syCitPi`). -/
theorem ti_eps_TB {σ τ a c : Ordinal.{0}} (h : Bases σ τ) (ha : 1 ≤ a) (hav : a < veblen a c)
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
theorem ti_opow_TB {σ τ g : Ordinal.{0}} (h : Bases σ τ) (hg : ggE ≤ g) (hne : ω ^ g ≠ g) (hM : ω ^ g < M) :
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g) := by
  rcases lt_trichotomy (ω ^ g) ggGam with hl | he | hg'
  · exact Sy.syCitPi.opow h hg hne hl
  · exfalso
    have hgl : g < ω ^ g := lt_of_le_of_ne (right_le_opow g one_lt_omega0) (Ne.symm hne)
    have h2 : ω ^ g < ggGam := Sv.sv_Gam_inE.opow_lt (by rw [← he]; exact hgl)
    rw [he] at h2; exact lt_irrefl _ h2
  · exact hP.opow h hg hne hg' hM

end API

/-- The data of a component: `tfDat (log_ω ξ)`, `tfDat (ξ mod ω^{log ξ}) ≤ tfDat ξ` for a non-`ε` `ξ ∈ (Ω₁, B_Γ)`. -/
theorem ti_dat_cnf {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < tfBG) (hE : ω ^ ξ ≠ ξ) :
    tfDat (log ω ξ) ≤ tfDat ξ ∧ tfDat (ξ % ω ^ log ω ξ) ≤ tfDat ξ := by
  rw [tfDat_cnf h1 h2 hE]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- The data of the arguments of an `ε`-number `ξ = φ(a, c) ∈ (Ω₁, B_Γ)` that is not an atom. -/
theorem ti_dat_phi {ξ : Ordinal.{0}} (h1 : Om1 < ξ) (h2 : ξ < tfBG) (hE : ω ^ ξ = ξ) (hI : invVeblen₁ ξ < ξ) :
    tfDat (invVeblen₁ ξ) ≤ tfDat ξ ∧ tfDat (invVeblen₂ ξ) ≤ tfDat ξ := by
  rw [tfDat_phi h1 h2 hE hI]; exact ⟨le_max_left _ _, le_max_right _ _⟩

/-- A finite nonzero ordinal has the single component `1`. -/
theorem ti_comps_fin {x : Ordinal.{0}} (h0 : x ≠ 0) (hx : x < ω) : comps x = [1] := by
  rw [si_comps_cons h0, Ordinal.log_eq_zero hx, opow_zero, Ordinal.mod_one, si_comps_zero]

/-- `comps (1 + c) = comps c` for `c ≠ 0`. -/
theorem ti_comps_one_add {c : Ordinal.{0}} (hc : c ≠ 0) : comps (1 + c) = comps c := by
  rcases lt_or_ge c ω with h | h
  · have h1 : (1 : Ordinal.{0}) + c < ω := (isPrincipal_add_omega0) one_lt_omega0 h
    rw [ti_comps_fin (lt_of_lt_of_le zero_lt_one le_self_add).ne' h1,
      ti_comps_fin hc h]
  · rw [one_add_of_omega0_le h]

/-- `comps (Ω₁·v + w) = Ω₁ :: comps w` for `0 < v < ω`, `w < Ω₁`. -/
theorem ti_comps_Om1 {v w : Ordinal.{0}} (hv0 : v ≠ 0) (hv : v < ω) (hw : w < Om1) :
    comps (Om1 * v + w) = Om1 :: comps w := by
  have hO : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  have hne : Om1 * v + w ≠ 0 :=
    (lt_of_lt_of_le (mul_pos rj_Om1_pos (pos_iff_ne_zero.2 hv0)) le_self_add).ne'
  have hw' : w < ω ^ (Om1 : Ordinal.{0}) := by rw [hO]; exact hw
  have hl : log ω (Om1 * v + w) = Om1 := by
    conv_lhs => rw [← hO]
    rw [log_opow_mul_add one_lt_omega0 hv0 hw', Ordinal.log_eq_zero hv, add_zero]
  rw [si_comps_cons hne, hl, hO]
  congr 2
  conv_lhs => rw [← hO]
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hw']

/-- **Every component of `c` is a component of `Ω₁ + 1 + c`.** -/
theorem ti_comps_sub (c : Ordinal.{0}) : ∀ p ∈ comps c, p ∈ comps (Om1 + 1 + c) := by
  intro p hp
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [si_comps_zero] at hp; simp at hp
  have hP : IsPrincipal (· + ·) (Om1 : Ordinal.{0}) := by
    rw [← rj_Om1_opow]; exact isPrincipal_add_omega0_opow _
  rw [add_assoc]
  rcases lt_or_ge c Om1 with h | h
  · have hy : 1 + c < Om1 := hP tf_one_lt_Om1 h
    have e : Om1 + (1 + c) = Om1 * 1 + (1 + c) := by rw [mul_one]
    rw [e, ti_comps_Om1 one_ne_zero one_lt_omega0 hy, ti_comps_one_add hc0]
    exact List.mem_cons_of_mem _ hp
  have hωc : ω ≤ c := (omega0_le_omega 1).trans h
  rw [one_add_of_omega0_le hωc]
  rcases lt_or_ge c (Om1 * ω) with h2 | h2
  · have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
    set q := c / Om1 with hq
    set r := c % Om1 with hr
    have hdec : Om1 * q + r = c := Ordinal.div_add_mod c Om1
    have hr1 : r < Om1 := Ordinal.mod_lt c hO0
    have hqω : q < ω := (Ordinal.lt_mul_iff_div_lt hO0).1 h2
    have hq0 : q ≠ 0 := by
      intro e
      have : c < Om1 := by rw [← hdec, e, mul_zero, zero_add]; exact hr1
      exact absurd h (not_le.2 this)
    have e2 : Om1 + c = Om1 * (1 + q) + r := by rw [← hdec, ← add_assoc, mul_add, mul_one]
    have h1q : 1 + q < ω := (isPrincipal_add_omega0) one_lt_omega0 hqω
    have h1q0 : 1 + q ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
    rw [← hdec] at hp
    rw [e2, ti_comps_Om1 h1q0 h1q hr1]
    rw [ti_comps_Om1 hq0 hqω hr1] at hp
    exact hp
  · rw [Ordinal.add_eq_right_iff_mul_omega0_le.2 h2]; exact hp

/-- **`SeComm` on the Veblen codes `[Ω₁, M)`** under `TiCitPi M`. -/
theorem tiUncG {M : Ordinal.{0}} (hP : TiCitPi M) (hMG : M ≤ tfBG)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → TfCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < M → tfDat ξ ≤ D →
      Bc.bcB S n ξ < tfBG ∧ pi σ τ ξ < tfBG ∧ TfCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hGs : SC (tfBG : Ordinal.{0}) := tfBG_SC
  have hEG : (ggE : Ordinal.{0}) < tfBG := Ss.ss_E_lt_Gam.trans tf_gg_lt_BG
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ pi σ τ w < tfBG ∧ TfCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), hπ1.trans tfBG_gt, TfCl.small hπc,
      Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξM hξD
  have hξG : ξ < tfBG := hξM.trans_le hMG
  have hξcl : TfCl (Bc.bcC S (n + 1)) ξ := tf_code hc0 ξ hξG (hξD.trans_lt hDc)
  have hBξG : Bc.bcB S n ξ < tfBG := tiB_lt_BG hξcl
  have hDξ := (tiB_cl (n := n) hξcl).1
  -- facts at a smaller code `b ∈ Tᵗ[σ]` with `ssDat b ≤ D`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → tfDat b ≤ D →
      Mv.MvD S b ∧ pi σ τ b < tfBG ∧ TfCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧ Mv.MvD S (pi σ τ b) ∧
        Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbD
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 (by rw [← tfDat_small hb1]; exact hbD)
    · obtain ⟨-, a3, a4, a7⟩ := IH b hbξ hbT hb1 (hbξ.trans hξM) hbD
      have hbcl : TfCl (Bc.bcC S (n + 1)) b := tf_code hc0 b (hbξ.trans hξG) (hbD.trans_lt hDc)
      exact ⟨(tiB_cl (n := n) hbcl).1, a3, a4, (tiB_cl (n := n) a4).1, a7⟩
  rcases lt_or_ge ξ ggE with hξE | hξE
  · -- below `E₁`: `Si.siUncE`
    have hrD : rjDat ξ ≤ D := by
      rw [← ssDat_eq_rj ξ hξE, ← tfDat_eq_ss ξ (hξE.trans Ss.ss_E_lt_Gam)]; exact hξD
    obtain ⟨-, a2, a3, a4⟩ := siUncE (n := n) h hτc hDc hH ξ hξ hξ1 hξE hrD
    exact ⟨hBξG, a2.trans hEG, tfCl_of_lg hc0 (lgCl_of_GgCl a3), a4⟩
  have hξ1' : Om1 < ξ := rj_Om1_lt_E.trans_le hξE
  by_cases hEps : ω ^ ξ = ξ
  · by_cases hI : invVeblen₁ ξ < ξ
    swap
    · -- an atom `ξ = Γ_ν = ψ_{Ω₂}(c)`, `ν = Ω₁ + 1 + c`
      have hg := tf_SC_gamma hξ1' hI
      set ν := tfIdx ξ with hνdef
      have h1 : Om1 < ν := by rw [← tf_Om1_lt_gamma, hg]; exact hξ1'
      set c := ν - (Om1 + 1) with hcdef
      have hνc : Om1 + 1 + c = ν := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)
      have hcξ : c < ξ := tf_atom_lt hξ1' hξG hI
      have hdc : tfDat c = tfDat ξ := by
        have e := tfDat_gamma h1 (by rw [hg]; exact hξG); rw [hg] at e; exact e.symm
      have hgA := ti_gam_TB hP h h1 (by rw [hg]; exact hξM)
      rw [hg] at hgA
      have hνT : ν ∈ TB τ σ := hgA.1.1 hξ
      have hτν : τ ≤ ν := h.2.2.2.le.trans h1.le
      have hcT : c ∈ TB τ σ := siTB_of_comps h hνT hτν fun p hp => by rw [← hνc]; exact ti_comps_sub c p hp
      obtain ⟨hDcc, hπcG, hπccl, hDπc, hcC⟩ := hsub c hcξ hcT (hdc.le.trans hξD)
      obtain ⟨hOT, hOπ⟩ := tf_Om1_succ_TB h
      obtain ⟨-, hνπ⟩ := pi_add h hOT hcT
      rw [hνc, hOπ] at hνπ
      have hπξ : pi σ τ ξ = gamma (Om1 + 1 + pi σ τ c) := by rw [hgA.2 hνT, hνπ]
      have h1' : ∀ y, Om1 < Om1 + 1 + y := fun y => (lt_add_one _).trans_le le_self_add
      have hlt : ∀ y, y < tfBG → gamma (Om1 + 1 + y) < tfBG := fun y hy => by
        rw [← tfBG_fix]; exact gamma_lt_gamma.2 (tf_BG_indec.add_lt (SC.add_one_lt tfBG_SC tfBG_gt) hy)
      -- `B_n ξ = Γ_{Ω₁+1+B_n c}`
      have hccl : TfCl (Bc.bcC S (n + 1)) c := tf_code hc0 c (hcξ.trans hξG) ((hdc.le.trans hξD).trans_lt hDc)
      have hBcB : Bc.bcB S n c < tfBG := tiB_lt_BG hccl
      obtain ⟨-, -, hBν, hBg⟩ := tiB_gamma (n := n) h1 (by rw [hg]; exact hξG) hDcc hBcB
      rw [hg, hBν] at hBg
      -- `B_n(π ξ) = Γ_{Ω₁+1+B_n(π c)}`
      have hπcB : Bc.bcB S n (pi σ τ c) < tfBG := tiB_lt_BG hπccl
      have hπcsub : Om1 + 1 + pi σ τ c - (Om1 + 1) = pi σ τ c := Ordinal.add_sub_cancel _ _
      obtain ⟨-, -, hBν', hBg'⟩ := tiB_gamma (n := n) (h1' (pi σ τ c)) (hlt _ hπcG)
        (by rw [hπcsub]; exact hDπc) (by rw [hπcsub]; exact hπcB)
      rw [hBν', hπcsub] at hBg'
      -- the image side at the bases `B_n σ < B_n τ`
      obtain ⟨hOT', hOπ'⟩ := tf_Om1_succ_TB hB'
      obtain ⟨hν'T, hν'π⟩ := pi_add hB' hOT' hcC.1
      rw [hOπ', hcC.2] at hν'π
      have hBξM : Bc.bcB S n ξ < M := hMB n ξ hξM hξcl
      rw [hBg] at hBξM
      have hgB := ti_gam_TB hP hB' (h1' _) hBξM
      refine ⟨hBξG, by rw [hπξ]; exact hlt _ hπcG,
        by rw [hπξ]; exact TfCl.gam (TfCl.add (TfCl.add TfCl.om (TfCl.one hc0)) hπccl) (h1' _), ?_, ?_⟩
      · rw [hBg]; exact hgB.1.2 hν'T
      · rw [hBg, hgB.2 hν'T, hν'π, hπξ, hBg']
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
    obtain ⟨haD, hcD⟩ := ti_dat_phi hξ1' hξG hEps hI
    have hepsξ := ti_eps_TB hP h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
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
    have heps' := ti_eps_TB hP hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBξ]; exact hBa) (by rw [← hBξ]; exact hBc)
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
    refine ⟨hBξG, by rw [hπξ]; exact hGs.2 _ hπaG _ hπcG, by rw [hπξ]; exact TfCl.phi hπacl hπccl, ?_, ?_⟩
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
    obtain ⟨hgD, hrD⟩ := ti_dat_cnf hξ1' hξG hEps
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
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < tfBG ∧ TfCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧
        Mv.MvD S (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · -- `ω^g = g` an `ε`-number below `ξ`
        have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT (hgD.trans hξD)
      · obtain ⟨hiff, hπp⟩ := ti_opow_TB hP h hgE hgE' (hpξ.trans_lt hξM)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hπgcl, hDπg, hgC⟩ := hsub g hgξ hgT (hgD.trans hξD)
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hgcl : TfCl (Bc.bcC S (n + 1)) g := tf_code hc0 g (hgξ.trans hξG) ((hgD.trans hξD).trans_lt hDc)
        have hpcl : TfCl (Bc.bcC S (n + 1)) (ω ^ g) := TfCl.opow hc0 hgcl
        have hBgE : ggE ≤ Bc.bcB S n g := Sv.sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpM : ω ^ Bc.bcB S n g < M := by rw [← hBp]; exact hMB n _ (hpξ.trans_lt hξM) hpcl
        obtain ⟨hiff', hπp'⟩ := ti_opow_TB hP hB' hBgE hBgne hBpM
        refine ⟨hDp, by rw [hπp hgT]; exact tf_BG_inE.opow_lt hπgG, by rw [hπp hgT]; exact TfCl.opow hc0 hπgcl,
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
    have hωG : (ω : Ordinal.{0}) < tfBG := omega0_lt_inE tf_BG_inE
    refine ⟨hBξG, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact tf_BG_inE.add_lt (tf_BG_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact TfCl.add (TfCl.mul_nat hc0 hπpcl k) hπrcl
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Ti
