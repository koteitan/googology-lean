import Googology.Trans.PoR.InaccPsi.R2.VmBase

/-!
# `Se.SeComm` on `Tᵗ[σ] ∩ [Ω₁, θ)` from (a) `Vm.VmPiLev` and (b) `Vm.VmAtomMove`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `π = pi σ τ`, `K_q = Ul.UlK S 0 q`, `Hˡ_γ = Ul.ulH S 1 γ`,
`B₂ = Uc.ucB`, `θ = ConjT.th S`.  The proof of `Uf.ufUncG` with the codes `Uc.UcCl` replaced by the `K⁽⁰⁾`-closure
`K_q` (`q ≤ c_{n+1}` strongly critical), the package `Vd.VdCitPi` (`Vd.vdCitPi`, from `R2.CitedVd`) on `[B₂, θ)`,
and `Uf.ufUncG` itself below `B₂`:

* `vmUncG` (**for `ξ ∈ Tᵗ[σ] ∩ [Ω₁, θ)` in `K_q`, given `SeComm` at the countable `w ∈ Tᵗ[σ] ∩ q`: `ξ` and `π ξ`
  are in the domain of `B_n`, `π ξ < Ω₂`, and `Se.SeComm` holds at `ξ`**).  The cases on `[B₂, θ)`: a non-`ε`
  `ξ = ω^g·k + r` (`Vd.VdCitPi.opow`, `Ld.ldB_opow`), an `ε`-number `φ(a, c)` that is not an atom (`Vd.VdCitPi.eps`,
  `Mw.mwB_phi`), an atom `ξ = Hˡ_λ(y)` (`Vd.vdAtom_nf` at `σ < τ` and at `B_n σ < B_n τ`; the level `λ < Ω₂` is below
  `ξ` and handled by the induction, a level `λ ≥ Ω₂` by (a); the moves of `ξ` and of `π ξ` by (b), `Vm.vmMove`).
  The datum of `π ξ` is read from `π ξ ∈ T^σ` (`Vm.vmDat_T`), with no tracking.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vm

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Vd
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Si

variable {S : InaccSeq.{0}}

theorem vm_Om2_inE : InE (OmTwo : Ordinal.{0}) := gg_SC_eps uc_SC_Om2

theorem vm_th_lt_Om2 : ConjT.th S < OmTwo := Vj.vj_th_lt_Om2

/-- **`SeComm` on `Tᵗ[σ] ∩ [Ω₁, θ) ∩ K_q`** under (a), (b), from `SeComm` at the countable terms below `q`. -/
theorem vmUncG (hA : VmPiLev S) (hM : VmAtomMove S) {n : ℕ} {σ τ q : Ordinal.{0}} (h : Bases σ τ)
    (hσL : Sp.SpLC σ) (hτL : LtInf1 τ) (hcτ : Bc.bcC S n ≤ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hq : SC q) (hqc : q ≤ Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w < q → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < ConjT.th S → UlK S 0 q ξ →
      Mv.MvD S ξ ∧ pi σ τ ξ < OmTwo ∧ Mv.MvD S (pi σ τ ξ) ∧ Se.SeComm S n σ τ ξ := by
  have hc := vm_c_SC (S := S) n
  have hc1 := vm_c_le (S := S) n
  have hq1 : q ≤ Om 1 := hqc.trans hc1
  have hq1' : q ≤ Om1 := by rw [rj_Om1]; exact hq1
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hθ2 : ConjT.th S < OmTwo := vm_th_lt_Om2
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → UlK S 0 q w →
      Mv.MvD S w ∧ pi σ τ w < OmTwo ∧ Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwK
    have hwq : w < q := ulK_lt_W (s := 0) omega0_pos hq (by rw [Om_zero]; exact hq.1) hwK
      (by rw [Vd.vd_Om01, ← rj_Om1]; exact hw1)
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt ((hwq.trans_le hqc).trans hcL), hπ1.trans (rj_Om1_lt_E.trans_le
      (vm_E_le_B.trans ucB_lt_Om2.le)), Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwq⟩
  -- the datum of `π x` for `x ≥ B₂`
  have hπD : ∀ x ∈ TB τ σ, ucB ≤ x → pi σ τ x < OmTwo → Mv.MvD S (pi σ τ x) := fun x hx hBx hπ2 =>
    vm_D_of_K (vmDat_T h.1 hσc ((pi_bijOn h).1.mapsTo hx) (vm_OO_le_X.trans (vm_X_lt_pi h hx hBx).le) hπ2)
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξθ hK
  have hdq : vdD S 0 ξ < q := (Vg.vg_code_iffK hq).2 hK
  have hKc : UlK S 0 (Bc.bcC S (n + 1)) ξ := hK.mono hqc
  have hDξ : Mv.MvD S ξ := vm_D_of_K hKc
  rcases lt_or_ge ξ ucB with hξB | hBξ
  · -- below `B₂`: `Uf.ufUncG`
    have hDq : ucDat ξ < q := (vd_dat_uc hξB hq hq1').2 hdq
    obtain ⟨-, a2, a3, a4⟩ := Uf.ufUncG ucCitPi le_rfl (fun n ξ _ h' => Uf.ufB_lt_B h') h hτc
      (hDq.trans_le hqc) (fun w hw hw1 hwD => hH w hw hw1 (hwD.trans_lt hDq)) ξ hξ hξ1 hξB le_rfl
    exact ⟨hDξ, a2.trans ucB_lt_Om2, (Uf.ufB_cl (n := n) a3).1, a4⟩
  have hξ1' : Om1 < ξ := ucB_gt.trans_le hBξ
  have hBθ : Bc.bcB S n ξ < ConjT.th S := vm_B_lt_th hKc hξθ
  -- facts at a smaller `b ∈ Tᵗ[σ] ∩ K_q`
  have hsub : ∀ b, b < ξ → b ∈ TB τ σ → UlK S 0 q b →
      Mv.MvD S b ∧ pi σ τ b < OmTwo ∧ Mv.MvD S (pi σ τ b) ∧ Se.SeComm S n σ τ b := by
    intro b hbξ hbT hbK
    rcases lt_or_ge b Om1 with hb1 | hb1
    · exact hcnt b hbT hb1 hbK
    · exact IH b hbξ hbT hb1 (hbξ.trans hξθ) hbK
  have hξE : ggE ≤ ξ := vm_E_le_B.trans hBξ
  by_cases hEps : ω ^ ξ = ξ
  · by_cases hI : invVeblen₁ ξ < ξ
    swap
    · -- an atom `ξ = Hˡ_λ(y)`
      have hSC : SC ξ := tl_SC_of hξ1' hI
      have h1 : Om 1 < ξ := by rw [← rj_Om1]; exact hξ1'
      obtain ⟨hnf, hyξ, hlV, hiff, hπf⟩ := vdAtom_nf h hSC hBξ hξθ
      have hne := vd_nf_ex hSC h1 hξθ
      obtain ⟨-, hlD, -, -, -⟩ := vdLev_spec hSC h1 hne
      obtain ⟨hdl, hdy⟩ := (vd_nf_dat hSC h1 hξθ hq hq1).1 hdq
      obtain ⟨hπ2, hAl⟩ := hA n σ τ h hσL hτL hcτ hτc ξ hξ hSC hBξ hξθ hKc
      generalize hldef : vdLev S ξ = l at hnf hyξ hlV hiff hπf hlD hdl hdy hAl
      generalize hydef : vdI S l ξ = y at hnf hyξ hiff hπf hdy
      obtain ⟨hlT, hyT⟩ := hiff.1 hξ
      have hπξ : pi σ τ ξ = ulH S 1 (pi σ τ l) (pi σ τ y) := hπf hlT hyT
      have hlK : UlK S 0 q l := (Vg.vg_code_iffK hq).1 hdl
      have hyK : UlK S 0 q y := (Vg.vg_code_iffK hq).1 hdy
      obtain ⟨hDy, -, hDπy, hyC⟩ := hsub y hyξ hyT hyK
      -- the level: `SeComm` and `π λ < Ω₃`
      have hlev : pi σ τ l < Om (1 + 1 + 1) ∧ Se.SeComm S n σ τ l := by
        rcases lt_or_ge l OmTwo with hl2 | hl2
        · have hlK1 : UlK S 1 ξ l := (ul_vis hSC).1 hlD
          have hlξ : l < ξ := ulK_lt_W (s := 1) one_lt_omega0 hSC h1 hlK1 (by rw [← Uf.uf_Om2]; exact hl2)
          obtain ⟨-, hπl2, -, hlC⟩ := hsub l hlξ hlT hlK
          exact ⟨hπl2.trans (ucE_gt.trans vd_E_lt_V), hlC⟩
        · exact hAl hl2
      obtain ⟨hπl3, hlC⟩ := hlev
      -- the move of `ξ`
      have hXξ : tlX ≤ ξ := (uc_X_lt_B.trans_le hBξ).le
      rw [← hnf] at hKc hXξ hξθ
      obtain ⟨hBl3, hBξ'⟩ := vmMove hM hlV (by rw [hnf]; exact hyξ) hXξ hξθ hKc
      rw [hnf] at hKc hXξ hξθ hBξ'
      have hBy : Bc.bcB S n y < ulH S 1 (Bc.bcB S n l) (Bc.bcB S n y) := by
        rw [← hBξ']; exact (Mv.mvB_lt_iff hDy hDξ).2 hyξ
      have hBB2 : ucB ≤ ulH S 1 (Bc.bcB S n l) (Bc.bcB S n y) := by rw [← hBξ']; exact vm_B2_le_B hDξ hBξ
      have hBθ' : ulH S 1 (Bc.bcB S n l) (Bc.bcB S n y) < ConjT.th S := by rw [← hBξ']; exact hBθ
      have hat' := vdCitPi.atom hB' hBl3 hBy hBB2 hBθ'
      -- the move of `π ξ`
      have hπy : pi σ τ y < ulH S 1 (pi σ τ l) (pi σ τ y) := by
        rw [← hπξ, ← hnf]; exact (pi_bijOn h).2 hyT (by rw [hnf]; exact hξ) (by rw [hnf]; exact hyξ)
      have hXπ : tlX ≤ ulH S 1 (pi σ τ l) (pi σ τ y) := by rw [← hπξ]; exact (vm_X_lt_pi h hξ hBξ).le
      have hπT : pi σ τ ξ ∈ Tset σ := (pi_bijOn h).1.mapsTo hξ
      have hπθ : ulH S 1 (pi σ τ l) (pi σ τ y) < ConjT.th S := by
        rw [← hπξ]; exact uzTBound σ h.1 (h.2.2.1.trans h.2.2.2) _ hπT hπ2
      have hπK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 (pi σ τ l) (pi σ τ y)) := by
        rw [← hπξ]; exact vmDat_T h.1 hσc hπT (vm_OO_le_X.trans (vm_X_lt_pi h hξ hBξ).le) hπ2
      obtain ⟨-, hBπ⟩ := vmMove hM hπl3 hπy hXπ hπθ hπK
      refine ⟨hDξ, hπ2, hπD ξ hξ hBξ hπ2, ?_, ?_⟩
      · rw [hBξ']; exact hat'.1.2 ⟨hlC.1, hyC.1⟩
      · rw [hBξ', hat'.2 hlC.1 hyC.1, hlC.2, hyC.2, hπξ, hBπ]
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
    have hKv : UlK S 0 q (veblen a c) := by rw [hev]; exact hK
    obtain ⟨haK, hcK⟩ := Uo.uoK_veb hKv (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    have hepsξ := vdCitPi.eps h (one_le_iff_ne_zero.2 ha0) (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
      (by rw [hev]; exact hξ1') (by rw [hev]; exact hξθ)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hξ
    have hπξ : pi σ τ ξ = veblen (pi σ τ a) (pi σ τ c) := hepsξ.2 haT hcT
    obtain ⟨hDa, hπaG, hDπa, haC⟩ := hsub a haξ haT haK
    obtain ⟨hDc', hπcG, hDπc, hcC⟩ := hsub c hcξ hcT hcK
    obtain ⟨-, hBv⟩ := Mw.mwB_phi (k := n) hDa hDc' (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    rw [hev] at hBv
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
    have heps' := vdCitPi.eps hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBv]; exact hBa)
      (by rw [← hBv]; exact hBc) (by rw [← hBv]; exact hOB) (by rw [← hBv]; exact hBθ)
    rw [← hBv] at heps'
    have hπinj : ∀ y ∈ TB τ σ, pi σ τ y = pi σ τ ξ → y = ξ := fun y hy he => (pi_bijOn h).1.injOn hy hξ he
    have hπa : pi σ τ a < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => haξ.ne (hπinj a haT e)
      rw [hπξ]; exact left_le_veblen _ _
    have hπc : pi σ τ c < pi σ τ ξ := by
      refine lt_of_le_of_ne ?_ fun e => hcξ.ne (hπinj c hcT e)
      rw [hπξ]; exact right_le_veblen _ _
    rw [hπξ] at hπa hπc
    obtain ⟨-, hBπ⟩ := Mw.mwB_phi (k := n) hDπa hDπc hπa hπc
    have hπ2 : pi σ τ ξ < OmTwo := by rw [hπξ]; exact uc_SC_Om2.2 _ hπaG _ hπcG
    refine ⟨hDξ, hπ2, hπD ξ hξ hBξ hπ2, ?_, ?_⟩
    · exact heps'.1.2 ⟨haC.1, hcC.1⟩
    · rw [heps'.2 haC.1 hcC.1, haC.2, hcC.2, hπξ, hBπ]
  · -- a non-`ε` `ξ = ω^g·k + r`, `g ≥ E₁`
    have hξ0 : ξ ≠ 0 := (rj_Om1_pos.trans hξ1').ne'
    have hτξ : τ ≤ ξ := h.2.2.2.le.trans hξ1'.le
    have hcξ := si_comps_cons hξ0
    obtain ⟨k, hξk, hgK, hrK, hrξ⟩ := ulK_split hq hK hξ0
    set g := log ω ξ with hgdef
    set r := ξ % ω ^ g with hrdef
    have hgE : ggE ≤ g := le_log_of_opow_le one_lt_omega0 (by rw [Rk.rk_E_inE]; exact hξE)
    have hgξ : g < ξ := ss_log_lt hξ0 hEps
    have hpTB : ω ^ g ∈ TB τ σ := by
      refine siTB_of_comps h hξ hτξ fun p hp => ?_
      have hg0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
      rw [si_comps_cons hg0, log_opow one_lt_omega0, Ordinal.mod_self, si_comps_zero] at hp
      rw [List.mem_singleton.1 hp, hcξ]; exact List.mem_cons_self
    have hrTB : r ∈ TB τ σ := siTB_of_comps h hξ hτξ fun p hp => by
      rw [hcξ]; exact List.mem_cons_of_mem _ hp
    have hpξ : ω ^ g ≤ ξ := opow_log_le_self ω hξ0
    have hpK : UlK S 0 q (ω ^ g) := UlK.opow hgK
    -- the facts at `ω^g`
    have hpF : Mv.MvD S (ω ^ g) ∧ pi σ τ (ω ^ g) < OmTwo ∧ Mv.MvD S (pi σ τ (ω ^ g)) ∧
        Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgT hgK
      · obtain ⟨hiff, hπp⟩ := vdCitPi.opow h hgE hgE' (hpξ.trans_lt hξθ)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgG, hDπg, hgC⟩ := hsub g hgξ hgT hgK
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hBgE : ggE ≤ Bc.bcB S n g := Sv.sv_B_geE hDg hgE
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpθ : ω ^ Bc.bcB S n g < ConjT.th S := by
          rw [← hBp]; exact vm_B_lt_th (hpK.mono hqc) (hpξ.trans_lt hξθ)
        obtain ⟨hiff', hπp'⟩ := vdCitPi.opow hB' hBgE hBgne hBpθ
        refine ⟨hDp, by rw [hπp hgT]; exact vm_Om2_inE.opow_lt hπgG, by rw [hπp hgT]; exact hDπp, ?_, ?_⟩
        · rw [hBp]; exact hiff'.2 hgC.1
        · rw [hBp, hπp' hgC.1, hgC.2, hπp hgT, hBπp]
    obtain ⟨hDp', hπpG, hDπp', hpC⟩ := hpF
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
        exact ⟨h0T, pi_lt h h0σ, hD0, hD0, hH 0 h0T rj_Om1_pos hq.1⟩
      | succ j ih =>
        obtain ⟨hT, hπ, hD, hDπ, hC⟩ := ih
        rw [Nat.cast_succ, mul_add_one, mul_add_one]
        obtain ⟨hsT, hsπ⟩ := pi_add h hT hpTB
        refine ⟨hsT, by rw [hsπ, hπ], (Mv.mvB_add (k := n) hD hDp').1, (Mv.mvB_add (k := n) hDπ hDπp').1, ?_⟩
        exact siComm_add h hτc hT hpTB hD hDp' (by rw [hπ]; exact hDπ) hDπp' hC hpC
    -- the remainder
    obtain ⟨hDr, hπrG, hDπr, hrC⟩ := hsub r hrξ hrTB hrK
    obtain ⟨hkT, hkπ, hkD, hkDπ, hkC⟩ := hmul k
    have hπξ : pi σ τ ξ = pi σ τ (ω ^ g) * k + pi σ τ r := by
      conv_lhs => rw [← hξk]
      rw [(pi_add h hkT hrTB).2, hkπ]
    have hωG : (ω : Ordinal.{0}) < OmTwo := omega0_lt_inE vm_Om2_inE
    refine ⟨hDξ, ?_, ?_, ?_⟩
    · rw [hπξ]
      exact vm_Om2_inE.add_lt (vm_Om2_inE.mul_lt hπpG ((natCast_lt_omega0 k).trans hωG)) hπrG
    · rw [hπξ]; exact (Mv.mvB_add (k := n) hkDπ hDπr).1
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

end Googology.Trans.PoR.InaccPsi.R2.Vm
