import Googology.Trans.PoR.InaccPsi.R2.VsPkg

/-!
# `Se.SeComm` on `Tᵗ[σ] ∩ Ω_ω` by one induction across the cardinal levels

`B_n = Bc.bcB S n`, `c' = c_{n+1} = Bc.bcC S (n + 1)`, `π = pi σ τ`, `K⁽ⁱ⁾_q = Ul.UlK S i q`, `Hˡ⁽ˢ⁾_γ = Ul.ulH S s γ`,
`B₂ = Uc.ucB`, `θ = ConjT.th S`, `E = Ω_{r+1}` (`r` finite).  The proof of `Vm.vmUncG` with the hypothesis (a)
`Vm.VmPiLev` replaced by the induction itself: an atom `ξ = Hˡ⁽ˢ⁾_λ(y)` of `(Ω_s, Ω_{s+1})` whose level `λ ≥ Ω_{s+1}`
is handled one cardinal up, by the same proof at `s + 1`.  The induction runs along `μ_r = Vs.vsMu S r` (`Vs.vs_wf`):
the parts `c < ξ` of `ξ` (`Vs.VsSub`) and the level `λ` (`Vs.vs_lex_lev`) are below `ξ`.  The bound `VsG S r ξ`
(`ξ ∈ K⁽ⁱ⁾_{ψ_{Ω_{i+1}}(E)}` for every finite `i ≥ 1`) passes to the parts and to the level (`Vs.vs_lev_bound`), and
keeps every level below `E`.

* `VsP S n σ τ x` (**`x ∈ MvD`, `π x ∈ K⁽⁰⁾_{c'}`, `SeComm` at `x`**), `VsG S r x` (**the bound**);
* `vs_sub_of_low` (**a part on the levels below `s` and `≤ ξ` is a part**), `vs_level` (**the cardinal level**),
  `vs_lev_G` (**the bound passes to a level `λ ≥ Ω_{s+1}`, and `λ < Ω_{r+1}`**);
* `vsStep` (**one atom / `ε`-number / `ω^g`-sum of `[L, U)` at the cardinal `Ω_{s+1}`, given `VsP` at its parts and
  at its level when that level is `≥ Ω_{s+1}`**, for a package `Vs.VsPkg S s L U G`);
* `vsComm` (**for bases `σ < τ < c'`, a strongly critical `q ≤ c'`, and `SeComm` at the countable `w ∈ Tᵗ[σ] ∩ q`:
  `VsP` at every `ξ ∈ Tᵗ[σ] ∩ K⁽⁰⁾_q ∩ Ω_{r+1}` with `VsG S r ξ`**).

No new axiom.  New definitions: `VsP`, `VsG` (Props).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Si

variable {S : InaccSeq.{0}}

/-- `x ∈ MvD`, `π x ∈ K⁽⁰⁾_{c_{n+1}}`, and `SeComm` at `x`. -/
def VsP (S : InaccSeq.{0}) (n : ℕ) (σ τ x : Ordinal.{0}) : Prop :=
  Mv.MvD S x ∧ UlK S 0 (Bc.bcC S (n + 1)) (pi σ τ x) ∧ Se.SeComm S n σ τ x

/-- The bound: `x ∈ K⁽ⁱ⁾_{ψ_{Ω_{i+1}}(Ω_{r+1})}` for every finite `i ≥ 1`. -/
def VsG (S : InaccSeq.{0}) (r : ℕ) (x : Ordinal.{0}) : Prop :=
  ∀ i : Ordinal.{0}, 1 ≤ i → i < ω → UlK S i (S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (i + 1))) x

/-- **A part on the levels below `s` and `≤ ξ < Ω_{s+1}` is a part.** -/
theorem vs_sub_of_low {s c ξ : Ordinal.{0}}
    (hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q, SC q → Om i < q → q ≤ Om (i + 1) → UlK S i q ξ → UlK S i q c)
    (hcξ : c ≤ ξ) (hξW : ξ < Om (s + 1)) : VsSub S c ξ := by
  intro i hi1 hi q hq hLq hqW hK
  rcases lt_or_ge i s with his | hsi
  · exact hlow i hi1 his q hq hLq hqW hK
  rcases hsi.lt_or_eq with hsi | hsi
  · refine UlK.small ((hcξ.trans_lt hξW).trans_le ((Om_le_Om.2 ?_).trans hLq.le))
    exact Order.add_one_le_of_lt hsi
  · subst hsi
    exact UlK.small (hcξ.trans_lt (ulK_lt_W hi hq hLq hK hξW))

/-- **The cardinal level**: for `Ω₁ ≤ ξ < Ω_{r+1}` there is `k < r` with `Ω_{k+1} ≤ ξ < Ω_{k+2}`. -/
theorem vs_level {r : ℕ} {ξ : Ordinal.{0}} (h1 : Om 1 ≤ ξ) (hr : ξ < Om ((r : Ordinal.{0}) + 1)) :
    ∃ k : ℕ, k < r ∧ Om ((k : Ordinal.{0}) + 1) ≤ ξ ∧ ξ < Om ((k : Ordinal.{0}) + 1 + 1) := by
  classical
  have hex : ∃ j : ℕ, ξ < Om ((j : Ordinal.{0}) + 1) := ⟨r, hr⟩
  set j0 := Nat.find hex with hj0
  have hj : ξ < Om ((j0 : Ordinal.{0}) + 1) := Nat.find_spec hex
  have hjr : j0 ≤ r := Nat.find_min' hex hr
  rcases Nat.eq_zero_or_eq_succ_pred j0 with h0 | h0
  · rw [h0, Nat.cast_zero, zero_add] at hj
    exact absurd h1 (not_le.2 hj)
  · set k := j0.pred
    have hk : ¬ ξ < Om ((k : Ordinal.{0}) + 1) := Nat.find_min hex (by omega)
    refine ⟨k, by omega, not_lt.1 hk, ?_⟩
    have e : ((j0 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 := by rw [h0]; push_cast; rfl
    rw [e] at hj
    exact hj

/-- **The bound passes to a level one cardinal up**: for an atom `ξ = Hˡ⁽ˢ⁾_λ(y) < ψ_{Ω_{s+1}}(E)` with `VsG S r ξ`
and `λ ≥ Ω_{s+1}`: `VsG S r λ` and `λ < E` (`E = Ω_{r+1}`; `Vs.vs_lev_bound`). -/
theorem vs_lev_G {r : ℕ} {s l y : Ordinal.{0}} (hs : s < ω) (hlV : l < Om (s + 1 + 1)) (hy : y < ulH S s l y)
    (hlW : Om (s + 1) ≤ l) (hG : VsG S r (ulH S s l y))
    (hE : ulH S s l y < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1))) :
    VsG S r l ∧ l < Om ((r : Ordinal.{0}) + 1) := by
  have hHW : ulH S s l y < Om (s + 1) := hE.trans (Ui.ui_psi_lt (s := s) _)
  obtain ⟨hlψ, hlE⟩ := vs_lev_bound hs hlV hy hE
  have hl0 : l ≠ 0 := (lt_of_lt_of_le (Ui.ui_SC_W _).1 hlW).ne'
  have hWE := hlE hl0
  refine ⟨fun i hi1 hi => ?_, hlV.trans_le (Om_le_Om.2 (Order.add_one_le_of_lt (Om_lt_Om.1 hWE)))⟩
  rcases lt_or_ge i s with his | hsi
  · exact ((vs_atom_parts hs his (Ui.ui_psi_SC (s := i) _) (Ui.ui_psi_lt (s := i) _).le hlV hy hHW).1.1
      (hG i hi1 hi)).1
  rcases hsi.lt_or_eq with hsi | hsi
  · refine UlK.small ?_
    rcases (Order.add_one_le_of_lt hsi).lt_or_eq with hsi' | hsi'
    · exact hlV.trans_le ((Om_le_Om.2 (Order.add_one_le_of_lt hsi')).trans (Ui.ui_L_lt_psi (s := i) _).le)
    · rw [← hsi']; exact hlψ
  · subst hsi; exact ((ul_vis (ulH_SC l y)).1 (ulH_D_lt l y)).mono hE.le

section Step

variable {n : ℕ} {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1)) (hq : SC q)
  (hqc : q ≤ Bc.bcC S (n + 1))
include h hτc hq hqc

/-- **One step at the cardinal `Ω_{s+1}`**: for `ξ ∈ Tᵗ[σ] ∩ [L, U) ∩ K⁽⁰⁾_q` with `Ω_s < ξ < ψ_{Ω_{s+1}}(E) ≤ U`
(`E = Ω_{r+1}`), given `VsP` at its parts `c < ξ` and at its level `λ ≥ Ω_{s+1}` when `ξ` is an atom: `VsP` at `ξ`. -/
theorem vsStep {s L U G : Ordinal.{0}} {r : ℕ} (hP : VsPkg S s L U G) (hs : s < ω) (hs1 : 1 ≤ s)
    (hLB : ∀ x, Mv.MvD S x → L ≤ x → L ≤ Bc.bcB S n x) (hGB : ∀ g, Mv.MvD S g → G ≤ g → G ≤ Bc.bcB S n g)
    (hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) ≤ U)
    {ξ : Ordinal.{0}} (hξ : ξ ∈ TB τ σ) (hLξ : L ≤ ξ) (hGξ : ω ^ G ≤ ξ) (hsξ : Om s < ξ)
    (hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1))) (hK : UlK S 0 q ξ)
    (hsub : ∀ b, b < ξ → VsSub S b ξ → b ∈ TB τ σ → UlK S 0 q b → VsP S n σ τ b)
    (hlev : ∀ l y, l < Om (s + 1 + 1) → y < ulH S s l y → ulH S s l y = ξ → Om (s + 1) ≤ l → l ∈ TB τ σ →
      UlK S 0 q l → VsP S n σ τ l) :
    VsP S n σ τ ξ := by
  have hs0 : s ≠ 0 := (lt_of_lt_of_le zero_lt_one hs1).ne'
  have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hc := Vm.vm_c_SC (S := S) n
  have hc1 := Vm.vm_c_le (S := S) n
  have hc01 : Bc.bcC S (n + 1) ≤ Om (0 + 1) := by rw [zero_add]; exact hc1
  have hq01 : q ≤ Om (0 + 1) := hqc.trans hc01
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hB' := Se.seBases_img h hτc
  have hKc : UlK S 0 (Bc.bcC S (n + 1)) ξ := hK.mono hqc
  have hDξ : Mv.MvD S ξ := Vm.vm_D_of_K hKc
  have hξW : ξ < Om (s + 1) := hξE.trans (Ui.ui_psi_lt (s := s) _)
  have hξU : ξ < U := hξE.trans_le hUE
  -- `B_n ξ < ψ_W(E) ≤ U`
  have hr : ((r : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega r
  obtain ⟨hDE, hBE⟩ := vsW_D (S := S) (n := n) (natCast_lt_omega0 r)
  have hEown : Om ((r : Ordinal.{0}) + 1) ∈ S.CSet (Om ((r : Ordinal.{0}) + 1))
      (S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1))) := Ui.ui_W_mem (natCast_lt_omega0 r) _ _
  obtain ⟨hDψE, hBψE, -⟩ := vsB_psi (n := n) hs hs0 hDE hEown
  rw [hBE] at hBψE
  have hBξU : Bc.bcB S n ξ < U := by
    have := (Mv.mvB_lt_iff (k := n) hDξ hDψE).2 hξE
    rw [hBψE] at this
    exact this.trans_le hUE
  have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le hsξ).ne'
  rcases vsShape (S := S) hs hs1 hsξ hξE with ⟨hEps, -, hgξ⟩ | ⟨hEps, -, ha1, haξ, hcξ, hev⟩ | ⟨hSC, hnf, hyξ, hlV, hlK⟩
  · -- a non-`ε` `ξ = ω^g·k + r`
    have hτξ : τ ≤ ξ := h.2.2.2.le.trans ((Rj.rj_Om1.symm ▸ (Om_le_Om.2 hs1)).trans hsξ.le)
    have hcξ := si_comps_cons hξ0
    obtain ⟨k, hξk, hgK, hrK, hrξ⟩ := ulK_split hq hK hξ0
    set g := log ω ξ with hgdef
    set r' := ξ % ω ^ g with hrdef
    have hGg : G ≤ g := le_log_of_opow_le one_lt_omega0 hGξ
    have hpTB : ω ^ g ∈ TB τ σ := by
      refine siTB_of_comps h hξ hτξ fun p hp => ?_
      have hg0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
      rw [si_comps_cons hg0, log_opow one_lt_omega0, Ordinal.mod_self, si_comps_zero] at hp
      rw [List.mem_singleton.1 hp, hcξ]; exact List.mem_cons_self
    have hrTB : r' ∈ TB τ σ := siTB_of_comps h hξ hτξ fun p hp => by
      rw [hcξ]; exact List.mem_cons_of_mem _ hp
    have hpξ : ω ^ g ≤ ξ := opow_log_le_self ω hξ0
    have hgsub : VsSub S g ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S r' ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' g
    have hpF : Mv.MvD S (ω ^ g) ∧ UlK S 0 (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) ∧ Se.SeComm S n σ τ (ω ^ g) := by
      by_cases hgE' : ω ^ g = g
      · have hgT : g ∈ TB τ σ := by rw [← hgE']; exact hpTB
        rw [hgE']
        exact hsub g hgξ hgsub hgT hgK
      · obtain ⟨hiff, hπp⟩ := hP.opow h hGg hgE' (hpξ.trans_lt hξU)
        have hgT : g ∈ TB τ σ := hiff.1 hpTB
        obtain ⟨hDg, hπgK, hgC⟩ := hsub g hgξ hgsub hgT hgK
        have hDπg : Mv.MvD S (pi σ τ g) := Vm.vm_D_of_K hπgK
        obtain ⟨hDp, hBp⟩ := Ld.ldB_opow (n := n) hDg
        obtain ⟨hDπp, hBπp⟩ := Ld.ldB_opow (n := n) hDπg
        have hBgne : ω ^ Bc.bcB S n g ≠ Bc.bcB S n g := by
          intro e
          rw [← hBp] at e
          rcases lt_trichotomy (ω ^ g) g with hl | hl | hl
          · exact absurd e ((Mv.mvB_lt_iff hDp hDg).2 hl).ne
          · exact hgE' hl
          · exact absurd e ((Mv.mvB_lt_iff hDg hDp).2 hl).ne'
        have hBpU : ω ^ Bc.bcB S n g < U := by
          rw [← hBp]
          rcases hpξ.lt_or_eq with hl | hl
          · exact ((Mv.mvB_lt_iff hDp hDξ).2 hl).trans hBξU
          · rw [hl]; exact hBξU
        obtain ⟨hiff', hπp'⟩ := hP.opow hB' (hGB g hDg hGg) hBgne hBpU
        refine ⟨hDp, by rw [hπp hgT]; exact UlK.opow hπgK, ?_, ?_⟩
        · rw [hBp]; exact hiff'.2 hgC.1
        · rw [hBp, hπp' hgC.1, hgC.2, hπp hgT, hBπp]
    obtain ⟨hDp', hπpK, hpC⟩ := hpF
    have hDπp' : Mv.MvD S (pi σ τ (ω ^ g)) := Vm.vm_D_of_K hπpK
    have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (Lw.lw_L_SC S ω).1
    have hmul : ∀ j : ℕ, ω ^ g * j ∈ TB τ σ ∧ pi σ τ (ω ^ g * j) = pi σ τ (ω ^ g) * j ∧
        Mv.MvD S (ω ^ g * j) ∧ Mv.MvD S (pi σ τ (ω ^ g) * j) ∧ Se.SeComm S n σ τ (ω ^ g * j) := by
      intro j
      induction j with
      | zero =>
        simp only [Nat.cast_zero, mul_zero]
        have h0T := mem_TB_of_lt h h0σ
        have h0q : (0 : Ordinal.{0}) < q := hq.1
        refine ⟨h0T, pi_lt h h0σ, hD0, hD0, ?_⟩
        obtain ⟨-, -, hC0⟩ := hsub 0 (lt_of_le_of_lt zero_le hsξ) (fun _ _ _ _ _ _ _ _ => UlK.zero) h0T UlK.zero
        exact hC0
      | succ j ih =>
        obtain ⟨hT, hπ, hD, hDπ, hC⟩ := ih
        rw [Nat.cast_succ, mul_add_one, mul_add_one]
        obtain ⟨hsT, hsπ⟩ := pi_add h hT hpTB
        refine ⟨hsT, by rw [hsπ, hπ], (Mv.mvB_add (k := n) hD hDp').1, (Mv.mvB_add (k := n) hDπ hDπp').1, ?_⟩
        exact siComm_add h hτc hT hpTB hD hDp' (by rw [hπ]; exact hDπ) hDπp' hC hpC
    obtain ⟨hDr, hπrK, hrC⟩ := hsub r' hrξ hrsub hrTB hrK
    have hDπr : Mv.MvD S (pi σ τ r') := Vm.vm_D_of_K hπrK
    obtain ⟨hkT, hkπ, hkD, hkDπ, hkC⟩ := hmul k
    have hπξ : pi σ τ ξ = pi σ τ (ω ^ g) * k + pi σ τ r' := by
      conv_lhs => rw [← hξk]
      rw [(pi_add h hkT hrTB).2, hkπ]
    refine ⟨hDξ, ?_, ?_⟩
    · rw [hπξ]; exact UlK.add (UlK.mul_nat hπpK k) hπrK
    · rw [← hξk]
      exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC
  · -- an `ε`-number `ξ = φ(a, c)`
    set a := invVeblen₁ ξ with hadef
    set c := invVeblen₂ ξ with hcdef
    have hKv : UlK S 0 q (veblen a c) := by rw [hev]; exact hK
    obtain ⟨haK, hcK⟩ := Uo.uoK_veb hKv (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    have hasub : VsSub S a ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
    have hcsub : VsSub S c ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
    have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
      (by rw [hev]; exact hξU)
    rw [hev] at hepsξ
    obtain ⟨haT, hcT⟩ := hepsξ.1.1 hξ
    have hπξ : pi σ τ ξ = veblen (pi σ τ a) (pi σ τ c) := hepsξ.2 haT hcT
    obtain ⟨hDa, hπaK, haC⟩ := hsub a haξ hasub haT haK
    obtain ⟨hDc', hπcK, hcC⟩ := hsub c hcξ hcsub hcT hcK
    have hDπa := Vm.vm_D_of_K hπaK
    have hDπc := Vm.vm_D_of_K hπcK
    obtain ⟨-, hBv⟩ := Mw.mwB_phi (k := n) hDa hDc' (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    rw [hev] at hBv
    have hBa : Bc.bcB S n a < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDa hDξ).2 haξ
    have hBc : Bc.bcB S n c < Bc.bcB S n ξ := (Mv.mvB_lt_iff hDc' hDξ).2 hcξ
    have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (lt_of_le_of_lt zero_le hcL)
    have ha0 : a ≠ 0 := (lt_of_lt_of_le zero_lt_one ha1).ne'
    have hBa0 : Bc.bcB S n a ≠ 0 := by
      intro e
      have h1 := (Mv.mvB_lt_iff (k := n) hD0 hDa).2 (pos_iff_ne_zero.2 ha0)
      rw [Bc.bcB_zero, e] at h1
      exact lt_irrefl _ h1
    have heps' := hP.eps hB' (one_le_iff_ne_zero.2 hBa0) (by rw [← hBv]; exact hBa)
      (by rw [← hBv]; exact hBc) (by rw [← hBv]; exact hLB ξ hDξ hLξ) (by rw [← hBv]; exact hBξU)
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
    refine ⟨hDξ, by rw [hπξ]; exact UlK.phi hπaK hπcK, ?_, ?_⟩
    · exact heps'.1.2 ⟨haC.1, hcC.1⟩
    · rw [heps'.2 haC.1 hcC.1, haC.2, hcC.2, hπξ, hBπ]
  · -- an atom `ξ = Hˡ⁽ˢ⁾_λ(y)`
    set l := Vp.vpLev S s ξ with hldef
    set y := Vp.vpI S s l ξ with hydef
    have hy : y < ulH S s l y := by rw [hnf]; exact hyξ
    have hHW : ulH S s l y < Om (s + 1) := by rw [hnf]; exact hξW
    have hparts : ∀ i q', i < s → SC q' → q' ≤ Om (i + 1) →
        (UlK S i q' (ulH S s l y) ↔ UlK S i q' l ∧ UlK S i q' y) := fun i q' his hq' hq'L =>
      (vs_atom_parts hs his hq' hq'L hlV hy hHW).1
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q', SC q' → Om i < q' → q' ≤ Om (i + 1) →
        UlK S i q' ξ → UlK S i q' l ∧ UlK S i q' y := fun i _ his q' hq' _ hq'L hK' =>
      (hparts i q' his hq' hq'L).1 (by rw [hnf]; exact hK')
    obtain ⟨hlK0, hyK0⟩ := (hparts 0 q h0s hq hq01).1 (by rw [hnf]; exact hK)
    have hat := hP.atom h hlV hy (by rw [hnf]; exact hLξ) (by rw [hnf]; exact hξU)
    rw [hnf] at hat
    obtain ⟨hlT, hyT⟩ := hat.1.1 hξ
    have hπξ : pi σ τ ξ = ulH S s (pi σ τ l) (pi σ τ y) := hat.2 hlT hyT
    obtain ⟨hDy, hπyK, hyC⟩ :=
      hsub y hyξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' => (hlow i hi1 his q' hq' hLq hqW hK').2)
        hyξ.le hξW) hyT hyK0
    -- the level
    have hlP : VsP S n σ τ l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC hsξ hlK hlW
        exact hsub l hlξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le hξW) hlT hlK0
      · exact hlev l y hlV hy hnf hlW hlT hlK0
    obtain ⟨hDl, hπlK, hlC⟩ := hlP
    have hs1' : s + 1 < ω := Ui.ui_s1_lt_omega hs
    have hπlV : pi σ τ l < Om (s + 1 + 1) := vs_pi_lt_Om h hs1' le_add_self hlT hlV
    have hπy : pi σ τ y < ulH S s (pi σ τ l) (pi σ τ y) := by
      rw [← hπξ]; exact (pi_bijOn h).2 hyT hξ hyξ
    have hπW : ulH S s (pi σ τ l) (pi σ τ y) < Om (s + 1) := by
      rw [← hπξ]; exact vs_pi_lt_Om h hs hs1 hξ hξW
    have hπK : UlK S 0 (Bc.bcC S (n + 1)) (pi σ τ ξ) := by
      rw [hπξ]
      exact (vs_atom_parts hs h0s hc hc01 hπlV hπy hπW).1.2 ⟨hπlK, hπyK⟩
    -- the move of `ξ`
    have hHE : ulH S s l y < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) := by rw [hnf]; exact hξE
    have hHK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S s l y) := by rw [hnf]; exact hKc
    obtain ⟨hBl3, hBξ'⟩ := vsMove hs hs1 hlV hy hHE hHK
    rw [hnf] at hBξ'
    have hBy : Bc.bcB S n y < ulH S s (Bc.bcB S n l) (Bc.bcB S n y) := by
      rw [← hBξ']; exact (Mv.mvB_lt_iff hDy hDξ).2 hyξ
    have hat' := hP.atom hB' hBl3 hBy (by rw [← hBξ']; exact hLB ξ hDξ hLξ) (by rw [← hBξ']; exact hBξU)
    -- the move of `π ξ`
    have hDπξ : Mv.MvD S (pi σ τ ξ) := Vm.vm_D_of_K hπK
    obtain ⟨a', ha'⟩ := mem_iUnion.1 hDπξ.1
    have hπA : ulH S s (pi σ τ l) (pi σ τ y) < S.psi a' (Om (s + 1)) := by
      rw [← hπξ]; exact lt_psi_of_mem hκ (CSet_mono le_rfl zero_le ha') (hπξ ▸ hπW)
    obtain ⟨-, hBπ⟩ := vsMove hs hs1 hπlV hπy hπA (by rw [← hπξ]; exact hπK)
    refine ⟨hDξ, hπK, ?_, ?_⟩
    · rw [hBξ']; exact hat'.1.2 ⟨hlC.1, hyC.1⟩
    · rw [hBξ', hat'.2 hlC.1 hyC.1, hlC.2, hyC.2, hπξ, hBπ]

/-- **`VsP` on `Tᵗ[σ] ∩ K⁽⁰⁾_q ∩ Ω_{r+1}` under the bound `VsG S r`**, for bases `σ < τ < c_{n+1}`, a strongly critical
`q ≤ c_{n+1}`, and `SeComm` at the countable `w ∈ Tᵗ[σ] ∩ q`.  Below `B₂` (at `Ω₁`): `Uf.ufUncG`; on `[B₂, Ω₂)`:
`vsStep` with `Vs.vsPkg_one`; `Ω_s` (`s ≥ 2`): `R2.vsOm_TB`; on `(Ω_s, Ω_{s+1})`, `s ≥ 2`: `vsStep` with
`Vs.vsPkg_gen`; the level of an atom one cardinal up by the induction along `Vs.vsMu S r`. -/
theorem vsComm (hH : ∀ w ∈ TB τ σ, w < Om1 → w < q → Se.SeComm S n σ τ w) (r : ℕ) :
    ∀ ξ, ξ ∈ TB τ σ → UlK S 0 q ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → VsP S n σ τ ξ := by
  have hc := Vm.vm_c_SC (S := S) n
  have hc1 := Vm.vm_c_le (S := S) n
  have hc1' : Bc.bcC S (n + 1) ≤ Om1 := by rw [Rj.rj_Om1]; exact hc1
  have hq1' : q ≤ Om1 := hqc.trans hc1'
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  have hrω : ((r : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega r
  have hEω : Om ((r : Ordinal.{0}) + 1) ≤ Om ω := Om_le_Om.2 hrω.le
  intro ξ
  refine (vs_wf (S := S) r).induction (C := fun ξ => ξ ∈ TB τ σ → UlK S 0 q ξ → VsG S r ξ →
    ξ < Om ((r : Ordinal.{0}) + 1) → VsP S n σ τ ξ) ξ ?_
  intro ξ IH hξ hK hG hr
  have hGsub : ∀ b, VsSub S b ξ → VsG S r b := fun b hb i hi1 hi =>
    hb i hi1 hi _ (Ui.ui_psi_SC (s := i) _) (Ui.ui_L_lt_psi (s := i) _) (Ui.ui_psi_lt (s := i) _).le (hG i hi1 hi)
  have hsub : ∀ b, b < ξ → VsSub S b ξ → b ∈ TB τ σ → UlK S 0 q b → VsP S n σ τ b :=
    fun b hbξ hbs hbT hbK => IH b (vs_lex_sub r hbs hbξ) hbT hbK (hGsub b hbs) (hbξ.trans hr)
  rcases lt_or_ge ξ Om1 with hξ1 | hξ1
  · -- countable
    have hξq : ξ < q := ulK_lt_W (s := 0) omega0_pos hq (by rw [Om_zero]; exact hq.1) hK
      (by rw [Vd.vd_Om01, ← Rj.rj_Om1]; exact hξ1)
    have hπ1 : pi σ τ ξ < Om1 := down_lt_Om1 h hξ hξ1
    have hπc : pi σ τ ξ < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hξ) hπ1
    exact ⟨Mv.mvD_of_lt ((hξq.trans_le hqc).trans hcL), UlK.small hπc, hH ξ hξ hξ1 hξq⟩
  obtain ⟨k, hkr, hk1, hk2⟩ := vs_level (r := r) (by rw [← Rj.rj_Om1]; exact hξ1) hr
  have hs : ((k : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega k
  have hs1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 := le_add_self
  have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG _ hs1 hs) hk2
  -- the level of an atom, one cardinal up
  have hlev : ∀ l y, l < Om ((k : Ordinal.{0}) + 1 + 1 + 1) → y < ulH S ((k : Ordinal.{0}) + 1) l y →
      ulH S ((k : Ordinal.{0}) + 1) l y = ξ → Om ((k : Ordinal.{0}) + 1 + 1) ≤ l → l ∈ TB τ σ →
      UlK S 0 q l → VsP S n σ τ l := by
    intro l y hlV hy hnf hlW hlT hlK
    have hSC : SC ξ := hnf ▸ ulH_SC l y
    have hsξ : Om ((k : Ordinal.{0}) + 1) < ξ := hnf ▸ ulH_gt l y
    have hHW : ulH S ((k : Ordinal.{0}) + 1) l y < Om ((k : Ordinal.{0}) + 1 + 1) := by rw [hnf]; exact hk2
    have hHE : ulH S ((k : Ordinal.{0}) + 1) l y <
        S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) := by rw [hnf]; exact hξE
    obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) hHE
    have hlK1 : UlK S ((k : Ordinal.{0}) + 1) ξ l := by
      rw [← hnf]; exact (ul_vis (ulH_SC l y)).1 (ulH_D_lt l y)
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < (k : Ordinal.{0}) + 1 → ∀ q', SC q' → Om i < q' →
        q' ≤ Om (i + 1) → UlK S i q' ξ → UlK S i q' l := fun i _ his q' hq' _ hq'L hK' => by
      rw [← hnf] at hK'; exact ((vs_atom_parts hs his hq' hq'L hlV hy hHW).1.1 hK').1
    have hlex := vs_lex_lev hkr hlow hlK1 hSC hsξ hk2
    exact IH l hlex hlT hlK hGl hlr
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- the cardinal `Ω₁`
    have hs1e : ((k : Ordinal.{0}) + 1) = 1 := by rw [hk0, Nat.cast_zero, zero_add]
    rcases lt_or_ge ξ ucB with hξB | hξB
    · have hdq : Vd.vdD S 0 ξ < q := (Vg.vg_code_iffK hq).2 hK
      have hDq : ucDat ξ < q := (Vd.vd_dat_uc hξB hq hq1').2 hdq
      obtain ⟨-, a2, a3, a4⟩ := Uf.ufUncG ucCitPi le_rfl (fun n ξ _ h' => Uf.ufB_lt_B h') h hτc
        (hDq.trans_le hqc) (fun w hw hw1 hwD => hH w hw hw1 (hwD.trans_lt hDq)) ξ hξ hξ1 hξB le_rfl
      exact ⟨Vm.vm_D_of_K (hK.mono hqc), (Uo.uo_cl_iffK hc hc1' a2).1 a3, a4⟩
    · have hP : VsPkg S ((k : Ordinal.{0}) + 1) ucB (ConjT.th S) Gg.ggE := by rw [hs1e]; exact vsPkg_one
      have hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) ≤ ConjT.th S := by
        rw [hs1e]; exact (psi_mono (InR_Om_succ 1) hEω).1
      have hGξ : ω ^ Gg.ggE ≤ ξ := by rw [Rk.rk_E_inE]; exact Vm.vm_E_le_B.trans hξB
      have hsξ : Om ((k : Ordinal.{0}) + 1) < ξ := by rw [hs1e]; exact Vd.vd_Om1_lt_B.trans_le hξB
      exact vsStep h hτc hq hqc hP hs hs1 (fun x hx hL => Vm.vm_B2_le_B hx hL) (fun g hg hGg => Sv.sv_B_geE hg hGg)
        hUE hξ hξB hGξ hsξ hξE hK hsub hlev
  · -- the cardinals `Ω_s`, `s ≥ 2`
    have hs2 : (1 : Ordinal.{0}) < (k : Ordinal.{0}) + 1 := by exact_mod_cast Nat.succ_lt_succ hk0
    obtain ⟨hDO, hBO⟩ := vsW_D (S := S) (n := n) (natCast_lt_omega0 k)
    have hOB : ∀ x, Mv.MvD S x → Om ((k : Ordinal.{0}) + 1) ≤ x →
        Om ((k : Ordinal.{0}) + 1) ≤ Bc.bcB S n x := fun x hx hle => by
      rcases hle.lt_or_eq with hlt | heq
      · have := (Mv.mvB_lt_iff (k := n) hDO hx).2 hlt; rw [hBO] at this; exact this.le
      · rw [← heq, hBO]
    rcases hk1.lt_or_eq with hlt | heq
    · have hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) ≤
          S.psi (Om ω) (Om ((k : Ordinal.{0}) + 1 + 1)) := (psi_mono (InR_Om_succ _) hEω).1
      have hΩE : ω ^ (Om ((k : Ordinal.{0}) + 1) : Ordinal.{0}) = Om ((k : Ordinal.{0}) + 1) :=
        Ui.ui_W_opow (k : Ordinal.{0})
      exact vsStep h hτc hq hqc (vsPkg_gen hs hs2) hs hs1 hOB hOB hUE hξ hlt.le (by rw [hΩE]; exact hlt.le) hlt
        hξE hK hsub hlev
    · -- `ξ = Ω_s`
      subst heq
      obtain ⟨hT, hπ⟩ := vsOm_TB h hs hs2
      obtain ⟨hT', hπ'⟩ := vsOm_TB hB' hs hs2
      refine ⟨hDO, by rw [hπ]; exact Us.us_K_Om (natCast_lt_omega0 k), ?_, ?_⟩
      · rw [hBO]; exact hT'
      · rw [hBO, hπ', hπ, hBO]

end Step

end Googology.Trans.PoR.InaccPsi.R2.Vs
