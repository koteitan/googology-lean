import Googology.Trans.PoR.InaccPsi.R2.VsTop
import Googology.Trans.PoR.InaccPsi.R2.UyFix
import Googology.Trans.PoR.InaccPsi.R2.WwGap
import Googology.Trans.PoR.InaccPsi.R2.CitedXe

/-!
# The node lemmas of `Uy.UyFix` at constant levels below `θ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `K⁽⁰⁾_q = Ul.UlK S 0 q`, `d_S = Vd.vdD S 0`, `B₂ = Uc.ucB`, `θ = ConjT.th S`.  The node lemmas of
`R2.UyFix` (`uy_pi_fix`, `uy_Om1_mul_TB`, `uy_arg_T`, `uyLt_vt_self`, `uyVt_tr`) are stated for levels `Ω₁·M < B₂`.
Here they are proved for every constant level `Ω₁·M < θ`:

* `xe_twin_disj` (**the ranges of `R2.uvVt_trL` and `R2.xeVt_trL` are disjoint**);
* `XeFx` (`x ∈ Tᵗ[σ]` and `π x = x`), `xeStep` (**one atom / `ε`-number / `ω^g`-sum at the cardinal `Ω_{s+1}`**, for
  a package `Vs.VsPkg`), `xe_pi_fix` (**the code `π`-fix on all of `K⁽⁰⁾_q ∩ Ω_{r+1}` under the bound `Vs.VsG S r`**,
  for a strongly critical `q ≤ σ`; the induction of `Vs.vsComm` along `Vs.vsMu`), `xe_pi_fix_th` (**every `z < θ`
  with `d_S(z) < q ≤ σ` is in `Tᵗ[σ]` and fixed by `π`**: `Uy.uy_pi_fix` widened from `B₂` to `θ`);
* `XeLev κ M` (**a constant level over `κ`**: `1 ≤ M`, `Ω₁·M < θ` for some `S`, `d_S(M)` below a strongly critical
  `q ≤ κ`), `xeLev_of_uy`, `xeLev_of_ltIn` (from `Vd.VdLtIn M γ`, the hypothesis of `Xb.XbThCl`), `xeLev_B` (**`M =
  B₂` is a level over every strongly critical `κ`**: the new levels are not empty);
* `xe_Om1_mul_TB`, `xe_arg_T`, `xeLt_vt_self`, `xeVt_tr` (**both translations of [W07a] Def 6.2 at every constant
  level `Ω₁·M < θ`**, from `R2.uvVt_trL` below `B₂` and `R2.xeVt_trL` on `[B₂, θ)`).

Axioms: those of the repository and `R2.xeVt_trL` (only in `xeVt_tr`).  New definitions: `XeFx`, `XeLev` (Props).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xe

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- **The two twin citations have disjoint ranges**: `Ω₁·M < B₂` (`R2.uvVt_trL`) and `B₂ ≤ M` (`R2.xeVt_trL`) never
hold together. -/
theorem xe_twin_disj {M : Ordinal.{0}} (h1 : Om1 * M < ucB) (h2 : ucB ≤ M) : False :=
  absurd ((le_mul_right M Rj.rj_Om1_pos).trans_lt h1) (not_lt.2 h2)

/-- `x ∈ Tᵗ[σ]` and `π_{σ,τ}(x) = x`. -/
def XeFx (σ τ x : Ordinal.{0}) : Prop := x ∈ TB τ σ ∧ pi σ τ x = x

section Step

variable {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hq : SC q) (hqσ : q ≤ σ)
include h hq hqσ

/-- **One step at the cardinal `Ω_{s+1}`**: for `ξ ∈ [L, U) ∩ K⁽⁰⁾_q` with `Ω_s < ξ < ψ_{Ω_{s+1}}(E) ≤ U` (`E =
Ω_{r+1}`), given `XeFx` at its parts `c < ξ` and at its level `λ ≥ Ω_{s+1}` when `ξ` is an atom: `XeFx` at `ξ`. -/
theorem xeStep {s L U G : Ordinal.{0}} {r : ℕ} (hP : VsPkg S s L U G) (hs : s < ω) (hs1 : 1 ≤ s)
    (hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) ≤ U)
    {ξ : Ordinal.{0}} (hLξ : L ≤ ξ) (hGξ : ω ^ G ≤ ξ) (hsξ : Om s < ξ)
    (hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1))) (hK : UlK S 0 q ξ)
    (hsub : ∀ b, b < ξ → VsSub S b ξ → UlK S 0 q b → XeFx σ τ b)
    (hlev : ∀ l y, l < Om (s + 1 + 1) → y < ulH S s l y → ulH S s l y = ξ → Om (s + 1) ≤ l →
      UlK S 0 q l → XeFx σ τ l) :
    XeFx σ τ ξ := by
  have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
  have hσ1 : σ < Om1 := h.2.2.1.trans h.2.2.2
  have hq01 : q ≤ Om (0 + 1) := by rw [zero_add, ← Rj.rj_Om1]; exact hqσ.trans hσ1.le
  have hξW : ξ < Om (s + 1) := hξE.trans (Ui.ui_psi_lt (s := s) _)
  have hξU : ξ < U := hξE.trans_le hUE
  have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le hsξ).ne'
  rcases vsShape (S := S) hs hs1 hsξ hξE with ⟨-, -, hgξ⟩ | ⟨-, -, ha1, haξ, hcξ, hev⟩ |
      ⟨hSC, hnf, hyξ, hlV, hlK⟩
  · -- a non-`ε` `ξ = ω^g·k + r`
    obtain ⟨k, hξk, hgK, hrK, hrξ⟩ := ulK_split hq hK hξ0
    have hGg : G ≤ log ω ξ := le_log_of_opow_le one_lt_omega0 hGξ
    have hgsub : VsSub S (log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    have hpξ : ω ^ log ω ξ ≤ ξ := opow_log_le_self ω hξ0
    have hgF := hsub _ hgξ hgsub hgK
    have hpF : XeFx σ τ (ω ^ log ω ξ) := by
      by_cases hgE' : ω ^ log ω ξ = log ω ξ
      · rw [hgE']; exact hgF
      · obtain ⟨hiff, hπp⟩ := hP.opow h hGg hgE' (hpξ.trans_lt hξU)
        exact ⟨hiff.2 hgF.1, by rw [hπp hgF.1, hgF.2]⟩
    have hm := Uy.uy_fix_mul_nat h hpF k
    obtain ⟨hrT, hrπ⟩ := hsub _ hrξ hrsub hrK
    obtain ⟨c1, c2⟩ := pi_add h hm.1 hrT
    rw [← hξk]
    exact ⟨c1, by rw [c2, hm.2, hrπ]⟩
  · -- an `ε`-number `ξ = φ(a, c)`
    have hKv : UlK S 0 q (veblen (invVeblen₁ ξ) (invVeblen₂ ξ)) := by rw [hev]; exact hK
    obtain ⟨haK, hcK⟩ := Uo.uoK_veb hKv (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
    have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
    have hepsξ := hP.eps h ha1 (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ) (by rw [hev]; exact hLξ)
      (by rw [hev]; exact hξU)
    rw [hev] at hepsξ
    obtain ⟨haT, haπ⟩ := hsub _ haξ hasub haK
    obtain ⟨hcT, hcπ⟩ := hsub _ hcξ hcsub hcK
    exact ⟨hepsξ.1.2 ⟨haT, hcT⟩, by rw [hepsξ.2 haT hcT, haπ, hcπ, hev]⟩
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
    obtain ⟨hyT, hyπ⟩ :=
      hsub y hyξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' => (hlow i hi1 his q' hq' hLq hqW hK').2)
        hyξ.le hξW) hyK0
    have hlF : XeFx σ τ l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC hsξ hlK hlW
        exact hsub l hlξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le hξW) hlK0
      · exact hlev l y hlV hy hnf hlW hlK0
    refine ⟨hat.1.2 ⟨hlF.1, hyT⟩, ?_⟩
    rw [hat.2 hlF.1 hyT, hlF.2, hyπ, hnf]

/-- **The code `π`-fix on `K⁽⁰⁾_q ∩ Ω_{r+1}` under the bound `VsG S r`**, for bases `σ < τ` and a strongly critical
`q ≤ σ`: every such `ξ` is in `Tᵗ[σ]` and `π ξ = ξ`.  Below `Ω₁`: `ξ < q ≤ σ`; at `Ω₁` below `B₂`: `Uy.uy_pi_fix`;
on `[B₂, θ)`: `xeStep` with `Vs.vsPkg_one`; `Ω_s`: `R2.vsOm_TB`; `(Ω_s, Ω_{s+1})`, `s ≥ 2`: `xeStep` with
`Vs.vsPkg_gen`; the level of an atom one cardinal up by the induction along `Vs.vsMu S r`. -/
theorem xe_pi_fix (r : ℕ) :
    ∀ ξ, UlK S 0 q ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → XeFx σ τ ξ := by
  have hσ1 : σ < Om1 := h.2.2.1.trans h.2.2.2
  have hq1' : q ≤ Om1 := hqσ.trans hσ1.le
  have hrω : ((r : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega r
  have hEω : Om ((r : Ordinal.{0}) + 1) ≤ Om ω := Om_le_Om.2 hrω.le
  intro ξ
  refine (vs_wf (S := S) r).induction (C := fun ξ => UlK S 0 q ξ → VsG S r ξ →
    ξ < Om ((r : Ordinal.{0}) + 1) → XeFx σ τ ξ) ξ ?_
  intro ξ IH hK hG hr
  have hGsub : ∀ b, VsSub S b ξ → VsG S r b := fun b hb i hi1 hi =>
    hb i hi1 hi _ (Ui.ui_psi_SC (s := i) _) (Ui.ui_L_lt_psi (s := i) _) (Ui.ui_psi_lt (s := i) _).le (hG i hi1 hi)
  have hsub : ∀ b, b < ξ → VsSub S b ξ → UlK S 0 q b → XeFx σ τ b :=
    fun b hbξ hbs hbK => IH b (vs_lex_sub r hbs hbξ) hbK (hGsub b hbs) (hbξ.trans hr)
  rcases lt_or_ge ξ Om1 with hξ1 | hξ1
  · -- countable
    have hξq : ξ < q := ulK_lt_W (s := 0) omega0_pos hq (by rw [Om_zero]; exact hq.1) hK
      (by rw [Vd.vd_Om01, ← Rj.rj_Om1]; exact hξ1)
    have hξσ := hξq.trans_le hqσ
    exact ⟨mem_TB_of_lt h hξσ, pi_lt h hξσ⟩
  obtain ⟨k, hkr, hk1, hk2⟩ := vs_level (r := r) (by rw [← Rj.rj_Om1]; exact hξ1) hr
  have hs : ((k : Ordinal.{0}) + 1) < ω := vs_nat_lt_omega k
  have hs1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 := le_add_self
  have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG _ hs1 hs) hk2
  -- the level of an atom, one cardinal up
  have hlev : ∀ l y, l < Om ((k : Ordinal.{0}) + 1 + 1 + 1) → y < ulH S ((k : Ordinal.{0}) + 1) l y →
      ulH S ((k : Ordinal.{0}) + 1) l y = ξ → Om ((k : Ordinal.{0}) + 1 + 1) ≤ l →
      UlK S 0 q l → XeFx σ τ l := by
    intro l y hlV hy hnf hlW hlK
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
    exact IH l hlex hlK hGl hlr
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- the cardinal `Ω₁`
    have hs1e : ((k : Ordinal.{0}) + 1) = 1 := by rw [hk0, Nat.cast_zero, zero_add]
    rcases lt_or_ge ξ ucB with hξB | hξB
    · have hdq : Vd.vdD S 0 ξ < q := (Vg.vg_code_iffK hq).2 hK
      have hDq : ucDat ξ < q := (Vd.vd_dat_uc hξB hq hq1').2 hdq
      exact Uy.uy_pi_fix h ξ hξB (hDq.trans_le hqσ)
    · have hP : VsPkg S ((k : Ordinal.{0}) + 1) ucB (ConjT.th S) Gg.ggE := by rw [hs1e]; exact vsPkg_one
      have hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) ≤ ConjT.th S := by
        rw [hs1e]; exact (psi_mono (InR_Om_succ 1) hEω).1
      have hGξ : ω ^ Gg.ggE ≤ ξ := by rw [Rk.rk_E_inE]; exact Vm.vm_E_le_B.trans hξB
      have hsξ : Om ((k : Ordinal.{0}) + 1) < ξ := by rw [hs1e]; exact Vd.vd_Om1_lt_B.trans_le hξB
      exact xeStep h hq hqσ hP hs hs1 hUE hξB hGξ hsξ hξE hK hsub hlev
  · -- the cardinals `Ω_s`, `s ≥ 2`
    have hs2 : (1 : Ordinal.{0}) < (k : Ordinal.{0}) + 1 := by exact_mod_cast Nat.succ_lt_succ hk0
    rcases hk1.lt_or_eq with hlt | heq
    · have hUE : S.psi (Om ((r : Ordinal.{0}) + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) ≤
          S.psi (Om ω) (Om ((k : Ordinal.{0}) + 1 + 1)) := (psi_mono (InR_Om_succ _) hEω).1
      have hΩE : ω ^ (Om ((k : Ordinal.{0}) + 1) : Ordinal.{0}) = Om ((k : Ordinal.{0}) + 1) :=
        Ui.ui_W_opow (k : Ordinal.{0})
      exact xeStep h hq hqσ (vsPkg_gen hs hs2) hs hs1 hUE hlt.le (by rw [hΩE]; exact hlt.le) hlt hξE hK hsub hlev
    · -- `ξ = Ω_s`
      subst heq
      exact vsOm_TB h hs hs2

end Step

/-- **The code `π`-fix below `θ`** (`Uy.uy_pi_fix` widened from `B₂` to `θ`): for bases `σ < τ`, a strongly critical
`q ≤ σ` and `z < θ` with `d_S(z) < q`: `z ∈ Tᵗ[σ]` and `π_{σ,τ}(z) = z`. -/
theorem xe_pi_fix_th {σ τ q z : Ordinal.{0}} (h : Bases σ τ) (hq : SC q) (hqσ : q ≤ σ) (hz : z < ConjT.th S)
    (hd : Vd.vdD S 0 z < q) : XeFx σ τ z := by
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hz
  have hK : UlK S 0 q z := (Vg.vg_code_iffK hq).1 hd
  exact xe_pi_fix h hq hqσ r z hK (vs_G_of_W2 hzr)
    ((hzr.trans (Ui.ui_psi_lt (s := 1) _)).trans_le (vs_W2_le hr1))

/-! ## Constant levels below `θ` -/

/-- `θ` is an `ε`-number with `Ω₁ < θ < Ω₂`. -/
theorem xe_th (S : InaccSeq.{0}) : InE (ConjT.th S) ∧ Om1 < ConjT.th S ∧ ConjT.th S < OmTwo :=
  ⟨Gg.gg_SC_eps (Vj.vj_th_SC (S := S)), by rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th,
    Vm.vm_th_lt_Om2⟩

/-- `M < θ ⇒ Ω₁·M < θ`. -/
theorem xe_mul_lt_th {M : Ordinal.{0}} (hM : M < ConjT.th S) : Om1 * M < ConjT.th S :=
  InE.mul_lt (xe_th S).1 (xe_th S).2.1 hM

/-- `M < B₂ ⇒ Ω₁·M < B₂`. -/
theorem xe_mul_lt_B {M : Ordinal.{0}} (hM : M < ucB) : Om1 * M < ucB :=
  InE.mul_lt (Gg.gg_SC_eps ucB_SC) ucB_gt hM

/-- `M ≤ Ω₁·M`. -/
theorem xe_le_mul (M : Ordinal.{0}) : M ≤ Om1 * M := le_mul_right M Rj.rj_Om1_pos

/-- **The datum of `Ω₁·M`**: `d_S(M) < q ⇒ d_S(Ω₁·M) < q` (`q` strongly critical). -/
theorem xe_Om1_mul_dat {q M : Ordinal.{0}} (hq : SC q) (h : Vd.vdD S 0 M < q) : Vd.vdD S 0 (Om1 * M) < q :=
  (Vg.vg_code_iffK hq).2 (Vm.vm_K_Om1mul hq ((Vg.vg_code_iffK hq).1 h))

/-- **The data of `Ω₁·M` from the data of a level** (the converse of `Uy.uy_dat_of_mul`): for an `ε`-number `κ`,
`M ≠ 0`, `Ω₁·M < B₂`: `ucDat M < κ ⇒ ucDat(Ω₁·M) < κ`. -/
theorem xe_dat_mul {κ : Ordinal.{0}} (hκ : InE κ) :
    ∀ M, M ≠ 0 → Om1 * M < ucB → ucDat M < κ → ucDat (Om1 * M) < κ := by
  have hκ0 : (0 : Ordinal.{0}) < κ := InE.pos hκ
  have hOm : InE (Om1 : Ordinal.{0}) := Rj.rj_Om1_opow
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM0 hMB hMd
  obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hM0
  have hrM : M % ω ^ log ω M < M := Rj.rj_mod_lt hM0
  set l := log ω M with hldef
  set v := M / ω ^ l with hvdef
  set r := M % ω ^ l with hrdef
  have hwl : Om1 * ω ^ l = ω ^ (Om1 + l) := Si.si_Om1_opow_eq l
  have hz : Om1 * M = ω ^ (Om1 + l) * v + Om1 * r := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, hwl]
  have hrz : Om1 * r < ω ^ (Om1 + l) := by
    rw [← hwl]; exact (mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 hr
  have hwz : ω ^ (Om1 + l) ≤ Om1 * M := by
    rw [hz]; exact (le_mul_left _ (pos_iff_ne_zero.2 hv0)).trans le_self_add
  have hlB : Om1 + l < ucB := ((right_le_opow _ one_lt_omega0).trans hwz).trans_lt hMB
  have hrB : Om1 * r < ucB := ((mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 hrM).trans hMB
  -- the remainder
  have hrpart : ucDat r < κ → ucDat (Om1 * r) < κ := fun hd => by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, mul_zero, ucDat_small Rj.rj_Om1_pos]; exact hκ0
    · exact IH r hrM h0 hrB hd
  rcases eq_or_ne M 1 with h1 | h1
  · rw [h1, mul_one, ucDat_Om1]; exact hκ0
  have hM1' : 1 < M := lt_of_le_of_ne (one_le_iff_ne_zero.2 hM0) (Ne.symm h1)
  have hz1 : Om1 < Om1 * M := by
    have := (mul_lt_mul_iff_right₀ Rj.rj_Om1_pos).2 hM1'
    rwa [mul_one] at this
  rcases lt_or_ge l Om1 with hl | hl
  · -- a countable level
    have hM1 : M < Om1 := (lt_opow_succ_log_self one_lt_omega0 M).trans
      (hOm.opow_lt (by rw [Order.succ_eq_add_one]; exact hOm.add_lt hl (Ub.ub_one_lt hOm)))
    rw [ucDat_small hM1] at hMd
    have hzE : Om1 * M < Gg.ggE := Si.si_E_inE.mul_lt Rj.rj_Om1_lt_E (hM1.trans Rj.rj_Om1_lt_E)
    have hE := Uy.uy_not_eps hz1 hzE
    rw [hz] at hz1 hE hMB ⊢
    rw [Uy.uy_dat_form hv0 hvω hrz hz1 hMB hE, Uy.uy_dat_Om1_add_small hl]
    refine max_lt ((log_le_self ω M).trans_lt hMd) (hrpart ?_)
    rw [ucDat_small (hrM.trans hM1)]; exact hrM.trans hMd
  · have hM1 : Om1 ≤ M := hl.trans ((right_le_opow l one_lt_omega0).trans (opow_log_le_self ω hM0))
    rcases hM1.lt_or_eq with hM1 | hM1
    · by_cases hME : ω ^ M = M
      · have hadd : Om1 + M = M := Ordinal.add_of_omega0_opow_le (by rw [hME]; exact hM1) hME.le
        have hzM : Om1 * M = M := by
          calc Om1 * M = Om1 * ω ^ M := by rw [hME]
            _ = ω ^ (Om1 + M) := Si.si_Om1_opow_eq M
            _ = M := by rw [hadd, hME]
        rwa [hzM]
      · have hzE : ω ^ (Om1 * M) ≠ Om1 * M := fun h => hME (Uy.uy_eps_of_mul hM1 h)
        have hMB0 : M < ucB := (xe_le_mul M).trans_lt hMB
        have hcnf := Uy.uy_dat_cnf hM1 hMB0 hME
        rw [← hldef, ← hrdef] at hcnf
        rw [hcnf] at hMd
        rw [hz] at hzE hz1 hMB ⊢
        rw [Uy.uy_dat_form hv0 hvω hrz hz1 hMB hzE, Uy.uy_dat_Om1_add hl hlB]
        exact max_lt ((le_max_left _ _).trans_lt hMd) (hrpart ((le_max_right _ _).trans_lt hMd))
    · -- `M = Ω₁`: `Ω₁·Ω₁ = ω^{Ω₁+Ω₁}`
      have hlog : log ω Om1 = Om1 := by
        conv_lhs => rw [← Rj.rj_Om1_opow]
        exact log_opow one_lt_omega0 _
      have hl1 : l = Om1 := by rw [hldef, ← hM1]; exact hlog
      have hzE : Om1 * M < Gg.ggE := Si.si_E_inE.mul_lt Rj.rj_Om1_lt_E (hM1 ▸ Rj.rj_Om1_lt_E)
      have hE := Uy.uy_not_eps hz1 hzE
      rw [hz] at hz1 hE hMB ⊢
      rw [Uy.uy_dat_form hv0 hvω hrz hz1 hMB hE, hl1, Uy.uy_dat_Om1_add le_rfl (by have := hlB; rwa [hl1] at this), ucDat_Om1]
      refine max_lt hκ0 (hrpart ?_)
      have hr0 : r = 0 := by rw [hrdef, hl1, Rj.rj_Om1_opow, ← hM1, Ordinal.mod_self]
      rw [hr0, ucDat_small Rj.rj_Om1_pos]; exact hκ0

/-- **A constant level over `κ`**: an old level `Uy.UyLev κ M` (`Ω₁·M < B₂`, data `< κ`), or `B₂ ≤ M < θ` (some `S`)
with `d_S(M)` below a strongly critical `q ≤ κ`. -/
def XeLev (κ M : Ordinal.{0}) : Prop :=
  Uy.UyLev κ M ∨ (ucB ≤ M ∧ ∃ S : InaccSeq.{0}, M < ConjT.th S ∧ ∃ q, SC q ∧ q ≤ κ ∧ Vd.vdD S 0 M < q)

theorem XeLev.mono {κ κ' M : Ordinal.{0}} (hκ : κ ≤ κ') (h : XeLev κ M) : XeLev κ' M := by
  rcases h with h | ⟨hB, S', hθ, q, hq, hqκ, hd⟩
  · exact Or.inl (h.mono hκ)
  · exact Or.inr ⟨hB, S', hθ, q, hq, hqκ.trans hκ, hd⟩

/-- `1 ≤ M` and `Ω₁·M < Ω₂` at a level. -/
theorem XeLev.one_le {κ M : Ordinal.{0}} (h : XeLev κ M) : 1 ≤ M ∧ Om1 * M < OmTwo := by
  rcases h with h | ⟨hB, S', hθ, -⟩
  · exact ⟨h.1, h.2.1.trans ucB_lt_Om2⟩
  · exact ⟨(Order.one_le_iff_pos).2 (lt_of_le_of_lt zero_le (ucB_gt.trans_le hB)),
      (xe_mul_lt_th hθ).trans (xe_th S').2.2⟩

/-- **The hypothesis of `Xb.XbThCl` gives a level**: `1 ≤ M` and `Vd.VdLtIn M γ` for an `ε`-number `γ`. -/
theorem xeLev_of_ltIn {γ M : Ordinal.{0}} (hγ : InE γ) (h1 : 1 ≤ M) (h : Vd.VdLtIn M γ) : XeLev γ M := by
  rcases h with ⟨hMB, hd⟩ | ⟨S', hB, hθ, q, hq, hqγ, hd⟩
  · exact Or.inl ⟨h1, xe_mul_lt_B hMB, hd,
      xe_dat_mul hγ M (one_le_iff_ne_zero.1 h1) (xe_mul_lt_B hMB) hd⟩
  · exact Or.inr ⟨hB, S', hθ, q, hq, hqγ, hd⟩

/-- **`M = B₂` is a constant level over every strongly critical `κ`** (`Ww.ww_B_dat`), and it is not an old level:
the new range `[B₂, θ)` of levels is not empty. -/
theorem xeLev_B (S : InaccSeq.{0}) {κ : Ordinal.{0}} (hκ : SC κ) : XeLev κ ucB ∧ ¬ Uy.UyLev κ ucB :=
  ⟨Or.inr ⟨le_rfl, S, Vd.vd_B_lt_th, κ, hκ, le_rfl, Ww.ww_B_dat hκ⟩,
    fun h => xe_twin_disj h.2.1 le_rfl⟩

/-- **`Ω₁·M ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·M) = Ω₁·M`** for a level over `κ ≤ σ` (`Uy.uy_Om1_mul_TB` below `θ`). -/
theorem xe_Om1_mul_TB {κ σ τ M : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hM : XeLev κ M) :
    XeFx σ τ (Om1 * M) := by
  rcases hM with hU | ⟨-, S', hθ, q, hq, hqκ, hd⟩
  · exact Uy.uy_Om1_mul_TB h hκσ hU
  · exact xe_pi_fix_th (S := S') h hq (hqκ.trans hκσ) (xe_mul_lt_th hθ) (xe_Om1_mul_dat hq hd)

/-- **`Ω₁·M + x ∈ Tᵗ[σ]` and `π(Ω₁·M + x) = Ω₁·M + π x`** for a level over `κ ≤ σ` and `x ∈ Tᵗ[σ]`. -/
theorem xe_arg_TB {κ σ τ M x : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hM : XeLev κ M) (hx : x ∈ TB τ σ) :
    Om1 * M + x ∈ TB τ σ ∧ pi σ τ (Om1 * M + x) = Om1 * M + pi σ τ x := by
  obtain ⟨hT, hπ⟩ := xe_Om1_mul_TB h hκσ hM
  obtain ⟨c1, c2⟩ := pi_add h hT hx
  exact ⟨c1, by rw [c2, hπ]⟩

/-- **`Ω₁·M + x ∈ Tᵗ` and `< Ω₂`** for a level `M` over `κ` (`κ < τ` bases) and `x ∈ Tᵗ ∩ Ω₁` (`Uy.uy_arg_T`). -/
theorem xe_arg_T {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : XeLev κ M) (hx : x ∈ Tset τ) (hx1 : x < Om1) :
    Om1 * M + x ∈ Tset τ ∧ Om1 * M + x < OmTwo := by
  have hΓ := (xe_Om1_mul_TB hB le_rfl hM).1.1
  refine ⟨vzT_add hB.2.1 hB.2.2.2 hΓ hx, ?_⟩
  exact (Lq.lq_SC_indec uc_SC_Om2).add_lt hM.one_le.2 (hx1.trans uc_Om1_lt_Om2)

/-- **The countable part is below the value**: `x < ϑᵗ(Ω₁·M + x)` for a level `M` over `κ < τ` and `x ∈ Tᵗ ∩ Ω₁`
(`Uy.uyLt_vt_self` below `B₂`; `R2.vdLevel_lt` on `[B₂, θ)`). -/
theorem xeLt_vt_self {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : XeLev κ M) (hx : x ∈ Tset τ)
    (hx1 : x < Om1) : x < vt τ (Om1 * M + x) := by
  rcases hM with hU | ⟨hMB, S', hMθ, q, _, hqκ, hd⟩
  · exact Uy.uyLt_vt_self hB hU hx hx1
  · have hMT : Vd.VdDatIn (· ∈ Tset τ) M :=
      Or.inr ⟨S', hMB, hMθ, (mem_TB_of_lt hB (hd.trans_le hqκ)).1⟩
    exact (vdLevel_lt hB.2.1 hB.2.2.2 (ucB_gt.le.trans hMB) hMT hx hx1).2

/-- **Both translations of [W07a] Def 6.2 at every constant level `Ω₁·M < θ` over `κ < τ`**, with membership:
`R2.uvVt_trL` below `B₂`, `R2.xeVt_trL` on `[B₂, θ)` (the subcase `Γ^* < α`; the data are below `κ < τ < α`). -/
theorem xeVt_tr {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM : XeLev κ M) (hρ1 : ρ < Om1) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) := by
  have hκα : κ ≤ Dl τ n := (hB.2.2.1.trans (Dl_E hB.2.1 hB.2.2.2 hn).1).le
  rcases hM with hU | ⟨hMB, S', hMθ, q, hq, hqκ, hd⟩
  · exact uvVt_trL hB.2.1 hB.2.2.2 hn hU.1 hU.2.1 (hU.2.2.2.trans_le hκα) hρ1
  · exact xeVt_trL (S := S') hB.2.1 hB.2.2.2 hn hMB hMθ hq (hqκ.trans hκα) hd hρ1

/-- **The base change at a `ϑ`-node with a constant level** (the node case of `Vi.viDown` below `θ`): for bases `σ <
τ`, a level over `κ ≤ σ` and `ρ ∈ Tᵗ[σ] ∩ Ω₁`: `ϑᵗ(Ω₁·M + ρ) ∈ Tᵗ[σ]` and `π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(Ω₁·M + π ρ)`. -/
theorem xeDown {κ σ τ M ρ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (hM : XeLev κ M) (hρ : ρ ∈ TB τ σ)
    (hρ1 : ρ < Om1) :
    vt τ (Om1 * M + ρ) ∈ TB τ σ ∧ pi σ τ (vt τ (Om1 * M + ρ)) = vt σ (Om1 * M + pi σ τ ρ) := by
  obtain ⟨c1, c2⟩ := xe_arg_TB h hκσ hM hρ
  have h2 : Om1 * M + ρ < OmTwo := (Lq.lq_SC_indec uc_SC_Om2).add_lt hM.one_le.2 (hρ1.trans uc_Om1_lt_Om2)
  have hv := vt_memTwo h.2.1 h.2.2.2 c1.1 h2
  refine ⟨⟨hv.1, by rw [hv.2.2.2.2]; exact c1.2⟩, ?_⟩
  rw [pi_vt_two h c1 h2, c2]

/-- **The segment move at a `ϑ`-node with a constant level and a constant argument**: for `ε`-bases `b, c < Ω₁`, a
level over an `ε`-number `κ < b, c` and `η < κ`: `mv b c (ϑ^b(Ω₁·M + η)) = ϑ^c(Ω₁·M + η)`. -/
theorem xeMv {κ b c M η : Ordinal.{0}} (hκ : InE κ) (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1)
    (hκb : κ < b) (hκc : κ < c) (hM : XeLev κ M) (hη : η < κ) :
    mv b c (vt b (Om1 * M + η)) = vt c (Om1 * M + η) := by
  have hη1 : η < Om1 := hη.trans (hκb.trans hb1)
  unfold mv
  rcases lt_trichotomy c b with hcb | hcb | hbc
  · rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    have hηT : η ∈ TB b c := mem_TB_of_lt hB (hη.trans hκc)
    rw [(xeDown hB hκc.le hM hηT hη1).2, pi_lt hB (hη.trans hκc)]
  · subst hcb; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]; rfl
  · rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    have hηT : η ∈ TB c b := mem_TB_of_lt hB (hη.trans hκb)
    obtain ⟨hT, hπ⟩ := xeDown hB hκb.le hM hηT hη1
    rw [pi_lt hB (hη.trans hκb)] at hπ
    rw [← hπ, up_pi hB hT]

#print axioms xe_pi_fix_th
#print axioms xe_dat_mul
#print axioms xe_Om1_mul_TB
#print axioms xe_arg_T
#print axioms xeLt_vt_self
#print axioms xeVt_tr
#print axioms xeDown
#print axioms xeMv
#print axioms xeLev_B

end Googology.Trans.PoR.InaccPsi.R2.Xe
