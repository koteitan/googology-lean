import Googology.Trans.PoR.InaccPsi.R2.YvPi
import Googology.Trans.PoR.InaccPsi.R2.XoNode

/-!
# The datum of a code below `θ` is decided by its leaves; the translation case of a node with a moving level

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`d_S = Vd.vdD S 0` (the `K⁽⁰⁾`-datum), `K⁽⁰⁾_q = Ul.UlK S 0 q`, `θ = ConjT.th S`, `α = Dl τ n`, `α⁺ = Dp τ n`.

* `yv_K_of_lv` (**all leaves below `q` ⇒ `z ∈ K⁽⁰⁾_q`**), `yv_lv_of_K` (**`z ∈ K⁽⁰⁾_q` ⇒ all leaves below `q`**,
  induction along `Vs.vsMu`), `yv_dat_iff` (**`d_S(z) < q ⇔ every leaf of `z` is below `q`** for every strongly
  critical `q ≤ Ω₁` and `z < θ`), `yv_lv_ex` (**every code below `θ` has the canonical decomposition**, all leaves
  countable);
* `yv_case_lo`, `yv_case_hi` (**the subcase of [W07a] Def 6.2 is decided by the leaves of the level**: all below a
  strongly critical `q ≤ α` ⇒ the subcase `Γ^* < α` (`R2.xeVt_trL`); not all below a strongly critical `q ≥ α` ⇒
  the subcase `Γ^* ≥ α` (`R2.xoVt_trH`)), `yv_node_up`, `yv_node_down` (**both translations at a level `B₂ ≤ M < θ`
  with moving leaves, the case read off the leaves**).

No new axiom (uses `R2.xeVt_trL`, `R2.xoVt_trH` through `Xo.xoVt_up`, `Xo.xoVt_down`).  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vs

variable {S : InaccSeq.{0}}

/-- `Ω_s ∈ K⁽⁰⁾_q` for finite `s`. -/
theorem yv_K_Om {q s : Ordinal.{0}} (hs : s < ω) : UlK S 0 q (Om s) := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hs
  exact UlK.om (UlK.nat n)

/-- **All leaves below `q` ⇒ `z ∈ K⁽⁰⁾_q`** (`q` strongly critical, `q ≤ Ω₁`). -/
theorem yv_K_of_lv {q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (r : ℕ) :
    ∀ ξ, YvLv S (· < q) ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → UlK S 0 q ξ := by
  have hqE : InE q := Gg.gg_SC_eps hq
  intro ξ hL
  induction hL with
  | low hz hLv =>
    intro _ _
    have hd : ucDat _ < q := (Vc.vc_dat_lt hqE _ hz).1 hLv
    exact (Vg.vg_code_iffK hq).1 ((Vd.vd_dat_uc hz hq hq1).1 hd)
  | om hs hs' e =>
    intro _ _
    subst e; exact yv_K_Om hs'
  | @cnf s ξ hs1 hs h1 h2 hB hE _ _ ihg ihr =>
    intro hG hr
    have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    have hlξ : log ω ξ < ξ := Ss.ss_log_lt hξ0 hE
    have hmξ : ξ % ω ^ log ω ξ < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S (log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    have hlK := ihg (yv_G_sub hG hgsub) (hlξ.trans hr)
    have hmK := ihr (yv_G_sub hG hrsub) (hmξ.trans hr)
    have hpos : ω ^ log ω ξ ≠ 0 := opow_ne_zero _ omega0_ne_zero
    have hlt : ξ < ω ^ log ω ξ * ω := by
      rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 ξ
    obtain ⟨n, hn⟩ := lt_omega0.1 ((Ordinal.div_lt hpos).2 hlt)
    have hdec : ω ^ log ω ξ * (n : Ordinal.{0}) + ξ % ω ^ log ω ξ = ξ := by
      rw [← hn]; exact Ordinal.div_add_mod _ _
    rw [← hdec]
    exact UlK.add (UlK.mul_nat (UlK.opow hlK) n) hmK
  | @veb s ξ hs1 hs h1 h2 hB hE hS _ _ iha ihc =>
    intro hG hr
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, -, -, haξ, hcξ, hev⟩ | ⟨hSC, -⟩
    · exact absurd hE hE'
    · have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
      have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
        (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
      have haK := iha (yv_G_sub hG hasub) (haξ.trans hr)
      have hcK := ihc (yv_G_sub hG hcsub) (hcξ.trans hr)
      rw [← hev]; exact UlK.phi haK hcK
    · exact absurd hSC hS
  | @atom s ξ hs1 hs h1 h2 hB hSC _ _ ihl ihy =>
    intro hG hr
    have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
      ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG s hs1 hs) h2
    rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE', -⟩ | ⟨-, hS, -⟩ | ⟨-, hnf, hyξ, hlV, hlK⟩
    · exact absurd (yv_SC_eps hSC) hE'
    · exact absurd hSC hS
    set l := Vp.vpLev S s ξ with hldef
    set y := Vp.vpI S s l ξ with hydef
    have hy : y < ulH S s l y := by rw [hnf]; exact hyξ
    have hHW : ulH S s l y < Om (s + 1) := by rw [hnf]; exact h2
    have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q', SC q' → Om i < q' → q' ≤ Om (i + 1) →
        UlK S i q' ξ → UlK S i q' l ∧ UlK S i q' y := fun i _ his q' hq' _ hq'L hK' =>
      ((vs_atom_parts hs his hq' hq'L hlV hy hHW).1).1 (by rw [hnf]; exact hK')
    have hyS : VsSub S y ξ := vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
      (hlow i hi1 his q' hq' hLq hqW hK').2) hyξ.le h2
    have hyK := ihy (yv_G_sub hG hyS) (hyξ.trans hr)
    have hlK0 : UlK S 0 q l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact ihl (yv_G_sub hG (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le h2)) (hlξ.trans hr)
      · obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
        exact ihl hGl hlr
    have hq01 : q ≤ Om (0 + 1) := by rw [zero_add, ← Rj.rj_Om1]; exact hq1
    have := ((vs_atom_parts hs h0s hq hq01 hlV hy hHW).1).2 ⟨hlK0, hyK⟩
    rwa [hnf] at this

/-- **`z ∈ K⁽⁰⁾_q` ⇒ all leaves below `q`** (`q` strongly critical, `q ≤ Ω₁`; induction along `Vs.vsMu`). -/
theorem yv_lv_of_K {q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (r : ℕ) :
    ∀ ξ, UlK S 0 q ξ → VsG S r ξ → ξ < Om ((r : Ordinal.{0}) + 1) → YvLv S (· < q) ξ := by
  have hqE : InE q := Gg.gg_SC_eps hq
  have hq01 : q ≤ Om (0 + 1) := by rw [zero_add, ← Rj.rj_Om1]; exact hq1
  intro ξ
  refine (vs_wf (S := S) r).induction (C := fun ξ => UlK S 0 q ξ → VsG S r ξ →
    ξ < Om ((r : Ordinal.{0}) + 1) → YvLv S (· < q) ξ) ξ ?_
  intro ξ IH hK hG hr
  have hsub : ∀ b, b < ξ → VsSub S b ξ → UlK S 0 q b → YvLv S (· < q) b :=
    fun b hbξ hbs hbK => IH b (vs_lex_sub r hbs hbξ) hbK (yv_G_sub hG hbs) (hbξ.trans hr)
  rcases lt_or_ge ξ ucB with hξB | hξB
  · have hd : Vd.vdD S 0 ξ < q := (Vg.vg_code_iffK hq).2 hK
    exact YvLv.low hξB ((Vc.vc_dat_lt hqE ξ hξB).2 ((Vd.vd_dat_uc hξB hq hq1).2 hd))
  have hξ1 : Om 1 ≤ ξ := (Vd.vd_Om1_lt_B.trans_le hξB).le
  obtain ⟨k, hkr, hk1, hk2⟩ := vs_level (r := r) hξ1 hr
  set s := (k : Ordinal.{0}) + 1 with hsdef
  have hs : s < ω := vs_nat_lt_omega k
  have hs1 : (1 : Ordinal.{0}) ≤ s := le_add_self
  rcases hk1.lt_or_eq with h1 | heq
  swap
  · -- `ξ = Ω_s`, `s ≥ 2`
    have hs2 : (1 : Ordinal.{0}) < s := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← heq, ← h] at hξB
        exact absurd (Vd.vd_Om1_lt_B) (not_lt.2 hξB)
    exact YvLv.om hs2 hs heq.symm
  have hξE : ξ < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (s + 1)) :=
    ulK_lt_W hs (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hG _ hs1 hs) hk2
  rcases vsShape (S := S) hs hs1 h1 hξE with ⟨hE, -, hlξ⟩ | ⟨hE, hS, -, haξ, hcξ, hev⟩ |
      ⟨hSC, hnf, hyξ, hlV, hlK⟩
  · have hξ0 : ξ ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
    have hmξ : ξ % ω ^ log ω ξ < ξ := Rj.rj_mod_lt hξ0
    have hgsub : VsSub S (log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => (ulK_dec hq' ξ hK').2
    have hrsub : VsSub S (ξ % ω ^ log ω ξ) ξ := fun i _ _ q' hq' _ _ hK' => ulK_mod hq' ξ hK' _
    exact YvLv.cnf hs1 hs h1 hk2 hξB hE (hsub _ hlξ hgsub (ulK_dec hq ξ hK).2)
      (hsub _ hmξ hrsub (ulK_mod hq ξ hK _))
  · have hKv : UlK S 0 q (veblen (invVeblen₁ ξ) (invVeblen₂ ξ)) := by rw [hev]; exact hK
    obtain ⟨haK, hcK⟩ := Uo.uoK_veb hKv (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)
    have hasub : VsSub S (invVeblen₁ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).1
    have hcsub : VsSub S (invVeblen₂ ξ) ξ := fun i _ _ q' hq' _ _ hK' =>
      (Uo.uoK_veb (by rw [hev]; exact hK') (by rw [hev]; exact haξ) (by rw [hev]; exact hcξ)).2
    exact YvLv.veb hs1 hs h1 hk2 hξB hE hS (hsub _ haξ hasub haK) (hsub _ hcξ hcsub hcK)
  · set l := Vp.vpLev S s ξ with hldef
    set y := Vp.vpI S s l ξ with hydef
    have h0s : (0 : Ordinal.{0}) < s := lt_of_lt_of_le zero_lt_one hs1
    have hy : y < ulH S s l y := by rw [hnf]; exact hyξ
    have hHW : ulH S s l y < Om (s + 1) := by rw [hnf]; exact hk2
    have hparts : ∀ i q', i < s → SC q' → q' ≤ Om (i + 1) →
        (UlK S i q' (ulH S s l y) ↔ UlK S i q' l ∧ UlK S i q' y) := fun i q' his hq' hq'L =>
      (vs_atom_parts hs his hq' hq'L hlV hy hHW).1
    have hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < s → ∀ q', SC q' → Om i < q' → q' ≤ Om (i + 1) →
        UlK S i q' ξ → UlK S i q' l ∧ UlK S i q' y := fun i _ his q' hq' _ hq'L hK' =>
      (hparts i q' his hq' hq'L).1 (by rw [hnf]; exact hK')
    obtain ⟨hlK0, hyK0⟩ := (hparts 0 q h0s hq hq01).1 (by rw [hnf]; exact hK)
    have hyL := hsub y hyξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
      (hlow i hi1 his q' hq' hLq hqW hK').2) hyξ.le hk2) hyK0
    have hlL : YvLv S (· < q) l := by
      rcases lt_or_ge l (Om (s + 1)) with hlW | hlW
      · have hlξ : l < ξ := ulK_lt_W hs hSC h1 hlK hlW
        exact hsub l hlξ (vs_sub_of_low (fun i hi1 his q' hq' hLq hqW hK' =>
          (hlow i hi1 his q' hq' hLq hqW hK').1) hlξ.le hk2) hlK0
      · obtain ⟨hGl, hlr⟩ := vs_lev_G hs hlV hy hlW (by rw [hnf]; exact hG) (by rw [hnf]; exact hξE)
        have hlK1 : UlK S s ξ l := by
          rw [← hnf]; exact (ul_vis (ulH_SC l y)).1 (ulH_D_lt l y)
        have hlow' : ∀ i : Ordinal.{0}, 1 ≤ i → i < (k : Ordinal.{0}) + 1 → ∀ q', SC q' → Om i < q' →
            q' ≤ Om (i + 1) → UlK S i q' ξ → UlK S i q' l := fun i hi1 his q' hq' hLq hq'L hK' =>
          (hlow i hi1 his q' hq' hLq hq'L hK').1
        have hlex := vs_lex_lev hkr hlow' hlK1 hSC h1 hk2
        exact IH l hlex hlK0 hGl hlr
    exact YvLv.atom hs1 hs h1 hk2 hξB hSC hlL hyL

/-- **`d_S(z) < q ⇔ every leaf of `z` is below `q`**, for a strongly critical `q ≤ Ω₁` and `z < θ`. -/
theorem yv_dat_iff {q z : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hz : z < ConjT.th S) :
    Vd.vdD S 0 z < q ↔ YvLv S (· < q) z := by
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hz
  have hG : VsG S r z := vs_G_of_W2 hzr
  have hzr' : z < Om ((r : Ordinal.{0}) + 1) :=
    (hzr.trans (Ui.ui_psi_lt (s := 1) _)).trans_le (vs_W2_le hr1)
  rw [Vg.vg_code_iffK hq]
  exact ⟨fun hK => yv_lv_of_K hq hq1 r z hK hG hzr', fun hL => yv_K_of_lv hq hq1 r z hL hG hzr'⟩

/-- **Every code below `θ` has the canonical decomposition**, with countable leaves. -/
theorem yv_lv_ex {z : Ordinal.{0}} (hz : z < ConjT.th S) : YvLv S (· < Om1) z := by
  have hq : SC (Om1 : Ordinal.{0}) := by rw [Rj.rj_Om1]; exact SC_Om one_ne_zero
  exact (yv_dat_iff hq le_rfl hz).1 (by rw [Rj.rj_Om1]; exact Vd.vdD_lt_Om1 hz)

/-- **The low subcase from the leaves**: every leaf of `M` below a strongly critical `q ≤ α` (`q ≤ Ω₁`, `M < θ`)
gives the case hypothesis of `R2.xeVt_trL`. -/
theorem yv_case_lo {α q M : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hqα : q ≤ α) (hM : M < ConjT.th S)
    (hL : YvLv S (· < q) M) : Xo.XoCase S α M :=
  Or.inl ⟨q, hq, hqα, (yv_dat_iff hq hq1 hM).2 hL⟩

/-- **The high subcase from the leaves**: some leaf of `M` not below a strongly critical `q` with `α ≤ q ≤ Ω₁`
gives the case hypothesis of `R2.xoVt_trH`. -/
theorem yv_case_hi {α q M : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hαq : α ≤ q) (hM : M < ConjT.th S)
    (hL : ¬ YvLv S (· < q) M) : Xo.XoCase S α M :=
  Or.inr ⟨q, hq, hαq, not_lt.1 fun hd => hL ((yv_dat_iff hq hq1 hM).1 hd)⟩

/-- **Both cases are covered** when `α` itself is strongly critical: the leaves of `M` decide the case. -/
theorem yv_case {α M : Ordinal.{0}} (hα : SC α) (hα1 : α ≤ Om1) (hM : M < ConjT.th S) : Xo.XoCase S α M := by
  by_cases hL : YvLv S (· < α) M
  · exact yv_case_lo hα hα1 le_rfl hM hL
  · exact yv_case_hi hα hα1 le_rfl hM hL

/-- **Both translations of [W07a] Def 6.2 at a level `B₂ ≤ M < θ` with moving leaves, the subcase read off the
leaves** (`α = Dl τ n` strongly critical): every leaf of `M` below `α` ⇒ the argument is shifted by `α`
(`R2.xeVt_trL`); some leaf `≥ α` ⇒ the argument is kept (`R2.xoVt_trH`). -/
theorem yv_node_tr {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hMB : ucB ≤ M) (hMθ : M < ConjT.th S) (hα : SC (Dl τ n)) (hρ1 : ρ < Om1) :
    (YvLv S (· < Dl τ n) M →
      (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
        Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
      (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
        Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ))) ∧
    (¬ YvLv S (· < Dl τ n) M →
      (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
        Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
      (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
        Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ))) := by
  have hα1 : Dl τ n ≤ Om1 := (Dl_spec hτ hτ1 n).2.1.le
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hd : Vd.vdD S 0 M < Dl τ n := (yv_dat_iff hα hα1 hMθ).2 hL
    exact xeVt_trL hτ hτ1 hn hMB hMθ hα le_rfl hd hρ1
  · have hd : Dl τ n ≤ Vd.vdD S 0 M := not_lt.1 fun hd => hL ((yv_dat_iff hα hα1 hMθ).1 hd)
    exact xoVt_trH hτ hτ1 hn hMB hMθ hα le_rfl hd hρ1

end Googology.Trans.PoR.InaccPsi.R2.Yv
