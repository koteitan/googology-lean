import Googology.Trans.PoR.InaccPsi.R2.VcNode
import Googology.Trans.PoR.InaccPsi.R2.UcUB

/-!
# The image of a level is again a level: `π z < B₂`, `Ω₁ ∣ π Γ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB` is the least strongly critical `z > Ω₁` fixed by every `H_γ` (`γ < E₂ = ε_{Ω₂+1}`, `C(γ) < z`);
`π = pi σ τ`.

* `vcT` (**the tower `t₀ = Ω₂ + 1`, `t_{n+1} = Ω₂^{t_n}`**): `t_n < E₂`, cofinal in `E₂` (`vcT_cof`), finite components;
* `vcA n = H_{t_{n+1}}(0)` (**atoms with finite data, cofinal in `B₂`**: `vcA_X`, `vcA_lt_B`, `vcA_dat`, `vcA_mono`,
  `vcA_cof`: every `z < B₂` lies below some `vcA n`);
* `vc_pi_lt_B` (**`π z < B₂` for every code `z ∈ Tᵗ[σ]` below `B₂`**: `π` fixes the cofinal atoms `vcA n`);
* `vc_pi_eps` (**`π` of an `ε`-number above `Ω₁` is an `ε`-number above `Ω₁`**), `vc_pi_dvd` (**`Ω₁ ∣ z ⇒ Ω₁ ∣ π z`**);
* `vc_level_img` (**the image of a level is a level**: `Γ = Ω₁·M ∈ Tᵗ[σ]`, `1 ≤ M`, `Γ < B₂` ⇒ `π Γ = vcSub π Γ =
  Ω₁·M'` with `1 ≤ M'`, `Ω₁·M' < B₂`: the hypotheses of `R2.uvVt_trL` / `R2.uvVt_trH` over `σ`), `vc_node_img`
  (**`π(ϑᵗ(Ω₁·M + ρ)) = ϑ^σ(Ω₁·M' + π ρ)` with `Ω₁·M' = vcSub π (Ω₁·M)` a level**).

No new axiom.  New definitions: `vcT`, `vcA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The tower** `t₀ = Ω₂ + 1`, `t_{n+1} = Ω₂^{t_n}`. -/
noncomputable def vcT : ℕ → Ordinal.{0}
  | 0 => OmTwo + 1
  | n + 1 => OmTwo ^ vcT n

theorem vc_one_lt_Om2 : (1 : Ordinal.{0}) < OmTwo :=
  one_lt_omega0.trans ((omega0_lt_inE Rj.rj_Om1_inE).trans uc_Om1_lt_Om2)

theorem vcT_le_succ (n : ℕ) : vcT n ≤ vcT (n + 1) := right_le_opow (vcT n) vc_one_lt_Om2

theorem vcT_mono : Monotone vcT := monotone_nat_of_le_succ vcT_le_succ

theorem vcT_ge (n : ℕ) : OmTwo + 1 ≤ vcT n := vcT_mono (Nat.zero_le n)

theorem vcT_one_le (n : ℕ) : 1 ≤ vcT n := le_add_self.trans (vcT_ge n)

theorem vcT_lt_E : ∀ n : ℕ, vcT n < ucE
  | 0 => uc_E_indec ucE_gt (vc_one_lt_Om2.trans ucE_gt)
  | n + 1 => by
    have hΩ : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := (uc_SC_facts uc_SC_Om2).1
    have h : vcT (n + 1) = ω ^ (OmTwo * vcT n) := by
      show OmTwo ^ vcT n = _
      conv_lhs => rw [← hΩ]
      rw [← opow_mul]
    rw [h]
    have hm : OmTwo * vcT n < ucE := uc_E_mulPrin ucE_gt (vcT_lt_E n)
    calc ω ^ (OmTwo * vcT n) < ω ^ ucE := (opow_lt_opow_iff_right one_lt_omega0).2 hm
      _ = ucE := ucE_fix

theorem vcT_gt (n : ℕ) : OmTwo < vcT (n + 1) := by
  show OmTwo < OmTwo ^ vcT n
  conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
  exact (opow_lt_opow_iff_right vc_one_lt_Om2).2 ((vc_one_lt_Om2.trans (lt_add_one _)).trans_le (vcT_ge n))

/-- **The tower is cofinal in `E₂`.** -/
theorem vcT_cof {γ : Ordinal.{0}} (hγ : γ < ucE) : ∃ n, γ < vcT n := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (show γ < nfp (fun x => ω ^ x) (OmTwo + 1) from hγ)
  refine ⟨n, hn.trans_le ?_⟩
  clear hn
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show ω ^ _ ≤ OmTwo ^ vcT n
    exact (opow_le_opow_right omega0_pos ih).trans
      (opow_le_opow_left _ (omega0_lt_inE Rj.rj_Om1_inE |>.le.trans uc_Om1_lt_Om2.le))

/-- **The components of `t_n` are finite.** -/
theorem vcT_comps : ∀ (n : ℕ), ∀ x ∈ ucComps (vcT n), x < ω
  | 0, x, hx => by
    have e : vcT 0 = OmTwo ^ (1 : Ordinal.{0}) * 1 + 1 := by
      show OmTwo + 1 = _; rw [opow_one, mul_one]
    have hE := vcT_lt_E 0
    rw [e] at hx hE
    rw [ucComps_cnf le_rfl one_ne_zero vc_one_lt_Om2 (by rw [opow_one]; exact vc_one_lt_Om2) hE,
      ucComps_small vc_one_lt_Om2] at hx
    rcases hx with hx | hx | hx <;> (try rw [mem_singleton_iff] at hx) <;> rw [hx] <;> exact one_lt_omega0
  | n + 1, x, hx => by
    have e : vcT (n + 1) = OmTwo ^ vcT n * 1 + 0 := by
      show OmTwo ^ vcT n = _; rw [mul_one, add_zero]
    have hE := vcT_lt_E (n + 1)
    rw [e] at hx hE
    rw [ucComps_cnf (vcT_one_le n) one_ne_zero vc_one_lt_Om2 (opow_pos _ (by
      exact Rj.rj_Om1_pos.trans uc_Om1_lt_Om2)) hE,
      ucComps_small (Rj.rj_Om1_pos.trans uc_Om1_lt_Om2)] at hx
    rcases hx with hx | hx | hx
    · exact vcT_comps n x hx
    · rw [mem_singleton_iff] at hx; rw [hx]; exact one_lt_omega0
    · rw [mem_singleton_iff] at hx; rw [hx]; exact omega0_pos

theorem vc_C_lt_Om1 {γ : Ordinal.{0}} (h : ∀ x ∈ ucComps γ, x < ω) : ucC γ < Om1 :=
  (ucFold_lt_iff id Rj.rj_Om1_pos γ).2 fun x hx => (h x hx).trans (omega0_lt_inE Rj.rj_Om1_inE)

/-- **The atoms `H_{t_{n+1}}(0)`.** -/
noncomputable def vcA (n : ℕ) : Ordinal.{0} := ucH (vcT (n + 1)) 0

theorem vcA_gt (n : ℕ) : Om1 < vcA n := ucH_gt _ _

/-- `X ≤ vcA n` (`vcA n` is a fixed point of `H_{Ω₂}`, and `X = H_{Ω₂}(0)`). -/
theorem vcA_X (n : ℕ) : tlX ≤ vcA n := by
  have hC : ucC OmTwo < vcA n :=
    (vc_C_lt_Om1 fun x hx => by
      rw [ucComps_Om2] at hx
      rcases hx with hx | hx
      · rw [hx]; exact one_lt_omega0
      · rw [mem_singleton_iff] at hx; rw [hx]; exact omega0_pos).trans (vcA_gt n)
  have hfix : ucG ucC Om1 OmTwo (vcA n) = vcA n := ucG_fix_lower (vcT_gt n) ⟨0, rfl⟩ hC
  rw [← ucH_Om2_zero]
  calc ucH OmTwo 0 ≤ ucH OmTwo (vcA n) := (ucH_normal OmTwo).strictMono.monotone zero_le
    _ = vcA n := hfix

theorem vcA_lt_B (n : ℕ) : vcA n < ucB := by
  have hfix := ucB_spec (vcT_lt_E (n + 1)) ((vc_C_lt_Om1 (vcT_comps (n + 1))).trans ucB_gt)
  calc vcA n < ucH (vcT (n + 1)) ucB := (ucH_lt_iff _).2 (Rj.rj_Om1_pos.trans ucB_gt)
    _ = ucB := hfix

/-- **`vcA n` has finite data.** -/
theorem vcA_dat (n : ℕ) : ucDat (vcA n) < ω := by
  rw [vcA, ucDat_H (vcT_lt_E (n + 1)) (Rj.rj_Om1_pos.trans (ucH_gt _ _)) (vcA_X n) (vcA_lt_B n)]
  refine max_lt ((ucFold_lt_iff ucDat omega0_pos _).2 fun x hx => ?_) ?_
  · have hx1 := vcT_comps (n + 1) x hx
    rw [ucDat_small (hx1.trans (omega0_lt_inE Rj.rj_Om1_inE))]; exact hx1
  · rw [ucDat_small Rj.rj_Om1_pos]; exact omega0_pos

theorem vcA_mono {n m : ℕ} (h : n ≤ m) : vcA n ≤ vcA m := by
  rcases (vcT_mono (Nat.succ_le_succ h)).lt_or_eq with hlt | heq
  · have hfix : ucG ucC Om1 (vcT (n + 1)) (vcA m) = vcA m :=
      ucG_fix_lower hlt ⟨0, rfl⟩ ((vc_C_lt_Om1 (vcT_comps (n + 1))).trans (vcA_gt m))
    calc vcA n ≤ ucH (vcT (n + 1)) (vcA m) := (ucH_normal _).strictMono.monotone zero_le
      _ = vcA m := hfix
  · rw [vcA, vcA, heq]

/-- **The atoms `vcA n` are cofinal in `B₂`.** -/
theorem vcA_cof {z : Ordinal.{0}} (hz : z < ucB) : ∃ n, z < vcA n := by
  have hbdd : BddAbove (range vcA) := ⟨ucB, by rintro _ ⟨n, rfl⟩; exact (vcA_lt_B n).le⟩
  have hne : (range vcA).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  set w := sSup (range vcA) with hw
  have hle : ∀ n, vcA n ≤ w := fun n => le_csSup hbdd ⟨n, rfl⟩
  have hSC : SC w := uc_SC_sSup (by rintro _ ⟨n, rfl⟩; exact ucH_SC _ _) hne hbdd
  have hlt : ∀ y, y < w → ∃ n, y < vcA n := fun y hy => by
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (lt_csSup_iff hbdd hne).1 hy
    exact ⟨n, hn⟩
  have hNF : w ∈ ucNoNF := by
    refine ⟨hSC, (vcA_gt 0).trans_le (hle 0), ?_⟩
    rintro ⟨γ, hγE, hγC, hne'⟩
    apply hne'
    refine le_antisymm (((ucH_normal γ).le_iff_forall_le hSC.isSuccLimit).2 fun y hy => ?_) (ucH_le_self γ w)
    obtain ⟨m, hm⟩ := hlt y hy
    obtain ⟨m', hm'⟩ := hlt _ hγC
    obtain ⟨k, hk⟩ := vcT_cof hγE
    set N := m + m' + k
    have hγN : γ < vcT (N + 1) := hk.trans_le (vcT_mono (by omega))
    have hCN : ucC γ < vcA N := hm'.trans_le (vcA_mono (by omega))
    have hfix : ucG ucC Om1 γ (vcA N) = vcA N := ucG_fix_lower hγN ⟨0, rfl⟩ hCN
    calc ucH γ y ≤ ucH γ (vcA N) := (ucH_normal γ).strictMono.monotone (hm.le.trans (vcA_mono (by omega)))
      _ = vcA N := hfix
      _ ≤ w := hle N
  exact hlt z (hz.trans_le (ucB_le hNF))

/-! ## The image of a code -/

/-- **`π z < B₂` for every code `z ∈ Tᵗ[σ]` below `B₂`.** -/
theorem vc_pi_lt_B {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hB : z < ucB) (hT : z ∈ TB τ σ) : pi σ τ z < ucB := by
  obtain ⟨n, hn⟩ := vcA_cof hB
  obtain ⟨hAT, hAπ⟩ := vc_pi_fix h (vcA_lt_B n) ((vcA_dat n).trans (omega0_lt_inE h.1))
  calc pi σ τ z < pi σ τ (vcA n) := (pi_bijOn h).2 hT hAT hn
    _ = vcA n := hAπ
    _ < ucB := vcA_lt_B n

/-- `π` keeps `Ω₁ < ·` on `Tᵗ[σ]`. -/
theorem vc_pi_gt_Om1 {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hT : z ∈ TB τ σ) (h1 : Om1 < z) :
    Om1 < pi σ τ z := by
  obtain ⟨o1, o2⟩ := pi_Om1 h
  rw [← o2]; exact (pi_bijOn h).2 o1 hT h1

/-- **`π` of an `ε`-number above `Ω₁` is an `ε`-number** (`φ(πa, πc)` with `πa ≥ 1`, or a rebuilt atom). -/
theorem vc_pi_eps {σ τ z : Ordinal.{0}} (h : Bases σ τ) (hB : z < ucB) (hT : z ∈ TB τ σ) (h1 : Om1 < z)
    (hE : ω ^ z = z) : ω ^ pi σ τ z = pi σ τ z := by
  have hL := vc_lv_TB h z hB hT
  rw [vc_pi_TB h hB hT]
  by_cases hI : invVeblen₁ z < z
  · rw [vcSub_phi _ h1 hB hE hI]
    have hcz : invVeblen₂ z < z := Tf.tf_inv2_lt hE
    have hev : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
    have ha0 : invVeblen₁ z ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ invVeblen₂ z = ω ^ z := by rw [hev, hE]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hcz.ne
    rw [VcLv_phi _ h1 hB hE hI] at hL
    obtain ⟨haT, haπ⟩ := vc_pi h _ (hI.trans hB) hL.1
    have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
    have ha : 0 < vcSub (pi σ τ) (invVeblen₁ z) := by
      rw [← haπ, ← pi_lt h h0σ]
      exact (pi_bijOn h).2 (mem_TB_of_lt h h0σ) haT (pos_iff_ne_zero.2 ha0)
    rw [← veblen_zero_apply]
    exact veblen_veblen_of_lt ha _
  · rw [vcSub_atom _ h1 hB hE hI]
    unfold ucRebuild
    split_ifs
    · exact Low.opow_eq_self_of_SC (rhF_SC _ _)
    · exact Low.opow_eq_self_of_SC (ucH_SC _ _)

/-- **`Ω₁ ∣ z ⇒ Ω₁ ∣ π z`** for codes `z ∈ Tᵗ[σ]` below `B₂`. -/
theorem vc_pi_dvd {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ z, z < ucB → z ∈ TB τ σ → Om1 ∣ z → Om1 ∣ pi σ τ z := by
  have hΩe : ∀ e, Om1 ≤ e → Om1 ∣ ω ^ e := fun e he => by
    rw [← Rj.rj_Om1_opow]; exact opow_dvd_opow ω he
  have hεd : ∀ x, Om1 ≤ x → ω ^ x = x → Om1 ∣ x := fun x hx hxE => by rw [← hxE]; exact hΩe x hx
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hT hd
  rcases lt_or_ge z Om1 with hz | hz
  · have hz0 : z = 0 := by
      by_contra h0
      exact absurd (le_of_dvd h0 hd) (not_le.2 hz)
    have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
    rw [hz0, pi_lt h h0σ]; exact dvd_zero _
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, (pi_Om1 h).2]
  have hπ1 := vc_pi_gt_Om1 h hT h1
  by_cases hE : ω ^ z = z
  · exact hεd _ hπ1.le (vc_pi_eps h hB hT h1 hE)
  -- `z = ω^l·k + r`
  have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
  obtain ⟨hdec, -, hvω, -⟩ := Si.si_dec hz0
  have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
  have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
  have hτz : τ ≤ z := (h.2.2.2.trans h1).le
  have hcomps := Si.si_comps_cons hz0
  have hwT : ω ^ log ω z ∈ TB τ σ := Si.siTB_of_comps h hT hτz (fun p hp => by
    rw [comps_opow, List.mem_singleton] at hp
    rw [hcomps, hp]; exact List.mem_cons_self ..)
  have hrT : z % ω ^ log ω z ∈ TB τ σ :=
    Si.siTB_of_comps h hT hτz (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
  have hwd : Om1 ∣ ω ^ log ω z * (k : Ordinal.{0}) := Dvd.dvd.mul_right (hΩe _ hl1) _
  have hrd : Om1 ∣ z % ω ^ log ω z := by
    have e : ω ^ log ω z * (k : Ordinal.{0}) + z % ω ^ log ω z = z := by rw [← hk]; exact hdec
    rw [← e] at hd
    exact (Ordinal.dvd_add_iff hwd).1 hd
  have hrπ := IH _ hrz (hrz.trans hB) hrT hrd
  have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
  have hw1 : Om1 ≤ ω ^ log ω z := (right_le_opow _ one_lt_omega0).trans' hl1
  -- `π(ω^l)` is a power of `ω` above `Ω₁`: either an `ε`-number or `Ω₁·ω^{b'}`
  have hwπ : Om1 ∣ pi σ τ (ω ^ log ω z) := by
    by_cases hl : ω ^ log ω z = log ω z
    · rcases hl1.eq_or_lt with hl' | hl'
      · rw [hl, ← hl', (pi_Om1 h).2]
      · have hlB : log ω z < ucB := (hl ▸ hwz).trans_lt hB
        have hlT : log ω z ∈ TB τ σ := hl ▸ hwT
        rw [hl]
        exact hεd _ (vc_pi_gt_Om1 h hlT hl').le (vc_pi_eps h hlB hlT hl' hl)
    · have hbl : Om1 + (log ω z - Om1) = log ω z := Ordinal.add_sub_cancel_of_le hl1
      have hwl : ω ^ log ω z = Om1 * ω ^ (log ω z - Om1) := by rw [Si.si_Om1_opow_eq, hbl]
      rcases lt_or_ge (log ω z) Gg.ggE with hlE | hlE
      · have hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → log ω z - Om1 < e := fun e he he1 =>
          ((Ordinal.sub_le_self _ _).trans_lt hlE).trans_le (Gg.ggE_le he (by rw [← Rj.rj_Om1]; exact he1))
        have o := om1_opow_TB_all h hbE
        rw [hwl] at hwT ⊢
        rw [o.2 (o.1.1 hwT)]; exact dvd_mul_right _ _
      · obtain ⟨o1, o2⟩ := ucOpow_TB h hlE hl (hwz.trans_lt hB)
        have hlT := o1.1 hwT
        rw [o2 hlT]
        obtain ⟨hET, hEπ⟩ := vc_pi_E h
        have hle : Gg.ggE ≤ pi σ τ (log ω z) := by
          rw [← hEπ]; exact ((pi_bijOn h).2.le_iff_le hET hlT).2 hlE
        exact hΩe _ (Rj.rj_Om1_lt_E.le.trans hle)
  rw [← hdec, hk]
  obtain ⟨m1, m2⟩ := vc_mul_nat h hwT k
  rw [(pi_add h m1 hrT).2, m2]
  exact dvd_add (Dvd.dvd.mul_right hwπ _) hrπ

/-- **The image of a level is a level**: for `Γ = Ω₁·M ∈ Tᵗ[σ]` with `1 ≤ M`, `Γ < B₂`: `π Γ = vcSub π Γ = Ω₁·M'`
with `1 ≤ M'` and `Ω₁·M' < B₂` (the level hypotheses of `R2.uvVt_trL` / `R2.uvVt_trH` over the new base). -/
theorem vc_level_img {σ τ M : Ordinal.{0}} (h : Bases σ τ) (hM1 : 1 ≤ M) (hB : Om1 * M < ucB)
    (hT : Om1 * M ∈ TB τ σ) :
    ∃ M', pi σ τ (Om1 * M) = Om1 * M' ∧ 1 ≤ M' ∧ Om1 * M' < ucB ∧
      pi σ τ (Om1 * M) = vcSub (pi σ τ) (Om1 * M) := by
  obtain ⟨M', hM'⟩ := vc_pi_dvd h _ hB hT (dvd_mul_right _ _)
  have hπB := vc_pi_lt_B h hB hT
  have hΓ1 : Om1 ≤ Om1 * M := le_mul_left Om1 (one_le_iff_pos.1 hM1)
  have hπ1 : Om1 ≤ pi σ τ (Om1 * M) := by
    obtain ⟨o1, o2⟩ := pi_Om1 h
    calc Om1 = pi σ τ Om1 := o2.symm
      _ ≤ pi σ τ (Om1 * M) := ((pi_bijOn h).2.le_iff_le o1 hT).2 hΓ1
  refine ⟨M', hM', one_le_iff_ne_zero.2 fun e => ?_, hM' ▸ hπB, vc_pi_TB h hB hT⟩
  rw [e, mul_zero] at hM'
  rw [hM'] at hπ1
  exact absurd hπ1 (not_le.2 Rj.rj_Om1_pos)

/-- **The base change of a node at a level with parameter leaves, with the image level**: for bases `σ < τ`,
`Γ = Ω₁·M` (`1 ≤ M`, `Γ < B₂`) with every leaf in `Tᵗ[σ]` and `ρ ∈ Tᵗ[σ] ∩ Ω₁`: `ϑᵗ(Γ + ρ) ∈ Tᵗ[σ]` and
`π(ϑᵗ(Γ + ρ)) = ϑ^σ(Ω₁·M' + π ρ)` with `Ω₁·M' = vcSub π Γ`, `1 ≤ M'`, `Ω₁·M' < B₂`, `π ρ < Ω₁`. -/
theorem vc_node_img {σ τ M ρ : Ordinal.{0}} (h : Bases σ τ) (hM1 : 1 ≤ M) (hB : Om1 * M < ucB)
    (hL : VcLv (· ∈ TB τ σ) (Om1 * M)) (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1) :
    vt τ (Om1 * M + ρ) ∈ TB τ σ ∧ ∃ M', Om1 * M' = vcSub (pi σ τ) (Om1 * M) ∧ 1 ≤ M' ∧ Om1 * M' < ucB ∧
      pi σ τ ρ < Om1 ∧ pi σ τ (vt τ (Om1 * M + ρ)) = vt σ (Om1 * M' + pi σ τ ρ) := by
  obtain ⟨-, n2, n3⟩ := vc_node_pi h hB hL hρ hρ1
  have hT := (vc_pi h _ hB hL).1
  obtain ⟨M', e1, e2, e3, e4⟩ := vc_level_img h hM1 hB hT
  have hρπ : pi σ τ ρ < Om1 := by
    obtain ⟨o1, o2⟩ := pi_Om1 h
    calc pi σ τ ρ < pi σ τ Om1 := (pi_bijOn h).2 hρ o1 hρ1
      _ = Om1 := o2
  exact ⟨n2, M', e1.symm.trans e4, e2, e3, hρπ, by rw [n3, ← e4, e1]⟩

end Googology.Trans.PoR.InaccPsi.R2.Vc
