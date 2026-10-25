import Googology.Trans.PoR.InaccPsi.R2.UoK
import Googology.Trans.PoR.InaccPsi.R2.UfHull
import Googology.Trans.PoR.InaccPsi.R2.UfDL
import Googology.Trans.PoR.InaccPsi.R2.UcFn

/-!
# At `s = 0` below `B₂`: the codes are the visibility closure, `UcCl q z ↔ z ∈ K_q`, and `Φ_μ = Uc.ucP μ`

`Ω₁ = Om 1`, `Ω₂ = Om (1 + 1)`, `ψ = S.psi · Ω₂`, `K_q = Ul.UlK S 0 q` (the visibility closure at the threshold `W =
Ω₁`), `UcCl q` the codes over `q` below `B₂ = Uc.ucB`, `TlCl q` the codes below `X = Tl.tlX`, `Φ_μ = Ul.ulH S 0 μ`
(the lifted hierarchy at `s = 0`), `ucP μ` (the hierarchy on the data `ucDatL μ = ucDat (Ω₁ + μ)`, `R2.UcFn`).  The
K-versions of the hull converse (`Tw.tw_mem_CSet`, `Uf.uf_mem_CSet`) and of the direct hull lemma (`Uf.uf_diglev`):
`K_q` has no bound on the collapse arguments, and the own argument of an atom code `c ∈ K_q` is in `K_q` by
`Uo.uoArg`, so neither the argument bound `a` nor the hypothesis on the collapses `ψ_{Ω₁}(e)` is needed:

* `uoW1`, `uoW2`, `uoLeWe`, `uoLeMulWe`, `uoPsi2`, `uo_K_comps` (**`x < E₂` is in `K_q` when its components are**);
* `uo_tlK` (**`TlCl q ⊆ K_q`**), `uo_ucK` (**`UcCl q ⊆ K_q`**), for a strongly critical `q ≤ Ω₁`;
* `uo_diglevK` (**every member of `K_q` has its `Ω₁`-digits and levels below `q`, is a code over `q` when below
  `B₂`, and has every component a code or `≥ B₂` when below `E₂`**, `q` strongly critical, `q ≤ Ω₁`);
* `uo_cl_iffK` (**`UcCl q z ↔ z ∈ K_q`** for `z < B₂`, `q ≤ Ω₁` strongly critical), `uo_K_big` (`z ∈ K_v` for
  every `z < B₂` and strongly critical `v > Ω₁`), `uo_vis_datL` (**`ulD j < v ↔ ucDatL j < v`** for `j < B₂`, every
  strongly critical `v`), `uo_phi_ucP` (**`Φ_μ = ucP μ` for every `μ < B₂`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Uf
  Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-! ## Membership helpers at `s = 0` -/

theorem uoW1 {q : Ordinal.{0}} : UlK S 0 q (Om 1) := by
  have := ulK_W (S := S) (s := 0) (q := q) omega0_pos; rwa [zero_add] at this

theorem uoW2 {q : Ordinal.{0}} : UlK S 0 q (Om (1 + 1)) := UlK.om (UlK.add UlK.one UlK.one)

theorem uo_W2_ne : Om (1 + 1) ≠ Om ((0 : Ordinal.{0}) + 1) := by
  rw [zero_add]; intro h
  have := Om_inj.1 h
  exact absurd this (by simp)

theorem uoLeWe {q e : Ordinal.{0}} (hq : SC q) (he : UlK S 0 q e) : UlK S 0 q (leWe e) := by
  have h := ulK_opow_mul hq (uoW2 (S := S) (q := q)) e he
  rw [ts_Om2_opow] at h
  exact UlK.opow h

theorem uoLeMulWe {q e x : Ordinal.{0}} (hq : SC q) (he : UlK S 0 q e) (hx : UlK S 0 q x) :
    UlK S 0 q (leWe e * x) := by
  have h := ulK_opow_mul hq (uoW2 (S := S) (q := q)) e he
  rw [ts_Om2_opow] at h
  exact ulK_opow_mul hq h x hx

theorem uoPsi2 {q B : Ordinal.{0}} (hB : UlK S 0 q B) : UlK S 0 q (S.psi B (Om (1 + 1))) :=
  UlK.coll (InR_Om_succ 1) uo_W2_ne uoW2 hB

/-- **`x < E₂` is in `K_q` when all its components are.** -/
theorem uo_K_comps {q : Ordinal.{0}} (hq : SC q) :
    ∀ x, x < ucE → (∀ c ∈ ucComps x, UlK S 0 q c) → UlK S 0 q x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx
  by_cases hx2 : x < OmTwo
  · exact hx x (by rw [ucComps_small hx2]; rfl)
  have hx2' := not_lt.1 hx2
  have hc := ucComps_big hx2' hxE
  have hel := uc_log_lt hx2' hxE
  have hrl := uc_mod_lt hx2'
  have he := IH _ hel (hel.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inl h)
  have hr := IH _ hrl (hrl.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inr (Or.inr h))
  have hd := hx (x / OmTwo ^ log OmTwo x) (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hW := uoLeMulWe hq he hd
  rw [uc_leWe] at hW
  rw [← uc_cnf_eq x]
  exact UlK.add hW hr

theorem uo_Z_Lam {Z : Ordinal.{0}} (hZ : Z ≤ Om1) : Z ≤ S.Lam := by
  refine (hZ.trans (le_of_lt ?_))
  rw [tw_Om1_eq]
  exact lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.one_mem (S := S) 0 0))

/-! ## The hull converse in `K_q` -/

/-- **`TlCl Z ⊆ K_Z`** for a strongly critical `Z ≤ Ω₁` (the K-version of `Tw.tw_mem_CSet`). -/
theorem uo_tlK {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) : ∀ x, TlCl Z x → UlK S 0 Z x := by
  have hZL : Z ≤ S.Lam := uo_Z_Lam hZ
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases lt_trichotomy x Om1 with h | rfl | h
  · exact UlK.small (hx.lt_of_lt_Om1 hZS h)
  · rw [tw_Om1_eq]; exact uoW1
  have hzX := tw_cl_lt hZ hx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := tl_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact UlK.phi (IH _ hI h1) (IH _ h2l h2)
    · have hSC := tl_SC_of h hI
      obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h hzX
      obtain ⟨hcβ, hcy⟩ := tl_cl_atom hZ x hx hSC h
      generalize hβdef : tlLev x = β at hnf hyz hlz hcβ hcy
      generalize hydef : tlI β x = y at hnf hyz hcy
      have hβX : β < tlX := hlz.trans hzX
      have h1' : Om 1 < rhF β y := by rw [hnf, ← tw_Om1_eq]; exact h
      have hyz' : y < rhF β y := by rw [hnf]; exact hyz
      have hzX' : rhF β y < tlX := by rw [hnf]; exact hzX
      obtain ⟨B, c, D, hown, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        twRun (S := S) hZS hZ hcy hβX hyz' h1' hzX'
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      have hβz : β < rhF β (c + D) := by rw [hcD, hnf]; exact hlz
      obtain ⟨hψe, -⟩ := twRun_eq hown hdvd hc hD2 hval hβz
      rw [hcD, hnf] at hψe
      have hβC := IH β hlz hcβ
      have hDC := IH D hDz hDc
      have hBC : UlK S 0 Z B := by
        rcases hcase with ⟨-, hB0, -⟩ | ⟨-, hBw, -⟩ | ⟨hc1, hcf, -⟩
        · rw [hB0]; exact UlK.zero
        · rw [hBw]; exact uoLeWe hZS hβC
        · have hcK := IH c hcz hcc
          have hψc : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          refine uoArg hZL (InR_Om_succ 1) hown (by rw [hψc]; exact hcK) ?_
          rw [hψc]; exact (hZ.trans_lt (by rw [tw_Om1_eq]; exact hc1)).le
      rw [← hψe]
      exact uoPsi2 (UlK.add hBC (uoLeMulWe hZS hβC hDC))
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tlDec hZS x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : TlCl Z (ω ^ g * k) := TlCl.mul_nat hZS.1 (TlCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := IH _ hgl hlog
    have hmC := IH _ hml hr
    rw [← hdec]
    exact UlK.add ((UlK.opow hgC).mul_nat k) hmC

/-- **`UcCl Z ⊆ K_Z`** for a strongly critical `Z ≤ Ω₁` (the K-version of `Uf.uf_mem_CSet`). -/
theorem uo_ucK {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) : ∀ x, UcCl Z x → UlK S 0 Z x := by
  have hZL : Z ≤ S.Lam := uo_Z_Lam hZ
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hxB := uf_cl_lt_B hZ hx
  rcases lt_or_ge x tlX with hxX | hXx
  · exact uo_tlK hZS hZ x (uc_cl_lt_X hx hxX)
  have h : Om1 < x := uc_Om1_lt_of_X hXx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := uc_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact UlK.phi (IH _ hI h1) (IH _ h2l h2)
    · have hSC := tl_SC_of h hI
      have hne := uc_nf_of_lt hSC h hxB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h hne
      obtain ⟨hcl, hcy⟩ := uc_cl_atom hZ x hx hSC hXx hxB
      generalize hldef : ucLev x = l at hlE hlv hnf hyz hcl hcy
      generalize hydef : ucI l x = y at hnf hyz hcy
      obtain ⟨B, c, D, hown, hBE, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        ufRun (S := S) hZS hZ hlE hcy (by rw [hnf]; exact hyz) (by rw [hnf]; exact hxB)
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      obtain ⟨hψe, -, -, -⟩ := ufRun_eq hlE hown hBE hdvd hc hD2 hval
      rw [hcD, hnf] at hψe
      have hlC : UlK S 0 Z l := uo_K_comps hZS l hlE fun c' hc' =>
        IH c' ((le_ucC hc').trans_lt hlv) (hcl c' hc')
      have hDC := IH D hDz hDc
      have hBC : UlK S 0 Z B := by
        rcases hcase with hc0 | ⟨hc1, hcf, -, -⟩
        · subst hc0
          rcases eq_or_ne l 0 with hl0 | hl0
          · subst hl0
            have hψ : S.psi B (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := by rw [← hc, uf_H0]
            rw [Ts.ts_own_unique hown (CSet.zero_mem _ _) hψ]; exact UlK.zero
          have h0B : ucH l 0 < ucB := ((uf_H_le_iff l).2 zero_le).trans_lt (by rw [hnf]; exact hxB)
          obtain ⟨K, hownK, -, hBK, -, hK⟩ :=
            uf_first_base (S := S) (Order.one_le_iff_ne_zero.2 hl0) hlE h0B hown hc
          have hWl : UlK S 0 Z (OmTwo ^ l) := by
            have := uoLeWe hZS hlC; rwa [uc_leWe] at this
          rw [hBK]
          refine UlK.add ?_ hWl
          rcases hK with ⟨hK0, -⟩ | ⟨hKm, -, hmaxK⟩
          · rw [hK0]; exact UlK.zero
          · have hmc : ucC l ∈ ucComps l := uf_ucC_mem l hlE
            have hvS : SC (S.psi K (Om (1 + 1))) := Ts.ts_psi_SC K
            have hv1 : Om1 < S.psi K (Om (1 + 1)) := by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi K
            obtain ⟨t, htc, htS, hvt, htm⟩ := uf_SC_code hZ _ (hcl _ hmc) _ hvS hv1 hKm
            have htv : t = S.psi K (Om (1 + 1)) := le_antisymm (hmaxK t htS (hv1.trans_le hvt) htm) hvt
            rw [htv] at htc
            have htK := IH _ (hKm.trans_lt hlv) htc
            exact uoArg hZL (InR_Om_succ 1) hownK htK (hZ.trans hv1.le)
        · have hcK := IH c hcz hcc
          have hψc : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          refine uoArg hZL (InR_Om_succ 1) hown (by rw [hψc]; exact hcK) ?_
          rw [hψc]; exact (hZ.trans_lt hc1).le
      have hWD : UlK S 0 Z (OmTwo ^ l * D) := by
        have := uoLeMulWe hZS hlC hDC; rwa [uc_leWe] at this
      rw [← hψe]
      exact uoPsi2 (UlK.add hBC hWD)
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ucDec hZS hZ x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : UcCl Z (ω ^ g * k) := UcCl.mul_nat hZS.1 (UcCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := IH _ hgl hlog
    have hmC := IH _ hml hr
    rw [← hdec]
    exact UlK.add ((UlK.opow hgC).mul_nat k) hmC

/-! ## The direct hull lemma in `K_q` -/

/-- **The direct hull lemma in `K_q` below `B₂`** (the K-version of `Uf.uf_diglev`, no hypothesis on the collapses
`ψ_{Ω₁}`): for a strongly critical `q ≤ Ω₁`, every member `x` of `K_q` has all its `Ω₁`-digits below `q`, all its
levels `j < B₂` with `ucDatL j < q`, is a code over `q` when `x < B₂`, and has every component a code over `q` or
`≥ B₂` when `x < E₂`. -/
theorem uo_diglevK {q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om 1) :
    ∀ x, UlK S 0 q x → RiDg q x ∧ UfLev q x ∧ (x < ucB → UcCl q x) ∧
      (x < ucE → UfP (UfK q) x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := gg_one_lt_of_SC hq
  have hq1' : q ≤ Om1 := by rw [rj_Om1]; exact hq1
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hqlim : IsSuccLimit q := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hq)
  have hfin : ∀ e : Ordinal.{0}, e < ω → UfK q e := fun e he _ =>
    UcCl.small (he.trans_le (omega0_le_of_isSuccLimit hqlim))
  have hK0 : UfK q 0 := fun _ => UcCl.zero hq.1
  have hK1 : UfK q 1 := fun _ => UcCl.one hq.1
  have hKadd : ∀ a b, UfK q a → UfK q b → UfK q (a + b) := fun a b ha hb h =>
    UcCl.add (ha (le_self_add.trans_lt h)) (hb (le_add_self.trans_lt h))
  have hKop : ∀ δ, δ < OmTwo → UfK q δ → UfK q (ω ^ δ) := fun δ _ hδ h =>
    UcCl.opow hq.1 (hδ (((isNormal_opow one_lt_omega0).strictMono.le_apply).trans_lt h))
  have hq2 : q < Om (1 + 1) := hq1.trans_lt ts_Om1_lt_Om2
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → UfLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h]
    unfold ucDatL; rw [add_zero, ucDat_Om1]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hsmall : ∀ v, v < q → RiDg q v ∧ UfLev q v ∧ (v < ucB → UcCl q v) ∧ (v < ucE → UfP (UfK q) v) :=
    fun v hv => ⟨hsmallD v hv, hcount v (hv.trans_le hq1), fun _ => UcCl.small hv,
      fun _ => (ufP_small (hv.trans (by rw [uf_Om2]; exact hq2))).2 fun _ => UcCl.small hv⟩
  have hB2 : (ucB : Ordinal.{0}) < Om (1 + 1) := by rw [← uf_Om2]; exact ucB_lt_Om2
  have hbig : ∀ p, ω ^ p = p → Om (1 + 1) < p → RiDg q p ∧ UfLev q p ∧ (p < ucB → UcCl q p) ∧
      (p < ucE → UfP (UfK q) p) := by
    intro p hp h2
    have hcl : p < ucB → UcCl q p := fun h => absurd (h.trans hB2) (not_lt.2 h2.le)
    exact ⟨hepsD p hp (ts_Om1_lt_Om2.le.trans h2.le), uf_eps_lev hq hq1' hp hcl, hcl,
      fun h => absurd h (uf_not_lt_E hp h2)⟩
  have hSCmid : ∀ p, SC p → Om 1 < p → p < Om (1 + 1) → (p < ucB → UcCl q p) →
      RiDg q p ∧ UfLev q p ∧ (p < ucB → UcCl q p) ∧ (p < ucE → UfP (UfK q) p) := by
    intro p hp h1 h2 hcl
    exact ⟨hepsD p (Low.opow_eq_self_of_SC hp) h1.le, uf_eps_lev hq hq1' (Low.opow_eq_self_of_SC hp) hcl, hcl,
      fun _ => (ufP_small (by rw [uf_Om2]; exact h2)).2 hcl⟩
  have hOm2P : UfP (UfK q) OmTwo := by
    intro c hc
    rw [ucComps_Om2] at hc
    rcases hc with rfl | hc
    · exact hK1
    · rw [mem_singleton_iff] at hc; rw [hc]; exact hK0
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact hbig _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n)
  | inaccW => exact hbig _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_, fun h => ?_, fun h => ?_⟩
    · intro j hj h
      by_cases hx0 : x / Le.leOe j % Om 1 = 0
      · by_cases hy0 : y / Le.leOe j % Om 1 = 0
        · exfalso
          have := rhk_dig_add j x y
          rw [hx0, hy0, add_zero] at this
          exact h (le_antisymm this zero_le)
        · exact ihy.2.1 j hj hy0
      · exact ihx.2.1 j hj hx0
    · exact UcCl.add (ihx.2.2.1 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.1 (lt_of_le_of_lt le_add_self h))
    · exact ufP_add hK0 hKadd h (ihx.2.2.2 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.2 (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    have hcl : veblen x y < ucB → UcCl q (veblen x y) := fun h =>
      UcCl.phi (ihx.2.2.1 ((left_le_veblen x y).trans_lt h)) (ihy.2.2.1 ((right_le_veblen x y).trans_lt h))
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨fun j => ?_, fun j hj h => ?_, hcl, fun h => ?_⟩
        · rw [veblen_zero_apply]
          have hy0 := ihy.1 0
          rw [rhk_dig_zero] at hy0
          exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
        · rw [veblen_zero_apply] at h
          obtain ⟨hjy, hyB⟩ := uf_dig_opow_lvl hj h
          rw [← hjy]
          exact uf_lvl_of_cl hq hq1' (ihy.2.2.1 hyB)
        · rw [veblen_zero_apply] at h ⊢
          have hyE : y < ucE := ((isNormal_opow one_lt_omega0).strictMono.le_apply).trans_lt h
          exact ufP_opow hK0 hfin hKop h (ihy.2.2.2 hyE)
      · have hε : ω ^ veblen x y = veblen x y := Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)
        refine ⟨hepsD _ hε hv, uf_eps_lev hq hq1' hε hcl, hcl, fun h => ?_⟩
        rcases lt_trichotomy (veblen x y) (Om (1 + 1)) with hlt | heq | hgt
        · exact (ufP_small (by rw [uf_Om2]; exact hlt)).2 hcl
        · rw [heq, ← uf_Om2]; exact hOm2P
        · exact absurd h (uf_not_lt_E hε hgt)
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1
    have hε : ω ^ Om x = Om x := Low.opow_eq_self_of_SC (SC_Om hx0)
    rcases lt_trichotomy (Om x) (Om (1 + 1)) with hlt | heq | hgt
    · have hx2 : x < 1 + 1 := Om_lt_Om.1 hlt
      have hx1 : x = 1 := le_antisymm (Order.lt_add_one_iff.1 hx2) (Order.one_le_iff_ne_zero.2 hx0)
      subst hx1
      have hcl : Om 1 < ucB → UcCl q (Om 1) := fun _ => by rw [← rj_Om1]; exact UcCl.om
      exact ⟨hepsD _ hε le_rfl, uf_eps_lev hq hq1' hε hcl, hcl,
        fun _ => (ufP_small (by rw [uf_Om2]; exact ts_Om1_lt_Om2)).2 hcl⟩
    · rw [heq]
      have hcl : Om (1 + 1) < ucB → UcCl q (Om (1 + 1)) := fun h => absurd (h.trans hB2) (lt_irrefl _)
      have hε2 : ω ^ Om (1 + 1) = Om (1 + 1) := ts_Om2_opow
      exact ⟨hepsD _ hε2 ts_Om1_lt_Om2.le, uf_eps_lev hq hq1' hε2 hcl, hcl, fun _ => by rw [← uf_Om2]; exact hOm2P⟩
    · exact hbig _ hε hgt
  | @coll π e hπ hπW _ _ _ ihe =>
    have hπ1 : π ≠ Om 1 := by rwa [zero_add] at hπW
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
      have hcl : S.psi e (Om (1 + 1)) < ucB → UcCl q (S.psi e (Om (1 + 1))) := by
        intro h
        have heE : e < ucE := by
          by_contra hc
          push Not at hc
          have := (psi_mono hκ hc).1
          rw [uc_psiE_eq_B] at this
          exact absurd h (not_lt.2 this)
        exact uf_key hq hq1' (ihe.2.2.2 heE) h
      exact hSCmid _ (SC_psi hκ e) (ts_Om1_lt_psi _) (ts_psi_lt _) hcl
    · exact hbig _ (Low.opow_eq_self_of_SC (SC_psi hπ e)) (ts_Om2_lt_psi hπ hπ1 hπ2)

/-! ## Codes are the visibility closure; `Φ = ucP` below `B₂` -/

/-- **`UcCl q z ↔ z ∈ K_q`** for `z < B₂` and a strongly critical `q ≤ Ω₁`. -/
theorem uo_cl_iffK {q z : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hz : z < ucB) :
    UcCl q z ↔ UlK S 0 q z :=
  ⟨uo_ucK hq hq1 z, fun h => (uo_diglevK hq (by rw [← tw_Om1_eq]; exact hq1) z h).2.2.1 hz⟩

/-- Every `z < B₂` is in `K_v` for a strongly critical `v > Ω₁`. -/
theorem uo_K_big {v z : Ordinal.{0}} (hv1 : Om1 < v) (hz : z < ucB) : UlK S 0 v z := by
  have hO : SC (Om1 : Ordinal.{0}) := by rw [tw_Om1_eq]; exact SC_Om one_ne_zero
  have hc : UcCl Om1 z := (uc_cl_iff hO hz).2 (ucDat_lt_Om1 z)
  exact (uo_ucK hO le_rfl z hc).mono hv1.le

/-- **`ulD j < v ↔ ucDatL j < v`** for `j < B₂` and every strongly critical `v`. -/
theorem uo_vis_datL {j v : Ordinal.{0}} (hj : j < ucB) (hv : SC v) : ulD S 0 j < v ↔ ucDatL j < v := by
  rw [ul_vis hv]
  rcases le_or_gt v Om1 with hv1 | hv1
  · obtain ⟨-, hjB⟩ := uc_lev_lt hj
    rw [← uo_cl_iffK hv hv1 hj, ucDatL, ← uc_cl_iff hv hjB, uc_cl_Om1_add hv hv1]
  · exact ⟨fun _ => (ucDatL_lt_Om1 j).trans hv1, fun _ => uo_K_big hv1 hj⟩

/-- **`Φ_μ = Uc.ucP μ` for every level `μ < B₂`** (the lifted hierarchy at `s = 0` is the hierarchy on the data). -/
theorem uo_phi_ucP {μ : Ordinal.{0}} (hμ : μ < ucB) : ulH S 0 μ = ucP μ := by
  unfold ulH ucP
  rw [Om_zero]
  exact ul_ucG_congr μ fun j hj v hv _ => uo_vis_datL (hj.trans_lt hμ) hv

end Googology.Trans.PoR.InaccPsi.R2.Uo
