import Googology.Trans.PoR.InaccPsi.R2.LpLx
import Googology.Trans.PoR.InaccPsi.R2.CitedLq

/-!
# The limit of the ladder over a base is a new base: the layer with top `ϑˣ(Ω₁·Ω₁ + k) = Γ_{x+1+k}`

For a base `B` whose top `E_K(x)` lies in `[ϑˣ(Ω₁·Ω₁ + j), ϑˣ(Ω₁·Ω₁ + k))` for every `j < k` (`LpLimH B k`), the whole
tower `lpSys B n`, `n < ω`, is one term system `lpUSys B k` with top `gk k x = ϑˣ(Ω₁·Ω₁ + k)`, and it is again a layer
(`R2.XtLay`) with an `ε`-number top in `Tˣ`, so the construction iterates.  From the cited facts already in the repo
(`R2.CitedLg`: `lgArg_mem`, `lgVt_lt_low`, `lgLt_of_vt_lt`, `lgQuot_mem`, `lgLhT_sq`, `lgPi_OmOm`; `R2.CitedLq`:
`lqVt_lt`), no new axiom:

* `gk`, `gk_facts`, `gk_lt` (**`k ↦ ϑˣ(Ω₁·Ω₁ + k)` is strictly increasing**), `gk_le1R` (**`gk ≤₁ gk·gk` in `R₁⁺`**),
  `gk_pi` (**Lemma EXACT for `gk`**: `π_{σ,ρ}(ϑ^ρ(Ω₁·Ω₁ + k)) = ϑ^σ(Ω₁·Ω₁ + k)`), `gk_lt_next`;
* `lp_gP_lt_gk`, `lp_lt_gk_iff` (**`v < ϑˣ(Ω₁·Ω₁ + k)` iff `v < gP B n x` for some `n`**: the tower over the base ends
  exactly at the next strongly critical ordinal), `lp_not_le1R_sq` (no `ε`-number `a ∈ (E_K(x), gk k x)` has
  `a ≤₁ a·a`);
* `lpUSys B k H` (the term system of all terms, top `gk k`), `LpLK.lpTopWit` (**the witness pair of the top**:
  `f(gk) ∈ E` and `gk(fρ) ≤ f(gk)`, from `gk ≤₁ gk·gk`, the witness of the top of `K` and `lp_not_le1R_sq`),
  `lpLim B k H : XtLay`, `lpLimB` (the new base package), `lpLimH_next`
  (**the hypothesis passes to the new base with `k + 1`**);
* `lpLim_topIn` (the stage tops are terms of `lpUSys`), `lpFam_lt_lim` (**`Λ^B = sup_n Λ⁺(lpSys B n) < Λ⁺(lpUSys)`**),
  `lpLim_topIn_K` (the top of `K` is a term), `lpLim_gt_K` (**`Λ⁺(K) < Λ⁺(lpUSys)`**).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu

/-- **`gk k x = ϑˣ(Ω₁·Ω₁ + k)`** (`= Γ_{x+1+k}`). -/
noncomputable def gk (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * Om1 + k)

section GK

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gk_nat (k : ℕ) : (k : Ordinal.{0}) ∈ Tset x ∧ (k : Ordinal.{0}) < Om1 ∧ (k : Ordinal.{0}) < x := by
  have hkx : (k : Ordinal.{0}) < x := (natCast_lt_omega0 k).trans_le (lu_omega_lt_E hx).le
  exact ⟨mem_T_of_le hx hx1 hkx.le, hkx.trans hx1, hkx⟩

theorem gk_arg (k : ℕ) : Om1 * Om1 + k ∈ Tset x ∧ Om1 * Om1 + k < OmTwo := by
  obtain ⟨hkT, hk1, -⟩ := gk_nat hx hx1 k
  exact ⟨lgArg_mem hx hx1 hkT hk1, lg_OmOm_lt hk1⟩

/-- The facts on `gk k x`. -/
theorem gk_facts (k : ℕ) : gk k x ∈ Tset x ∧ x < gk k x ∧ gk k x < Om1 ∧ InE (gk k x) ∧ Indec (gk k x) := by
  obtain ⟨hT, h2⟩ := gk_arg hx hx1 k
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hT h2
  have hE := (vt_E_iff hx hx1 hT h2).2 (lg_Om1_le_OmOm.trans le_self_add)
  exact ⟨hvT, hE.1, hv1, hE.2, hvP⟩

/-- **`k ↦ ϑˣ(Ω₁·Ω₁ + k)` is strictly increasing.** -/
theorem gk_lt {j k : ℕ} (h : j < k) : gk j x < gk k x := by
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 (lu_one_lt_E hx).le
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (lu_one_lt_E hx).trans hx1
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hjT, hj1, hjx⟩ := gk_nat hx hx1 j
  obtain ⟨hkT, hk1, -⟩ := gk_nat hx hx1 k
  obtain ⟨-, hxv, -, -, -⟩ := gk_facts hx hx1 k
  have hjk : (j : Ordinal.{0}) < k := by exact_mod_cast h
  have e1 : ∀ z, Om1 * (Om1 * 1 + 0) + z = Om1 * Om1 + z := fun z => by rw [mul_one, add_zero]
  have := lqVt_lt hx hx1 h1T h1Ω h0T h0Ω hjT hj1 le_rfl h1T h1Ω h0T h0Ω hkT hk1
    (by rw [e1, e1]; exact (add_lt_add_iff_left _).2 hjk)
    (by rw [e1]; exact (lu_one_lt_E hx).trans hxv) (by rw [e1]; exact hx.pos.trans hxv)
    (by rw [e1]; exact hjx.trans hxv)
  rw [e1, e1] at this
  exact this

theorem gk_mono {j k : ℕ} (h : j ≤ k) : gk j x ≤ gk k x := by
  rcases h.lt_or_eq with h | rfl
  · exact (gk_lt hx hx1 h).le
  · exact le_rfl

/-- **`gk k x ≤₁ gk k x · gk k x` in `R₁⁺`.** -/
theorem gk_le1R (k : ℕ) : le1R (gk k x) (gk k x * gk k x) := by
  obtain ⟨hT, h2⟩ := gk_arg hx hx1 k
  obtain ⟨hVT, hxV, hV1, hVE, hVP⟩ := gk_facts hx hx1 k
  have hL := lh_eq_lhT (Or.inr hx) hx1 hVT hxV hV1 hVP
  have hsq := lgLhT_sq hx hx1 hT h2 le_self_add
  exact le1R_of_le (le_mul_left _ hVE.pos) hsq hL.1

/-- `gk k x` lies below every next point above the base. -/
theorem gk_lt_next (k : ℕ) {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : gk k x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, h1, -, -⟩ := gk_facts hx hx1 k
  exact ((hTm _ h1).1 hT).trans_le (hmin u hxu hu)

end GK

/-- **Lemma EXACT for `gk`**: `π_{σ,ρ}(ϑ^ρ(Ω₁·Ω₁ + k)) = ϑ^σ(Ω₁·Ω₁ + k)`. -/
theorem gk_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (k : ℕ) : gk k ρ ∈ TB ρ σ ∧ pi σ ρ (gk k ρ) = gk k σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hB' : Bases σ ρ := ⟨hσE, hρE, hσρ, hρ1⟩
  have hσ1 : σ < Om1 := hσρ.trans hρ1
  obtain ⟨hTB0, hpi0⟩ := lgPi_OmOm hB'
  have hkσ : (k : Ordinal.{0}) < σ := (gk_nat hσE hσ1 k).2.2
  obtain ⟨hTBs, hpis⟩ := pi_add hB' hTB0 (mem_TB_of_lt hB' hkσ)
  rw [hpi0, pi_lt hB' hkσ] at hpis
  have h2 := (gk_arg hρE hρ1 k).2
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1 + k))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * Om1 + k)) = vt σ (Om1 * Om1 + k)
    rw [pi_vt_two hB' hTBs h2, hpis]

theorem gk_lt_next_ups (k : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    gk k (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (gk_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) k (upsilon_normal.strictMono h1) hτU.2).trans
    (upsilon_normal.strictMono (lt_add_one _))

/-- **The limit hypothesis**: `ϑˣ(Ω₁·Ω₁ + j) ≤ E_K(x) < ϑˣ(Ω₁·Ω₁ + k)` for every `j < k`. -/
structure LpLimH (B : LpB) (k : ℕ) : Prop where
  lo : ∀ x, InE x → x < Om1 → ∀ j : ℕ, j < k → gk j x ≤ B.K.E x
  hi : ∀ x, InE x → x < Om1 → B.K.E x < gk k x

section Lim

variable {B : LpB} {k : ℕ} (H : LpLimH B k)
include H

theorem lp_gP_lt_gk {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ∀ n : ℕ, gP B n x < gk k x
  | 0 => H.hi x hx hx1
  | n + 1 => by
      obtain ⟨hgT, -, hg1, -⟩ := gP_facts B hx hx1 n
      obtain ⟨hkT, hk1, -⟩ := gk_nat hx hx1 k
      have ih := lp_gP_lt_gk hx hx1 n
      have h := lgVt_lt_low hx hx1 hgT hg1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hkT hk1 ih
        (hx.pos.trans (gk_facts hx hx1 k).2.1)
      rw [add_zero] at h
      exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + k)` iff `v < gP B n x` for some `n`.** -/
theorem lp_lt_gk_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ v, v < gk k x → ∃ n, v < gP B n x := by
  obtain ⟨hGT, hxG, hG1, -, -⟩ := gk_facts hx hx1 k
  obtain ⟨hkT, hk1, hkx⟩ := gk_nat hx hx1 k
  have hEP1 : B.K.E x < gP B 1 x := gP_lt_succ B hx hx1 0
  have hxE := Lx.lx_E_gt B.ek hx hx1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (B.K.E x) with hvE | hEv
  · exact ⟨1, hvE.trans_lt hEP1⟩
  have hxv : x < v := hxE.trans hEv
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + k :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hkT hk1 (by rw [hξv]; exact hkx.trans hxv) (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2 + 1, ?_⟩
        have hq' : ξ / Om1 < gP B (max n1 n2) x := hn1.trans_le (gP_mono B hx hx1 (le_max_left _ _))
        have hr' : ξ % Om1 < gP B (max n1 n2 + 1) x :=
          hn2.trans_le (gP_mono B hx hx1 ((le_max_right _ _).trans (Nat.le_succ _)))
        rw [← hξv, ← hdec]
        exact lp_lt_top B hx hx1 hqT hq' hrT hr1 hr'
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < k := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ := lt_omega0.1 (hjk.trans (natCast_lt_omega0 k))
        have hj' : j < k := by
          have : (j : Ordinal.{0}) < k := hj ▸ hjk
          exact_mod_cast this
        have hvj : v = gk j x := by rw [← hξv, ← hje, hj]; rfl
        exact absurd (H.lo x hx hx1 j hj') (not_le.2 (hvj ▸ hEv))
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gP_facts B hx hx1 n).2.2.2.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gP_facts B hx hx1 _).2.2.2).add_lt (h1.trans_le (gP_mono B hx hx1 (le_max_left _ _)))
      (h2.trans_le (gP_mono B hx hx1 (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (E_K(x), ϑˣ(Ω₁·Ω₁ + k))` has `a ≤₁ a·a` in `R₁⁺`.** -/
theorem lp_not_le1R_sq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {a : Ordinal.{0}} (haE : InE a)
    (hEa : B.K.E x < a) (hak : a < gk k x) : ¬ le1R a (a * a) := by
  intro hR
  have hxa : x < a := (Lx.lx_E_gt B.ek hx hx1).trans hEa
  obtain ⟨n, hn⟩ := lp_lt_gk_iff H hx hx1 a hak
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd hn (not_lt.2 hEa.le)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gP_facts B hx hx1 (M + 1)
  have ha1 : a < Om1 := hn.trans hT1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gP B M x :=
    lp_quot hx hx1 M ξ hξT hξ2 (by rw [hξv]; exact hxa) (by rw [hξv]; exact haE) (by rw [hξv]; exact hEa)
      (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gP_facts B hx hx1 M
  have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 hMT hM1 hqM.le
  set q := ξ / Om1 with hq
  set r := ξ % Om1 with hr
  have hv : vt x (Om1 * q + r) = a := by rw [hdec, hξv]
  have hζr : luZeta x q r < a := by
    refine lu_zeta_le.trans_lt ?_
    rcases lt_or_ge q x with hqx | hxq
    · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
      rwa [hv] at this
    · have := (Lv.gen_facts hx hx1 hqT hxq (hqM.trans hM1) hrT hr1).2.2.2.2.2.2.2.2
      rwa [hv] at this
  have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
    rcases lt_or_ge q x with hqx | hxq
    · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
      rw [hv] at h
      exact ⟨h, hqx.trans hxa⟩
    · have h := Lv.lv_lh_gen hx hx1 hqT hxq (hqM.trans hM1) hrT hr1
      have hqv := (Lv.gen_facts hx hx1 hqT hxq (hqM.trans hM1) hrT hr1).2.2.2.2.2.2.2.1
      rw [hv] at h hqv
      exact ⟨h, hqv⟩
  have hle := hL.1.2 _ hR
  exact absurd hle (not_le.2 (lg_luL_lt_sq haE hL.2 hζr))

end Lim

/-- **The limit term system over the base**: all terms of `LpT B`, top `gk k = ϑˣ(Ω₁·Ω₁ + k)`. -/
noncomputable def lpUSys (B : LpB) (k : ℕ) (H : LpLimH B k) : XtSys where
  Tm := LpT B
  val := LpT.val
  CB := LpT.CBt
  cs := LpT.cs
  cst := LpT.cst
  top := gk k
  cb_cst := fun _ _ h => LpT.cbt_cst h
  cb_iff := fun _ _ _ h hc => LpT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (LpT.lp_T (ups_inE hl) (ups_lt_Om1 l hl1) t hCB).2.trans (lp_gP_lt_gk H (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (gk_facts (ups_inE hl) (ups_lt_Om1 l hl1) k).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨n, hn⟩ := lp_lt_gk_iff H (ups_inE hl) (ups_lt_Om1 l hl1) v hv
    obtain ⟨t, h1, -, h3⟩ :=
      lp_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) (Lx.lxRep_ri B.ek hl hl1) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => gk_lt_next_ups k hl hl1
  pkg := fun _ hl hl1 _ hCB h1 R => LpGK.pkgLp R (Lx.lxRep_ri B.ek hl hl1) (Lx.lxBase_ri B.ek hl hl1 R) hCB h1
  rs := fun _ _ _ _ hCB => rsStep_Lp hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => LpT.uni_le hσ hρ hB ht hu
  small := fun t => by
    rcases lp_small t with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx1 hc => h x hx hx1 hc

theorem lpUSys_top (B : LpB) (k : ℕ) (H : LpLimH B k) (x : Ordinal.{0}) : (lpUSys B k H).top x = gk k x := rfl

namespace LpLK

variable {B : LpB} {k : ℕ} (H : LpLimH B k) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem gk_lt_δ : gk k ρ < δ := (gk_lt_next (upsPt_inE h.ρU) h.ρ1 k h.ρτ h.τU.2).trans h.τδ

/-- **The block witness of the top**: `f(gk) ∈ E` and, off the `υ`-points, `f(gk) ≤₁ f(gk)·f(gk)`. -/
theorem lpImgP {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    (hGA : gk k ρ ∈ A) (hGGA : gk k ρ + gk k ρ ∈ A) (hPA : gk k ρ * gk k ρ ∈ A)
    (hPGA : gk k ρ * gk k ρ + gk k ρ ∈ A) :
    InE (f (gk k ρ)) ∧ (¬ UpsPt (f (gk k ρ)) → le1R (f (gk k ρ)) (f (gk k ρ) * f (gk k ρ))) := by
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, -⟩ := gk_facts hρE h.ρ1 k
  set G := gk k ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := gk_lt_δ h
  have hPδ : P < δ := h.δE.mul_lt hGδ hGδ
  have hPGδ : P + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hfE : InE (f G) := LuK.luFE h C hGE hρG.le hGδ hGA hGGA
  refine ⟨hfE, fun hU => ?_⟩
  have hGP : G < P := lt_mul_of_one_lt_right hGE.pos (lu_one_lt_E hGE)
  have hsrc1 : le1 G P := (h.lowδ _ _ hρG hPδ.le).2 (gk_le1R hρE h.ρ1 k)
  have hR1 : le1R (f G) (f P) := (C.sk _ (C.low _ hGA) hU _).1 (C.cov1 G hGA P hPA hsrc1)
  have hfGP : f G < f P := C.mono hGA hPA hGP
  have hPge : f G * f G ≤ f P := by
    by_cases hUP : UpsPt (f P)
    · exact ((upsPt_inE hUP).mul_lt hfGP hfGP).le
    have hPe : P = ω ^ (G + G) := by
      rw [hP]; conv_lhs => rw [← show ω ^ G = G from hGE]
      rw [← opow_add]
    have hc0 : G + G ≠ 0 := (lt_of_lt_of_le hGE.pos le_self_add).ne'
    have hclt : G + G < ω ^ (G + G) := by
      rw [← hPe, hP, ← mul_two_eq G]
      have h2ω : (2 : Ordinal.{0}) < ω := by simpa using natCast_lt_omega0 2
      exact (mul_lt_mul_iff_right₀ hGE.pos).2 (h2ω.trans_le (lu_omega_lt_E hGE).le)
    have hGlg : G ≤ lg (G + G) := le_lg hc0 ⟨2, by rw [show ω ^ G = G from hGE]; exact (mul_two_eq G).symm⟩
    have hLP := lu_lh_opow hc0 hclt
    have hsrcR : le1R P (P + G) := by
      rw [hPe]
      exact le1R_of_le le_self_add ((add_le_add_iff_left _).2 hGlg) hLP.1
    have hρP : ρ < P := hρG.trans hGP
    have hsrc2 : le1 P (P + G) := (h.lowδ _ _ hρP hPGδ.le).2 hsrcR
    have himg : le1 (f P) (f P + f G) := by
      have := C.cov1 P hPA _ hPGA hsrc2
      rwa [← C.add P hPA G hGA _ hPGA rfl] at this
    have hR2 := (C.sk _ (C.low _ hPA) hUP _).1 himg
    obtain ⟨d, hd⟩ := indec_eq_opow (C.indec P hPA (by rw [hPe]; exact indec_opow _))
    rw [hd] at hR2 hfGP ⊢
    exact LgK.lg_sq_le_of_reach hfE hfGP hR2
  exact le1R_of_le (le_mul_left _ hfE.pos) hPge hR1

include H in
/-- **The witness pair of the top `gk`**: `f(gk(ρ)) ∈ E` and `gk(fρ) ≤ f(gk(ρ))`. -/
theorem lpTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gk k ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (gk k ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gk k (f ρ) ≤ f (gk k ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gk_facts hρE h.ρ1 k
  set G := gk k ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := gk_lt_δ h
  have hPδ : P < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : P + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hG0 : 0 < G := hGE.pos
  have hGP : G < P := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : P = ω ^ (G + G) := by
    rw [hP]; conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {P, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {P + G, P, G + G, G} ∅ := by
    have := w3.insW ((hρG.le.trans hGP.le).trans le_self_add) hPGδ
      (Or.inr ⟨P, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := B.K.top_wit ρ τ δ h
  have w5 : WZ ρ δ ({P + G, P, G + G, G} ∪ WE) (∅ ∪ ZE) := w4.union wE
  rw [Finset.empty_union] at w5
  refine ⟨{P + G, P, G + G, G} ∪ WE, ZE, w5, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hTA : B.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hsq⟩ := lpImgP h C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  -- `E_K(fρ) ≤ f(E_K(ρ)) < f(G)`
  have hTρ : B.K.sys.top ρ = B.K.E ρ := Lx.lx_top B.ek hρE h.ρ1
  have hTy : B.K.sys.top (f ρ) = B.K.E (f ρ) := Lx.lx_top B.ek hyE hy1
  have hEG : B.K.E ρ < G := H.hi ρ hρE h.ρ1
  have hfEG : f (B.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : B.K.E (f ρ) < f G := by
    have := (hIE A f hWE hZ C).2
    rw [hTy] at this
    exact this.trans_lt hfEG
  by_cases hU : UpsPt (f G)
  · exact (gk_lt_next hyE hy1 k hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    exact lp_not_le1R_sq H hyE hy1 hfE hEy hlt (hsq hU)

end LpLK

/-- **The limit layer over the base**: `lpUSys B k H` with top `ϑˣ(Ω₁·Ω₁ + k)`. -/
noncomputable def lpLim (B : LpB) (k : ℕ) (H : LpLimH B k) : XtLay where
  sys := lpUSys B k H
  E := gk k
  top_eq := fun x hx hx1 => (gk_facts hx hx1 k).2.2.2.1.symm
  exp_dvd := fun x hx hx1 => opow_dvd_of_inE (gk_facts hx hx1 k).2.2.2.1 (gk_facts hx hx1 k).2.1.le
  exp_lt := fun x hx hx1 => (gk_facts hx hx1 k).2.2.1
  top_gt := fun x hx hx1 => (gk_facts hx hx1 k).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => gk_lt_next hx hx1 k hxu hu.2
  lt_top_E := fun x hx hx1 t ht => (LpT.lp_T hx hx1 t ht).2.trans (lp_gP_lt_gk H hx hx1 _)
  exact := fun _ _ hσ hρ hB t ht => LpT.pi hσ hρ hB t ht
  exp_pi := fun _ _ _ _ hB => gk_pi hB k
  top_wit := fun _ _ _ h => LpLK.lpTopWit H h

/-- **The new base package**: the limit layer. -/
noncomputable def lpLimB (B : LpB) (k : ℕ) (H : LpLimH B k) : LpB where
  K := lpLim B k H
  ek := fun x hx hx1 => (gk_facts hx hx1 k).2.2.2.1
  mem := fun x hx hx1 => (gk_facts hx hx1 k).1

theorem lpLimB_E (B : LpB) (k : ℕ) (H : LpLimH B k) (x : Ordinal.{0}) : (lpLimB B k H).K.E x = gk k x := rfl

/-- **The limit hypothesis passes to the new base with `k + 1`.** -/
theorem lpLimH_next (B : LpB) (k : ℕ) (H : LpLimH B k) : LpLimH (lpLimB B k H) (k + 1) :=
  ⟨fun _ hx hx1 _ hj => gk_mono hx hx1 (Nat.lt_succ_iff.1 hj), fun _ hx hx1 => gk_lt hx hx1 (Nat.lt_succ_self k)⟩

section Rel

variable {B : LpB} {k : ℕ} (H : LpLimH B k)

/-- **The stage tops are terms of the limit system**, with gap `> 1`. -/
theorem lpLim_topIn (n : ℕ) : LyTopIn (lpUSys B k H) (lpSys B n) := by
  refine ⟨gTm n, fun x hx _ => ⟨(gTm_val (B := B) (upsPt_inE hx) n).1, (gTm_val (B := B) (upsPt_inE hx) n).2⟩,
    fun l hl hl1 => ?_⟩
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  have hE := (gP_facts B hρE hρ1 (n + 1)).2.2.2
  rw [lpSys_top, lpUSys_top]
  exact ((inE_indec hE).add_lt (gP_lt_succ B hρE hρ1 n) (lu_one_lt_E hE)).trans (lp_gP_lt_gk H hρE hρ1 (n + 1))

/-- **The top of the base layer is a term of the limit system.** -/
theorem lpLim_topIn_K : LyTopIn (lpUSys B k H) B.K.sys := by
  refine ⟨LpT.tp, fun x hx hx1 => ⟨trivial, ?_⟩, fun l hl hl1 => ?_⟩
  · show B.K.E x = B.K.sys.top x
    rw [Lx.lx_top B.ek (upsPt_inE hx) hx1]
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hG := (gk_facts hρE hρ1 k).2.2.2.1
    rw [lpUSys_top, Lx.lx_top B.ek hρE hρ1]
    exact (inE_indec hG).add_lt (H.hi _ hρE hρ1) (lu_one_lt_E hG)

theorem lpLim_topPkg : XtTopPkg (lpUSys B k H) := XtLay.topPkg (lpLim B k H)

/-- **`Λ^B = sup_n Λ⁺(lpSys B n) < Λ⁺(lpUSys B k H)`.** -/
theorem lpFam_lt_lim : (lpFam B).famSup < xtB1 (lpUSys B k H) := by
  refine lt_of_le_of_lt (Ordinal.iSup_le fun n => ?_) (lyLamLtB1 (lpLim_topPkg H))
  exact (lyLamGt (lpSys_topPkg n) (lpLim_topIn H n)).le

/-- **`Λ⁺(K) < Λ⁺(lpUSys B k H)`.** -/
theorem lpLim_gt_K : xtB1 B.K.sys < xtB1 (lpUSys B k H) :=
  lyB1_lt (lpLim_topPkg H) (XtLay.topPkg B.K) (lpLim_topIn_K H)

/-- **`O_{lpUSys} = O_{lpSys B n}` below `Λ⁺(lpSys B n)`.** -/
theorem lpLim_eq (n : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lpSys B n)) :
    xtOrec (lpUSys B k H) μ = xtOrec (lpSys B n) μ :=
  lyEq (lpSys_topPkg n) (lpLim_topIn H n) hμ h

end Rel

end Googology.Trans.PoR.InaccPsi.R2.Lp
