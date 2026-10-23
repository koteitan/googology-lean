import Googology.Trans.PoR.InaccPsi.R2.GdJ
import Googology.Trans.PoR.InaccPsi.R2.GcDiag

/-!
# The limit of the ladder over a gated base: the gated layer with top `ϑˣ(Ω₁·Ω₁ + η)` above the gate

`R2.GbLim` above a gate: for a gated base `B` whose top `E_K(x)` lies in `[ϑˣ(Ω₁·Ω₁ + j), ϑˣ(Ω₁·Ω₁ + η))` for every
`j < η` at every base above the gate, and `η` below every base above the gate (`GdqH B η`), all the terms of `GdT B`
form one gated term system `gdqUSys B η H` with top `gq η x`, again a gated layer with an `ε`-number top in `Tˣ`:

* `rs_rstGd`, `rsStep_Gd` (**Lemma RS for every term above the gate**: `rs_rstF` with the gate among the constants);
* `gdq_gP_lt`, `gdq_lt_iff` (**`v < ϑˣ(Ω₁·Ω₁ + η)` iff `v < gdP B n x` for some `n`**), `gdq_not_le1R_sq`;
* `gdqUSys`, `GdqK.gdqTopWit` (the witness pair of the top, for the copies that keep the gate), `gdqLim : GdLay`,
  `gdqLimB : GdB`, `gdqLimB_E`.

No new axiom.  New definitions: `GdqH`, `gdqUSys`, `gdqLim`, `gdqLimB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb

variable {B : GdB}

/-! ## Lemma RS above the gate -/

/-- **Lemma RS with the target `t(ρ)`** for `GdT B` above the gate (the gate is one of the constants). -/
theorem rs_rstGd {r : Ordinal.{0}}
    (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1))) (hg : B.g < upsilon r)
    {s : GdT B} (hs : GdT.CBt s (upsilon r)) (hρs : upsilon r ≤ GdT.val s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + GdT.val s (upsilon μ) → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + GdT.val s (upsilon r) + 1) := by
  classical
  have hnx := upsilon_isNext r
  have hCs : ∀ σ, (∀ c ∈ insert B.g (GdT.cs s).toFinset, c < σ) → GdT.CBt s σ := fun σ hσ =>
    GdT.cbt_iff hs (fun c hc => hσ c (Finset.mem_insert_of_mem (List.mem_toFinset.2 hc)))
  have hgσ : ∀ σ, (∀ c ∈ insert B.g (GdT.cs s).toFinset, c < σ) → B.g < σ := fun σ hσ =>
    hσ _ (Finset.mem_insert_self _ _)
  refine rs_rstF (T := GdT.val s) (C := insert B.g (GdT.cs s).toFinset) h
    (fun c hc => by
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact hg
      · exact GdT.cbt_cst hs c (List.mem_toFinset.1 hc)) hρs
    (GdT.gd_lt_ups h.ρE h.ρ1 hg hs hnx.1 hnx.2.1) ?_ ?_ htarget
  · intro σ hσ hB hCσ _
    exact (GdT.pi hσ h.ρU hB (hgσ σ hCσ) s (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    exact GdT.gd_lt_next hσE (hσρ.trans h.ρ1) (hgσ σ hCσ) (hCs σ hCσ) hσρ h.ρU.2

/-- **Lemma RS for every term of `GdT B`** with constants below `ρ_λ` above the gate. -/
theorem rsStep_Gd {l : Ordinal.{0}} (hg : B.g < upsilon l) {s : GdT B} (hs : GdT.CBt s (upsilon l)) :
    RsStep l (GdT.val s) := by
  intro R htg
  by_cases hρs : upsilon l ≤ GdT.val s (upsilon l)
  · exact rs_rstGd R hg hs hρs htg
  · have hn : GdT.noB s := by
      by_contra hn
      exact hρs (GdT.le_of_not_noB R.ρE R.ρ1 hg s hs hn)
    set c := GdT.val s (upsilon l) with hc
    have e : GdT.val s = OT.ev (OT.k c) := funext (fun y => by
      rw [OT.ev_k, hc, GdT.noB_val s hn y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have h := rs_rstT R hcb htg
    rwa [OT.ev_k] at h

/-! ## The limit hypothesis above the gate -/

/-- **The limit hypothesis above the gate**: `η` is below every base above the gate, and
`ϑˣ(Ω₁·Ω₁ + j) ≤ E_K(x) < ϑˣ(Ω₁·Ω₁ + η)` for every `j < η` at every base above the gate. -/
structure GdqH (B : GdB) (η : Ordinal.{0}) : Prop where
  cst : ∀ x, InE x → B.g < x → η < x
  lo : ∀ x, InE x → x < Om1 → B.g < x → ∀ j, j < η → gq j x ≤ B.K.E x
  hi : ∀ x, InE x → x < Om1 → B.g < x → B.K.E x < gq η x

section Lim

variable {η : Ordinal.{0}} (H : GdqH B η)
include H

theorem gdq_gP_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) : ∀ n : ℕ, gdP B n x < gq η x
  | 0 => H.hi x hx hx1 hg
  | n + 1 => by
      obtain ⟨hgT, -, hg1, -⟩ := gdP_facts B hx hx1 hg n
      obtain ⟨hkT, hk1⟩ := gq_cst hx hx1 (H.cst x hx hg)
      have ih := gdq_gP_lt hx hx1 hg n
      have h := lgVt_lt_low hx hx1 hgT hg1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hkT hk1 ih
        (hx.pos.trans (gq_facts hx hx1 (H.cst x hx hg)).2.1)
      rw [add_zero] at h
      exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + η)` iff `v < gdP B n x` for some `n`** (above the gate). -/
theorem gdq_lt_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ v, v < gq η x → ∃ n, v < gdP B n x := by
  have hηx := H.cst x hx hg
  obtain ⟨hGT, -, hG1, -, -⟩ := gq_facts hx hx1 hηx
  obtain ⟨hkT, hk1⟩ := gq_cst hx hx1 hηx
  have hEP1 : B.K.E x < gdP B 1 x := gdP_lt_succ B hx hx1 hg 0
  have hxE := gdx_E_gt hx hx1 hg
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
      have hξk : ξ < Om1 * Om1 + η :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hkT hk1 (by rw [hξv]; exact hηx.trans hxv) (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
            have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2 + 1, ?_⟩
        have hq' : ξ / Om1 < gdP B (max n1 n2) x := hn1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _))
        have hr' : ξ % Om1 < gdP B (max n1 n2 + 1) x :=
          hn2.trans_le (gdP_mono B hx hx1 hg ((le_max_right _ _).trans (Nat.le_succ _)))
        rw [← hξv, ← hdec]
        exact gd_lt_top B hx hx1 hg hqT hq' hrT hr1 hr'
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < η := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ : ∃ j, j = ξ - Om1 * Om1 := ⟨_, rfl⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje, ← hj]; rfl
        exact absurd (H.lo x hx hx1 hg j (hj ▸ hjk)) (not_le.2 (hvj ▸ hEv))
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gdP_facts B hx hx1 hg n).2.2.2.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gdP_facts B hx hx1 hg _).2.2.2).add_lt
      (h1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _)))
      (h2.trans_le (gdP_mono B hx hx1 hg (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (E_K(x), ϑˣ(Ω₁·Ω₁ + η))` has `a ≤₁ a·a` in `R₁⁺`** (above the gate). -/
theorem gdq_not_le1R_sq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) {a : Ordinal.{0}}
    (haE : InE a) (hEa : B.K.E x < a) (hak : a < gq η x) : ¬ le1R a (a * a) := by
  intro hR
  have hxa : x < a := (gdx_E_gt hx hx1 hg).trans hEa
  obtain ⟨n, hn⟩ := gdq_lt_iff H hx hx1 hg a hak
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := by
    rcases n with _ | M
    · exact absurd hn (not_lt.2 hEa.le)
    · exact ⟨M, rfl⟩
  obtain ⟨hTT, -, hT1, -⟩ := gdP_facts B hx hx1 hg (M + 1)
  have ha1 : a < Om1 := hn.trans hT1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hTT hT1 hn.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
  have hqM : ξ / Om1 < gdP B M x :=
    gd_quot hx hx1 hg M ξ hξT hξ2 (by rw [hξv]; exact hxa) (by rw [hξv]; exact haE) (by rw [hξv]; exact hEa)
      (by rw [hξv]; exact hn)
  obtain ⟨hMT, -, hM1, -⟩ := gdP_facts B hx hx1 hg M
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

theorem gdq_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hg : B.g < upsilon l) :
    gq η (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact (gq_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) (H.cst _ (ups_inE hl) hg) (upsilon_normal.strictMono h1)
    hτU.2).trans (upsilon_normal.strictMono (lt_add_one _))

end Lim

/-! ## The gated limit system and layer -/

/-- **The limit term system over the gated base**: all terms of `GdT B`, top `gq η = ϑˣ(Ω₁·Ω₁ + η)`. -/
noncomputable def gdqUSys (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) : GdSys B.g where
  Tm := GdT B
  val := GdT.val
  CB := GdT.CBt
  cs := GdT.cs
  cst := GdT.cst
  top := gq η
  cb_cst := fun _ _ h => GdT.cbt_cst h
  cb_iff := fun _ _ _ h hc => GdT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 hg t hCB =>
    (GdT.gd_T (ups_inE hl) (ups_lt_Om1 l hl1) hg t hCB).2.trans
      (gdq_gP_lt H (ups_inE hl) (ups_lt_Om1 l hl1) hg _)
  one_le_top := fun l hl hl1 hg =>
    one_le_iff_pos.2 (gq_facts (ups_inE hl) (ups_lt_Om1 l hl1) (H.cst _ (ups_inE hl) hg)).2.2.2.1.pos
  rep := fun l hl hl1 hg v hv => by
    obtain ⟨n, hn⟩ := gdq_lt_iff H (ups_inE hl) (ups_lt_Om1 l hl1) hg v hv
    obtain ⟨t, h1, -, h3⟩ :=
      gd_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) hg (gdxRep_ri hl hl1 hg) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 hg => gdq_lt_next_ups H hl hl1 hg
  pkg := fun _ hl hl1 hg _ hCB h1 R => GdGK.pkgGd R hg (gdxRep_ri hl hl1 hg) (gdxBase_ri hl hl1 hg R) hCB h1
  rs := fun _ _ _ hg _ hCB => rsStep_Gd hg hCB
  uni_le := fun _ _ hσ hρ hB hg _ _ ht hu => GdT.uni_le hσ hρ hB hg ht hu
  small := gd_small

theorem gdqUSys_top (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) (x : Ordinal.{0}) :
    (gdqUSys B η H).top x = gq η x := rfl

namespace GdqK

variable {η : Ordinal.{0}} (H : GdqH B η) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hg : B.g < ρ)
include H h hg

theorem gdq_lt_δ : gq η ρ < δ :=
  (gq_lt_next (upsPt_inE h.ρU) h.ρ1 (H.cst _ (upsPt_inE h.ρU) hg) h.ρτ h.τU.2).trans h.τδ

/-- **The witness pair of the top `gq η`** above the gate: `f(gq η ρ) ∈ E` and `gq η (fρ) ≤ f(gq η ρ)` for the
copies that keep the gate. -/
theorem gdqTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq η ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx B.g ρ A f →
      (∃ e', f (gq η ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq η (f ρ) ≤ f (gq η ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  have hηρ := H.cst ρ hρE hg
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gq_facts hρE h.ρ1 hηρ
  have hR0 := gq_le1R hρE h.ρ1 hηρ
  set G := gq η ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := gdq_lt_δ H h hg
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
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := B.K.top_wit ρ τ δ h hg
  have w5 : WZ ρ δ ({P + G, P, G + G, G} ∪ WE) (∅ ∪ ZE) := w4.union wE
  rw [Finset.empty_union] at w5
  refine ⟨{P + G, P, G + G, G} ∪ WE, ZE, w5, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hTA : B.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C.1 hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
  have hgy : B.g < f ρ := C.lt hg
  have hTρ : B.K.sys.top ρ = B.K.E ρ := gdx_top hρE h.ρ1 hg
  have hTy : B.K.sys.top (f ρ) = B.K.E (f ρ) := gdx_top hyE hy1 hgy
  have hEG : B.K.E ρ < G := H.hi ρ hρE h.ρ1 hg
  have hfEG : f (B.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : B.K.E (f ρ) < f G := by
    have := (hIE A f hWE hZ C).2
    rw [hTy] at this
    exact this.trans_lt hfEG
  by_cases hU : UpsPt (f G)
  · exact (gq_lt_next hyE hy1 (H.cst _ hyE hgy) hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc1 : le1 G P := (h.lowδ _ _ hρG hPδ.le).2 hR0
    have hR1 : le1R (f G) (f P) := (C.sk _ (C.low _ hGA) hU _).1 (C.cov1 G hGA P hPA hsrc1)
    exact gdq_not_le1R_sq H hyE hy1 hgy hfE hEy hlt (le1R_of_le (le_mul_left _ hfE.pos) hPge hR1)

end GdqK

/-- **The limit layer over the gated base**: `gdqUSys B η H` with top `ϑˣ(Ω₁·Ω₁ + η)`, above the gate. -/
noncomputable def gdqLim (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) : GdLay B.g where
  sys := gdqUSys B η H
  E := gq η
  top_eq := fun x hx hx1 hg => (gq_facts hx hx1 (H.cst x hx hg)).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg =>
    opow_dvd_of_inE (gq_facts hx hx1 (H.cst x hx hg)).2.2.2.1 (gq_facts hx hx1 (H.cst x hx hg)).2.1.le
  exp_lt := fun x hx hx1 hg => (gq_facts hx hx1 (H.cst x hx hg)).2.2.1
  top_gt := fun x hx hx1 hg => (gq_facts hx hx1 (H.cst x hx hg)).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu => gq_lt_next hx hx1 (H.cst x hx hg) hxu hu.2
  lt_top_E := fun x hx hx1 hg t ht => (GdT.gd_T hx hx1 hg t ht).2.trans (gdq_gP_lt H hx hx1 hg _)
  exact := fun _ _ hσ hρ hB hg t ht => GdT.pi hσ hρ hB hg t ht
  exp_pi := fun σ _ _ _ hB hg => gq_pi hB (H.cst σ hB.1 hg)
  top_wit := fun _ _ _ h hg => GdqK.gdqTopWit H h hg

/-- **The new gated base package**: the limit layer (same gate). -/
noncomputable def gdqLimB (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) : GdB where
  g := B.g
  K := gdqLim B η H
  ek := fun x hx hx1 hg => (gq_facts hx hx1 (H.cst x hx hg)).2.2.2.1
  mem := fun x hx hx1 hg => (gq_facts hx hx1 (H.cst x hx hg)).1

theorem gdqLimB_E (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) (x : Ordinal.{0}) :
    (gdqLimB B η H).K.E x = gq η x := rfl

theorem gdqLimB_g (B : GdB) (η : Ordinal.{0}) (H : GdqH B η) : (gdqLimB B η H).g = B.g := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gd
