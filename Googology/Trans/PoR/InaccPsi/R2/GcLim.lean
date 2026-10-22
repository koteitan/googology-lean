import Googology.Trans.PoR.InaccPsi.R2.GbLim

/-!
# THE GENERIC LIMIT BASE: the layer with top `Γ_{x+λ} = ϑˣ(Ω₁·Ω₁ + λ)` for every constant limit `λ`

`R2.GbW` makes the union of the tower `lpTK k` with top `Γ_{x+ω}`; its top witness separates `Γ_{x+ω}` from every
`Γ_{x+1+k}` by the `R₁⁺`-reach.  Here the same for every constant limit `λ` at once, over any family of layers
`K_β`, `β < λ`, with tops `ϑˣ(Ω₁·Ω₁ + 1 + β)`:

* `gc_one_add_lt`, `gc_lg_pos`, `gc_lg_lt` (**for `λ = λ' + ω^e`, `e = logend(λ)`, every `ν ∈ (λ', λ)` has
  `logend(ν) < e`**);
* `gc_zeta`, `gc_lh` (**`lh(ϑˣ(Ω₁·Ω₁ + ν)) = G·G + G + logend(ν)`** for every constant `ν > 0`, from `Lq.lq_lh_sq`),
  `gc_lt_lim_iff` (**`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`**), `gc_not_le1R_lim` (**no `ε`-number
  `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**);
* `GcLimH λ` (`λ` a constant limit), `GcLimF λ` (the family of layers), `gcUSys` (the union), `GcLK.gcTopWit`
  (**THE TOP WITNESS of `Γ_{x+λ}`**: `f(G) ∈ E`, and `Γ_{fρ+λ} ≤ f(G)` from the copy of `G ≤₁ G·G + G + e` and the
  witness of the layer `K_{λ'}` below), `gcLimL : XtLay`, `gcLimB : LpB`;
* `GcLift` (every term of one system is a term of another), `gcLim_lift`, `gcLim_topIn`, `gcLim_gt`, `gcLim_eq`.

No new axiom.  New definitions: `GcLimH`, `GcLimF`, `gcUSys`, `gcLimL`, `gcLimB`, `GcLift`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lp Lu
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gb

/-! ## Offsets and logends -/

theorem gc_one_add_lt {l β : Ordinal.{0}} (hl : IsSuccLimit l) (hβ : β < l) : 1 + β < l := by
  rcases lt_or_ge β ω with h | h
  · obtain ⟨n, rfl⟩ := lt_omega0.1 h
    have e : (1 : Ordinal.{0}) + n = n + 1 := by
      calc (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by norm_cast
        _ = ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.add_comm]
        _ = n + 1 := by norm_cast
    rw [e]; exact hl.add_one_lt hβ
  · rw [one_add_of_omega0_le h]; exact hβ

theorem gc_lg_pos {l : Ordinal.{0}} (hl : IsSuccLimit l) : 0 < lg l := by
  have hd : ω ∣ l := isSuccPrelimit_iff_omega0_dvd.1 hl.isSuccPrelimit
  have h1 : (1 : Ordinal.{0}) ≤ lg l := le_lg hl.bot_lt.ne' (by rw [opow_one]; exact hd)
  exact lt_of_lt_of_le zero_lt_one h1

/-- **For `λ = λ' + ω^e` with `e = logend(λ)` and `ω^e ∣ λ'`, every `ν ∈ (λ', λ)` has `logend(ν) < e`.** -/
theorem gc_lg_lt {l l' ν : Ordinal.{0}} (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l') (h1 : l' < ν)
    (h2 : ν < l) : lg ν < lg l := by
  by_contra hle
  push Not at hle
  have hν0 : ν ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  have hd : ω ^ lg l ∣ ν := (le_lg_iff hν0 _).1 hle
  obtain ⟨δ, rfl⟩ := exists_add_of_le h1.le
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [add_zero] at h1
    exact lt_irrefl _ h1
  have hδ : δ < ω ^ lg l := by
    have h2' := h2
    rw [hdec] at h2'
    exact (add_lt_add_iff_left _).1 h2'
  obtain ⟨p, hp⟩ := hdvd
  have hm := dvd_iff_mod_eq_zero.1 hd
  rw [hp, mul_add_mod_self, mod_eq_of_lt hδ] at hm
  exact hδ0 hm

/-! ## The reaches of the tops and the separation -/

section GQL

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gc_zeta {ν : Ordinal.{0}} (hν0 : 0 < ν) (hνx : ν < x) : lqZeta x (Om1 * Om1) ν = lg ν := by
  have h := (gq_facts hx hx1 (hν0.trans hνx)).2.1
  unfold lqZeta
  rw [if_pos ⟨0, hν0, hνx.trans h⟩]

/-- **`lh(ϑˣ(Ω₁·Ω₁ + ν)) = G·G + G + logend(ν)`** in `R₁⁺` for every constant `0 < ν < x`. -/
theorem gc_lh {ν : Ordinal.{0}} (hνx : ν < x) (hν0 : 0 < ν) :
    IsLh1 (gq ν x) (gq ν x * gq ν x + gq ν x + lg ν) := by
  obtain ⟨hνT, hν1⟩ := gq_cst hx hx1 hνx
  have h := (Lq.lq_lh_sq hx hx1 hνT hν1).1
  rw [gc_zeta hx hx1 hν0 hνx] at h
  exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` a limit below `x`). -/
theorem gc_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlx : l < x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := gq_facts hx hx1 hlx
  obtain ⟨hlT, hl1⟩ := gq_cst hx hx1 hlx
  have h0x : (0 : Ordinal.{0}) < x := hx.pos
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v x with hvx | hxv
  · exact ⟨0, hl.bot_lt, hvx.trans_lt (gq_facts hx hx1 h0x).2.1⟩
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + l :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlx.trans hxv) (by rw [hξv]; exact hv)
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
        obtain ⟨n1, hn1l, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2l, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        have hml : max n1 n2 < l := max_lt hn1l hn2l
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x := hn1.trans_le (gq_mono hx hx1 (hml.trans hlx) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x := hn2.trans_le (gq_mono hx hx1 (hml.trans hlx) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := gq_cst hx hx1 (hml.trans hlx)
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        rw [hvj]
        exact gq_lt hx hx1 ((hl.add_one_lt hjk).trans hlx) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (gq_facts hx hx1 (hnl.trans hlx)).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (gq_facts hx hx1 (hml.trans hlx)).2.2.2.1).add_lt
      (h1.trans_le (gq_mono hx hx1 (hml.trans hlx) (le_max_left _ _)))
      (h2.trans_le (gq_mono hx hx1 (hml.trans hlx) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for a constant limit
`λ = λ' + ω^e`, `e = logend(λ)`, `ω^e ∣ λ'`. -/
theorem gc_not_le1R_lim {l l' : Ordinal.{0}} (hlx : l < x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hGT, -, hG1, -, -⟩ := gq_facts hx hx1 hlx
  obtain ⟨hlT, hl1⟩ := gq_cst hx hx1 hlx
  have hxa : x < a := (gq_facts hx hx1 (hl'l.trans hlx)).2.1.trans h1
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξk : ξ < Om1 * Om1 + l :=
    lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlx.trans hxa) (by rw [hξv]; exact h2)
  have haa : a * a ≤ a * a + a + lg l := le_self_add.trans le_self_add
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · obtain ⟨hq1, hrT, hr1, hdec'⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    set q := ξ / Om1 with hq
    set r := ξ % Om1 with hr
    have hv : vt x (Om1 * q + r) = a := by rw [hdec', hξv]
    have hζr : luZeta x q r < a := by
      refine lu_zeta_le.trans_lt ?_
      rcases lt_or_ge q x with hqx | hxq
      · have := (lu_th_facts hx hx1 hq1 hqx hrT hr1).2.2.2.2.2.2.2
        rwa [hv] at this
      · have := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.2
        rwa [hv] at this
    have hL : IsLh1 a (luL a q + luZeta x q r) ∧ q < a := by
      rcases lt_or_ge q x with hqx | hxq
      · have h := lu_lh_th hx hx1 hq1 hqx hrT hr1
        rw [hv] at h
        exact ⟨h, hqx.trans hxa⟩
      · have h := Lv.lv_lh_gen hx hx1 hqT hxq hqΩ hrT hr1
        have hqv := (Lv.gen_facts hx hx1 hqT hxq hqΩ hrT hr1).2.2.2.2.2.2.2.1
        rw [hv] at h hqv
        exact ⟨h, hqv⟩
    have hle := hL.1.2 _ hR
    exact absurd ((haa.trans hle).trans_lt (lg_luL_lt_sq haE hL.2 hζr)) (lt_irrefl _)
  · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
    obtain ⟨ν, hν⟩ : ∃ ν, ξ - Om1 * Om1 = ν := ⟨_, rfl⟩
    rw [hν] at hje
    have hνl : ν < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := gq_mono hx hx1 (hl'l.trans hlx) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := gc_lh hx hx1 (hνl.trans hlx) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))

end GQL

/-! ## The union of a family of layers below a limit offset -/

/-- **`λ` is a constant limit offset.** -/
structure GcLimH (l : Ordinal.{0}) : Prop where
  lim : IsSuccLimit l
  cst : GqCst l

/-- **A family of layers below a limit offset `λ`**: for every `β < λ` a layer with top `ϑˣ(Ω₁·Ω₁ + 1 + β)`. -/
structure GcLimF (l : Ordinal.{0}) where
  K : Iio l → XtLay
  E_eq : ∀ β x, InE x → x < Om1 → (K β).E x = gq (1 + β.1) x

section Fam

variable {l : Ordinal.{0}} (H : GcLimH l) (F : GcLimF l)
include H

theorem gcF_lt {β : Iio l} {x : Ordinal.{0}} (hx : InE x) : 1 + β.1 < x :=
  (gc_one_add_lt H.lim β.2).trans (H.cst x hx)

/-- The top of the layer `K_β` is `ϑˣ(Ω₁·Ω₁ + 1 + β)`. -/
theorem gcF_top (β : Iio l) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (F.K β).sys.top x = gq (1 + β.1) x := by
  rw [(F.K β).top_eq x hx hx1, F.E_eq β x hx hx1]
  exact (gq_facts hx hx1 (gcF_lt H hx)).2.2.2.1

theorem gcLim_val_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (p : Σ β : Iio l, (F.K β).sys.Tm)
    (h : (F.K p.1).sys.CB p.2 x) : (F.K p.1).sys.val p.2 x < gq l x := by
  have h1 := (F.K p.1).lt_top_E x hx hx1 p.2 h
  rw [gcF_top H F p.1 hx hx1] at h1
  exact h1.trans (gq_lt hx hx1 (H.cst x hx) (gc_one_add_lt H.lim p.1.2))

end Fam

/-- **The union of the family**: the terms of every `K_β`, top `ϑˣ(Ω₁·Ω₁ + λ)`. -/
noncomputable def gcUSys (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) : XtSys where
  Tm := Σ β : Iio l, (F.K β).sys.Tm
  val := fun p x => (F.K p.1).sys.val p.2 x
  CB := fun p x => (F.K p.1).sys.CB p.2 x
  cs := fun p => (F.K p.1).sys.cs p.2
  cst := fun c => ⟨⟨0, H.lim.bot_lt⟩, (F.K ⟨0, H.lim.bot_lt⟩).sys.cst c⟩
  top := gq l
  cb_cst := fun p s h => (F.K p.1).sys.cb_cst p.2 s h
  cb_iff := fun p s s' h h' => (F.K p.1).sys.cb_iff p.2 s s' h h'
  val_cst := fun c x => (F.K ⟨0, H.lim.bot_lt⟩).sys.val_cst c x
  cb_cstI := fun c x h => (F.K ⟨0, H.lim.bot_lt⟩).sys.cb_cstI c x h
  lt_top := fun _ hr hr1 p h => gcLim_val_lt H F (ups_inE hr) (ups_lt_Om1 _ hr1) p h
  one_le_top := fun _ hr hr1 =>
    one_le_iff_pos.2 (gq_facts (ups_inE hr) (ups_lt_Om1 _ hr1) (H.cst _ (ups_inE hr))).2.2.2.1.pos
  rep := fun r hr hr1 v hv => by
    obtain ⟨ν, hν, hv'⟩ := gc_lt_lim_iff (ups_inE hr) (ups_lt_Om1 r hr1) H.lim (H.cst _ (ups_inE hr)) v hv
    have hlt : v < (F.K ⟨ν, hν⟩).sys.top (upsilon r) := by
      rw [gcF_top H F ⟨ν, hν⟩ (ups_inE hr) (ups_lt_Om1 r hr1)]
      exact hv'.trans_le (gq_mono (ups_inE hr) (ups_lt_Om1 r hr1) (gcF_lt H (β := ⟨ν, hν⟩) (ups_inE hr))
        le_add_self)
    obtain ⟨t, ht, et⟩ := (F.K ⟨ν, hν⟩).sys.rep r hr hr1 v hlt
    exact ⟨⟨⟨ν, hν⟩, t⟩, ht, et⟩
  top_lt := fun _ hr hr1 => gq_lt_next_ups H.cst hr hr1
  pkg := fun r hr hr1 p h h1 R => (F.K p.1).sys.pkg r hr hr1 p.2 h h1 R
  rs := fun r hr hr1 p h => (F.K p.1).sys.rs r hr hr1 p.2 h
  uni_le := fun σ ρ hσ hρ hB p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).exact σ ρ hσ hρ hB p.2 hp) ((F.K q.1).exact σ ρ hσ hρ hB q.2 hq)
  small := fun p => (F.K p.1).sys.small p.2

theorem gcUSys_top (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) (x : Ordinal.{0}) :
    (gcUSys l H F).top x = gq l x := rfl

namespace GcLK

variable {l : Ordinal.{0}} (H : GcLimH l) (F : GcLimF l) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include H F h

/-- **THE TOP WITNESS of `Γ_{x+λ}`** for a constant limit `λ = λ' + ω^e` (`e = logend(λ)`): `f(G) ∈ E`, and
`ϑ^{fρ}(Ω₁·Ω₁ + λ) ≤ f(G)`, from the copy `f(G) ≤₁ f(G)·f(G) + f(G) + e` of `G ≤₁ G·G + G + e` (`Lq.lq_lh_sq`), the
witness of the layer `K_{λ'}` below (`f(G) > ϑ^{fρ}(Ω₁·Ω₁ + 1 + λ')`) and `gc_not_le1R_lim`. -/
theorem gcTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq l ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (gq l ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq l (f ρ) ≤ f (gq l ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  have hlρ := H.cst ρ hρE
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gq_facts hρE h.ρ1 hlρ
  have hl0 : l ≠ 0 := H.lim.bot_lt.ne'
  obtain ⟨l', hdec, hdvd, hl'l⟩ := lg_split hl0
  have hζ0 : 0 < lg l := gc_lg_pos H.lim
  have hLG := gc_lh hρE h.ρ1 hlρ H.lim.bot_lt
  set G := gq l ρ with hG
  set ζ := lg l with hζ
  have hζρ : ζ < ρ := (lg_le hl0).trans_lt hlρ
  have hGδ : G < δ := (gq_lt_next hρE h.ρ1 hlρ h.ρτ h.τU.2).trans h.τδ
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPGζδ : G * G + G + ζ < δ := (inE_indec h.δE).add_lt hPGδ (hζρ.trans (h.ρτ.trans h.τδ))
  have hG0 : 0 < G := hGE.pos
  have hGP : G < G * G := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have hρPG : ρ ≤ G * G + G := (hρG.le.trans hGP.le).trans le_self_add
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {G * G, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {G * G + G, G * G, G + G, G} ∅ := by
    have := w3.insW hρPG hPGδ
      (Or.inr ⟨G * G, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  have w5 : WZ ρ δ {G * G + G + ζ, G * G + G, G * G, G + G, G} {ζ} := by
    have := (w4.insZ hζρ).insW (hρPG.trans le_self_add) hPGζδ
      (Or.inr ⟨G * G + G, by simp, ζ, by simp, lt_add_of_pos_right _ hζ0,
        hζρ.trans_le (hρPG.trans le_self_add), rfl⟩)
    simpa using this
  set K' := F.K ⟨l', hl'l⟩ with hK'
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := K'.top_wit ρ τ δ h
  have w6 := w5.union wE
  refine ⟨{G * G + G + ζ, G * G + G, G * G, G + G, G} ∪ WE, {ζ} ∪ ZE, w6, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPGζA : G * G + G + ζ ∈ A := hW (by simp)
  have hζA : ζ ∈ A := hZ (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZE : ↑ZE ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hTA : K'.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have hTρ : K'.sys.top ρ = gq (1 + l') ρ := gcF_top H F ⟨l', hl'l⟩ hρE h.ρ1
  have hTy : K'.sys.top (f ρ) = gq (1 + l') (f ρ) := gcF_top H F ⟨l', hl'l⟩ hyE hy1
  have hEG : gq (1 + l') ρ < G := gq_lt hρE h.ρ1 hlρ (gc_one_add_lt H.lim hl'l)
  have hfEG : f (K'.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : gq l' (f ρ) < f G := by
    have h1 := (hIE A f hWE hZE C).2
    rw [hTy] at h1
    exact (gq_mono hyE hy1 (gcF_lt H (β := ⟨l', hl'l⟩) hyE) le_add_self).trans_lt (h1.trans_lt hfEG)
  by_cases hU : UpsPt (f G)
  · exact (gq_lt_next hyE hy1 (H.cst _ hyE) hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ζ) := (h.lowδ _ _ hρG hPGζδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGζA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hfζ : f ζ = ζ := C.fix ζ hζA hζρ
    have hadd1 : f (G * G + G) + f ζ = f (G * G + G + ζ) := C.add (G * G + G) hPGA ζ hζA _ hPGζA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + ζ ≤ f (G * G + G + ζ) := by
      rw [← hadd1, hfζ, ← hadd2]
      exact add_le_add_left (add_le_add_left hPge _) _
    have hlo : f G ≤ f G * f G + f G + ζ :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    exact gc_not_le1R_lim hyE hy1 (H.cst _ hyE) hdec hdvd hl'l hfE hEy hlt (le1R_of_le hlo hle hR)

end GcLK

/-- **The limit layer**: `gcUSys λ H F` with top `ϑˣ(Ω₁·Ω₁ + λ)`. -/
noncomputable def gcLimL (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) : XtLay where
  sys := gcUSys l H F
  E := gq l
  top_eq := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.2.1.symm
  exp_dvd := fun x hx hx1 =>
    opow_dvd_of_inE (gq_facts hx hx1 (H.cst x hx)).2.2.2.1 (gq_facts hx hx1 (H.cst x hx)).2.1.le
  exp_lt := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.1
  top_gt := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => gq_lt_next hx hx1 (H.cst x hx) hxu hu.2
  lt_top_E := fun x hx hx1 p h => gcLim_val_lt H F hx hx1 p h
  exact := fun σ ρ hσ hρ hB p hp => (F.K p.1).exact σ ρ hσ hρ hB p.2 hp
  exp_pi := fun σ _ _ _ hB => gq_pi hB (H.cst σ hB.1)
  top_wit := fun _ _ _ h => GcLK.gcTopWit H F h

/-- **The new base package**: the limit layer. -/
noncomputable def gcLimB (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) : LpB where
  K := gcLimL l H F
  ek := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).2.2.2.1
  mem := fun x hx hx1 => (gq_facts hx hx1 (H.cst x hx)).1

theorem gcLimB_E (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) (x : Ordinal.{0}) :
    (gcLimB l H F).K.E x = gq l x := rfl

theorem gcLimB_sys (l : Ordinal.{0}) (H : GcLimH l) (F : GcLimF l) : (gcLimB l H F).K.sys = gcUSys l H F := rfl

/-! ## Lifting terms, tops as terms, comparison of the offsets -/

/-- **Every term of `Y` is a term of `X`** with the same value and a weaker constant condition. -/
def GcLift (X Y : XtSys) : Prop :=
  ∀ s : Y.Tm, ∃ t : X.Tm, ∀ x, (Y.CB s x → X.CB t x) ∧ X.val t x = Y.val s x

theorem gcLift_refl (X : XtSys) : GcLift X X := fun s => ⟨s, fun _ => ⟨id, rfl⟩⟩

theorem gcLift_trans {X Y W : XtSys} (h1 : GcLift X Y) (h2 : GcLift Y W) : GcLift X W := fun s => by
  obtain ⟨t, ht⟩ := h2 s
  obtain ⟨u, hu⟩ := h1 t
  exact ⟨u, fun x => ⟨fun h => (hu x).1 ((ht x).1 h), (hu x).2.trans (ht x).2⟩⟩

/-- **The layers of the family lift into the union.** -/
theorem gcLim_lift {l : Ordinal.{0}} (H : GcLimH l) (F : GcLimF l) (β : Iio l) :
    GcLift (gcUSys l H F) (F.K β).sys := fun s => ⟨⟨β, s⟩, fun _ => ⟨id, rfl⟩⟩

/-- **The ladder over a base lifts the base.** -/
theorem gc_lift_lp (B : LpB) (n : ℕ) : GcLift (lpSys B n) B.K.sys :=
  fun s => ⟨LpT.ak s, fun _ => ⟨fun h => ⟨h, Nat.zero_le n⟩, rfl⟩⟩

theorem gc_lift_gq (B : LpB) (η : Ordinal.{0}) (H : GqLimH B η) : GcLift (gqUSys B η H) B.K.sys :=
  fun s => ⟨LpT.ak s, fun _ => ⟨fun h => h, rfl⟩⟩

/-- **A term with the value of a top, lifted, gives `LyTopIn`** when the top is far enough below. -/
theorem gc_topIn_of_lift {X Y W : XtSys} (hL : GcLift X Y) {t : Y.Tm}
    (ht : ∀ x, UpsPt x → x < Om1 → Y.CB t x ∧ Y.val t x = W.top x)
    (hgap : ∀ r, IsRestartIdx r → r < Om1 → W.top (upsilon r) + 1 < X.top (upsilon r)) : LyTopIn X W := by
  obtain ⟨u, hu⟩ := hL t
  exact ⟨u, fun x hx hx1 => ⟨(hu x).1 (ht x hx hx1).1, (hu x).2.trans (ht x hx hx1).2⟩, hgap⟩

end Googology.Trans.PoR.InaccPsi.R2.Gc
