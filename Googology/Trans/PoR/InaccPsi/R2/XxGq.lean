import Googology.Trans.PoR.InaccPsi.R2.GmGq

/-!
# XxGq: THE FOUR OFFSET FACTS FOR EVERY OFFSET BOUND `ϑˣ(Ω₁·Ω₁ + W) = Γ_{x+1+W}`, `W < ε₀`

`Gm.GmGq` proves the facts of the layer construction for the offsets `η < Γ_{x+2} = ϑˣ(Ω₁·Ω₁ + 1)` (the readings of
the codes of region (A), base atom `G = Γ(0)`).  The layer `k` of region (B) reads its codes below
`Γ_{x+2+k} = ϑˣ(Ω₁·Ω₁ + (k+1))`.  Here the same facts hold for every constant bound `W < ε₀` (one statement for every
`W`; `W = 1` is `Gm.GmGq`, `W = k + 1` is the layer `k`):

* `xxW_T`, `xxW_lt_q0` (**`W ∈ Tˣ`, `W < x < ϑˣ(Ω₁·Ω₁)`**), `xx_facts`, `xx_T` (**every offset below `ϑˣ(Ω₁·Ω₁+W)` lies
  in `Tˣ ∩ Ω₁`**), `xx_lt`, `xx_mono`, `xx_sigma`, `xx_lh` (**`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`**);
* `xx_lt_lim_iff` (**`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`**);
* `xx_not_le1R_lim` (no `ε`-number in `(ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` is `≤₁ a·a + a + logend(λ)` in `R₁⁺`).  The
  proof of `Gm.gm1_not_le1R_lim` used `a < Γ_{x+2} ⇒ a = Γ_{x+1}`; here the second case splits on `λ < a` (then
  `a = ϑˣ(Ω₁·Ω₁ + ν)` with `ν < λ` by Lemma 3.30) and `a ≤ λ` (then `a = ϑˣ(Ω₁·Ω₁ + ν)` with `ν < W`, and `ν < a ≤ λ`);
* `xx_one_lt_lim_iff`, `xx_one_not_le1R_lim` (the instance `W = 1` restates `Gm.gm1_lt_lim_iff`,
  `Gm.gm1_not_le1R_lim`).

No new axiom.  New definitions: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gm

section GQW

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {W : Ordinal.{0}} (hW : W < ε₀)
include hx hx1 hW

/-- **A constant `W < ε₀` lies in `Tˣ ∩ Ω₁` and below `x`.** -/
theorem xxW_T : W ∈ Tset x ∧ W < Om1 ∧ W < x := by
  have hWx : W < x := hW.trans_le (gc_eps0_le hx)
  exact ⟨mem_T_of_le hx hx1 hWx.le, hWx.trans hx1, hWx⟩

/-- **`W < ϑˣ(Ω₁·Ω₁)`.** -/
theorem xxW_lt_q0 : W < gq 0 x := (xxW_T hx hx1 hW).2.2.trans (gfq0_facts hx hx1).2.1

theorem xx_facts : gq W x ∈ Tset x ∧ x < gq W x ∧ gq W x < Om1 ∧ InE (gq W x) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := geq_facts hx hx1 (xxW_T hx hx1 hW).1 (xxW_T hx hx1 hW).2.1
  exact ⟨h1, h2, h3, h4⟩

/-- **Every offset below `ϑˣ(Ω₁·Ω₁ + W)` lies in `Tˣ ∩ Ω₁`.** -/
theorem xx_T {η : Ordinal.{0}} (h : η < gq W x) : η ∈ Tset x ∧ η < Om1 := by
  obtain ⟨h1, -, h3, -⟩ := xx_facts hx hx1 hW
  exact ⟨vz_T_down hx hx1 h1 h3 h.le, h.trans h3⟩

theorem xx_lt {j η : Ordinal.{0}} (hη : η < gq W x) (h : j < η) : gq j x < gq η x :=
  gmq_lt hx hx1 (xx_T hx hx1 hW hη).1 (xx_T hx hx1 hW hη).2 h

theorem xx_mono {j η : Ordinal.{0}} (hη : η < gq W x) (h : j ≤ η) : gq j x ≤ gq η x :=
  gmq_mono hx hx1 (xx_T hx hx1 hW hη).1 (xx_T hx hx1 hW hη).2 h

/-- **Some `σ < η` has `η < ϑˣ(Ω₁·Ω₁ + σ)`** for `0 < η < ϑˣ(Ω₁·Ω₁ + W)` (`σ = 0` below `Γ_{x+1}`, `σ = W` above). -/
theorem xx_sigma {η : Ordinal.{0}} (h : η < gq W x) (h0 : 0 < η) : ∃ σ, σ < η ∧ η < gq σ x := by
  rcases lt_or_ge η (gq 0 x) with h' | h'
  · exact ⟨0, h0, h'⟩
  · exact ⟨W, (xxW_lt_q0 hx hx1 hW).trans_le h', h⟩

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for `0 < η < ϑˣ(Ω₁·Ω₁ + W)`. -/
theorem xx_lh {η : Ordinal.{0}} (hη : η < gq W x) (h0 : 0 < η) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) :=
  (gfq_lh_gen hx hx1 (xx_T hx hx1 hW hη).1 (xx_T hx hx1 hW hη).2).1 (xx_sigma hx hx1 hW hη h0)

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` a limit below `ϑˣ(Ω₁·Ω₁ + W)`). -/
theorem xx_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlG : l < gq W x) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := xx_T hx hx1 hW hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · rcases lt_or_ge l (gq 0 x) with hl0 | hl0
    · exact ⟨0, hl.bot_lt, hvx.trans_lt (max_lt (gfq0_facts hx hx1).2.1 hl0)⟩
    · exact ⟨W, (xxW_lt_q0 hx hx1 hW).trans_le hl0, hvx.trans_lt (max_lt (xx_facts hx hx1 hW).2.1 hlG)⟩
  have hxv : x < v := (le_max_left _ _).trans_lt hxv0
  have hlv : l < v := (le_max_right _ _).trans_lt hxv0
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + l :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hlv) (by rw [hξv]; exact hv)
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
        have hq' : ξ / Om1 < gq (max n1 n2) x :=
          hn1.trans_le (xx_mono hx hx1 hW (hml.trans hlG) (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x :=
          hn2.trans_le (xx_mono hx hx1 hW (hml.trans hlG) (le_max_right _ _))
        obtain ⟨hmT, hm1⟩ := xx_T hx hx1 hW (hml.trans hlG)
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
        exact xx_lt hx hx1 hW ((hl.add_one_lt hjk).trans hlG) (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, hnl, (geq_facts hx hx1 (xx_T hx hx1 hW (hnl.trans hlG)).1 (xx_T hx hx1 hW
          (hnl.trans hlG)).2).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 (xx_T hx hx1 hW (hml.trans hlG)).1
      (xx_T hx hx1 hW (hml.trans hlG)).2).2.2.2.1).add_lt
      (h1.trans_le (xx_mono hx hx1 hW (hml.trans hlG) (le_max_left _ _)))
      (h2.trans_le (xx_mono hx hx1 hW (hml.trans hlG) (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for `λ = λ' + ω^e`,
`e = logend(λ)`, `ω^e ∣ λ'`, `λ < ϑˣ(Ω₁·Ω₁ + W)`. -/
theorem xx_not_le1R_lim {l l' : Ordinal.{0}} (hlG : l < gq W x) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := xx_T hx hx1 hW hlG
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := xx_T hx hx1 hW (hl'l.trans hlG)
  have hxa : x < a := (geq_facts hx hx1 hl'T hl'1).2.1.trans h1
  have ha1 : a < Om1 := h2.trans hG1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hGT hG1 h2.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
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
    have hva : a = gq ν x := by rw [← hξv, ← hje]; rfl
    -- `ν < λ`: either `λ < a` (Lemma 3.30 at the offset `λ`), or `a ≤ λ` (Lemma 3.30 at the offset `W`, `ν < a`)
    have hνl : ν < l := by
      rcases lt_or_ge l a with hla | hal
      · have hξk : ξ < Om1 * Om1 + l :=
          lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hla) (by rw [hξv]; exact h2)
        exact (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
      · obtain ⟨hWT, hW1, hWx⟩ := xxW_T hx hx1 hW
        have hWa : W < a :=
          ((xxW_lt_q0 hx hx1 hW).trans_le (gfq0_le hx hx1 hl'T hl'1)).trans h1
        have haW : a < gq W x := hal.trans_lt hlG
        have hξW : ξ < Om1 * Om1 + W :=
          lgLt_of_vt_lt hx hx1 hξT hξ2 hWT hW1 (by rw [hξv]; exact hWa) (by rw [hξv]; exact haW)
        have hνW : ν < W := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξW)
        have hνx : ν < x := hνW.trans hWx
        have hνa : ν < a := by
          rw [hva]; exact gmq_gt hx hx1 (mem_T_of_le hx hx1 hνx.le) (hνx.trans hx1)
        exact hνa.trans_le hal
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := xx_mono hx hx1 hW (hl'l.trans hlG) hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := xx_lh hx hx1 hW (hνl.trans hlG) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))

end GQW

/-- **The instance `W = 1`** of `xx_lt_lim_iff` is the statement of `Gm.gm1_lt_lim_iff`. -/
theorem xx_one_lt_lim_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {l : Ordinal.{0}} (hl : IsSuccLimit l)
    (hlG : l < gq 1 x) : ∀ v, v < gq l x → ∃ ν < l, v < gq ν x :=
  xx_lt_lim_iff hx hx1 (one_lt_omega0.trans (omega0_lt_epsilon 0)) hl hlG

/-- **The instance `W = 1`** of `xx_not_le1R_lim` is the statement of `Gm.gm1_not_le1R_lim`. -/
theorem xx_one_not_le1R_lim {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {l l' : Ordinal.{0}} (hlG : l < gq 1 x)
    (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l') (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a)
    (h1 : gq l' x < a) (h2 : a < gq l x) : ¬ le1R a (a * a + a + lg l) :=
  xx_not_le1R_lim hx hx1 (one_lt_omega0.trans (omega0_lt_epsilon 0)) hlG hdec hdvd hl'l haE h1 h2

end Googology.Trans.PoR.InaccPsi.R2.Xx
