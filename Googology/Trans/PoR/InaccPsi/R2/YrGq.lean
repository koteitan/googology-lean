import Googology.Trans.PoR.InaccPsi.R2.XxGq
import Googology.Trans.PoR.InaccPsi.R2.XkImg

/-!
# YrGq: THE OFFSET FACTS FOR EVERY OFFSET THAT IS NOT PAST A FIXED POINT OF `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` (READ INDICES)

`Xx.XxGq` proves the facts of the layer construction for offsets `η < ϑˣ(Ω₁·Ω₁ + W)` with a CONSTANT bound `W < ε₀`.
The constant is used only to know that `η ∈ Tˣ ∩ Ω₁` and that no limit `l ≤ η` is a fixed point of
`ν ↦ Γ_{x+1+ν} = ϑˣ(Ω₁·Ω₁ + ν)`.  Here these two facts are the hypothesis itself (`YrN x η`), so the bound may be
a reading `W(x)` of a code (an index read with `Ω₁ ↦ x`):

* `YrN x v` (**`v ∈ Tˣ ∩ Ω₁` and every limit `l ≤ v` has some `σ < l` with `l < ϑˣ(Ω₁·Ω₁ + σ)`**);
* closure: `yrN_down`, `yrN_succ`, `yrN_gq` (**`YrN x v ⇒ YrN x (ϑˣ(Ω₁·Ω₁ + v))`**), `yrN_lt_gq`, `yrN_cst`
  (**every constant `v < x`**), `yrN_of_cst` (**every `v < ϑˣ(Ω₁·Ω₁ + W)`, `W < ε₀`**: the old bound);
* the facts: `yr_T`, `yr_facts`, `yr_lt`, `yr_mono`, `yr_sigma`, `yr_lh`, `yr_lt_lim_iff`, `yr_not_le1R_lim` (the
  statements of `Xx.xx_T` … `Xx.xx_not_le1R_lim` under `YrN`).

No new axiom.  New definition: `YrN`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Xx

/-- **An admissible offset at the base `x`**: `v ∈ Tˣ ∩ Ω₁`, and no limit `l ≤ v` is a fixed point of
`ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` from below (some `σ < l` has `l < ϑˣ(Ω₁·Ω₁ + σ)`). -/
def YrN (x v : Ordinal.{0}) : Prop :=
  v ∈ Tset x ∧ v < Om1 ∧ ∀ l, IsSuccLimit l → l ≤ v → ∃ σ, σ < l ∧ l < gq σ x

section GQN

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

omit hx hx1 in
theorem yr_T {v : Ordinal.{0}} (h : YrN x v) : v ∈ Tset x ∧ v < Om1 := ⟨h.1, h.2.1⟩

theorem yrN_down {u v : Ordinal.{0}} (h : YrN x v) (huv : u ≤ v) : YrN x u :=
  ⟨vz_T_down hx hx1 h.1 h.2.1 huv, huv.trans_lt h.2.1, fun l hl hlu => h.2.2 l hl (hlu.trans huv)⟩

theorem yr_facts {v : Ordinal.{0}} (h : YrN x v) :
    gq v x ∈ Tset x ∧ x < gq v x ∧ gq v x < Om1 ∧ InE (gq v x) ∧ Indec (gq v x) :=
  geq_facts hx hx1 h.1 h.2.1

theorem yrN_succ {v : Ordinal.{0}} (h : YrN x v) : YrN x (v + 1) := by
  obtain ⟨hT, h1⟩ := Xk.xk_succT hx hx1 h.1 h.2.1
  refine ⟨hT, h1, fun l hl hle => ?_⟩
  have hlv : l ≤ v := by
    rcases hle.lt_or_eq with h' | h'
    · exact Order.lt_add_one_iff.1 h'
    · rw [h'] at hl; exact absurd hl (by rw [← succ_eq_add_one]; exact Order.not_isSuccLimit_succ v)
  exact h.2.2 l hl hlv

/-- **`YrN x v ⇒ YrN x (ϑˣ(Ω₁·Ω₁ + v))`.** -/
theorem yrN_gq {v : Ordinal.{0}} (h : YrN x v) : YrN x (gq v x) := by
  obtain ⟨hGT, -, hG1, hGE, -⟩ := yr_facts hx hx1 h
  have hvG : v < gq v x := gmq_gt hx hx1 h.1 h.2.1
  refine ⟨hGT, hG1, fun l hl hle => ?_⟩
  rcases le_or_gt l v with hlv | hvl
  · exact h.2.2 l hl hlv
  rcases hle.lt_or_eq with hlt | heq
  · exact ⟨v, hvl, hlt⟩
  · obtain ⟨hv1T, hv1⟩ := Xk.xk_succT hx hx1 h.1 h.2.1
    refine ⟨v + 1, ?_, ?_⟩
    · rw [heq]; exact (ev_isSuccLimit_of_inE hGE).add_one_lt hvG
    · rw [heq]; exact gmq_lt hx hx1 hv1T hv1 (lt_add_one v)

theorem yrN_lt_gq {W v : Ordinal.{0}} (h : YrN x W) (hv : v < gq W x) : YrN x v :=
  yrN_down hx hx1 (yrN_gq hx hx1 h) hv.le

/-- **Every constant `v ≤ x` is admissible.** -/
theorem yrN_cst {v : Ordinal.{0}} (hv : v ≤ x) : YrN x v := by
  refine ⟨mem_T_of_le hx hx1 hv, hv.trans_lt hx1, fun l hl hle => ⟨0, hl.bot_lt, ?_⟩⟩
  exact (hle.trans hv).trans_lt (gfq0_facts hx hx1).2.1

/-- **The old bound**: every `v < ϑˣ(Ω₁·Ω₁ + W)` with a constant `W < ε₀` is admissible. -/
theorem yrN_of_cst {W v : Ordinal.{0}} (hW : W < ε₀) (hv : v < gq W x) : YrN x v :=
  yrN_lt_gq hx hx1 (yrN_cst hx hx1 (hW.trans_le (gc_eps0_le hx)).le) hv

theorem yr_lt {j η : Ordinal.{0}} (hη : YrN x η) (h : j < η) : gq j x < gq η x :=
  gmq_lt hx hx1 hη.1 hη.2.1 h

theorem yr_mono {j η : Ordinal.{0}} (hη : YrN x η) (h : j ≤ η) : gq j x ≤ gq η x :=
  gmq_mono hx hx1 hη.1 hη.2.1 h

/-- **Some `σ < η` has `η < ϑˣ(Ω₁·Ω₁ + σ)`** for every admissible `η > 0`. -/
theorem yr_sigma {η : Ordinal.{0}} (h : YrN x η) (h0 : 0 < η) : ∃ σ, σ < η ∧ η < gq σ x := by
  rcases zero_or_succ_or_isSuccLimit η with h' | ⟨s, hs⟩ | hl
  · exact absurd h' h0.ne'
  · rw [succ_eq_add_one] at hs
    have hsη : s < η := by rw [← hs]; exact lt_add_one s
    have hsN := yrN_down hx hx1 h hsη.le
    obtain ⟨-, -, -, hGE, -⟩ := yr_facts hx hx1 hsN
    refine ⟨s, hsη, ?_⟩
    rw [← hs]
    exact (ev_isSuccLimit_of_inE hGE).add_one_lt (gmq_gt hx hx1 hsN.1 hsN.2.1)
  · exact h.2.2 η hl le_rfl

/-- **`lh(ϑˣ(Ω₁·Ω₁ + η)) = G·G + G + logend(η)`** for every admissible `η > 0`. -/
theorem yr_lh {η : Ordinal.{0}} (hη : YrN x η) (h0 : 0 < η) :
    IsLh1 (gq η x) (gq η x * gq η x + gq η x + lg η) :=
  (gfq_lh_gen hx hx1 hη.1 hη.2.1).1 (yr_sigma hx hx1 hη h0)

/-- **`v < ϑˣ(Ω₁·Ω₁ + λ)` iff `v < ϑˣ(Ω₁·Ω₁ + ν)` for some `ν < λ`** (`λ` an admissible limit). -/
theorem yr_lt_lim_iff {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlN : YrN x l) :
    ∀ v, v < gq l x → ∃ ν < l, v < gq ν x := by
  obtain ⟨hlT, hl1⟩ := yr_T hlN
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  have hdown : ∀ ν, ν ≤ l → ν ∈ Tset x ∧ ν < Om1 := fun ν hν => yr_T (yrN_down hx hx1 hlN hν)
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (max x l) with hvx | hxv0
  · rcases le_or_gt v x with hvx' | hxv'
    · exact ⟨0, hl.bot_lt, hvx'.trans_lt (gfq0_facts hx hx1).2.1⟩
    · have hvl : v ≤ l := by
        rcases le_max_iff.1 hvx with h | h
        · exact absurd h (not_le.2 hxv')
        · exact h
      obtain ⟨σ, hσl, hlσ⟩ := hlN.2.2 l hl le_rfl
      exact ⟨σ, hσl, hvl.trans_lt hlσ⟩
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
        obtain ⟨hmT, hm1⟩ := hdown _ hml.le
        refine ⟨max n1 n2, hml, ?_⟩
        have hq' : ξ / Om1 < gq (max n1 n2) x :=
          hn1.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_left _ _))
        have hr' : ξ % Om1 < gq (max n1 n2) x :=
          hn2.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_right _ _))
        have h := lgVt_lt_low hx hx1 hqT hqΩ hrT hr1 hmT hm1 hq' hr'
        rw [hdec, hξv] at h
        exact h
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        obtain ⟨j, hj⟩ : ∃ j, ξ - Om1 * Om1 = j := ⟨_, rfl⟩
        rw [hj] at hje
        have hjk : j < l := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        refine ⟨j + 1, hl.add_one_lt hjk, ?_⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje]; rfl
        obtain ⟨hj1T, hj11⟩ := hdown _ (hl.add_one_lt hjk).le
        rw [hvj]
        exact gmq_lt hx hx1 hj1T hj11 (lt_add_one _)
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hnl, hn⟩ := IH L hL (hL.trans hv)
      obtain ⟨hnT, hn1⟩ := hdown _ hnl.le
      exact ⟨n, hnl, (geq_facts hx hx1 hnT hn1).2.2.2.1.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, hn1l, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, hn2l, h2⟩ := IH u2 hu2 (hu2.trans hv)
    have hml : max n1 n2 < l := max_lt hn1l hn2l
    obtain ⟨hmT, hm1⟩ := hdown _ hml.le
    refine ⟨max n1 n2, hml, ?_⟩
    rw [← hsum]
    exact (inE_indec (geq_facts hx hx1 hmT hm1).2.2.2.1).add_lt
      (h1.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_left _ _)))
      (h2.trans_le (gmq_mono hx hx1 hmT hm1 (le_max_right _ _)))

/-- **No `ε`-number `a ∈ (ϑˣ(Ω₁·Ω₁ + λ'), ϑˣ(Ω₁·Ω₁ + λ))` has `a ≤₁ a·a + a + e` in `R₁⁺`**, for an admissible
`λ = λ' + ω^e`, `e = logend(λ)`, `ω^e ∣ λ'` (`λ` a limit or a successor). -/
theorem yr_not_le1R_lim {l l' : Ordinal.{0}} (hlN : YrN x l) (hdec : l = l' + ω ^ lg l) (hdvd : ω ^ lg l ∣ l')
    (hl'l : l' < l) {a : Ordinal.{0}} (haE : InE a) (h1 : gq l' x < a) (h2 : a < gq l x) :
    ¬ le1R a (a * a + a + lg l) := by
  intro hR
  obtain ⟨hlT, hl1⟩ := yr_T hlN
  obtain ⟨hGT, -, hG1, -, -⟩ := geq_facts hx hx1 hlT hl1
  obtain ⟨hl'T, hl'1⟩ := yr_T (yrN_down hx hx1 hlN hl'l.le)
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
    -- `ν < λ`: either `λ < a` (Lemma 3.30 at the offset `λ`), or `a ≤ λ` (Lemma 3.30 at an offset `σ < a` with
    -- `a < ϑˣ(Ω₁·Ω₁ + σ)`, `yr_sigma` at the admissible `a`)
    have hνl : ν < l := by
      rcases lt_or_ge l a with hla | hal
      · have hξk : ξ < Om1 * Om1 + l :=
          lgLt_of_vt_lt hx hx1 hξT hξ2 hlT hl1 (by rw [hξv]; exact hla) (by rw [hξv]; exact h2)
        exact (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
      · have haN : YrN x a := yrN_down hx hx1 hlN hal
        obtain ⟨σ, hσa, haσ⟩ := yr_sigma hx hx1 haN haE.pos
        obtain ⟨hσT, hσ1⟩ := yr_T (yrN_down hx hx1 haN hσa.le)
        have hξσ : ξ < Om1 * Om1 + σ :=
          lgLt_of_vt_lt hx hx1 hξT hξ2 hσT hσ1 (by rw [hξv]; exact hσa) (by rw [hξv]; exact haσ)
        have hνσ : ν < σ := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξσ)
        exact (hνσ.trans hσa).trans_le hal
    have hl'ν : l' < ν := by
      by_contra hle
      push Not at hle
      have h3 : gq ν x ≤ gq l' x := gmq_mono hx hx1 hl'T hl'1 hle
      rw [← hva] at h3
      exact absurd (h1.trans_le h3) (lt_irrefl _)
    have hν0 : 0 < ν := lt_of_le_of_lt zero_le hl'ν
    have hL := yr_lh hx hx1 (yrN_down hx hx1 hlN hνl.le) hν0
    rw [← hva] at hL
    have hle := (add_le_add_iff_left (a * a + a)).1 (hL.2 _ hR)
    exact absurd hle (not_le.2 (gc_lg_lt hdec hdvd hl'ν hνl))

end GQN

end Googology.Trans.PoR.InaccPsi.R2.Yr
