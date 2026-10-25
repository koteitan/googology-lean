import Googology.Trans.PoR.InaccPsi.R2.UrTerm

/-!
# Term existence with gap levels: ordinal data give well-formed terms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Un.unExist` for the node conditions `Ur.WFr`, with one more clause: a `ϑᵗ`-node at a **low level** (every leaf of
the hereditary Cantor normal form of `Ω₁·M` a parameter `p < τ`), e.g. the gap levels `Ω₁·υ_{λ+h'}` at the base
`υ_{λ+h}` (`h' < h`), whose leaves are inner points below the base.

* `urLeafDat`, `urNodeHi`, `urNodeLo` (**`Un.unLeafDat`, `Un.unNodeHi`, `Un.unNodeLo` for `WFr`**), `urNodeLow`
  (**the node conditions at a low level**: leaves `< τ ≤` the value, the remainder below the value by [W07a]
  Lemma 3.30);
* `urLevelEx` (**`Un.unLevelEx` for `WFr`, with a leaf property `Q` carried**), `LoL_of_Lf`;
* `UrGd` (**`Un.UnGd` and the low clause `thl`**), `urExist` (**every `y` with `UrGd κ τ P y` is the value of a
  well-formed term**), `urGd_of_un` (**`Un.UnGd ⇒ UrGd`**).

No new axiom.  New definitions: `UrGd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ur

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT

/-- **Every leaf of a level term in full Cantor normal form is `≤ rjDat Γ`** (`Γ = G[τ]`; `Uk.UkL.dat_om_add`,
`dat_om_add_r`). -/
theorem urLeafDat {τ : Ordinal.{0}} :
    ∀ (G : UnT true), WFr τ G → FNF τ G → Lf (fun c => ev τ c ≤ Rj.rjDat (ev τ G)) G
  | .lf c, hw, _ => by
    show ev τ c ≤ Rj.rjDat (ev τ c)
    rw [Rj.rjDat_small hw.2]
  | .om b, hw, hf => by
    have ih := urLeafDat b hw hf
    have hbE := ev_lt_Er b hw
    have hle : Rj.rjDat (ev τ b) ≤ Rj.rjDat (ev τ (UnT.om b)) := by
      by_cases hb0 : ev τ b = 0
      · rw [hb0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · have := Uk.UkL.dat_om_add (y := 0) hb0 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
        rw [add_zero] at this
        exact this
    exact Lf_mono (fun c hc => hc.trans hle) b ih
  | .ad (.om b) y, hw, hf => by
    have ihb := urLeafDat b hw.1 hf.1
    have ihy := urLeafDat y hw.2 hf.2.1
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hf.2.2.2
    have hle1 : Rj.rjDat (ev τ b) ≤ Rj.rjDat (ev τ (UnT.ad (.om b) y)) := by
      by_cases hb0 : ev τ b = 0
      · rw [hb0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · exact Uk.UkL.dat_om_add hb0 hbE hy
    have hle2 : Rj.rjDat (ev τ y) ≤ Rj.rjDat (ev τ (UnT.ad (.om b) y)) := by
      by_cases hy0 : ev τ y = 0
      · rw [hy0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · exact dat_om_add_r hbE hy0 hy
    exact ⟨Lf_mono (fun c hc => hc.trans hle1) b ihb, Lf_mono (fun c hc => hc.trans hle2) y ihy⟩
  | .ad (.lf _) _, _, hf => hf.2.2.1.elim
  | .ad (.ad _ _) _, _, hf => hf.2.2.1.elim

/-- **The node conditions of the normal-form mode at uncountable levels** (`Ω₁·Ω₁ ≤ Γ`): if `G`, `r` are well
formed, `r[τ] < Ω₁`, `Ω₁ ∣ G`, `G` is in full normal form with a high leaf and `G[τ] + r[τ] ∈ Tᵗ`, then
`thg true G r` is well formed ([W07a] Lemma 3.30 through `R2.rjLevel_lt_vt`, `R2.rkArg_dat`, `R2.vzRem_T`). -/
theorem urNodeHi {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (G : UnT true) (r : UnT false) (hG : WFr τ G)
    (hr : WFr τ r) (hr1 : ev τ r < Om1) (hgs : Gs G) (hf : FNF τ G) (hd : HdE τ G)
    (hOO : Om1 * Om1 ≤ ev τ G) (hmem : ev τ G + ev τ r ∈ Tset τ) : WFr τ (UnT.thg true G r) := by
  obtain ⟨M, hM, -⟩ := UnT.ev_dvd (τ := τ) G hgs
  have hOM : Om1 ≤ M := by
    by_contra hlt
    have := mul_lt_mul_of_pos_left (not_le.1 hlt) Rj.rj_Om1_pos
    rw [← hM] at this
    exact absurd hOO (not_le.2 this)
  have hGE := ev_lt_Er G hG
  have hME : M < Gg.ggE := lt_of_le_of_lt (le_mul_right M Rj.rj_Om1_pos) (hM ▸ hGE)
  rw [hM] at hmem
  have hdT := rkArg_dat hτ hτ1 hOM hME hr1 hmem
  have hrT : ev τ r ∈ Tset τ :=
    vzRem_T hτ hτ1 hmem (Uk.arg_lt2 (hM ▸ hGE) hr1) rfl (dvd_mul_right _ _) hr1
  obtain ⟨hdl, hrl⟩ := rjLevel_lt_vt hτ hτ1 hOM hME hdT hrT hr1
  have hlv := urLeafDat G hG hf
  rw [hM] at hlv
  have hdd := Si.si_rjDat_Om1_mul M hOM hME
  refine ⟨hG, hr, ⟨hr1, hgs, hf, Or.inl hd, by rw [hM]; exact hmem, ?_, by rw [hM]; exact hrl⟩⟩
  rw [hM]
  exact Lf_mono (fun c hc => (hc.trans hdd).trans_lt hdl) G hlv

/-- **The node conditions of the normal-form mode at countable levels** (`Γ = Ω₁·q`, `q < Ω₁`, `q ∈ Tᵗ`): as
`urNodeHi`, through `R2.lvLevel_lt_vt` (the high leaf gives `τ ≤ q`). -/
theorem urNodeLo {κ τ : Ordinal.{0}} (hB : Bases κ τ) (G : UnT true) (r : UnT false) (hG : WFr τ G)
    (hlG : Lv (· ∈ Tset τ) G) (hqG : Qs κ G) (hr : WFr τ r) (hr1 : ev τ r < Om1) (hgs : Gs G) (hf : FNF τ G)
    (hd : HdE τ G) {q : Ordinal.{0}} (hq : ev τ G = Om1 * q) (hq1 : q < Om1) (hqT : q ∈ Tset τ)
    (hmem : ev τ G + ev τ r ∈ Tset τ) : WFr τ (UnT.thg true G r) := by
  have hτ := hB.2.1
  have hτ1 := hB.2.2.2
  have hdq := Si.si_rjDat_Om1_mul_small q hq1
  have hτq : τ ≤ q := by
    have := (urDatFN hB G hlG hG hqG hf hd).1
    rw [hq] at this
    exact this.trans hdq
  have hGE := ev_lt_Er G hG
  rw [hq] at hmem
  have hrT : ev τ r ∈ Tset τ :=
    vzRem_T hτ hτ1 hmem (Uk.arg_lt2 (hq ▸ hGE) hr1) rfl (dvd_mul_right _ _) hr1
  obtain ⟨hql, hrl⟩ := lvLevel_lt_vt hτ hτ1 hqT hτq hq1 hrT hr1
  have hlv := urLeafDat G hG hf
  rw [hq] at hlv
  refine ⟨hG, hr, ⟨hr1, hgs, hf, Or.inl hd, by rw [hq]; exact hmem, ?_, by rw [hq]; exact hrl⟩⟩
  rw [hq]
  exact Lf_mono (fun c hc => (hc.trans hdq).trans_lt hql) G hlv

/-- `x + ⋯ + x + R` keeps the argument bounds `WFr`. -/
theorem adRep_WFr {τ : Ordinal.{0}} {x R : UnT true} (hx : WFr τ x) (hR : WFr τ R) :
    ∀ n : ℕ, WFr τ (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_WFr hx hR n⟩

/-- `x + ⋯ + x + R` keeps a leaf property. -/
theorem adRep_Lf {Q : UnT false → Prop} {x R : UnT true} (hx : Lf Q x) (hR : Lf Q R) :
    ∀ n : ℕ, Lf Q (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_Lf hx hR n⟩

/-- **Leaves that are parameters below `τ` make a low level.** -/
theorem LoL_of_Lf {τ : Ordinal.{0}} :
    ∀ (G : UnT true), Lf (fun t => ∃ p, t = .par p ∧ p < τ) G → LoL τ G
  | .lf c, h => by
    obtain ⟨p, rfl, hp⟩ := h
    exact hp
  | .om b, h => LoL_of_Lf b h
  | .ad x y, h => ⟨LoL_of_Lf x h.1, LoL_of_Lf y h.2⟩

/-- **The node conditions at a low level** (every leaf a parameter `< τ`; `Ω₁ ≤ M` or `M < τ`): if `G`, `r` are
well formed, `r[τ] < Ω₁`, `Ω₁ ∣ G`, `G` is in full normal form and `G[τ] + r[τ] ∈ Tᵗ`, then `thg true G r` is well
formed (the leaves are `< τ ≤` the value, `R2.vt_memTwo`; `r[τ] <` the value by [W07a] Lemma 3.30 through
`R2.rjLevel_lt_vt` resp. `R2.luLt_vt_self`). -/
theorem urNodeLow {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (G : UnT true) (r : UnT false) (hG : WFr τ G)
    (hr : WFr τ r) (hr1 : ev τ r < Om1) (hgs : Gs G) (hf : FNF τ G) (hl : LoL τ G) {M : Ordinal.{0}}
    (hM : ev τ G = Om1 * M) (hM1 : 1 ≤ M) (hME : Om1 * M < Gg.ggE) (hMc : Om1 ≤ M ∨ M < τ)
    (hmem : ev τ G + ev τ r ∈ Tset τ) : WFr τ (UnT.thg true G r) := by
  rw [hM] at hmem
  have hlt2 : Om1 * M + ev τ r < OmTwo := Uk.arg_lt2 hME hr1
  have hrT : ev τ r ∈ Tset τ := vzRem_T hτ hτ1 hmem hlt2 rfl (dvd_mul_right _ _) hr1
  have hτv : τ ≤ vt τ (Om1 * M + ev τ r) := (vt_memTwo hτ hτ1 hmem hlt2).2.1
  have hrl : ev τ r < vt τ (Om1 * M + ev τ r) := by
    rcases hMc with hOM | hMτ
    · have hMEM : M < Gg.ggE := lt_of_le_of_lt (le_mul_right M Rj.rj_Om1_pos) hME
      exact (rjLevel_lt_vt hτ hτ1 hOM hMEM (rkArg_dat hτ hτ1 hOM hMEM hr1 hmem) hrT hr1).2
    · exact luLt_vt_self hτ hτ1 hM1 hMτ hrT hr1
  refine ⟨hG, hr, ⟨hr1, hgs, hf, Or.inr ⟨rfl, hl⟩, by rw [hM]; exact hmem, ?_, by rw [hM]; exact hrl⟩⟩
  rw [hM]
  exact Lf_mono (fun c hc => hc.trans_le hτv) G (LoL_Lf G hl)

/-- **Level-term existence** (`Un.unLevelEx` for `WFr`, with the leaves tracked): every `z < ε_{Ω₁+1}` whose leaves
are values of given terms satisfying `Q` is the value of a level term in full Cantor normal form whose leaves satisfy
`Q`, with a high leaf when `τ ≤ rjDat z` and the shape `Gs` when `Ω₁ ∣ z`. -/
theorem urLevelEx {κ τ : Ordinal.{0}} (hτ0 : 0 < τ) (P : Ordinal.{0} → Prop) (Q : UnT false → Prop) :
    ∀ z : Ordinal.{0}, z < Gg.ggE →
      (∀ c, UnLeaf z c → ∃ t : UnT false, ev τ t = c ∧ WFr τ t ∧ Qs κ t ∧ Lv P t ∧ Lv (· ∈ Tset τ) t ∧
        (τ ≤ c → HiC τ t) ∧ Q t) →
      ∃ G : UnT true, ev τ G = z ∧ WFr τ G ∧ FNF τ G ∧ Qs κ G ∧ Lv P G ∧ Lv (· ∈ Tset τ) G ∧
        (τ ≤ Rj.rjDat z → HdE τ G) ∧ (Om1 ∣ z → z ≠ 0 → Gs G) ∧ Lf Q G := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE horc
  rcases lt_or_ge z Om1 with hz1 | hz1
  · obtain ⟨t, e, w, q, l, lT, hh, hQ⟩ := horc z (UnLeaf.small hz1)
    refine ⟨.lf t, e, ⟨w, e ▸ hz1⟩, trivial, q, l, lT, fun h => hh (by rwa [Rj.rjDat_small hz1] at h),
      fun hd h0 => ?_, hQ⟩
    obtain ⟨k, hk⟩ := hd
    have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact h0 hk
    have : Om1 ≤ z := hk ▸ le_mul_left Om1 (pos_iff_ne_zero.2 hk0)
    exact absurd hz1 (not_lt.2 this)
  · have hz0 : z ≠ 0 := (lt_of_lt_of_le Rj.rj_Om1_pos hz1).ne'
    obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hz0
    set g := log ω z with hgdef
    set v := z / ω ^ g with hvdef
    set r := z % ω ^ g with hrdef
    set b := g - Om1 with hbdef
    have hg1 : Om1 ≤ g := Si.si_Om1_le_log hz1
    have hgb : Om1 + b = g := Ordinal.add_sub_cancel_of_le hg1
    have hwg : ω ^ g = Om1 * ω ^ b := by rw [← hgb, Si.si_Om1_opow_eq]
    have hgz : ω ^ g ≤ z := opow_log_le_self ω hz0
    have hrz : r < z := hr.trans_le hgz
    -- the data and `b < z`
    have hfacts : b < z ∧ Rj.rjDat b ≤ Rj.rjDat z ∧ Rj.rjDat r ≤ Rj.rjDat z ∧
        (τ ≤ Rj.rjDat z → τ ≤ Rj.rjDat b ∨ τ ≤ Rj.rjDat r) := by
      rcases hz1.lt_or_eq with hlt | heq
      · have hgz' : g < z := Rj.rj_log_lt hlt hzE
        have hbz : b < z := lt_of_le_of_lt (hgb ▸ le_add_self) hgz'
        have hd : Rj.rjDat z = max (Rj.rjDat g) (Rj.rjDat r) := Rj.rjDat_eq hlt hzE
        have hgd : Rj.rjDat g = Rj.rjDat b := by rw [← hgb]; exact unDat_Om1_add (hbz.trans hzE)
        rw [hgd] at hd
        rw [hd]
        exact ⟨hbz, le_max_left _ _, le_max_right _ _, fun h => (le_max_iff.1 h)⟩
      · have hgO : g = Om1 := by
          rw [hgdef, ← heq]
          conv_lhs => rw [← Rj.rj_Om1_opow]
          exact log_opow one_lt_omega0 _
        have hb0 : b = 0 := by rw [hbdef, hgO, Ordinal.sub_self]
        have hr0 : r = 0 := by
          rw [hrdef, hgO, Rj.rj_Om1_opow, ← heq, Ordinal.mod_self]
        rw [hb0, hr0, ← heq, Rj.rjDat_Om1, Rj.rjDat_small Rj.rj_Om1_pos]
        exact ⟨heq ▸ Rj.rj_Om1_pos, le_rfl, le_rfl, fun h => absurd h (not_le.2 hτ0)⟩
    obtain ⟨hbz, hdb, hdr, hdτ⟩ := hfacts
    -- the exponent part
    obtain ⟨Gb, eb, wb, fb, qb, lb, lTb, hdGb, -, lfb⟩ := IH b hbz (hbz.trans hzE)
      (fun c hc => horc c (UnLeaf.exp hz1 hc))
    set x : UnT true := .om Gb with hxdef
    have hex : ev τ x = ω ^ g := by rw [hwg]; show Om1 * ω ^ ev τ Gb = _; rw [eb]
    have hx0 : 0 < ev τ x := by rw [hex]; exact opow_pos _ omega0_pos
    have hxx : ev τ x < ev τ x * ω := by
      calc ev τ x = ev τ x * 1 := (mul_one _).symm
        _ < ev τ x * ω := mul_lt_mul_of_pos_left one_lt_omega0 hx0
    obtain ⟨n', hn'⟩ := lt_omega0.1 hvω
    have hn0 : n' ≠ 0 := by rintro rfl; exact hv0 (by rw [hn']; rfl)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hvn : v = (n : Ordinal.{0}) + 1 := by rw [hn', Nat.cast_succ]
    have hdvx : Om1 ∣ ω ^ g * v := ⟨ω ^ b * v, by rw [hwg, mul_assoc]⟩
    by_cases hr0 : r = 0
    · -- `z = x·(n+1)`
      refine ⟨adRep x n x, ?_, adRep_WFr (x := x) (R := x) wb wb n,
        (adRep_FNF (x := x) (R := x) fb fb trivial hxx n).1, adRep_Qs (x := x) (R := x) qb qb n,
        adRep_Lv (x := x) (R := x) lb lb n, adRep_Lv (x := x) (R := x) lTb lTb n, fun h => ?_,
        fun _ _ => adRep_Gs (x := x) (R := x) trivial trivial n, adRep_Lf (x := x) (R := x) lfb lfb n⟩
      · rw [adRep_ev, hex]
        conv_rhs => rw [← hdec, hr0, add_zero, hvn, mul_add_one]
      · have h1 : τ ≤ Rj.rjDat b := by
          rcases hdτ h with h1 | h1
          · exact h1
          · rw [hr0, Rj.rjDat_small Rj.rj_Om1_pos] at h1; exact absurd h1 (not_le.2 hτ0)
        exact adRep_HdE_R (x := x) (R := x) (hdGb h1) n
    · obtain ⟨Gr, er, wr, fr, qr, lr, lTr, hdGr, gsGr, lfr⟩ := IH r hrz (hrz.trans hzE)
        (fun c hc => horc c (UnLeaf.rem hz1 hc))
      have hrx : ev τ Gr < ev τ x * ω := by rw [er, hex]; exact hr.trans (hex ▸ hxx)
      refine ⟨adRep x (n + 1) Gr, ?_, adRep_WFr (x := x) wb wr (n + 1),
        (adRep_FNF (x := x) fb fr trivial hrx (n + 1)).1, adRep_Qs (x := x) qb qr (n + 1),
        adRep_Lv (x := x) lb lr (n + 1), adRep_Lv (x := x) lTb lTr (n + 1), fun h => ?_,
        fun hd _ => adRep_Gs (x := x) trivial (gsGr ((Ordinal.dvd_add_iff hdvx).1 (hdec.symm ▸ hd)) hr0) (n + 1),
        adRep_Lf (x := x) lfb lfr (n + 1)⟩
      · rw [adRep_ev, hex, er, Nat.cast_succ, ← hvn]
        exact hdec
      · rcases hdτ h with h1 | h1
        · exact adRep_HdE_x (x := x) (hdGb h1) n
        · exact adRep_HdE_R (x := x) (hdGr h1) (n + 1)


/-- **A decomposition of `y` over `τ` by ordinal data, with gap levels**: the clauses of `Un.UnGd` (parameters
`p < τ` with `P p`, the base `τ`, sums, `ϑᵗ(1 + s)`, `ϑᵗ(Ω₁·q + r)` at a constant level over `κ`, `ϑᵗ(Ω₁·M + r)`
with `τ ≤ rjDat(Ω₁·M)` and every leaf decomposed again) and **`thl`**: `ϑᵗ(Ω₁·M + r)` with `Ω₁·M < ε_{Ω₁+1}`,
`M ≥ Ω₁` or `M < τ`, `Ω₁·M + r ∈ Tᵗ`, `r < Ω₁`, and every leaf of `Ω₁·M` (`UnLeaf`) a parameter `p < τ` with
`P p` (a **low level**, e.g. `ϑ^{υ_{λ+h}}(Ω₁·υ_{λ+h'} + r)`, `h' < h`). -/
inductive UrGd (κ τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : Ordinal.{0} → Prop
  | par {p : Ordinal.{0}} : p < τ → P p → UrGd κ τ P p
  | base : UrGd κ τ P τ
  | add {a b : Ordinal.{0}} : UrGd κ τ P a → UrGd κ τ P b → (τ ≤ a + b → τ ≤ a) → UrGd κ τ P (a + b)
  | th1 {s : Ordinal.{0}} : s < Om1 → UrGd κ τ P s → UrGd κ τ P (vt τ (1 + s))
  | thc {q r : Ordinal.{0}} : UhLev κ q → r < Om1 → UrGd κ τ P r → UrGd κ τ P (vt τ (Om1 * q + r))
  | thg {M r : Ordinal.{0}} : 1 ≤ M → Om1 * M < Gg.ggE → (Om1 ≤ M ∨ (M < Om1 ∧ M ∈ Tset τ)) →
      τ ≤ Rj.rjDat (Om1 * M) → Om1 * M + r ∈ Tset τ → r < Om1 → UrGd κ τ P r →
      (∀ c, UnLeaf (Om1 * M) c → UrGd κ τ P c) → UrGd κ τ P (vt τ (Om1 * M + r))
  | thl {M r : Ordinal.{0}} : 1 ≤ M → Om1 * M < Gg.ggE → (Om1 ≤ M ∨ M < τ) → Om1 * M + r ∈ Tset τ → r < Om1 →
      UrGd κ τ P r → (∀ c, UnLeaf (Om1 * M) c → c < τ ∧ P c) → UrGd κ τ P (vt τ (Om1 * M + r))

/-- **Term existence**: every `y` with a decomposition `UrGd κ τ P y` is the value over `τ` of a well-formed term of
`Un.UnT` with the node conditions `Ur.WFr` (normal-form mode at the level terms) with levels over `κ`,
parameters satisfying `P` and in `Tᵗ`, and a
high head when `τ ≤ y`. -/
theorem urExist {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop} {y : Ordinal.{0}}
    (h : UrGd κ τ P y) :
    ∃ t : UnT false, ev τ t = y ∧ WFr τ t ∧ Qs κ t ∧ Lv P t ∧ Lv (· ∈ Tset τ) t ∧ (τ ≤ y → HiC τ t) := by
  have hτ := hB.2.1
  have hτ1 := hB.2.2.2
  induction h with
  | @par p hp hP => exact ⟨.par p, rfl, trivial, trivial, hP, uh_T_le hτ hτ1 hp.le, fun h => h⟩
  | base => exact ⟨.base, rfl, trivial, trivial, trivial, trivial, fun _ => trivial⟩
  | @add a b _ _ hab iha ihb =>
    obtain ⟨ta, ea, wa, qa, la, lTa, ha⟩ := iha
    obtain ⟨tb, eb, wb, qb, lb, lTb, -⟩ := ihb
    refine ⟨.add ta tb, by show ev τ ta + ev τ tb = _; rw [ea, eb], ⟨wa, wb⟩, ⟨qa, qb⟩, ⟨la, lb⟩, ⟨lTa, lTb⟩,
      fun h => ha (hab h)⟩
  | @th1 s hs _ ih =>
    obtain ⟨ts, es, ws, qs, ls, lTs, -⟩ := ih
    exact ⟨.th1 ts, by show vt τ (1 + ev τ ts) = _; rw [es], ⟨ws, es ▸ hs⟩, qs, ls, lTs, fun _ => trivial⟩
  | @thc q r hq hr _ ih =>
    obtain ⟨tr, er, wr, qr, lr, lTr, -⟩ := ih
    exact ⟨.thc q tr, by show vt τ (Om1 * q + ev τ tr) = _; rw [er], ⟨wr, er ▸ hr⟩, ⟨hq, qr⟩, lr, lTr,
      fun _ => trivial⟩
  | @thg M r hM1 hME hMc hd hmem hr _ _ ihr ihc =>
    obtain ⟨tr, er, wr, qr, lr, lTr, -⟩ := ihr
    obtain ⟨G, eG, wG, fG, qG, lG, lTG, hdG, gsG, -⟩ :=
      urLevelEx (κ := κ) (InE.pos hτ) P (fun _ => True) (Om1 * M) hME
        (fun c hc => (ihc c hc).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, trivial⟩)
    have hM0 : Om1 * M ≠ 0 := (mul_pos Rj.rj_Om1_pos (lt_of_lt_of_le zero_lt_one hM1)).ne'
    have hgs : Gs G := gsG (dvd_mul_right _ _) hM0
    have hdE : HdE τ G := hdG hd
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hmem' : ev τ G + ev τ tr ∈ Tset τ := by rw [eG, er]; exact hmem
    have hW : WFr τ (UnT.thg true G tr) := by
      rcases hMc with hM | ⟨hM, hMT⟩
      · exact urNodeHi hτ hτ1 G tr wG wr hr' hgs fG hdE (by rw [eG]; exact mul_le_mul_right hM Om1) hmem'
      · exact urNodeLo hB G tr wG lTG qG wr hr' hgs fG hdE eG hM hMT hmem'
    exact ⟨.thg true G tr, by show vt τ (ev τ G + ev τ tr) = _; rw [eG, er], hW, ⟨qG, qr⟩, ⟨lG, lr⟩,
      ⟨lTG, lTr⟩, fun _ => trivial⟩
  | @thl M r hM1 hME hMc hmem hr _ hlo ihr =>
    obtain ⟨tr, er, wr, qr, lr, lTr, -⟩ := ihr
    obtain ⟨G, eG, wG, fG, qG, lG, lTG, -, gsG, lfG⟩ :=
      urLevelEx (κ := κ) (InE.pos hτ) P (fun t => ∃ p, t = .par p ∧ p < τ) (Om1 * M) hME
        (fun c hc => ⟨.par c, rfl, trivial, trivial, (hlo c hc).2, uh_T_le hτ hτ1 (hlo c hc).1.le,
          fun h => h, c, rfl, (hlo c hc).1⟩)
    have hM0 : Om1 * M ≠ 0 := (mul_pos Rj.rj_Om1_pos (lt_of_lt_of_le zero_lt_one hM1)).ne'
    have hgs : Gs G := gsG (dvd_mul_right _ _) hM0
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hmem' : ev τ G + ev τ tr ∈ Tset τ := by rw [eG, er]; exact hmem
    have hW : WFr τ (UnT.thg true G tr) :=
      urNodeLow hτ hτ1 G tr wG wr hr' hgs fG (LoL_of_Lf G lfG) eG hM1 hME hMc hmem'
    exact ⟨.thg true G tr, by show vt τ (ev τ G + ev τ tr) = _; rw [eG, er], hW, ⟨qG, qr⟩, ⟨lG, lr⟩,
      ⟨lTG, lTr⟩, fun _ => trivial⟩


/-- **`Un.UnGd ⇒ UrGd`** (every clause of `Un.UnGd` is a clause of `UrGd`). -/
theorem urGd_of_un {κ τ : Ordinal.{0}} {P : Ordinal.{0} → Prop} {y : Ordinal.{0}} (h : UnGd κ τ P y) :
    UrGd κ τ P y := by
  induction h with
  | par hp hP => exact .par hp hP
  | base => exact .base
  | add _ _ hab iha ihb => exact .add iha ihb hab
  | th1 hs _ ih => exact .th1 hs ih
  | thc hq hr _ ih => exact .thc hq hr ih
  | thg hM1 hME hMc hd hmem hr _ _ ihr ihc => exact .thg hM1 hME hMc hd hmem hr ihr ihc

end Googology.Trans.PoR.InaccPsi.R2.Ur
