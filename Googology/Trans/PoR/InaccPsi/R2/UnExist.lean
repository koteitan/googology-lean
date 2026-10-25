import Googology.Trans.PoR.InaccPsi.R2.UnNode

/-!
# Term existence: ordinal data of the normal-form decomposition give well-formed terms

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

* `UnLeaf z c` (**the leaves of the hereditary Cantor normal form of `z < ε_{Ω₁+1}` over `{0, Ω₁}`**: `z` itself
  for `z < Ω₁`; for `z ≥ Ω₁` with `z = ω^{Ω₁+b}·v + r` (`r < ω^{Ω₁+b}`) the leaves of `b` and of `r`), `adRep`;
* `unLevelEx` (**every `z < ε_{Ω₁+1}` is the value of a level term in full Cantor normal form whose leaves are
  given terms for the `UnLeaf z`-leaves; it has a high leaf when `τ ≤ rjDat z` and the top shape `Gs` when
  `Ω₁ ∣ z`**);
* `UnGd κ τ P y` (**a decomposition of `y` into parameters `< τ` with `P`, `τ`, sums, `ϑᵗ(1 + s)`,
  `ϑᵗ(Ω₁·q + r)` at constant levels over `κ`, and `ϑᵗ(Ω₁·M + r)` given by ORDINAL data**: `Ω₁·M < ε_{Ω₁+1}`,
  `τ ≤ rjDat(Ω₁·M)`, `Ω₁·M + r ∈ Tᵗ`, `M ≥ Ω₁` or `M ∈ Tᵗ`, and the leaves of `Ω₁·M` decomposed again);
* `unExist` (**every `y` with `UnGd κ τ P y` is the value of a well-formed term of `Un.UnT`** whose parameters
  satisfy `P`: the level terms are built by `unLevelEx` and the node conditions come from [W07a] Lemma 3.30 through
  `Un.unNodeHi`, `Un.unNodeLo`).

No new axiom.  New definitions: `UnLeaf`, `adRep`, `UnGd`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Un

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh UnT

/-- **The leaves of the hereditary Cantor normal form** of `z` over `{0, Ω₁}`. -/
inductive UnLeaf : Ordinal.{0} → Ordinal.{0} → Prop
  | small {z : Ordinal.{0}} : z < Om1 → UnLeaf z z
  | exp {z c : Ordinal.{0}} : Om1 ≤ z → UnLeaf (log ω z - Om1) c → UnLeaf z c
  | rem {z c : Ordinal.{0}} : Om1 ≤ z → UnLeaf (z % ω ^ log ω z) c → UnLeaf z c

theorem UnLeaf.lt_Om1 {z c : Ordinal.{0}} (h : UnLeaf z c) : c < Om1 := by
  induction h with
  | small h => exact h
  | exp _ _ ih => exact ih
  | rem _ _ ih => exact ih

/-- `x + ⋯ + x + R` (`n` copies of `x`). -/
def adRep (x : UnT true) : ℕ → UnT true → UnT true
  | 0, R => R
  | n + 1, R => .ad x (adRep x n R)

theorem adRep_ev (τ : Ordinal.{0}) (x R : UnT true) : ∀ n : ℕ, ev τ (adRep x n R) = ev τ x * n + ev τ R
  | 0 => by simp [adRep]
  | n + 1 => by
    show ev τ x + ev τ (adRep x n R) = _
    rw [adRep_ev τ x R n, Nat.cast_succ, mul_add_one, ← add_assoc]
    congr 1
    -- `x + x·n = x·n + x`
    have e : ∀ m : ℕ, ev τ x + ev τ x * m = ev τ x * m + ev τ x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.cast_succ, mul_add_one, ← add_assoc, ih]
    exact e n

theorem adRep_WF {τ : Ordinal.{0}} {x R : UnT true} (hx : WF τ x) (hR : WF τ R) : ∀ n : ℕ, WF τ (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_WF hx hR n⟩

theorem adRep_Qs {κ : Ordinal.{0}} {x R : UnT true} (hx : Qs κ x) (hR : Qs κ R) : ∀ n : ℕ, Qs κ (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_Qs hx hR n⟩

theorem adRep_Lv {P : Ordinal.{0} → Prop} {x R : UnT true} (hx : Lv P x) (hR : Lv P R) :
    ∀ n : ℕ, Lv P (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_Lv hx hR n⟩

theorem adRep_Gs {x R : UnT true} (hx : Gs x) (hR : Gs R) : ∀ n : ℕ, Gs (adRep x n R)
  | 0 => hR
  | n + 1 => ⟨hx, adRep_Gs hx hR n⟩

theorem adRep_HdE_R {τ : Ordinal.{0}} {x R : UnT true} (hR : HdE τ R) : ∀ n : ℕ, HdE τ (adRep x n R)
  | 0 => hR
  | n + 1 => Or.inr (adRep_HdE_R hR n)

theorem adRep_HdE_x {τ : Ordinal.{0}} {x R : UnT true} (hx : HdE τ x) (n : ℕ) : HdE τ (adRep x (n + 1) R) :=
  Or.inl hx

theorem adRep_FNF {τ : Ordinal.{0}} {x R : UnT true} (hx : FNF τ x) (hR : FNF τ R) (hox : IsOm x)
    (hRx : ev τ R < ev τ x * ω) : ∀ n : ℕ, FNF τ (adRep x n R) ∧ ev τ (adRep x n R) < ev τ x * ω
  | 0 => ⟨hR, hRx⟩
  | n + 1 => by
    obtain ⟨a1, a2⟩ := adRep_FNF hx hR hox hRx n
    refine ⟨⟨hx, a1, hox, a2⟩, ?_⟩
    show ev τ x + ev τ (adRep x n R) < ev τ x * ω
    obtain ⟨m, hm⟩ := unLt_mul_omega_iff.1 a2
    refine unLt_mul_omega_iff.2 ⟨1 + m, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    exact (add_lt_add_iff_left _).2 hm

/-- The data of `Ω₁ + b` are those of `b` (`b < ε_{Ω₁+1}`). -/
theorem unDat_Om1_add {b : Ordinal.{0}} (hbE : b < Gg.ggE) : Rj.rjDat (Om1 + b) = Rj.rjDat b := by
  rcases lt_or_ge b Om1 with hb1 | hb1
  · by_cases hb0 : b = 0
    · rw [hb0, add_zero, Rj.rjDat_Om1, Rj.rjDat_small Rj.rj_Om1_pos]
    · rw [Rj.rjDat_Om1_add hb0 hb1, Rj.rjDat_small hb1]
  · exact Si.si_rjDat_Om1_add hb1 hbE

/-- **Level-term existence**: every `z < ε_{Ω₁+1}` whose leaves are values of given terms is the value of a level
term in full Cantor normal form, with a high leaf when `τ ≤ rjDat z` and the shape `Gs` when `Ω₁ ∣ z`. -/
theorem unLevelEx {κ τ : Ordinal.{0}} (hτ0 : 0 < τ) (P : Ordinal.{0} → Prop) :
    ∀ z : Ordinal.{0}, z < Gg.ggE →
      (∀ c, UnLeaf z c → ∃ t : UnT false, ev τ t = c ∧ WF τ t ∧ Qs κ t ∧ Lv P t ∧ Lv (· ∈ Tset τ) t ∧
        (τ ≤ c → HiC τ t)) →
      ∃ G : UnT true, ev τ G = z ∧ WF τ G ∧ FNF τ G ∧ Qs κ G ∧ Lv P G ∧ Lv (· ∈ Tset τ) G ∧
        (τ ≤ Rj.rjDat z → HdE τ G) ∧ (Om1 ∣ z → z ≠ 0 → Gs G) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE horc
  rcases lt_or_ge z Om1 with hz1 | hz1
  · obtain ⟨t, e, w, q, l, lT, hh⟩ := horc z (UnLeaf.small hz1)
    refine ⟨.lf t, e, ⟨w, e ▸ hz1⟩, trivial, q, l, lT, fun h => hh (by rwa [Rj.rjDat_small hz1] at h),
      fun hd h0 => ?_⟩
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
    obtain ⟨Gb, eb, wb, fb, qb, lb, lTb, hdGb, -⟩ := IH b hbz (hbz.trans hzE)
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
      refine ⟨adRep x n x, ?_, adRep_WF (x := x) (R := x) wb wb n,
        (adRep_FNF (x := x) (R := x) fb fb trivial hxx n).1, adRep_Qs (x := x) (R := x) qb qb n,
        adRep_Lv (x := x) (R := x) lb lb n, adRep_Lv (x := x) (R := x) lTb lTb n, fun h => ?_,
        fun _ _ => adRep_Gs (x := x) (R := x) trivial trivial n⟩
      · rw [adRep_ev, hex]
        conv_rhs => rw [← hdec, hr0, add_zero, hvn, mul_add_one]
      · have h1 : τ ≤ Rj.rjDat b := by
          rcases hdτ h with h1 | h1
          · exact h1
          · rw [hr0, Rj.rjDat_small Rj.rj_Om1_pos] at h1; exact absurd h1 (not_le.2 hτ0)
        exact adRep_HdE_R (x := x) (R := x) (hdGb h1) n
    · obtain ⟨Gr, er, wr, fr, qr, lr, lTr, hdGr, gsGr⟩ := IH r hrz (hrz.trans hzE)
        (fun c hc => horc c (UnLeaf.rem hz1 hc))
      have hrx : ev τ Gr < ev τ x * ω := by rw [er, hex]; exact hr.trans (hex ▸ hxx)
      refine ⟨adRep x (n + 1) Gr, ?_, adRep_WF (x := x) wb wr (n + 1),
        (adRep_FNF (x := x) fb fr trivial hrx (n + 1)).1, adRep_Qs (x := x) qb qr (n + 1),
        adRep_Lv (x := x) lb lr (n + 1), adRep_Lv (x := x) lTb lTr (n + 1), fun h => ?_,
        fun hd _ => adRep_Gs (x := x) trivial (gsGr ((Ordinal.dvd_add_iff hdvx).1 (hdec.symm ▸ hd)) hr0) (n + 1)⟩
      · rw [adRep_ev, hex, er, Nat.cast_succ, ← hvn]
        exact hdec
      · rcases hdτ h with h1 | h1
        · exact adRep_HdE_x (x := x) (hdGb h1) n
        · exact adRep_HdE_R (x := x) (hdGr h1) (n + 1)

/-- **A decomposition of `y` over `τ` by ordinal data**: parameters `p < τ` with `P p`, the base `τ`, sums (whose
left part carries `τ ≤ y`), `ϑᵗ(1 + s)`, `ϑᵗ(Ω₁·q + r)` at a constant level over `κ`, and `ϑᵗ(Ω₁·M + r)` with
`Ω₁·M < ε_{Ω₁+1}`, `M ≥ Ω₁` or `M ∈ Tᵗ ∩ Ω₁`, `τ ≤ rjDat(Ω₁·M)` (`Γ^* ≥ τ`), `Ω₁·M + r ∈ Tᵗ`, `r < Ω₁`, and every
leaf of `Ω₁·M` (`UnLeaf`) decomposed again. -/
inductive UnGd (κ τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : Ordinal.{0} → Prop
  | par {p : Ordinal.{0}} : p < τ → P p → UnGd κ τ P p
  | base : UnGd κ τ P τ
  | add {a b : Ordinal.{0}} : UnGd κ τ P a → UnGd κ τ P b → (τ ≤ a + b → τ ≤ a) → UnGd κ τ P (a + b)
  | th1 {s : Ordinal.{0}} : s < Om1 → UnGd κ τ P s → UnGd κ τ P (vt τ (1 + s))
  | thc {q r : Ordinal.{0}} : UhLev κ q → r < Om1 → UnGd κ τ P r → UnGd κ τ P (vt τ (Om1 * q + r))
  | thg {M r : Ordinal.{0}} : 1 ≤ M → Om1 * M < Gg.ggE → (Om1 ≤ M ∨ (M < Om1 ∧ M ∈ Tset τ)) →
      τ ≤ Rj.rjDat (Om1 * M) → Om1 * M + r ∈ Tset τ → r < Om1 → UnGd κ τ P r →
      (∀ c, UnLeaf (Om1 * M) c → UnGd κ τ P c) → UnGd κ τ P (vt τ (Om1 * M + r))

/-- **Term existence**: every `y` with a decomposition `UnGd κ τ P y` is the value over `τ` of a well-formed term of
`Un.UnT` (normal-form mode at the level terms) with levels over `κ`, parameters satisfying `P` and in `Tᵗ`, and a
high head when `τ ≤ y`. -/
theorem unExist {κ τ : Ordinal.{0}} (hB : Bases κ τ) {P : Ordinal.{0} → Prop} {y : Ordinal.{0}}
    (h : UnGd κ τ P y) :
    ∃ t : UnT false, ev τ t = y ∧ WF τ t ∧ Qs κ t ∧ Lv P t ∧ Lv (· ∈ Tset τ) t ∧ (τ ≤ y → HiC τ t) := by
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
    obtain ⟨G, eG, wG, fG, qG, lG, lTG, hdG, gsG⟩ :=
      unLevelEx (κ := κ) (InE.pos hτ) P (Om1 * M) hME (fun c hc => ihc c hc)
    have hM0 : Om1 * M ≠ 0 := (mul_pos Rj.rj_Om1_pos (lt_of_lt_of_le zero_lt_one hM1)).ne'
    have hgs : Gs G := gsG (dvd_mul_right _ _) hM0
    have hdE : HdE τ G := hdG hd
    have hr' : ev τ tr < Om1 := er ▸ hr
    have hmem' : ev τ G + ev τ tr ∈ Tset τ := by rw [eG, er]; exact hmem
    have hW : WF τ (UnT.thg true G tr) := by
      rcases hMc with hM | ⟨hM, hMT⟩
      · exact unNodeHi hτ hτ1 G tr wG wr hr' hgs fG hdE (by rw [eG]; exact mul_le_mul_right hM Om1) hmem'
      · exact unNodeLo hB G tr wG lTG qG wr hr' hgs fG hdE eG hM hMT hmem'
    exact ⟨.thg true G tr, by show vt τ (ev τ G + ev τ tr) = _; rw [eG, er], hW, ⟨qG, qr⟩, ⟨lG, lr⟩,
      ⟨lTG, lTr⟩, fun _ => trivial⟩

end Googology.Trans.PoR.InaccPsi.R2.Un
