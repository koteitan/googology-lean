import Googology.Trans.PoR.InaccPsi.R2.TrMv

/-!
# Theorem FRAG on low-parameter configurations, with the segment move on every segment

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`R2.soFrag` gives the realizer map `Ψ = mv b_0 c_0` only on `D_1` (the lowest segment).  Here the configuration
`F` consists of points below `κ` and of points `x ∈ seg(b_k)` with `Parᵇᵏ(x) ⊆ κ` (**low-parameter points**,
`TrLowPt`); for such `F` the map `Ψ := mv b_k c_k` on `seg(b_k)` (identity below `κ`) satisfies every clause of
Theorem FRAG with (F-f), on **every** segment.  Points of different segments interact only by absorption
(`x < b_k ≤ y ⇒ x + y = y`), and a sum `x + y ∈ seg(b_k)` with `y < b_k` forces `y < κ` (`Tr.trTB_sub`).

* `TrLowPt` (a point below `κ`, or a low-parameter point of some `seg(b_k)`);
* `trAdd_shape` (**the shape of `x + y = z` among low-parameter points**: `z < κ`, or `z ∈ seg(b_k)` and either
  `x < b_k ≤ y = z` or all three lie in `Tᵇᵏ[κ]`);
* `trFragLow` (**Theorem FRAG with (F-f) for low-parameter configurations, and `Ψ = mv b_k c_k` on `F ∩ seg(b_k)`
  for every `k < m`**);
* `trFragLow_comp` (the carry through an intermediate chain: on `F ∩ seg(b_k)` the composite of the maps
  `b → c → d` is `mv b_k d_k`, by `Tr.trMv_comp`).

No new axiom.  New definition: `TrLowPt` (a predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tr

open Ordinal Set Googology.Trans.PoR.InaccPsi.R2

/-- **A low-parameter point** for the chain `e`: below `κ`, or in some `seg(e_k)` with parameters below `κ`. -/
def TrLowPt (κ : Ordinal.{0}) (e : ℕ → Ordinal.{0}) (m : ℕ) (x : Ordinal.{0}) : Prop :=
  x < κ ∨ ∃ k, k < m ∧ InSeg (e k) x ∧ x ∈ TB (e k) κ

section Chain

variable {κ : Ordinal.{0}} {e : ℕ → Ordinal.{0}} {m : ℕ}

theorem trBases_chain (he : Chain κ e m) {k : ℕ} (hk : k < m) : Bases κ (e k) :=
  ⟨upsPt_inE he.kap, upsPt_inE (he.ups k hk).1, he.bot k hk, (he.ups k hk).2⟩

theorem trLowT_of_lt (he : Chain κ e m) {k : ℕ} (hk : k < m) {w : Ordinal.{0}} (hw : w < κ) :
    w ∈ TrLowT (e k) κ :=
  ⟨(TB_inter_lt (trBases_chain he hk) (hw.trans (he.bot k hk))).2 hw, hw.trans he.kap1⟩

theorem trLowT_of_seg {k : ℕ} {w : Ordinal.{0}} (hs : InSeg (e k) w) (hT : w ∈ TB (e k) κ) :
    w ∈ TrLowT (e k) κ := ⟨hT, hs.2.1⟩

/-- A low-parameter point `w` with `e_k ≤ w ≤ z ∈ seg(e_k)` lies in `seg(e_k) ∩ Tᵉᵏ[κ]`. -/
theorem trLowPt_seg (he : Chain κ e m) {k : ℕ} (hk : k < m) {w z : Ordinal.{0}} (hw : TrLowPt κ e m w)
    (hkw : e k ≤ w) (hwz : w ≤ z) (hz : InSeg (e k) z) : InSeg (e k) w ∧ w ∈ TrLowT (e k) κ := by
  have hs : InSeg (e k) w := ⟨hkw, hwz.trans_lt hz.2.1, fun u hu hu' => hwz.trans_lt (hz.2.2 u hu hu')⟩
  rcases hw with hw | ⟨j, hj, hjs, hjT⟩
  · exact absurd (hw.trans ((he.bot k hk).trans_le hkw)) (lt_irrefl _)
  · obtain rfl := InSeg.unique he hj hk hjs hs
    exact ⟨hs, trLowT_of_seg hjs hjT⟩

/-- A point of `Tᵉᵏ[κ] ∩ Ω₁` is below `κ` or in `seg(e_k)`. -/
theorem trLowT_cases (he : Chain κ e m) {k : ℕ} (hk : k < m) {w : Ordinal.{0}} (hw : w ∈ TrLowT (e k) κ) :
    w < κ ∨ InSeg (e k) w := by
  rcases lt_or_ge w (e k) with h | h
  · exact Or.inl ((TB_inter_lt (trBases_chain he hk) h).1 hw.1)
  · exact Or.inr ((inSeg_iff (he.ups k hk).1 (he.ups k hk).2).2 ⟨h, hw.2, hw.1.1⟩)

/-- **The shape of `x + y = z` among low-parameter points.** -/
theorem trAdd_shape (he : Chain κ e m) {x y z : Ordinal.{0}} (hx : TrLowPt κ e m x) (hy : TrLowPt κ e m y)
    (hz : TrLowPt κ e m z) (hxyz : x + y = z) :
    z < κ ∨ ∃ k, k < m ∧ InSeg (e k) z ∧ ((InSeg (e k) y ∧ x < e k ∧ z = y) ∨
      (x ∈ TrLowT (e k) κ ∧ y ∈ TrLowT (e k) κ ∧ z ∈ TrLowT (e k) κ)) := by
  rcases hz with hz | ⟨k, hk, hzs, hzT⟩
  · exact Or.inl hz
  refine Or.inr ⟨k, hk, hzs, ?_⟩
  have hE : InE (e k) := upsPt_inE (he.ups k hk).1
  have hxz : x ≤ z := hxyz ▸ le_self_add
  have hyz : y ≤ z := hxyz ▸ le_add_self
  have hzL := trLowT_of_seg hzs hzT
  rcases lt_or_ge y (e k) with hyk | hyk
  · -- `y < e_k`: then `x ≥ e_k` and `y ∈ Tᵉᵏ[κ]`
    have hxk : e k ≤ x := by
      by_contra h
      exact absurd (hxyz ▸ hE.add_lt (not_le.1 h) hyk) (not_lt.2 hzs.1)
    have hxL := (trLowPt_seg he hk hx hxk hxz hzs).2
    have hyT := trTB_sub (trBases_chain he hk) hxL.1 hzT hzs.2.1 hxyz
    exact Or.inr ⟨hxL, ⟨hyT, hyz.trans_lt hzs.2.1⟩, hzL⟩
  · have hyS := trLowPt_seg he hk hy hyk hyz hzs
    rcases lt_or_ge x (e k) with hxk | hxk
    · refine Or.inl ⟨hyS.1, hxk, ?_⟩
      rw [← hxyz]
      exact Ordinal.add_of_omega0_opow_le (hE.symm ▸ hxk) (hE.symm ▸ hyk)
    · exact Or.inr ⟨(trLowPt_seg he hk hx hxk hxz hzs).2, hyS.2, hzL⟩

end Chain

/-- The map: `mv b_k c_k` on `seg(b_k)`, the identity elsewhere. -/
private noncomputable def trPsi (b c : ℕ → Ordinal.{0}) (m : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if h : ∃ k, k < m ∧ InSeg (b k) x then mv (b (Nat.find h)) (c (Nat.find h)) x else x

section Frag

variable {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ}

private theorem trPsi_seg (hb : Chain κ b m) {k : ℕ} (hk : k < m) {x : Ordinal.{0}} (hs : InSeg (b k) x) :
    trPsi b c m x = mv (b k) (c k) x := by
  classical
  have h : ∃ k, k < m ∧ InSeg (b k) x := ⟨k, hk, hs⟩
  have hf : Nat.find h = k := InSeg.unique hb (Nat.find_spec h).1 hk (Nat.find_spec h).2 hs
  unfold trPsi
  rw [dif_pos h, hf]

private theorem trPsi_lt (hb : Chain κ b m) {x : Ordinal.{0}} (hx : x < κ) : trPsi b c m x = x := by
  classical
  have h : ¬ ∃ k, k < m ∧ InSeg (b k) x := by
    rintro ⟨k, hk, hs⟩
    exact absurd (hx.trans ((hb.bot k hk).trans_le hs.1)) (lt_irrefl _)
  unfold trPsi
  rw [dif_neg h]

/-- On `Tᵇᵏ[κ] ∩ Ω₁` the map is `mv b_k c_k`. -/
private theorem trPsi_lowT (hb : Chain κ b m) (hc : Chain κ c m) {k : ℕ} (hk : k < m) {w : Ordinal.{0}}
    (hw : w ∈ TrLowT (b k) κ) : trPsi b c m w = mv (b k) (c k) w := by
  rcases trLowT_cases hb hk hw with h | h
  · rw [trPsi_lt hb h, trMv_lt (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
      (hb.bot k hk) (hc.bot k hk) h]
  · exact trPsi_seg hb hk h

/-- The image of a low-parameter point is a low-parameter point of the chain `c`, in the matching segment. -/
private theorem trPsi_low (hb : Chain κ b m) (hc : Chain κ c m) {x : Ordinal.{0}} (hx : TrLowPt κ b m x) :
    (x < κ ∧ trPsi b c m x = x) ∨ ∃ k, k < m ∧ InSeg (b k) x ∧ x ∈ TrLowT (b k) κ ∧
      trPsi b c m x = mv (b k) (c k) x ∧ InSeg (c k) (trPsi b c m x) ∧
      trPsi b c m x ∈ TrLowT (c k) κ := by
  rcases hx with hx | ⟨k, hk, hs, hT⟩
  · exact Or.inl ⟨hx, trPsi_lt hb hx⟩
  · have hL := trLowT_of_seg hs hT
    refine Or.inr ⟨k, hk, hs, hL, trPsi_seg hb hk hs, ?_, ?_⟩
    · rw [trPsi_seg hb hk hs]
      exact trMv_inSeg (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
        (hb.bot k hk) (hc.bot k hk) hL hs
    · rw [trPsi_seg hb hk hs]
      exact trMv_maps (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
        (hb.bot k hk) (hc.bot k hk) hL

private theorem trPsi_lowPt (hb : Chain κ b m) (hc : Chain κ c m) {x : Ordinal.{0}}
    (hx : TrLowPt κ b m x) : TrLowPt κ c m (trPsi b c m x) := by
  rcases trPsi_low hb hc hx with ⟨h, e⟩ | ⟨k, hk, -, -, -, hs, hL⟩
  · exact Or.inl (by rw [e]; exact h)
  · exact Or.inr ⟨k, hk, hs, hL.1⟩

/-- `Ψ` is strictly increasing on the low-parameter points. -/
private theorem trPsi_mono (hb : Chain κ b m) (hc : Chain κ c m) {x y : Ordinal.{0}} (hx : TrLowPt κ b m x)
    (hy : TrLowPt κ b m y) (hxy : x < y) : trPsi b c m x < trPsi b c m y := by
  rcases trPsi_low hb hc hx with ⟨hxk, ex⟩ | ⟨j, hj, hxs, hxL, ex, hxs', -⟩ <;>
    rcases trPsi_low hb hc hy with ⟨hyk, ey⟩ | ⟨k, hk, hys, hyL, ey, hys', -⟩
  · rw [ex, ey]; exact hxy
  · rw [ex]; exact hxk.trans ((hc.bot k hk).trans_le hys'.1)
  · exact absurd ((hxy.trans hyk).trans ((hb.bot j hj).trans_le hxs.1)) (lt_irrefl _)
  · rcases lt_trichotomy j k with hjk | rfl | hjk
    · exact (hxs'.2.2 (c k) (hc.mono j k hjk hk) (hc.ups k hk).1).trans_le hys'.1
    · rw [ex, ey]
      exact trMv_mono (hb.ups j hj).1 (hb.ups j hj).2 (hc.ups j hj).1 (hc.ups j hj).2
        (hb.bot j hj) (hc.bot j hj) hxL hyL hxy
    · exact absurd ((hxy.trans (hys.2.2 (b j) (hb.mono k j hjk hj) (hb.ups j hj).1)).trans_le hxs.1)
        (lt_irrefl _)

/-- `Ψ` keeps and reflects the graph of `+` on the low-parameter points. -/
private theorem trPsi_add (hb : Chain κ b m) (hc : Chain κ c m) {x y z : Ordinal.{0}}
    (hx : TrLowPt κ b m x) (hy : TrLowPt κ b m y) (hz : TrLowPt κ b m z) :
    x + y = z ↔ trPsi b c m x + trPsi b c m y = trPsi b c m z := by
  have Pk := fun (k : ℕ) (hk : k < m) =>
    And.intro (hb.ups k hk) (And.intro (hc.ups k hk) (And.intro (hb.bot k hk) (hc.bot k hk)))
  -- a point is in `seg(b_k)` iff its image is in `seg(c_k)`
  have back : ∀ w, TrLowPt κ b m w → ∀ k, k < m → InSeg (c k) (trPsi b c m w) → InSeg (b k) w := by
    intro w hw k hk hs'
    rcases trPsi_low hb hc hw with ⟨hwk, ew⟩ | ⟨j, hj, hws, -, -, hws', -⟩
    · rw [ew] at hs'
      exact absurd (hwk.trans ((hc.bot k hk).trans_le hs'.1)) (lt_irrefl _)
    · rwa [InSeg.unique hc hk hj hs' hws']
  have below : ∀ w, TrLowPt κ b m w → ∀ k, k < m → trPsi b c m w < c k → w < b k := by
    intro w hw k hk hlt
    rcases trPsi_low hb hc hw with ⟨hwk, -⟩ | ⟨j, hj, hws, -, -, hws', -⟩
    · exact hwk.trans (hb.bot k hk)
    · rcases lt_or_ge j k with hjk | hjk
      · exact hws.2.2 (b k) (hb.mono j k hjk hk) (hb.ups k hk).1
      · exfalso
        have : c k ≤ c j := by
          rcases hjk.lt_or_eq with h | rfl
          · exact (hc.mono k j h hj).le
          · exact le_rfl
        exact absurd (hlt.trans_le (this.trans hws'.1)) (lt_irrefl _)
  constructor
  · intro hxyz
    rcases trAdd_shape hb hx hy hz hxyz with hzk | ⟨k, hk, hzs, ⟨hys, hxk, hzy⟩ | ⟨hxL, hyL, hzL⟩⟩
    · have hxk : x < κ := lt_of_le_of_lt (hxyz ▸ le_self_add) hzk
      have hyk : y < κ := lt_of_le_of_lt (hxyz ▸ le_add_self) hzk
      rw [trPsi_lt hb hxk, trPsi_lt hb hyk, trPsi_lt hb hzk, hxyz]
    · rw [hzy]
      have hE : InE (c k) := upsPt_inE (hc.ups k hk).1
      have hys' : InSeg (c k) (trPsi b c m y) := by
        rcases trPsi_low hb hc hy with ⟨hyk, -⟩ | ⟨j, hj, hjs, -, -, hjs', -⟩
        · exact absurd (hyk.trans ((hb.bot k hk).trans_le hys.1)) (lt_irrefl _)
        · rwa [InSeg.unique hb hj hk hjs hys] at hjs'
      have hxc : trPsi b c m x < c k := by
        rcases trPsi_low hb hc hx with ⟨hxκ, ex⟩ | ⟨j, hj, hjs, -, -, hjs', -⟩
        · rw [ex]; exact hxκ.trans (hc.bot k hk)
        · have hjk : j < k := by
            by_contra h
            have : b k ≤ b j := by
              rcases (not_lt.1 h).lt_or_eq with h' | h'
              · exact (hb.mono k j h' hj).le
              · rw [h']
            exact absurd (hxk.trans_le (this.trans hjs.1)) (lt_irrefl _)
          exact hjs'.2.2 (c k) (hc.mono j k hjk hk) (hc.ups k hk).1
      exact Ordinal.add_of_omega0_opow_le (hE.symm ▸ hxc) (hE.symm ▸ hys'.1)
    · obtain ⟨⟨hbk, hbk1⟩, ⟨hck, hck1⟩, hκb, hκc⟩ := Pk k hk
      rw [trPsi_lowT hb hc hk hxL, trPsi_lowT hb hc hk hyL, trPsi_lowT hb hc hk hzL]
      exact (trMv_add hbk hbk1 hck hck1 hκb hκc x hxL y hyL z hzL).1 hxyz
  · intro hxyz
    rcases trAdd_shape hc (trPsi_lowPt hb hc hx) (trPsi_lowPt hb hc hy) (trPsi_lowPt hb hc hz) hxyz with
      hzk | ⟨k, hk, hzs, ⟨hys, hxk, hzy⟩ | ⟨hxL, hyL, hzL⟩⟩
    · -- all images below `κ`
      have lowof : ∀ w, TrLowPt κ b m w → trPsi b c m w < κ → w < κ := by
        intro w hw hlt
        rcases trPsi_low hb hc hw with ⟨hwk, -⟩ | ⟨j, hj, -, -, -, hws', -⟩
        · exact hwk
        · exact absurd ((hlt.trans (hc.bot j hj)).trans_le hws'.1) (lt_irrefl _)
      have hxk := lowof x hx (lt_of_le_of_lt (hxyz ▸ le_self_add) hzk)
      have hyk := lowof y hy (lt_of_le_of_lt (hxyz ▸ le_add_self) hzk)
      have hzk' := lowof z hz hzk
      rwa [trPsi_lt hb hxk, trPsi_lt hb hyk, trPsi_lt hb hzk'] at hxyz
    · have hzy' : z = y := by
        rcases lt_trichotomy z y with h | h | h
        · exact absurd hzy (ne_of_lt (trPsi_mono hb hc hz hy h))
        · exact h
        · exact absurd hzy (ne_of_gt (trPsi_mono hb hc hy hz h))
      have hysb := back y hy k hk hys
      have hxb := below x hx k hk hxk
      have hE : InE (b k) := upsPt_inE (hb.ups k hk).1
      rw [hzy']
      exact Ordinal.add_of_omega0_opow_le (hE.symm ▸ hxb) (hE.symm ▸ hysb.1)
    · obtain ⟨⟨hbk, hbk1⟩, ⟨hck, hck1⟩, hκb, hκc⟩ := Pk k hk
      have pull : ∀ w, TrLowPt κ b m w → trPsi b c m w ∈ TrLowT (c k) κ → w ∈ TrLowT (b k) κ := by
        intro w hw hL
        rcases trPsi_low hb hc hw with ⟨hwk, -⟩ | ⟨j, hj, hws, hwL, -, hws', -⟩
        · exact trLowT_of_lt hb hk hwk
        · rcases trLowT_cases hc hk hL with h | h
          · exact absurd ((h.trans (hc.bot j hj)).trans_le hws'.1) (lt_irrefl _)
          · rwa [InSeg.unique hc hj hk hws' h] at hwL
      have hxL' := pull x hx hxL
      have hyL' := pull y hy hyL
      have hzL' := pull z hz hzL
      rw [trPsi_lowT hb hc hk hxL', trPsi_lowT hb hc hk hyL', trPsi_lowT hb hc hk hzL'] at hxyz
      exact (trMv_add hbk hbk1 hck hck1 hκb hκc x hxL' y hyL' z hzL').2 hxyz

/-- **Theorem FRAG with (F-f) for low-parameter configurations, with `Ψ = mv b_k c_k` on `F ∩ seg(b_k)` for every
`k < m`.** -/
theorem trFragLow (hb : Chain κ b m) (hc : Chain κ c m) (F : Finset Ordinal.{0})
    (hF : ∀ x ∈ F, TrLowPt κ b m x) :
    ∃ Ψ, LrFragConcl κ b c m F Ψ ∧ ∀ k, k < m → ∀ x ∈ F, InSeg (b k) x → Ψ x = mv (b k) (c k) x := by
  classical
  set F₁ := F ∪ (Finset.range m).image b with hF₁def
  have hbL : ∀ k, k < m → TrLowPt κ b m (b k) := fun k hk =>
    Or.inr ⟨k, hk, InSeg.self (hb.ups k hk).2, (pi_base (trBases_chain hb hk)).1⟩
  have hF₁ : ∀ x ∈ F₁, TrLowPt κ b m x := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hF x h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      exact hbL k (Finset.mem_range.1 hk)
  have hbF₁ : ∀ k, k < m → b k ∈ F₁ := fun k hk =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk))
  have hD : ↑F₁ ⊆ DD κ b m := by
    intro x hx
    rcases hF₁ x hx with h | ⟨k, hk, hs, hT⟩
    · exact Iio_sub_DD m h
    · exact DD_mono (show k + 1 ≤ m by omega)
        (Or.inr ⟨hs, hT.1, hT.2.trans ((Iio_sub_DD k).trans (ClS.sub _))⟩)
  have hmono : StrictMonoOn (trPsi b c m) ↑F₁ := fun x hx y hy hxy =>
    trPsi_mono hb hc (hF₁ x hx) (hF₁ y hy) hxy
  have Q := concl_of hb hc hD hbF₁ (Ψ := trPsi b c m) (fun x _ hx => trPsi_lt hb hx)
    (fun k hk x hx hs => by
      rcases trPsi_low hb hc (hF₁ x hx) with ⟨hxk, -⟩ | ⟨j, hj, hjs, -, -, hjs', -⟩
      · exact absurd (hxk.trans ((hb.bot k hk).trans_le hs.1)) (lt_irrefl _)
      · rwa [← InSeg.unique hb hj hk hjs hs])
    (fun k hk => by
      rw [trPsi_seg hb hk (InSeg.self (hb.ups k hk).2)]
      exact trMv_base (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2)
    hmono (fun x hx y hy z hz => trPsi_add hb hc (hF₁ x hx) (hF₁ y hy) (hF₁ z hz))
    (fun k hk x hx y hy hxs hys hbx => by
      have hxL : x ∈ TrLowT (b k) κ := (trLowPt_seg hb hk (hF₁ x hx) hxs.1 le_rfl hxs).2
      have hyL : y ∈ TrLowT (b k) κ := (trLowPt_seg hb hk (hF₁ y hy) hys.1 le_rfl hys).2
      rw [trPsi_seg hb hk hxs, trPsi_seg hb hk hys]
      exact trMv_le1 (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
        (hb.bot k hk) (hc.bot k hk) hxL hyL hbx)
    (fun k hk x hx hxs hbx hE => by
      have hxL : x ∈ TrLowT (b k) κ := (trLowPt_seg hb hk (hF₁ x hx) hxs.1 le_rfl hxs).2
      rw [trPsi_seg hb hk hxs]
      exact (trMv_E (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
        (hb.bot k hk) (hc.bot k hk) hxL hbx).1 hE)
  obtain ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7⟩ := Q
  have Q8 : ∀ x ∈ F₁, Indec x → Indec (trPsi b c m x) := by
    intro x hx hI
    rcases trPsi_low hb hc (hF₁ x hx) with ⟨-, ex⟩ | ⟨k, hk, -, hxL, ex, -, -⟩
    · rw [ex]; exact hI
    · rw [ex]
      exact trMv_indec (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2
        (hb.bot k hk) (hc.bot k hk) hxL hI
  have hsub : F ⊆ F₁ := Finset.subset_union_left
  have hsub' : (↑F : Set Ordinal.{0}) ⊆ ↑F₁ := Finset.coe_subset.2 hsub
  refine ⟨trPsi b c m, ⟨⟨fun x hx => Q1 x (hsub hx), fun k hk x hx => Q2 k hk x (hsub hx),
    fun k hk _ => Q3 k hk (hbF₁ k hk), ⟨(Q4.2.1.mono hsub').injOn.bijOn_image,
      Q4.2.1.mono hsub', fun x hx y hy z hz => Q4.2.2 x (hsub hx) y (hsub hy) z (hsub hz)⟩,
    fun x hx y hy => Q5 x (hsub hx) y (hsub hy), fun x hx => Q6 x (hsub hx),
    fun x hx => Q7 x (hsub hx)⟩, fun x hx hI => Q8 x (hsub hx) hI⟩,
    fun k hk x _ hs => trPsi_seg hb hk hs⟩

end Frag

/-- **The carry through an intermediate chain**: for low-parameter points of `seg(b_k)` the composite of the
segment moves `b_k → c_k → d_k` is the single move `b_k → d_k`, and the composite lands in `seg(d_k)`. -/
theorem trFragLow_comp {κ : Ordinal.{0}} {b c d : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    (hc : Chain κ c m) (hd : Chain κ d m) {k : ℕ} (hk : k < m) {x : Ordinal.{0}} (hs : InSeg (b k) x)
    (hT : x ∈ TB (b k) κ) :
    mv (c k) (d k) (mv (b k) (c k) x) = mv (b k) (d k) x ∧ InSeg (d k) (mv (b k) (d k) x) := by
  have hL := trLowT_of_seg hs hT
  exact ⟨trMv_comp (hb.ups k hk).1 (hb.ups k hk).2 (hc.ups k hk).1 (hc.ups k hk).2 (hd.ups k hk).1
      (hd.ups k hk).2 (hb.bot k hk) (hc.bot k hk) (hd.bot k hk) hL,
    trMv_inSeg (hb.ups k hk).1 (hb.ups k hk).2 (hd.ups k hk).1 (hd.ups k hk).2 (hb.bot k hk) (hd.bot k hk)
      hL hs⟩

end Googology.Trans.PoR.InaccPsi.R2.Tr
