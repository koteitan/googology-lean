import Googology.Trans.PoR.InaccPsi.R2.ZkSum

/-!
# The level image at levels mixing leaves of several segments: sums of one-segment pieces

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Zf.zf_img_pi` / `Zf.zf_img_piG` give the level image `yvSub D (Ω₁·val L) = Ω₁·img L` at levels whose leaves are
moved by ONE base change.  Here the levels that are **sums of countable one-segment pieces at different segments**
(`ZkSS (zkPc …)`: every piece is `Zf.XoPiG` at a segment `g` of the configuration — `g = 0` or `υ_{λ+g} ∈ Y` — with
its value in `T^{υ_{λ+g}}[υ_μ] ∩ Ω₁`), e.g. `old (sg h b) + old (lo a)` with `a ∈ seg(υ_λ)`, `b ∈ seg(υ_{λ+h})`.

The proof is ONE induction on the sum tree (`Zk.zk_ss_lev`) with the map

  `G(p) = p` for `p < υ_μ`,  `G(p) = π_{υ_{μ+f g}, υ_{λ+g}}(p)` on `seg(υ_{λ+g}) ∩ T^{υ_{λ+g}}[υ_μ]`

(`zkG`); its invariant is the segment structure of the Cantor-normal-form exponents: every exponent of a piece value
lies below `υ_μ` or in the segment of the piece with parameters below `υ_μ` (`zkDom`), `G` is strictly increasing
there (`zk_G_mono`: the images of `seg(υ_{λ+g})` lie in `[υ_{μ+f g}, υ_{μ+f g+1})`, and `f` is increasing on the
offsets), so the absorptions of the sum are kept; and on the leaves of `Ω₁·val L` (the nonzero exponents) the
realizer `D` equals `G` (`zk_DG`, from the segment clause of the shift).

* `zkSegIx`, `zkG`, `ZkOK`, `zkDom`, `zkPc` (definitions), `ZkSegH` (the segment facts of a shift, a structure);
* `zk_seg`, `zk_G_mono`, `zk_pc_cnf`, `zk_DG`, `zk_lev_seg` (**the level image at every sum of one-segment
  pieces**).

No new axiom.  New definitions: `zkSegIx`, `zkG` (functions), `ZkOK`, `zkDom`, `zkPc` (predicates), `ZkSegH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xo

/-- The segment index of a point `p ≥ υ_λ`: the `g` with `υ_{λ+g} ≤ p < υ_{λ+g+1}`. -/
noncomputable def zkSegIx (l p : Ordinal.{0}) : Ordinal.{0} :=
  Classical.epsilon (fun g => upsilon (l + g) ≤ p ∧ p < upsilon (succ (l + g)))

theorem zkSegIx_eq {l p g : Ordinal.{0}} (h1 : upsilon (l + g) ≤ p) (h2 : p < upsilon (succ (l + g))) :
    zkSegIx l p = g := by
  have hs := Classical.epsilon_spec (p := fun g => upsilon (l + g) ≤ p ∧ p < upsilon (succ (l + g))) ⟨g, h1, h2⟩
  exact Zf.zf_seg_unique hs.1 hs.2 h1 h2

/-- **The segment map**: identity below `υ_μ`, the segment base change `mv(υ_{λ+g}, υ_{μ+f g})` above. -/
noncomputable def zkG (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (p : Ordinal.{0}) : Ordinal.{0} :=
  if p < upsilon μ then p else mv (upsilon (l + zkSegIx l p)) (upsilon (μ + f (zkSegIx l p))) p

/-- The admissible segments: `0` and the offsets `g > 0` with `υ_{λ+g}` in the configuration. -/
def ZkOK (Y : Finset Ordinal.{0}) (l g : Ordinal.{0}) : Prop := g = 0 ∨ (0 < g ∧ upsilon (l + g) ∈ Y)

/-- **The domain**: below `υ_μ`, or in an admissible segment with parameters below `υ_μ`. -/
def zkDom (l μ : Ordinal.{0}) (Y : Finset Ordinal.{0}) : Set Ordinal.{0} :=
  {p | p < upsilon μ ∨ ∃ g, ZkOK Y l g ∧ p ∈ TB (upsilon (l + g)) (upsilon μ) ∧ upsilon (l + g) ≤ p ∧ p < Om1}

/-- **A one-segment piece**: countable, `Zf.XoPiG` at an admissible segment, value with parameters below `υ_μ`. -/
def zkPc (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (Y : Finset Ordinal.{0}) (L : XoE) :
    Prop :=
  xoVal S l L < Om1 ∧ ∃ g, ZkOK Y l g ∧ Zf.XoPiG S l μ (upsilon (μ + f g)) (upsilon (l + g)) f L ∧
    xoVal S l L ∈ TB (upsilon (l + g)) (upsilon μ)

/-- **The segment facts of a shift.** -/
structure ZkSegH (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (Y : Finset Ordinal.{0}) : Prop where
  l0 : 0 < l
  μ0 : 0 < μ
  μl : upsilon μ < upsilon l
  f0 : f 0 = 0
  bases : ∀ g, ZkOK Y l g → upsilon (μ + f g) < upsilon (l + g) ∧ upsilon (l + g) < Om1
  fmono : ∀ g g', ZkOK Y l g → ZkOK Y l g' → g < g' → f g < f g'

variable {S : InaccSeq.{0}}

theorem ZkSegH.basesB {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) {g : Ordinal.{0}} (hg : ZkOK Y l g) :
    Bases (upsilon (μ + f g)) (upsilon (l + g)) :=
  ⟨upsPt_inE (upsPt_upsilon (H.μ0.trans_le le_self_add)), upsPt_inE (upsPt_upsilon (H.l0.trans_le le_self_add)),
    (H.bases g hg).1, (H.bases g hg).2⟩

theorem ZkSegH.basesμ {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) {g : Ordinal.{0}} (hg : ZkOK Y l g) : Bases (upsilon μ) (upsilon (l + g)) :=
  ⟨upsPt_inE (upsPt_upsilon H.μ0), upsPt_inE (upsPt_upsilon (H.l0.trans_le le_self_add)),
    H.μl.trans_le (upsilon_normal.monotone le_self_add), (H.bases g hg).2⟩

/-- **A point of an admissible segment**: `G` is the segment base change there, with image in
`[υ_{μ+f g}, υ_{μ+f g+1})`. -/
theorem zk_seg {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}} (H : ZkSegH l μ f Y)
    {g p : Ordinal.{0}} (hg : ZkOK Y l g) (hp : p ∈ TB (upsilon (l + g)) (upsilon μ))
    (hτp : upsilon (l + g) ≤ p) (hp1 : p < Om1) :
    p < upsilon (succ (l + g)) ∧ ¬ p < upsilon μ ∧
      zkG l μ f p = pi (upsilon (μ + f g)) (upsilon (l + g)) p ∧
      zkG l μ f p = mv (upsilon (l + g)) (upsilon (μ + f g)) p ∧
      upsilon (μ + f g) ≤ zkG l μ f p ∧ zkG l μ f p < upsilon (succ (μ + f g)) := by
  have hB := H.basesB hg
  have hm := upsilon_normal.strictMono
  set τ := upsilon (l + g) with hτdef
  set σ := upsilon (μ + f g) with hσdef
  have hμσ : upsilon μ ≤ σ := upsilon_normal.monotone le_self_add
  have hpT : p ∈ TB τ σ := ⟨hp.1, hp.2.trans (Set.Iio_subset_Iio hμσ)⟩
  have hτU : UpsPt τ := upsPt_upsilon (H.l0.trans_le le_self_add)
  have hps : p < upsilon (succ (l + g)) :=
    Za.za_lt_next hB.2.1 hB.2.2.2 hp.1 hp1 (hm (Order.lt_succ _))
      (upsPt_upsilon (H.l0.trans_le (le_self_add.trans (Order.le_succ _))))
  have hnl : ¬ p < upsilon μ := fun h =>
    absurd ((H.μl.trans_le (upsilon_normal.monotone le_self_add)).trans_le hτp) (not_lt.2 h.le)
  have hGp : zkG l μ f p = mv τ σ p := by
    unfold zkG; rw [if_neg hnl, zkSegIx_eq hτp hps]
  have hmv : mv τ σ p = pi σ τ p := by
    show (if σ < τ then pi σ τ else if τ < σ then up τ σ else id) p = pi σ τ p
    rw [if_pos hB.2.2.1]
  obtain ⟨hτT, hπτ⟩ := pi_base hB
  have hlo : σ ≤ pi σ τ p := by
    rcases hτp.lt_or_eq with h | h
    · have := (pi_bijOn hB).2 hτT hpT h
      rw [hπτ] at this; exact this.le
    · rw [← h, hπτ]
  have hπT : pi σ τ p ∈ Tset σ := (pi_bijOn hB).1.mapsTo hpT
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  have hπ1 : pi σ τ p < Om1 := by
    have := (pi_bijOn hB).2 hpT hOT hp1
    rwa [hpO] at this
  have hhi : pi σ τ p < upsilon (succ (μ + f g)) :=
    Za.za_lt_next hB.1 (hB.2.2.1.trans hB.2.2.2) hπT hπ1 (hm (Order.lt_succ _))
      (upsPt_upsilon (H.μ0.trans_le (le_self_add.trans (Order.le_succ _))))
  refine ⟨hps, hnl, hGp.trans hmv, hGp, ?_, ?_⟩
  · rw [hGp, hmv]; exact hlo
  · rw [hGp, hmv]; exact hhi

/-- **`G` is strictly increasing on the domain.** -/
theorem zk_G_mono {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) : StrictMonoOn (zkG l μ f) (zkDom l μ Y) := by
  have hm := upsilon_normal.strictMono
  intro p hp q hq hpq
  rcases hp with hp | ⟨g, hg, hpT, hτp, hp1⟩
  · have hGp : zkG l μ f p = p := by unfold zkG; rw [if_pos hp]
    rw [hGp]
    rcases hq with hq | ⟨g', hg', hqT, hτq, hq1⟩
    · have hGq : zkG l μ f q = q := by unfold zkG; rw [if_pos hq]
      rw [hGq]; exact hpq
    · obtain ⟨-, -, -, -, hlo, -⟩ := zk_seg H hg' hqT hτq hq1
      exact hp.trans_le ((upsilon_normal.monotone le_self_add).trans hlo)
  · obtain ⟨hps, hpn, hGp, -, -, hphi⟩ := zk_seg H hg hpT hτp hp1
    have hlp : upsilon μ ≤ p := not_lt.1 hpn
    rcases hq with hq | ⟨g', hg', hqT, hτq, hq1⟩
    · exact absurd (hlp.trans_lt (hpq.trans hq)) (lt_irrefl _)
    · obtain ⟨hqs, -, hGq, -, hqlo, -⟩ := zk_seg H hg' hqT hτq hq1
      rcases lt_trichotomy g g' with hgg | rfl | hgg
      · have hf := H.fmono g g' hg hg' hgg
        have h1 : upsilon (succ (μ + f g)) ≤ upsilon (μ + f g') :=
          upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left μ).2 hf))
        exact hphi.trans_le (h1.trans hqlo)
      · rw [hGp, hGq]
        have hB := H.basesB hg
        have hμσ : upsilon μ ≤ upsilon (μ + f g) := upsilon_normal.monotone le_self_add
        exact (pi_bijOn hB).2 ⟨hpT.1, hpT.2.trans (Set.Iio_subset_Iio hμσ)⟩
          ⟨hqT.1, hqT.2.trans (Set.Iio_subset_Iio hμσ)⟩ hpq
      · have h1 : upsilon (succ (l + g')) ≤ upsilon (l + g) :=
          upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hgg))
        exact absurd ((hqs.trans_le h1).trans_le hτp) (not_lt.2 hpq.le)

/-- **A piece is moved by `G` through its exponents.** -/
theorem zk_pc_cnf {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) (P : XoE) (hP : zkPc S l μ f Y P) :
    xoVal S l P < Om1 ∧ ZkEx (· ∈ zkDom l μ Y) (xoVal S l P) ∧
      xoImg S l μ f P = zkCnf (zkG l μ f) (xoVal S l P) := by
  obtain ⟨h1, g, hg, hPG, hTμ⟩ := hP
  have hB := H.basesB hg
  have hBμ := H.basesμ hg
  obtain ⟨hvT, hpv⟩ := Zf.zf_imgG f hB P hPG
  obtain ⟨hcnf, -⟩ := zk_pi_cnf (S := S) hB hvT h1
  obtain ⟨-, hEμ⟩ := zk_pi_cnf (S := S) hBμ hTμ h1
  have hElt : ZkEx (· < Om1) (xoVal S l P) := zkEx_lt _ Om1 (by rw [zk_Om1_opow]; exact h1)
  have hE := zkEx_and _ hEμ hElt
  have hμσ : upsilon μ ≤ upsilon (μ + f g) := upsilon_normal.monotone le_self_add
  refine ⟨h1, zkEx_mono (fun c hc => ?_) _ hE, ?_⟩
  · by_cases hcτ : c < upsilon (l + g)
    · exact Or.inl ((TB_inter_lt hBμ hcτ).1 hc.1)
    · exact Or.inr ⟨g, hg, hc.1, not_lt.1 hcτ, hc.2⟩
  · have hEq : ZkEx (fun c => zkG l μ f c = pi (upsilon (μ + f g)) (upsilon (l + g)) c) (xoVal S l P) := by
      refine zkEx_mono (fun c hc => ?_) _ hE
      by_cases hcτ : c < upsilon (l + g)
      · have hcμ : c < upsilon μ := (TB_inter_lt hBμ hcτ).1 hc.1
        have hGc : zkG l μ f c = c := by unfold zkG; rw [if_pos hcμ]
        rw [hGc, pi_lt hB (hcμ.trans_le hμσ)]
      · exact (zk_seg H hg hc.1 (not_lt.1 hcτ) hc.2).2.2.1
    rw [← hpv, hcnf, zkCnf_congr _ hEq]

/-- **The realizer equals `G` on the leaves in the domain** (from the segment clause of the shift). -/
theorem zk_DG {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) (hXγ : ∀ x ∈ X, x < γ) (hγμ : γ < upsilon μ) (hid : ∀ x, x < γ → D x = x)
    (hYl : ∀ y ∈ Y, upsilon l ≤ y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y) :
    ∀ c, c ∈ zkDom l μ Y → (c ∈ X ∪ Y ∨ c < γ) → D c = zkG l μ f c := by
  intro c hc hP
  have hlow : c < γ → D c = zkG l μ f c := fun h => by
    have hGc : zkG l μ f c = c := by unfold zkG; rw [if_pos (h.trans hγμ)]
    rw [hGc, hid c h]
  rcases hP with hXY | hcγ
  · rcases Finset.mem_union.1 hXY with hx | hy
    · exact hlow (hXγ c hx)
    · have hlc := hYl c hy
      rcases hc with hc | ⟨g, hg, hcT, hτc, hc1⟩
      · exact absurd (hlc.trans_lt (hc.trans H.μl)) (lt_irrefl _)
      · obtain ⟨hcs, -, -, hGmv, -, -⟩ := zk_seg H hg hcT hτc hc1
        rw [hGmv]
        exact hmv c hy g hτc hcs fun p hp => (hcT.2 (Finset.mem_coe.2 hp)).trans H.μl
  · exact hlow hcγ

/-- **The level image at every sum of one-segment pieces.** -/
theorem zk_lev_seg {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) (hXγ : ∀ x ∈ X, x < γ) (hγμ : γ < upsilon μ) (hid : ∀ x, x < γ → D x = x)
    (hγ0 : 0 < γ) (hYl : ∀ y ∈ Y, upsilon l ≤ y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (L : XoE) (hL : ZkSS (zkPc S l μ f Y) L)
    (hLv : Yv.YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L)) :
    Yv.yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
  have hG0 : zkG l μ f 0 = 0 := by
    unfold zkG; rw [if_pos (hγ0.trans hγμ)]
  exact zk_ss_lev (zk_G_mono H) (zk_pc_cnf H) hG0 (hid 0 hγ0) (zk_DG H hXγ hγμ hid hYl hmv) L hL hLv

end Googology.Trans.PoR.InaccPsi.R2.Zk
