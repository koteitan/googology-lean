import Googology.Trans.PoR.InaccPsi.R2.ZkSeg

/-!
# `Zf.ZfImgP2` from the level image off the segment sums

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Zf.ZfImgP2 S` (the skeleton leaf `skLevImgHi2`) asks the level image `yvSub D (Ω₁·val L) = Ω₁·img L` at the node
levels that are one-segment terms at no segment.  `Zk.zk_lev_seg` proves it at every **sum of countable one-segment
pieces** (`Zk.ZkSS (Zk.zkPc …)`), i.e. at the levels mixing leaves of several segments by `+`.  So the statement is
needed only at the other levels (`ZkImgHi3`, `ZkImgP3`):

* `ZkImgHi3`, `ZkImgP3` (statements: `Zf.ZfImgHi2`, `Zf.ZfImgP2` with the extra hypothesis `¬ ZkSS (zkPc …) L`);
* `zkSegH_of` (the segment facts `Zk.ZkSegH` from the clauses of the shift and `Sl.SlOff`);
* `zkImgP2_of_P3` (**`ZkImgP3 S ⇒ Zf.ZfImgP2 S`**; the realizer is asked with `Q ∧ Sl.SlOff`, which the supply
  gives), `zkImgP3_of_P2` (the converse: the two statements are equivalent), `zkShift2_P3` (`⇒ Yq.XoShift2 S`);
* `zk_wit2` (**non-vacuity of the fragment**: `old (sg h υ_{λ+h}) + old (lo υ_λ)` is a segment sum, one-segment at
  no segment, so it is a genuine instance of `Zf.ZfImgHi2` now proved).

No new axiom.  New definitions: `ZkImgHi3`, `ZkImgP3` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The level image off the segment sums** (statement): `Zf.ZfImgHi2` at the levels that are no sum of countable
one-segment pieces. -/
def ZkImgHi3 (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L → ¬ XoPi S l μ L →
    (∀ h', 0 < h' → upsilon (l + h') ∈ Y → ¬ Zf.XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L) →
    ¬ ZkSS (zkPc S l μ f Y) L →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) → ¬ Zf.ZfNest S l L →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the level image off the segment sums** (statement): `Zf.ZfImgP2` with `ZkImgHi3`. -/
def ZkImgP3 (S : InaccSeq.{0}) : Prop :=
  ∀ (l β : Ordinal.{0})
    (Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop),
    IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    (∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os) →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) →
    ∀ (X Y : Finset Ordinal.{0}), (∀ x ∈ X, x < upsilon l) → (∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) →
    ∃ D μ f B γ Os, (Q μ f B γ Os ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ Ls.LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + B)) ∧
      (upsilon μ < upsilon l ∧ ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
        (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : Ub.UbT, Ub.UbT.IsA t →
        Ub.UbT.WF (upsilon (l + g)) t → Ub.UbT.Lv (· ∈ X ∪ Y) t → Ub.UbT.ev (upsilon (l + g)) t = y →
        D y = Ub.UbT.ev (upsilon (μ + f g)) (t.map D) ∧ Ub.UbT.WF (upsilon (μ + f g)) (t.map D)) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t)) ∧
      VlLC (fun p => p ∈ X ∪ Y ∨ p < γ) D ∧ (∀ x, x < γ → D x = x) ∧ UpsPt γ) ∧
      Za.ZaHiD S l μ γ f D X Y ∧ ZkImgHi3 S l β μ γ f D X Y

/-- **The segment facts from the clauses of the shift.** -/
theorem zkSegH_of {l β μ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    {Os : Finset Ordinal.{0}} {B : Ordinal.{0}} (hl0 : 0 < l) (hl1 : upsilon l < Om1)
    (hb1 : upsilon (l + β) ≤ Om1) (hY : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β))
    (hLs : Ls.LsMapW S l X Y D μ) (hμl : upsilon μ < upsilon l)
    (hres : ∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g))
    (hSl : Sl.SlOff f Os B) : ZkSegH l μ f Y := by
  have hmem : ∀ g, ZkOK Y l g → g ∈ (↑(insert 0 Os) : Set Ordinal.{0}) := by
    intro g hg
    rcases hg with rfl | ⟨_, hgY⟩
    · exact Finset.mem_coe.2 (Finset.mem_insert_self 0 Os)
    · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hres g hgY).1)
  refine ⟨hl0, pos_iff_ne_zero.2 hLs.rng.1.1, hμl, hSl.zero, fun g hg => ?_, fun g g' hg hg' hlt =>
    hSl.mono (hmem g hg) (hmem g' hg') hlt⟩
  rcases hg with rfl | ⟨_, hgY⟩
  · rw [hSl.zero, add_zero, add_zero]; exact ⟨hμl, hl1⟩
  · have e := (hres g hgY).2
    refine ⟨?_, (hY _ hgY).2.trans_le hb1⟩
    rw [← e]; exact (hLs.below _ hgY).trans_le (hY _ hgY).1

/-- **`ZkImgP3 S ⇒ Zf.ZfImgP2 S`.** -/
theorem zkImgP2_of_P3 (hP : ZkImgP3 S) : Zf.ZfImgP2 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, ⟨⟨hQ, hSl⟩, hrest⟩, hZa, hHi⟩ :=
    hP l β (fun μ f B γ Os => Q μ f B γ Os ∧ Sl.SlOff f Os B) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8, h7⟩)
      hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, hrest⟩, hZa, ?_⟩
  obtain ⟨hXγ, hγμ, hLs, hres, -, ⟨hμl, -⟩, hmv, -, -, -, hid, hγU⟩ := hrest
  intro h L e hW hF hR hp hM1 hPi hG hLv hN
  by_cases hSS : ZkSS (zkPc S l μ f Y) L
  · have H : ZkSegH l μ f Y := zkSegH_of (pos_iff_ne_zero.2 hl.1) hl1 (hνβ.trans nuC_le_Om1) hY hLs hμl hres hSl
    have hγ0 : 0 < γ := omega0_pos.trans (omega0_lt_inE (upsPt_inE hγU))
    exact zk_lev_seg H hXγ hγμ hid hγ0 (fun y hy => (hY y hy).1) hmv L hSS hLv
  · exact hHi h L e hW hF hR hp hM1 hPi hG hSS hLv hN

/-- **The converse**: `Zf.ZfImgP2 S ⇒ ZkImgP3 S` (so the two statements are equivalent). -/
theorem zkImgP3_of_P2 (hP : Zf.ZfImgP2 S) : ZkImgP3 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hA, hZa, hHi⟩ := hP l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  exact ⟨D, μ, f, B, γ, Os, hA, hZa, fun h L e hW hF hR hp hM1 hPi hG _ hLv hN => hHi h L e hW hF hR hp hM1 hPi hG hLv hN⟩

/-- **`ZkImgP3 S ⇒ Yq.XoShift2 S`.** -/
theorem zkShift2_P3 (hLN : Zf.ZfLevNode S) (hP : ZkImgP3 S) : XoShift2 S := Zf.zfShift2_P2 hLN (zkImgP2_of_P3 hP)

/-- **Non-vacuity of the fragment**: the two-segment level `old (sg h υ_{λ+h}) + old (lo υ_λ)` (`h > 0`,
`υ_{λ+h} ∈ Y`) is a segment sum; it is not `Xo.XoPi`, and it is `Zf.XoPiG` at no segment `h'` with
`υ_{μ+f h'} < υ_λ`. -/
theorem zk_wit2 {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) {h : Ordinal.{0}} (h0 : 0 < h) (hτY : upsilon (l + h) ∈ Y) :
    ZkSS (zkPc S l μ f Y) (.add (.old (.sg h (upsilon (l + h)))) (.old (.lo (upsilon l)))) ∧
      ¬ XoPi S l μ (.add (.old (.sg h (upsilon (l + h)))) (.old (.lo (upsilon l)))) ∧
      ∀ h', 0 < h' → upsilon (μ + f h') < upsilon l → upsilon (l + h') < Om1 →
        ¬ Zf.XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f
          (.add (.old (.sg h (upsilon (l + h)))) (.old (.lo (upsilon l)))) := by
  have hgh : ZkOK Y l h := Or.inr ⟨h0, hτY⟩
  have hg0 : ZkOK Y l 0 := Or.inl rfl
  have hBh := H.basesB hgh
  have hBμh := H.basesμ hgh
  have hB0 := H.basesB hg0
  have hBμ0 := H.basesμ hg0
  rw [add_zero] at hBμ0
  refine ⟨ZkSS.add (ZkSS.piece ⟨hBh.2.2.2, h, hgh, ⟨(pi_base hBh).1, hBh.2.2.2, ?_⟩, (pi_base hBμh).1⟩)
    (ZkSS.piece ⟨hBμ0.2.2.2, 0, hg0, ?_, by rw [add_zero]; exact (pi_base hBμ0).1⟩), fun hP => hP.1, ?_⟩
  · show mv (upsilon (l + h)) (upsilon (μ + f h)) (upsilon (l + h)) =
      pi (upsilon (μ + f h)) (upsilon (l + h)) (upsilon (l + h))
    show (if upsilon (μ + f h) < upsilon (l + h) then pi (upsilon (μ + f h)) (upsilon (l + h))
      else if upsilon (l + h) < upsilon (μ + f h) then up (upsilon (l + h)) (upsilon (μ + f h)) else id)
        (upsilon (l + h)) = _
    rw [if_pos hBh.2.2.1]
  · show upsilon l ∈ TB (upsilon (l + 0)) (upsilon (μ + f 0)) ∧ upsilon l < Om1 ∧
      pi (upsilon μ) (upsilon l) (upsilon l) = pi (upsilon (μ + f 0)) (upsilon (l + 0)) (upsilon l)
    rw [H.f0, add_zero, add_zero]
    exact ⟨(pi_base hBμ0).1, hBμ0.2.2.2, rfl⟩
  · intro h' h'0 hσl hτ1 hPG
    have hlt : upsilon l < upsilon (l + h') :=
      upsilon_normal.strictMono ((lt_add_iff_pos_right l).2 h'0)
    have hB' : Bases (upsilon (μ + f h')) (upsilon (l + h')) :=
      ⟨upsPt_inE (upsPt_upsilon (H.μ0.trans_le le_self_add)), upsPt_inE (upsPt_upsilon (H.l0.trans_le le_self_add)),
        hσl.trans hlt, hτ1⟩
    have hT : upsilon l ∈ TB (upsilon (l + h')) (upsilon (μ + f h')) := hPG.2.1
    exact absurd ((TB_inter_lt hB' hlt).1 hT) (not_lt.2 hσl.le)

end Googology.Trans.PoR.InaccPsi.R2.Zk
