import Googology.Trans.PoR.InaccPsi.R2.XoTest
import Googology.Trans.PoR.InaccPsi.R2.XeFix

/-!
# The leaf substitution on levels agrees with the base change on one segment

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

For a level term whose moving leaves all lie in the segment `[0, υ_{λ+1})` of the base `υ_λ` (old leaves `lo c`, `c
∈ T^{υ_λ}[υ_μ]`), whose fixed constants have data below a strongly critical `q ≤ υ_μ` (they lie below `θ`), built by
`+` and by `φ` in normal form (the range of `R2.vdPhi_TB`), the image `xoImg` of the term is `π_{υ_μ,υ_λ}` of its value
(`xoImg_pi`).  So on such levels the leaf substitution is the base change of [W07a] Def 5.1: the image does not
depend on the term chosen for the level.

* `XoPi` (the shape), `xoImg_pi` (**`val ∈ T^{υ_λ}[υ_μ]` and `π(val) = img`**, from `R2.pi_add`, `R2.vdPhi_TB`,
  `Xe.xe_pi_fix_th`), `xoXj_lev_pi` (**at the witness: `π(B₂ + λ) = B₂ + υ_μ`**, the image level of `X′`).

No new axiom.  New definition: `XoPi` (a predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **One-segment level terms**: leaves `lo c` with `c ∈ T^{υ_λ}[υ_μ]`, fixed constants below `θ` with data below a
strongly critical `q ≤ υ_μ`, `+`, and `φ(a, b)` in normal form (`1 ≤ a`, `a, b < φ(a, b)`, `Ω₁ < φ(a, b) < θ`). -/
def XoPi (S : InaccSeq.{0}) (l μ : Ordinal.{0}) : XoE → Prop
  | .old (.lo c) => c ∈ TB (upsilon l) (upsilon μ)
  | .lc M => M < ConjT.th S ∧ ∃ q, SC q ∧ q ≤ upsilon μ ∧ Vd.vdD S 0 M < q
  | .add s t => XoPi S l μ s ∧ XoPi S l μ t
  | .phi a b => XoPi S l μ a ∧ XoPi S l μ b ∧ 1 ≤ xoVal S l a ∧
      xoVal S l a < veblen (xoVal S l a) (xoVal S l b) ∧ xoVal S l b < veblen (xoVal S l a) (xoVal S l b) ∧
      Om1 < veblen (xoVal S l a) (xoVal S l b) ∧ veblen (xoVal S l a) (xoVal S l b) < ConjT.th S
  | _ => False

variable {S : InaccSeq.{0}}

/-- **The leaf substitution is the base change on one-segment level terms.** -/
theorem xoImg_pi {l μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hB : Bases (upsilon μ) (upsilon l)) :
    ∀ L : XoE, XoPi S l μ L →
      xoVal S l L ∈ TB (upsilon l) (upsilon μ) ∧ pi (upsilon μ) (upsilon l) (xoVal S l L) = xoImg S l μ f L
  | .old (.lo c), h => ⟨h, rfl⟩
  | .lc M, ⟨hM, q, hq, hqμ, hd⟩ => by
    obtain ⟨h1, h2⟩ := Xe.xe_pi_fix_th (S := S) hB hq hqμ hM hd
    exact ⟨h1, h2⟩
  | .add s t, ⟨hs, ht⟩ => by
    obtain ⟨hs1, hs2⟩ := xoImg_pi f hB s hs
    obtain ⟨ht1, ht2⟩ := xoImg_pi f hB t ht
    obtain ⟨h1, h2⟩ := pi_add hB hs1 ht1
    refine ⟨h1, ?_⟩
    show pi (upsilon μ) (upsilon l) (xoVal S l s + xoVal S l t) = xoImg S l μ f s + xoImg S l μ f t
    rw [h2, hs2, ht2]
  | .phi a b, ⟨ha, hb, h1a, haz, hbz, hΩ, hθ⟩ => by
    obtain ⟨ha1, ha2⟩ := xoImg_pi f hB a ha
    obtain ⟨hb1, hb2⟩ := xoImg_pi f hB b hb
    obtain ⟨hm, hp⟩ := vdPhi_TB hB h1a haz hbz hΩ (Or.inr ⟨S, hθ⟩)
    refine ⟨hm.2 ⟨ha1, hb1⟩, ?_⟩
    show pi (upsilon μ) (upsilon l) (veblen (xoVal S l a) (xoVal S l b)) =
      veblen (xoImg S l μ f a) (xoImg S l μ f b)
    rw [hp ha1 hb1, ha2, hb2]
  | .old (.sg _ _), h => h.elim
  | .old (.ub _ _), h => h.elim
  | .old (.tm _ _ _ _), h => h.elim
  | .old (.add _ _), h => h.elim
  | .th _ _ _, h => h.elim
  | .om _, h => h.elim
  | .coll _ _, h => h.elim

/-- **The image level of the witness is `π(B₂ + λ) = B₂ + υ_μ`.** -/
theorem xoXj_lev_pi (k : ℕ) {μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hμ0 : 0 < μ)
    (hμl : upsilon μ < upsilon (Nc.ncL S (k : Ordinal.{0}))) :
    pi (upsilon μ) (upsilon (Nc.ncL S (k : Ordinal.{0}))) (Uc.ucB + Nc.ncL S (k : Ordinal.{0})) =
      Uc.ucB + upsilon μ := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlO : upsilon l < Om1 := by rw [hlfix]; exact hlu1.trans hu1O
  have hB : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hlO⟩
  have hlT : l ∈ TB (upsilon l) (upsilon μ) :=
    (congrArg (· ∈ TB (upsilon l) (upsilon μ)) hlfix).mp (pi_base hB).1
  have hP : XoPi S l μ (.add (.lc Uc.ucB) (.old (.lo l))) :=
    ⟨⟨Vd.vd_B_lt_th, gamma 0, Lq.lq_gamma_SC 0, Gq.gq_gam_le_ups S (upsPt_upsilon hμ0),
      Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)⟩, hlT⟩
  have h := (xoImg_pi (S := S) f hB _ hP).2
  have hpi : pi (upsilon μ) (upsilon l) l = upsilon μ := by
    have h' := (pi_base hB).2
    rwa [hlfix] at h' ⊢
  have h2 : xoImg S l μ f (.add (.lc Uc.ucB) (.old (.lo l))) = Uc.ucB + upsilon μ := by
    show Uc.ucB + pi (upsilon μ) (upsilon l) l = _
    rw [hpi]
  exact h.trans h2

end Googology.Trans.PoR.InaccPsi.R2.Xo
