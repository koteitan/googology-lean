import Googology.Trans.PoR.InaccPsi.R2.ZkCnf

/-!
# The level image at sums of pieces: one induction on the sum tree

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

A level term that is a **sum tree** (`ZkSS Pc`: pieces `Pc` joined by `add`) of countable pieces, each of which is
moved by one map `G` through its Cantor-normal-form exponents (`img P = zkCnf G (val P)`), with all exponents in a
set `A` on which `G` is strictly increasing: then

* `zk_ss_img`: the whole tree has `img L = zkCnf G (val L)` (the absorptions of the sum are kept, `Zk.zk_add`);
* `zk_ss_lev`: **the level image** `yvSub D (Ω₁·val L) = Ω₁·img L` for every `D` that agrees with `G` on the
  exponents of `val L` that satisfy the leaf predicate `P` (and `D 0 = G 0 = 0`), given `YvLv P (Ω₁·val L)`
  (`Zk.zk_yvSub_mul`, `Zk.zk_yvLv_mul`).

No new axiom.  New definition: `ZkSS` (an inductive predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xo

/-- **Sum trees** of pieces. -/
inductive ZkSS (Pc : XoE → Prop) : XoE → Prop
  | piece {L : XoE} : Pc L → ZkSS Pc L
  | add {s t : XoE} : ZkSS Pc s → ZkSS Pc t → ZkSS Pc (.add s t)

theorem zk_Om1_principal : IsPrincipal (· + ·) (Om1 : Ordinal.{0}) := by
  rw [← zk_Om1_opow]; exact isPrincipal_add_omega0_opow _

variable {S : InaccSeq.{0}}

/-- **The image of a sum tree is the exponent map of its value.** -/
theorem zk_ss_img {l μ : Ordinal.{0}} {f G : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}}
    (hG : StrictMonoOn G A) {Pc : XoE → Prop}
    (hPc : ∀ P, Pc P → xoVal S l P < Om1 ∧ ZkEx (· ∈ A) (xoVal S l P) ∧
      xoImg S l μ f P = zkCnf G (xoVal S l P)) :
    ∀ L, ZkSS Pc L → xoVal S l L < Om1 ∧ ZkEx (· ∈ A) (xoVal S l L) ∧
      xoImg S l μ f L = zkCnf G (xoVal S l L) := by
  intro L hL
  induction hL with
  | piece h => exact hPc _ h
  | add _ _ ihs iht =>
    obtain ⟨s1, s2, s3⟩ := ihs
    obtain ⟨t1, t2, t3⟩ := iht
    rename_i s t _ _
    obtain ⟨hA, hE⟩ := zk_add hG _ _ s2 t2
    show xoVal S l s + xoVal S l t < Om1 ∧ ZkEx (· ∈ A) (xoVal S l s + xoVal S l t) ∧
      xoImg S l μ f s + xoImg S l μ f t = zkCnf G (xoVal S l s + xoVal S l t)
    exact ⟨zk_Om1_principal s1 t1, hA, by rw [hE, s3, t3]⟩

/-- **The level image at a sum tree.** -/
theorem zk_ss_lev {l μ : Ordinal.{0}} {f G D : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}}
    {P : Ordinal.{0} → Prop} (hG : StrictMonoOn G A) {Pc : XoE → Prop}
    (hPc : ∀ P, Pc P → xoVal S l P < Om1 ∧ ZkEx (· ∈ A) (xoVal S l P) ∧
      xoImg S l μ f P = zkCnf G (xoVal S l P))
    (hG0 : G 0 = 0) (hD0 : D 0 = 0) (hDG : ∀ c, c ∈ A → P c → D c = G c)
    (L : XoE) (hL : ZkSS Pc L) (hLv : Yv.YvLv S P (Om1 * xoVal S l L)) :
    Yv.yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
  obtain ⟨h1, hA, hI⟩ := zk_ss_img hG hPc L hL
  have hE := zk_yvLv_mul h1 hLv
  have hEq : ZkEx (fun c => D c = G c) (xoVal S l L) := by
    refine zkEx_mono (fun c hc => ?_) _ (zkEx_and _ hA hE)
    rcases hc.2 with h0 | hP
    · rw [h0, hD0, hG0]
    · exact hDG c hc.1 hP
  rw [zk_yvSub_mul D hD0 h1, zkCnf_congr _ hEq, hI]

end Googology.Trans.PoR.InaccPsi.R2.Zk
