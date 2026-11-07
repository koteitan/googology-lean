import Googology.Trans.PoR.InaccPsi.R2.ZfShift
import Googology.Trans.PoR.InaccPsi.R2.XoSub

/-!
# The level image on one-segment levels (a3, first part): `ZfImgCl` there is a theorem

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

A level term `L` of the shape `Xo.XoPi` (moving leaves `lo c` of the lowest segment, fixed constants, `+`, `φ` in
normal form above `Ω₁`) has `img L = π(val L)` (`Xo.xoImg_pi`).  Here also `π(Ω₁·val L) = Ω₁·img L` (`zf_pi_mul_pi`:
`Gl.gl_pi_mul` at the countable leaves, `Xe.xe_pi_fix_th` at the constants, `R2.pi_add` at sums, and `Ω₁·x = x` at the
`ε`-numbers `x > Ω₁`), and at a node of the configuration `D = π` on the leaves of `Ω₁·val L` (they lie in `T^{υ_λ}`,
so below `υ_{λ+1}`, where the shift is `π`, or below `γ`, where both are the identity), so `yvSub D (Ω₁·val L) =
yvSub π (Ω₁·val L) = π(Ω₁·val L) = Ω₁·img L` (`zf_img_pi`).  So the level image is needed only at the other levels:
`ZfImgP S` (the shift with `ZfImgHi`, the clause at levels that are not one-segment terms) implies `ZfImg S`
(`zfImg_of_P`), hence `Yq.XoShift2 S` (`zfShift2_P`).

* `zf_yv_and` (`YvLv P ∧ YvLv Q ⇒ YvLv (P ∧ Q)`), `zf_Om1_mul_eps`, `zf_pi_mul_pi`, `zf_img_pi`;
* `ZfImgHi`, `ZfImgP` (statements), `zfImg_of_P`, `zfShift2_P`.

No new axiom.  New definitions: `ZfImgHi`, `ZfImgP` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **`YvLv P z ∧ YvLv Q z ⇒ YvLv (P ∧ Q) z`** (the canonical decomposition of `z` is unique). -/
theorem zf_yv_and {P Q : Ordinal.{0} → Prop} {z : Ordinal.{0}} (hP : YvLv S P z) :
    YvLv S Q z → YvLv S (fun x => P x ∧ Q x) z := by
  induction hP with
  | low hz hL =>
    intro hQ
    cases hQ with
    | low _ hL' => exact YvLv.low hz (Vc.VcLv_and _ hL hL')
    | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
    | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | om hs hs' e => intro _; exact YvLv.om hs hs' e
  | cnf a b h1 h2 hB hE _ _ ih1 ih2 =>
    intro hQ
    cases hQ with
    | low hz _ => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ _ q1 q2 => exact YvLv.cnf a b h1 h2 hB hE (ih1 q1) (ih2 q2)
    | veb _ _ _ _ _ hE' => exact absurd hE' hE
    | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) hE
  | veb a b h1 h2 hB hE hS _ _ ih1 ih2 =>
    intro hQ
    cases hQ with
    | low hz _ => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd hE hE'
    | veb _ _ _ _ _ _ _ q1 q2 => exact YvLv.veb a b h1 h2 hB hE hS (ih1 q1) (ih2 q2)
    | atom _ _ _ _ _ hSC => exact absurd hSC hS
  | atom a b h1 h2 hB hSC _ _ ih1 ih2 =>
    intro hQ
    cases hQ with
    | low hz _ => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps hSC) hE'
    | veb _ _ _ _ _ _ hS => exact absurd hSC hS
    | atom _ _ h1' h2' _ _ q1 q2 =>
      have e := yv_lev_unique h1 h2 h1' h2'
      subst e
      exact YvLv.atom a b h1 h2 hB hSC (ih1 q1) (ih2 q2)

/-- **`Ω₁·x = x` for an `ε`-number `x > Ω₁`.** -/
theorem zf_Om1_mul_eps {x : Ordinal.{0}} (hE : InE x) (h1 : Om1 < x) : Om1 * x = x := by
  have hO : (ω : Ordinal.{0}) ^ Om1 = Om1 := Rj.rj_Om1_inE
  have hx : (ω : Ordinal.{0}) ^ x = x := hE
  have hadd : Om1 + x = x := Ordinal.add_of_omega0_opow_le (b := x) (by rw [hx]; exact h1) (by rw [hx])
  calc Om1 * x = ω ^ Om1 * ω ^ x := by rw [hO, hx]
    _ = ω ^ (Om1 + x) := (opow_add _ _ _).symm
    _ = x := by rw [hadd, hx]

/-- **`π(Ω₁·val L) = Ω₁·img L` on one-segment level terms** (`Xo.XoPi`, well formed). -/
theorem zf_pi_mul_pi {l β μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hB : Bases (upsilon μ) (upsilon l))
    (hs1 : upsilon (succ l) ≤ Om1) :
    ∀ L : XoE, XoPi S l μ L → XoWF S l β L →
      Om1 * xoVal S l L ∈ TB (upsilon l) (upsilon μ) ∧
        pi (upsilon μ) (upsilon l) (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L
  | .old (.lo c), h, hW => by
    have hc1 : c < Om1 := (show c < upsilon (succ l) from hW).trans_le hs1
    exact Gl.gl_pi_mul hB h hc1
  | .lc M, ⟨hM, q, hq, hqμ, hd⟩, _ => by
    obtain ⟨h1, h2⟩ := Xe.xe_pi_fix_th (S := S) hB hq hqμ (Xe.xe_mul_lt_th hM) (Xe.xe_Om1_mul_dat hq hd)
    exact ⟨h1, h2⟩
  | .add s t, ⟨hs, ht⟩, ⟨hWs, hWt⟩ => by
    obtain ⟨hs1', hs2⟩ := zf_pi_mul_pi f hB hs1 s hs hWs
    obtain ⟨ht1', ht2⟩ := zf_pi_mul_pi f hB hs1 t ht hWt
    obtain ⟨h1, h2⟩ := pi_add hB hs1' ht1'
    show Om1 * (xoVal S l s + xoVal S l t) ∈ TB (upsilon l) (upsilon μ) ∧
      pi (upsilon μ) (upsilon l) (Om1 * (xoVal S l s + xoVal S l t)) =
        Om1 * (xoImg S l μ f s + xoImg S l μ f t)
    rw [mul_add, mul_add]
    exact ⟨h1, by rw [h2, hs2, ht2]⟩
  | .phi a b, hP, _ => by
    have hP0 := hP
    obtain ⟨ha, hb, h1a, haz, hbz, hΩ, hθ⟩ := hP
    obtain ⟨hvT, hvp⟩ := xoImg_pi (S := S) f hB (.phi a b) hP0
    set v := veblen (xoVal S l a) (xoVal S l b) with hvdef
    have hvE : InE v := Lu.luP_E h1a (Lu.luP_veblen _ _)
    have hv : Om1 * v = v := zf_Om1_mul_eps hvE hΩ
    have himg : xoImg S l μ f (.phi a b) = pi (upsilon μ) (upsilon l) v := hvp.symm
    have hOT := pi_Om1 hB
    have hpv : Om1 < pi (upsilon μ) (upsilon l) v := by
      have := (pi_bijOn hB).2 hOT.1 hvT hΩ
      rwa [hOT.2] at this
    -- the image is an `ε`-number: `π` maps `1 ≤ val a` to `1 ≤ img a`
    obtain ⟨haT, hapi⟩ := xoImg_pi (S := S) f hB a ha
    obtain ⟨o1, o2⟩ := one_TB hB
    have h1img : 1 ≤ xoImg S l μ f a := by
      rcases h1a.lt_or_eq with hlt | heq
      · have := (pi_bijOn hB).2 o1 haT hlt
        rw [o2, hapi] at this; exact this.le
      · rw [← hapi, ← heq, o2]
    have hpE : InE (pi (upsilon μ) (upsilon l) v) := by
      rw [← himg]; exact Lu.luP_E h1img (Lu.luP_veblen _ _)
    show Om1 * v ∈ TB (upsilon l) (upsilon μ) ∧ pi (upsilon μ) (upsilon l) (Om1 * v) =
      Om1 * xoImg S l μ f (.phi a b)
    rw [hv, himg, zf_Om1_mul_eps hpE hpv]
    exact ⟨hvT, rfl⟩
  | .old (.sg _ _), h, _ => h.elim
  | .old (.ub _ _), h, _ => h.elim
  | .old (.tm _ _ _ _), h, _ => h.elim
  | .old (.add _ _), h, _ => h.elim
  | .th _ _ _, h, _ => h.elim
  | .om _, h, _ => h.elim
  | .coll _ _, h, _ => h.elim

/-- **The level image on one-segment levels**: if the shift is `π` on the lowest segment and the identity below `γ`
(`X` below `γ < υ_μ`), then at a one-segment level term whose leaves lie in `X ∪ Y ∪ γ`, `yvSub D (Ω₁·val L) =
Ω₁·img L`. -/
theorem zf_img_pi {l β μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl0 : 0 < l) (hB : Bases (upsilon μ) (upsilon l)) (hs1 : upsilon (succ l) ≤ Om1)
    (hpi : ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y) (hid : ∀ x, x < γ → D x = x)
    (hXγ : ∀ x ∈ X, x < γ) (hγμ : γ < upsilon μ) (L : XoE) (hP : XoPi S l μ L) (hW : XoWF S l β L)
    (hz : Om1 * xoVal S l L < ConjT.th S) (hL : YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L)) :
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
  obtain ⟨hT, hpe⟩ := zf_pi_mul_pi f hB hs1 L hP hW
  set z := Om1 * xoVal S l L with hzdef
  have hLT : YvLv S (· ∈ TB (upsilon l) (upsilon μ)) z := (yv_TB_iff hB hz).1 hT
  have hO : SC (Om1 : Ordinal.{0}) := by rw [Rj.rj_Om1]; exact SC_Om one_ne_zero
  have hL1 : YvLv S (· < Om1) z := (yv_dat_iff hO le_rfl hz).1 (Rj.rj_Om1 ▸ Vd.vdD_lt_Om1 hz)
  have hlU : UpsPt (upsilon l) := upsPt_upsilon hl0
  have hsU : UpsPt (upsilon (succ l)) := upsPt_upsilon (hl0.trans_le (Order.le_succ l))
  have hls : upsilon l < upsilon (succ l) := upsilon_normal.strictMono (Order.lt_succ l)
  have hl1 : upsilon l < Om1 := hls.trans_le hs1
  have hEq : YvLv S (fun p => pi (upsilon μ) (upsilon l) p = D p) z := by
    refine (zf_yv_and (zf_yv_and hL hLT) hL1).mono fun p hp => ?_
    obtain ⟨⟨hpXY, hpT⟩, hp1⟩ := hp
    have hlow : ∀ x, x < γ → pi (upsilon μ) (upsilon l) x = D x := fun x hx =>
      by rw [hid x hx, pi_lt hB (hx.trans hγμ)]
    rcases hpXY with hXY | hpγ
    · rcases Finset.mem_union.1 hXY with hx | hy
      · exact hlow p (hXγ p hx)
      · have hps : p < upsilon (succ l) := Za.za_lt_next (upsPt_inE hlU) hl1 hpT.1 hp1 hls hsU
        exact (hpi p hy hps).symm
    · exact hlow p hpγ
  obtain ⟨-, hR⟩ := yv_pi_th hB hz hLT
  rw [yvSub_eq (yvR_congr hEq hR), hpe]

/-- **The level image at the levels that are not one-segment terms** (statement). -/
def ZfImgHi (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L → ¬ XoPi S l μ L →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) → ¬ ZfNest S l L →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the moving-level clause and the level image at the levels that are not one-segment terms**
(statement): `Zf.ZfImg` with `ZfImgHi` in place of `Zf.ZfImgCl`. -/
def ZfImgP (S : InaccSeq.{0}) : Prop :=
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
      Za.ZaHiD S l μ γ f D X Y ∧ ZfImgHi S l β μ γ f D X Y

/-- **`ZfImgP S ⇒ ZfImg S`**: at one-segment levels the level image is `zf_img_pi`. -/
theorem zfImg_of_P (hP : ZfImgP S) : ZfImg S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hA, hZa, hHi⟩ := hP l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, hA, hZa, ?_⟩
  obtain ⟨-, hXγ, hγμ, hLs, -, -, ⟨hμl, hpi⟩, -, -, -, -, hid, -⟩ := hA
  intro h L e hW hF hR hp hM1 hL hN
  by_cases hPi : XoPi S l μ L
  · have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
    have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hLs.rng.1.1))
    have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
    have hβ1 : 1 ≤ β := Order.one_le_iff_ne_zero.2 (lt_of_le_of_lt zero_le hW.2.1).ne'
    have hs1 : upsilon (succ l) ≤ Om1 := by
      have : upsilon (succ l) ≤ upsilon (l + β) := by
        rw [Order.succ_eq_add_one]; exact upsilon_normal.monotone (add_le_add_right hβ1 l)
      exact this.trans (hνβ.trans nuC_le_Om1)
    obtain ⟨h0, hhβ, hWL, _, hη1, hξT, hξ2, hby, hys⟩ := hW
    have hτU : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 :=
      (hby.trans_lt hys).trans_le (upsilon_normal.monotone (Order.succ_le_of_lt
        ((add_lt_add_iff_left l).2 hhβ)) |>.trans (hνβ.trans nuC_le_Om1))
    have hθ := uzTBound (S := S) _ (upsPt_inE hτU) hτ1 _ hξT hξ2
    exact zf_img_pi hl0 hBμ hs1 hpi hid hXγ hγμ L hPi hWL (le_self_add.trans_lt hθ) hL
  · exact hHi h L e hW hF hR hp hM1 hPi hL hN

/-- **`ZfImgP S ⇒ Yq.XoShift2 S`.** -/
theorem zfShift2_P (hLN : ZfLevNode S) (hP : ZfImgP S) : XoShift2 S := zfShift2 hLN (zfImg_of_P hP)

end Googology.Trans.PoR.InaccPsi.R2.Zf
