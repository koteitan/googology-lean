import Googology.Trans.PoR.InaccPsi.R2.ZfPi

/-!
# The level image on one-segment levels at every segment (a3, second part)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Zf.zf_img_pi` treats level terms whose moving leaves lie in the lowest segment.  Here the same for a level term all of
whose old leaves are moved by ONE base change `π' = π_{σ',τ'}` (`XoPiG`: old leaves with value in `T^{τ'}[σ'] ∩ Ω₁`
and image `π'` of the value; fixed constants with data below `σ'`; `+`; `φ` in normal form above `Ω₁`): `img L =
π'(val L)` (`zf_imgG`), `π'(Ω₁·val L) = Ω₁·img L` (`zf_pi_mulG`), and if `D = π'` on the leaves of `Ω₁·val L` then
`yvSub D (Ω₁·val L) = Ω₁·img L` (`zf_img_piG`).  At a segment `h ≥ 1` of the configuration (`τ' = υ_{λ+h} ∈ Y`,
`σ' = D τ' = υ_{μ+f h}`) the shift is `mv τ' σ' = π_{σ',τ'}` on the points with parameters below `υ_λ`, so the leaves
condition holds (`zf_seg_D`), and the level image at such levels is a theorem: `ZfImgP2 S` (the level image only at
levels that are one-segment terms at NO segment) implies `ZfImgP S` (`zfImgP_of_P2`), hence `Yq.XoShift2 S`.

* `XoPiG` (a predicate), `zf_imgG`, `zf_pi_mulG`, `zf_img_piG`, `zf_seg_D`;
* `ZfImgHi2`, `ZfImgP2` (statements), `zfImgP_of_P2`, `zfShift2_P2`.

No new axiom.  New definitions: `XoPiG` (a predicate), `ZfImgHi2`, `ZfImgP2` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **One-base level terms** for the base change `π_{σ,τ}`: old leaves with countable value in `Tᵗ[σ]` and image
`π` of the value, fixed constants below `θ` with data below a strongly critical `q ≤ σ`, `+`, `φ` in normal form. -/
def XoPiG (S : InaccSeq.{0}) (l μ σ τ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : XoE → Prop
  | .old E => Vr.vrVal l E ∈ TB τ σ ∧ Vr.vrVal l E < Om1 ∧ Vr.vrImg l μ f E = pi σ τ (Vr.vrVal l E)
  | .lc M => M < ConjT.th S ∧ ∃ q, SC q ∧ q ≤ σ ∧ Vd.vdD S 0 M < q
  | .add s t => XoPiG S l μ σ τ f s ∧ XoPiG S l μ σ τ f t
  | .phi a b => XoPiG S l μ σ τ f a ∧ XoPiG S l μ σ τ f b ∧ 1 ≤ xoVal S l a ∧
      xoVal S l a < veblen (xoVal S l a) (xoVal S l b) ∧ xoVal S l b < veblen (xoVal S l a) (xoVal S l b) ∧
      Om1 < veblen (xoVal S l a) (xoVal S l b) ∧ veblen (xoVal S l a) (xoVal S l b) < ConjT.th S
  | _ => False

/-- **`val ∈ Tᵗ[σ]` and `π(val) = img`** on one-base level terms. -/
theorem zf_imgG {l μ σ τ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hB : Bases σ τ) :
    ∀ L : XoE, XoPiG S l μ σ τ f L → xoVal S l L ∈ TB τ σ ∧ pi σ τ (xoVal S l L) = xoImg S l μ f L
  | .old E, h => ⟨h.1, h.2.2.symm⟩
  | .lc M, ⟨hM, q, hq, hqσ, hd⟩ => by
    obtain ⟨h1, h2⟩ := Xe.xe_pi_fix_th (S := S) hB hq hqσ hM hd
    exact ⟨h1, h2⟩
  | .add s t, ⟨hs, ht⟩ => by
    obtain ⟨hs1, hs2⟩ := zf_imgG f hB s hs
    obtain ⟨ht1, ht2⟩ := zf_imgG f hB t ht
    obtain ⟨h1, h2⟩ := pi_add hB hs1 ht1
    refine ⟨h1, ?_⟩
    show pi σ τ (xoVal S l s + xoVal S l t) = xoImg S l μ f s + xoImg S l μ f t
    rw [h2, hs2, ht2]
  | .phi a b, ⟨ha, hb, h1a, haz, hbz, hΩ, hθ⟩ => by
    obtain ⟨ha1, ha2⟩ := zf_imgG f hB a ha
    obtain ⟨hb1, hb2⟩ := zf_imgG f hB b hb
    obtain ⟨hm, hp⟩ := vdPhi_TB hB h1a haz hbz hΩ (Or.inr ⟨S, hθ⟩)
    refine ⟨hm.2 ⟨ha1, hb1⟩, ?_⟩
    show pi σ τ (veblen (xoVal S l a) (xoVal S l b)) = veblen (xoImg S l μ f a) (xoImg S l μ f b)
    rw [hp ha1 hb1, ha2, hb2]
  | .th _ _ _, h => h.elim
  | .om _, h => h.elim
  | .coll _ _, h => h.elim

/-- **`π(Ω₁·val) = Ω₁·img`** on one-base level terms. -/
theorem zf_pi_mulG {l μ σ τ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hB : Bases σ τ) :
    ∀ L : XoE, XoPiG S l μ σ τ f L →
      Om1 * xoVal S l L ∈ TB τ σ ∧ pi σ τ (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L
  | .old E, h => by
    obtain ⟨m1, m2⟩ := Gl.gl_pi_mul hB h.1 h.2.1
    refine ⟨m1, ?_⟩
    show pi σ τ (Om1 * Vr.vrVal l E) = Om1 * Vr.vrImg l μ f E
    rw [m2, h.2.2]
  | .lc M, ⟨hM, q, hq, hqσ, hd⟩ => by
    obtain ⟨h1, h2⟩ := Xe.xe_pi_fix_th (S := S) hB hq hqσ (Xe.xe_mul_lt_th hM) (Xe.xe_Om1_mul_dat hq hd)
    exact ⟨h1, h2⟩
  | .add s t, ⟨hs, ht⟩ => by
    obtain ⟨hs1, hs2⟩ := zf_pi_mulG f hB s hs
    obtain ⟨ht1, ht2⟩ := zf_pi_mulG f hB t ht
    obtain ⟨h1, h2⟩ := pi_add hB hs1 ht1
    show Om1 * (xoVal S l s + xoVal S l t) ∈ TB τ σ ∧
      pi σ τ (Om1 * (xoVal S l s + xoVal S l t)) = Om1 * (xoImg S l μ f s + xoImg S l μ f t)
    rw [mul_add, mul_add]
    exact ⟨h1, by rw [h2, hs2, ht2]⟩
  | .phi a b, hP => by
    have hP0 := hP
    obtain ⟨ha, hb, h1a, haz, hbz, hΩ, hθ⟩ := hP
    obtain ⟨hvT, hvp⟩ := zf_imgG (S := S) f hB (.phi a b) hP0
    set v := veblen (xoVal S l a) (xoVal S l b) with hvdef
    have hvE : InE v := Lu.luP_E h1a (Lu.luP_veblen _ _)
    have hv : Om1 * v = v := zf_Om1_mul_eps hvE hΩ
    have himg : xoImg S l μ f (.phi a b) = pi σ τ v := hvp.symm
    have hOT := pi_Om1 hB
    have hpv : Om1 < pi σ τ v := by
      have := (pi_bijOn hB).2 hOT.1 hvT hΩ
      rwa [hOT.2] at this
    obtain ⟨haT, hapi⟩ := zf_imgG (S := S) f hB a ha
    obtain ⟨o1, o2⟩ := one_TB hB
    have h1img : 1 ≤ xoImg S l μ f a := by
      rcases h1a.lt_or_eq with hlt | heq
      · have := (pi_bijOn hB).2 o1 haT hlt
        rw [o2, hapi] at this; exact this.le
      · rw [← hapi, ← heq, o2]
    have hpE : InE (pi σ τ v) := by
      rw [← himg]; exact Lu.luP_E h1img (Lu.luP_veblen _ _)
    show Om1 * v ∈ TB τ σ ∧ pi σ τ (Om1 * v) = Om1 * xoImg S l μ f (.phi a b)
    rw [hv, himg, zf_Om1_mul_eps hpE hpv]
    exact ⟨hvT, rfl⟩
  | .th _ _ _, h => h.elim
  | .om _, h => h.elim
  | .coll _ _, h => h.elim

/-- **The level image on one-base levels**: if `D = π_{σ,τ}` on every countable leaf in `Tᵗ[σ]` that lies in
`X ∪ Y ∪ γ`, then `yvSub D (Ω₁·val L) = Ω₁·img L`. -/
theorem zf_img_piG {l μ σ τ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hB : Bases σ τ)
    (hD : ∀ p, p ∈ TB τ σ → p < Om1 → (p ∈ X ∪ Y ∨ p < γ) → D p = pi σ τ p)
    (L : XoE) (hP : XoPiG S l μ σ τ f L) (hz : Om1 * xoVal S l L < ConjT.th S)
    (hL : YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L)) :
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
  obtain ⟨hT, hpe⟩ := zf_pi_mulG f hB L hP
  set z := Om1 * xoVal S l L with hzdef
  have hLT : YvLv S (· ∈ TB τ σ) z := (yv_TB_iff hB hz).1 hT
  have hO : SC (Om1 : Ordinal.{0}) := by rw [Rj.rj_Om1]; exact SC_Om one_ne_zero
  have hL1 : YvLv S (· < Om1) z := (yv_dat_iff hO le_rfl hz).1 (Rj.rj_Om1 ▸ Vd.vdD_lt_Om1 hz)
  have hEq : YvLv S (fun p => pi σ τ p = D p) z :=
    (zf_yv_and (zf_yv_and hL hLT) hL1).mono fun p hp => (hD p hp.1.2 hp.2 hp.1.1).symm
  obtain ⟨-, hR⟩ := yv_pi_th hB hz hLT
  rw [yvSub_eq (yvR_congr hEq hR), hpe]

/-- **At a segment `h ≥ 1` of the configuration the shift is one base change on the leaves**: `τ' = υ_{λ+h} ∈ Y`, `σ' =
υ_{μ+f h} = D τ'`; every countable `p ∈ T^{τ'}[σ']` in `X ∪ Y ∪ γ` has `D p = π_{σ',τ'}(p)`. -/
theorem zf_seg_D {l μ γ h : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (hl0 : 0 < l) (hl1 : upsilon l < Om1) (hXl : ∀ x ∈ X, x < upsilon l)
    (hYl : ∀ y ∈ Y, upsilon l ≤ y) (hXγ : ∀ x ∈ X, x < γ) (hγl : γ < upsilon l)
    (hid : ∀ x, x < γ → D x = x) (hbelow : ∀ y ∈ Y, D y < upsilon l)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (hτY : upsilon (l + h) ∈ Y) (hDτ : D (upsilon (l + h)) = upsilon (μ + f h)) (hσE : InE (upsilon (μ + f h)))
    (hγσ : γ ≤ upsilon (μ + f h)) (hτ1 : upsilon (l + h) < Om1) :
    Bases (upsilon (μ + f h)) (upsilon (l + h)) ∧
      ∀ p, p ∈ TB (upsilon (l + h)) (upsilon (μ + f h)) → p < Om1 → (p ∈ X ∪ Y ∨ p < γ) →
        D p = pi (upsilon (μ + f h)) (upsilon (l + h)) p := by
  set τ := upsilon (l + h) with hτdef
  set σ := upsilon (μ + f h) with hσdef
  have hτU : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hlτ : upsilon l ≤ τ := hYl _ hτY
  have hστ : σ < τ := (hDτ ▸ hbelow _ hτY).trans_le hlτ
  have hσl : σ < upsilon l := hDτ ▸ hbelow _ hτY
  have hB : Bases σ τ := ⟨hσE, upsPt_inE hτU, hστ, hτ1⟩
  refine ⟨hB, fun p hpT hp1 hpXY => ?_⟩
  have hlow : ∀ x, x < γ → D x = pi σ τ x := fun x hx => by
    rw [hid x hx, pi_lt hB (hx.trans_le hγσ)]
  rcases hpXY with hXY | hpγ
  · rcases Finset.mem_union.1 hXY with hx | hy
    · exact hlow p (hXγ p hx)
    · have hlp := hYl p hy
      have hτp : τ ≤ p := by
        by_contra hc
        push Not at hc
        exact absurd ((TB_inter_lt hB hc).1 hpT) (not_lt.2 (hσl.le.trans hlp))
      have hsU : UpsPt (upsilon (succ (l + h))) := upsPt_upsilon (hl0.trans_le (le_self_add.trans (Order.le_succ _)))
      have hps : p < upsilon (succ (l + h)) :=
        Za.za_lt_next (upsPt_inE hτU) hτ1 hpT.1 hp1 (upsilon_normal.strictMono (Order.lt_succ _)) hsU
      have hpar : ∀ q ∈ Par (upsilon (l + h)) p, q < upsilon l := fun q hq =>
        (hpT.2 (Finset.mem_coe.2 hq)).trans hσl
      rw [hmv p hy h hτp hps hpar]
      show (if σ < τ then pi σ τ else if τ < σ then up τ σ else id) p = pi σ τ p
      rw [if_pos hστ]
  · exact hlow p hpγ

/-- **The level image at the levels that are one-base terms at no segment** (statement): neither `Xo.XoPi` (lowest
segment) nor `XoPiG` for the segment map of any configuration segment `υ_{λ+h} ∈ Y`, `h > 0`. -/
def ZfImgHi2 (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L → ¬ XoPi S l μ L →
    (∀ h', 0 < h' → upsilon (l + h') ∈ Y → ¬ XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L) →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the level image at the levels that are one-base terms at no segment** (statement): `Zf.ZfImgP`
with `ZfImgHi2` in place of `Zf.ZfImgHi`. -/
def ZfImgP2 (S : InaccSeq.{0}) : Prop :=
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
      Za.ZaHiD S l μ γ f D X Y ∧ ZfImgHi2 S l β μ γ f D X Y

/-- **`ZfImgP2 S ⇒ ZfImgP S`**: at a one-base level of a segment `h' ≥ 1` the level image is `zf_img_piG` with
`zf_seg_D`. -/
theorem zfImgP_of_P2 (hP : ZfImgP2 S) : ZfImgP S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hA, hZa, hHi⟩ := hP l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, hA, hZa, ?_⟩
  obtain ⟨-, hXγ, hγμ, hLs, hres, -, ⟨hμl, -⟩, hmv, -, -, -, hid, -⟩ := hA
  intro h L e hW hF hR hp hM1 hPi hL
  by_cases hG : ∃ h', 0 < h' ∧ upsilon (l + h') ∈ Y ∧ XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L
  · obtain ⟨h', h'0, hτY, hPG⟩ := hG
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hLs.rng.1.1
    have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
    have hσE : InE (upsilon (μ + f h')) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
    have hγσ : γ ≤ upsilon (μ + f h') := hγμ.le.trans (upsilon_normal.monotone le_self_add)
    obtain ⟨hB', hD'⟩ := zf_seg_D hl0 hl1 hX (fun y hy => (hY y hy).1) hXγ (hγμ.trans hμl) hid hLs.below hmv hτY
      (hres h' hτY).2 hσE hγσ ((hY _ hτY).2.trans_le hb1)
    obtain ⟨h0, hhβ, hWL, _, hη1, hξT, hξ2, hby, hys⟩ := hW
    have hτU : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 :=
      (hby.trans_lt hys).trans_le (upsilon_normal.monotone (Order.succ_le_of_lt
        ((add_lt_add_iff_left l).2 hhβ)) |>.trans hb1)
    have hθ := uzTBound (S := S) _ (upsPt_inE hτU) hτ1 _ hξT hξ2
    exact zf_img_piG hB' hD' L hPG (le_self_add.trans_lt hθ) hL
  · push Not at hG
    exact hHi h L e hW hF hR hp hM1 hPi hG hL

/-- **`ZfImgP2 S ⇒ Yq.XoShift2 S`.** -/
theorem zfShift2_P2 (hP : ZfImgP2 S) : XoShift2 S := zfShift2_P (zfImgP_of_P2 hP)

end Googology.Trans.PoR.InaccPsi.R2.Zf
