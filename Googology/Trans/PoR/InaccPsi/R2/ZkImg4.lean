import Googology.Trans.PoR.InaccPsi.R2.ZkPre

/-!
# The level image at levels with one uncountable one-segment prefix and countable mixed-segment rests

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The levels `P + C`, `c + P + C`, `(P + c₁) + c₂`, …: exactly one **prefix piece** `P` (`zkPf`: `Zf.XoPiG` at an
admissible segment `g`, `Ω₁ ∣ val P`, `Ω₁ ≤ val P`; e.g. `lc B₂`) and countable segment sums elsewhere (`ZkPS`; a
countable part left of `P` is absorbed, a countable part right of `P` is moved by the segment map `G`), e.g. the
level `B₂ + b + a` with `b`, `a` in different segments.  ONE induction on the term (`zk_ps_inv`: `val L = val P + c`,
`img L = img P + zkCnf G c`), then the leaf substitution splits at `Ω₁·val P + Ω₁·c` (`Zk.zk_yv_add`), the prefix
by `Zf.zf_img_piG` (one base change, `zk_D_pi`), the rest by the exponent map (`Zk.zk_lev_seg`'s argument):

* `zkPf`, `ZkPS` (definitions), `zk_G_lt_Om1`, `zk_cnf_lt_Om1`, `zk_ps_inv`, `zk_D_pi`, `zk_lev_ps`
  (**the level image at every prefix level**);
* `ZkImgHi4`, `ZkImgP4` (statements: `ZkImgHi3`, `ZkImgP3` with the extra hypothesis `¬ ZkPS … L`),
  `zkImgP3_of_P4`, `zkImgP4_of_P3` (equivalent), `zkImgP2_of_P4`, `zkShift2_P4` (`⇒ Yq.XoShift2 S`);
* `zk_wit3` (the prefix level `lc B₂ + (old (sg h υ_{λ+h}) + old (lo υ_λ))` is a prefix level, given a strongly
  critical `q ≤ υ_μ`).

No new axiom.  New definitions: `zkPf` (a predicate), `ZkPS` (an inductive predicate), `ZkImgHi4`, `ZkImgP4`
(statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

/-- **A prefix piece**: `Zf.XoPiG` at an admissible segment, value an `Ω₁`-multiple `≥ Ω₁`. -/
def zkPf (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (Y : Finset Ordinal.{0}) (L : XoE) :
    Prop :=
  ∃ g, ZkOK Y l g ∧ Zf.XoPiG S l μ (upsilon (μ + f g)) (upsilon (l + g)) f L ∧ Om1 ∣ xoVal S l L ∧
    Om1 ≤ xoVal S l L

/-- **Prefix levels**: one prefix piece, countable sum trees left (absorbed) and right of it. -/
inductive ZkPS (Pc Pf : XoE → Prop) : XoE → Prop
  | pre {P : XoE} : Pf P → ZkPS Pc Pf P
  | addC {s t : XoE} : ZkPS Pc Pf s → ZkSS Pc t → ZkPS Pc Pf (.add s t)
  | addL {s t : XoE} : ZkSS Pc s → ZkPS Pc Pf t → ZkPS Pc Pf (.add s t)

variable {S : InaccSeq.{0}}

/-- `G` maps its domain below `Ω₁`. -/
theorem zk_G_lt_Om1 {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) : ∀ p ∈ zkDom l μ Y, zkG l μ f p < Om1 := by
  intro p hp
  rcases hp with hp | ⟨g, hg, hpT, hτp, hp1⟩
  · have hGp : zkG l μ f p = p := by unfold zkG; rw [if_pos hp]
    have h1 := (H.bases 0 (Or.inl rfl)).2
    rw [add_zero] at h1
    rw [hGp]; exact hp.trans (H.μl.trans h1)
  · obtain ⟨-, -, hGp, -, -, -⟩ := zk_seg H hg hpT hτp hp1
    have hB := H.basesB hg
    have hμσ : upsilon μ ≤ upsilon (μ + f g) := upsilon_normal.monotone le_self_add
    have hpT' : p ∈ TB (upsilon (l + g)) (upsilon (μ + f g)) := ⟨hpT.1, hpT.2.trans (Set.Iio_subset_Iio hμσ)⟩
    obtain ⟨hOT, hpO⟩ := pi_Om1 hB
    rw [hGp]
    have := (pi_bijOn hB).2 hpT' hOT hp1
    rwa [hpO] at this

/-- The exponent map stays below `Ω₁` when the exponents are mapped below `Ω₁`. -/
theorem zk_cnf_lt_Om1 {G : Ordinal.{0} → Ordinal.{0}} :
    ∀ v, ZkEx (fun e => G e < Om1) v → zkCnf G v < Om1 := by
  refine zk_ind (fun _ => by rw [zkCnf_zero]; exact Rj.rj_Om1_pos) ?_
  intro c k r hk0 hk hr IH h
  rw [zkEx_step _ hk0 hk hr] at h
  rw [zkCnf_step G hk0 hk hr]
  have h1 : ω ^ G c * k < Om1 := by
    have h2 : ω ^ G c * k < ω ^ G c * ω := mul_lt_mul_of_pos_left hk (opow_pos _ omega0_pos)
    rw [← opow_succ] at h2
    refine h2.trans_le ?_
    rw [← zk_Om1_opow]
    exact opow_le_opow_right omega0_pos (Order.succ_le_of_lt h.1)
  exact zk_Om1_principal h1 (IH h.2)

/-- **The invariant of a prefix level**: `val L = val P + c`, `img L = img P + zkCnf G c`. -/
theorem zk_ps_inv {l μ : Ordinal.{0}} {f G : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}}
    (hG : StrictMonoOn G A) (hGA : ∀ p ∈ A, G p < Om1) {Pc Pf : XoE → Prop}
    (hPc : ∀ P, Pc P → xoVal S l P < Om1 ∧ ZkEx (· ∈ A) (xoVal S l P) ∧
      xoImg S l μ f P = zkCnf G (xoVal S l P))
    (hPf : ∀ P, Pf P → Om1 ≤ xoVal S l P ∧ Om1 ≤ xoImg S l μ f P) :
    ∀ L, ZkPS Pc Pf L → ∃ P c, Pf P ∧ c < Om1 ∧ ZkEx (· ∈ A) c ∧ xoVal S l L = xoVal S l P + c ∧
      xoImg S l μ f L = xoImg S l μ f P + zkCnf G c := by
  intro L hL
  induction hL with
  | pre h => exact ⟨_, 0, h, Rj.rj_Om1_pos, zkEx_zero _, by rw [add_zero], by rw [zkCnf_zero, add_zero]⟩
  | addC _ ht ih =>
    rename_i s t _
    obtain ⟨P, c, hP, hc1, hcA, hv, hi⟩ := ih
    obtain ⟨t1, t2, t3⟩ := zk_ss_img hG hPc t ht
    obtain ⟨hA, hE⟩ := zk_add hG c _ hcA t2
    refine ⟨P, c + xoVal S l t, hP, zk_Om1_principal hc1 t1, hA, ?_, ?_⟩
    · show xoVal S l s + xoVal S l t = _
      rw [hv, add_assoc]
    · show xoImg S l μ f s + xoImg S l μ f t = _
      rw [hi, t3, hE, add_assoc]
  | addL hs _ ih =>
    rename_i s t _
    obtain ⟨P, c, hP, hc1, hcA, hv, hi⟩ := ih
    obtain ⟨s1, s2, s3⟩ := zk_ss_img hG hPc s hs
    obtain ⟨hPv, hPi⟩ := hPf P hP
    refine ⟨P, c, hP, hc1, hcA, ?_, ?_⟩
    · show xoVal S l s + xoVal S l t = _
      have h1 : xoVal S l s < ω ^ (Om1 : Ordinal.{0}) := by rw [zk_Om1_opow]; exact s1
      have h2 : ω ^ (Om1 : Ordinal.{0}) ≤ xoVal S l P := by rw [zk_Om1_opow]; exact hPv
      rw [hv, ← add_assoc, add_of_omega0_opow_le h1 h2]
    · show xoImg S l μ f s + xoImg S l μ f t = _
      have hs1 : xoImg S l μ f s < Om1 := by
        rw [s3]
        exact zk_cnf_lt_Om1 _ (zkEx_mono (fun e he => hGA e he) _ s2)
      have h1 : xoImg S l μ f s < ω ^ (Om1 : Ordinal.{0}) := by rw [zk_Om1_opow]; exact hs1
      have h2 : ω ^ (Om1 : Ordinal.{0}) ≤ xoImg S l μ f P := by rw [zk_Om1_opow]; exact hPi
      rw [hi, ← add_assoc, add_of_omega0_opow_le h1 h2]

/-- **The realizer is the segment base change on the countable leaves of a segment** (`g = 0`: the clause `D = π`
below `υ_{λ+1}`; `g > 0`: `Zf.zf_seg_D`). -/
theorem zk_D_pi {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) (hl1 : upsilon l < Om1) (hX : ∀ x ∈ X, x < upsilon l) (hXγ : ∀ x ∈ X, x < γ)
    (hγμ : γ < upsilon μ) (hid : ∀ x, x < γ → D x = x) (hYl : ∀ y ∈ Y, upsilon l ≤ y)
    (hbelow : ∀ y ∈ Y, D y < upsilon l)
    (hres : ∀ g, upsilon (l + g) ∈ Y → D (upsilon (l + g)) = upsilon (μ + f g))
    (hpi : ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    {g : Ordinal.{0}} (hg : ZkOK Y l g) :
    ∀ p, p ∈ TB (upsilon (l + g)) (upsilon (μ + f g)) → p < Om1 → (p ∈ X ∪ Y ∨ p < γ) →
      D p = pi (upsilon (μ + f g)) (upsilon (l + g)) p := by
  rcases hg with rfl | ⟨hg0, hgY⟩
  · rw [H.f0, add_zero, add_zero]
    have hB : Bases (upsilon μ) (upsilon l) := by
      have := H.basesB (Or.inl rfl); rwa [H.f0, add_zero, add_zero] at this
    intro p hpT hp1 hP
    have hlow : p < γ → D p = pi (upsilon μ) (upsilon l) p := fun h => by
      rw [hid p h, pi_lt hB (h.trans hγμ)]
    rcases hP with hXY | hpγ
    · rcases Finset.mem_union.1 hXY with hx | hy
      · exact hlow (hXγ p hx)
      · have hps : p < upsilon (succ l) :=
          Za.za_lt_next hB.2.1 hl1 hpT.1 hp1 (upsilon_normal.strictMono (Order.lt_succ _))
            (upsPt_upsilon (H.l0.trans_le (Order.le_succ _)))
        exact hpi p hy hps
    · exact hlow hpγ
  · have hσE : InE (upsilon (μ + f g)) := upsPt_inE (upsPt_upsilon (H.μ0.trans_le le_self_add))
    have hγσ : γ ≤ upsilon (μ + f g) := hγμ.le.trans (upsilon_normal.monotone le_self_add)
    exact (Zf.zf_seg_D H.l0 hl1 hX hYl hXγ (hγμ.trans H.μl) hid hbelow hmv hgY (hres g hgY) hσE hγσ
      (H.bases g (Or.inr ⟨hg0, hgY⟩)).2).2

/-- **The level image at every prefix level.** -/
theorem zk_lev_ps {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) (hl1 : upsilon l < Om1) (hX : ∀ x ∈ X, x < upsilon l) (hXγ : ∀ x ∈ X, x < γ)
    (hγμ : γ < upsilon μ) (hid : ∀ x, x < γ → D x = x) (hγ0 : 0 < γ) (hYl : ∀ y ∈ Y, upsilon l ≤ y)
    (hbelow : ∀ y ∈ Y, D y < upsilon l)
    (hres : ∀ g, upsilon (l + g) ∈ Y → D (upsilon (l + g)) = upsilon (μ + f g))
    (hpi : ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (L : XoE) (hL : ZkPS (zkPc S l μ f Y) (zkPf S l μ f Y) L) (hθ : Om1 * xoVal S l L < ConjT.th S)
    (hLv : YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L)) :
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
  have hG0 : zkG l μ f 0 = 0 := by unfold zkG; rw [if_pos (hγ0.trans hγμ)]
  have hD0 : D 0 = 0 := hid 0 hγ0
  have hPf : ∀ P, zkPf S l μ f Y P → Om1 ≤ xoVal S l P ∧ Om1 ≤ xoImg S l μ f P := by
    intro P ⟨g, hg, hPG, _, hO⟩
    have hB := H.basesB hg
    obtain ⟨hvT, hpv⟩ := Zf.zf_imgG f hB P hPG
    obtain ⟨hOT, hpO⟩ := pi_Om1 hB
    refine ⟨hO, ?_⟩
    rw [← hpv, ← hpO]
    rcases hO.lt_or_eq with h | h
    · exact ((pi_bijOn hB).2 hOT hvT h).le
    · rw [h]
  obtain ⟨P, c, hP, hc1, hcA, hv, hi⟩ := zk_ps_inv (zk_G_mono H) (zk_G_lt_Om1 H) (zk_pc_cnf H) hPf L hL
  obtain ⟨g, hg, hPG, ⟨u, hu⟩, hO⟩ := hP
  have hB := H.basesB hg
  -- the split `Ω₁·val L = Ω₁·val P + Ω₁·c`
  have hsplit : Om1 * xoVal S l L = Om1 * xoVal S l P + Om1 * c := by rw [hv, mul_add]
  have hEx : ZkEx (fun e => Om1 * 2 ≤ e) (Om1 * xoVal S l P) := by
    rw [hu, ← mul_assoc, ← zk_W2_eq]; exact zkEx_opow_mul _ u
  have hb : Om1 * c < ω ^ ((Om1 : Ordinal.{0}) * 2) := by
    rw [zk_W2_eq]; exact mul_lt_mul_of_pos_left hc1 Rj.rj_Om1_pos
  have hP0 : (fun p => p ∈ X ∪ Y ∨ p < γ) 0 := Or.inr hγ0
  rw [hsplit] at hθ hLv ⊢
  obtain ⟨hLa, hLb, hadd⟩ := zk_yv_add D hD0 hP0 _ hEx _ hb hθ hLv
  have hθa : Om1 * xoVal S l P < ConjT.th S := le_self_add.trans_lt hθ
  have ha : yvSub S D (Om1 * xoVal S l P) = Om1 * xoImg S l μ f P :=
    Zf.zf_img_piG hB (zk_D_pi H hl1 hX hXγ hγμ hid hYl hbelow hres hpi hmv hg) P hPG hθa hLa
  have hE := zk_yvLv_mul hc1 hLb
  have hEq : ZkEx (fun x => D x = zkG l μ f x) c := by
    refine zkEx_mono (fun x hx => ?_) _ (zkEx_and _ hcA hE)
    rcases hx.2 with h0 | hPx
    · rw [h0, hD0, hG0]
    · exact zk_DG H hXγ hγμ hid hYl hmv x hx.1 hPx
  have hbb : yvSub S D (Om1 * c) = Om1 * zkCnf (zkG l μ f) c := by
    rw [zk_yvSub_mul D hD0 hc1, zkCnf_congr _ hEq]
  rw [hadd, ha, hbb, hi, mul_add]

/-- **The level image off the segment sums and the prefix levels** (statement). -/
def ZkImgHi4 (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L → ¬ XoPi S l μ L →
    (∀ h', 0 < h' → upsilon (l + h') ∈ Y → ¬ Zf.XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L) →
    ¬ ZkSS (zkPc S l μ f Y) L → ¬ ZkPS (zkPc S l μ f Y) (zkPf S l μ f Y) L →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) → ¬ Zf.ZfNest S l L →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the level image off the segment sums and the prefix levels** (statement): `ZkImgP3` with
`ZkImgHi4`. -/
def ZkImgP4 (S : InaccSeq.{0}) : Prop :=
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
      Za.ZaHiD S l μ γ f D X Y ∧ ZkImgHi4 S l β μ γ f D X Y

/-- **`ZkImgP4 S ⇒ ZkImgP3 S`.** -/
theorem zkImgP3_of_P4 (hP : ZkImgP4 S) : ZkImgP3 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, ⟨⟨hQ, hSl⟩, hrest⟩, hZa, hHi⟩ :=
    hP l β (fun μ f B γ Os => Q μ f B γ Os ∧ Sl.SlOff f Os B) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8, h7⟩)
      hstd hlL X Y hX hY
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, hrest⟩, hZa, ?_⟩
  obtain ⟨hXγ, hγμ, hLs, hres, -, ⟨hμl, hpi⟩, hmv, -, -, -, hid, hγU⟩ := hrest
  intro h L e hW hF hR hp hM1 hPi hG hSS hLv hN
  by_cases hPS : ZkPS (zkPc S l μ f Y) (zkPf S l μ f Y) L
  · have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
    have H : ZkSegH l μ f Y := zkSegH_of hl0 hl1 hb1 hY hLs hμl hres hSl
    have hγ0 : 0 < γ := omega0_pos.trans (omega0_lt_inE (upsPt_inE hγU))
    obtain ⟨h0, hhβ, hWL, _, hη1, hξT, hξ2, hby, hys⟩ := hW
    have hτU : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 :=
      (hby.trans_lt hys).trans_le (upsilon_normal.monotone (Order.succ_le_of_lt
        ((add_lt_add_iff_left l).2 hhβ)) |>.trans hb1)
    have hθ := uzTBound (S := S) _ (upsPt_inE hτU) hτ1 _ hξT hξ2
    exact zk_lev_ps H hl1 hX hXγ hγμ hid hγ0 (fun y hy => (hY y hy).1) hLs.below
      (fun g hg => (hres g hg).2) hpi hmv L hPS (le_self_add.trans_lt hθ) hLv
  · exact hHi h L e hW hF hR hp hM1 hPi hG hSS hPS hLv hN

/-- **The converse**: `ZkImgP3 S ⇒ ZkImgP4 S`. -/
theorem zkImgP4_of_P3 (hP : ZkImgP3 S) : ZkImgP4 S := by
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  obtain ⟨D, μ, f, B, γ, Os, hA, hZa, hHi⟩ := hP l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  exact ⟨D, μ, f, B, γ, Os, hA, hZa,
    fun h L e hW hF hR hp hM1 hPi hG hSS _ hLv hN => hHi h L e hW hF hR hp hM1 hPi hG hSS hLv hN⟩

/-- **`ZkImgP4 S ⇒ Zf.ZfImgP2 S`.** -/
theorem zkImgP2_of_P4 (hP : ZkImgP4 S) : Zf.ZfImgP2 S := zkImgP2_of_P3 (zkImgP3_of_P4 hP)

/-- **`ZkImgP4 S ⇒ Yq.XoShift2 S`.** -/
theorem zkShift2_P4 (hLN : Zf.ZfLevNode S) (hP : ZkImgP4 S) : XoShift2 S := zkShift2_P3 hLN (zkImgP3_of_P4 hP)

/-- **A prefix level** (given a strongly critical `q ≤ υ_μ`): `lc B₂ + (old (sg h υ_{λ+h}) + old (lo υ_λ))`. -/
theorem zk_wit3 {l μ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Y : Finset Ordinal.{0}}
    (H : ZkSegH l μ f Y) {h : Ordinal.{0}} (h0 : 0 < h) (hτY : upsilon (l + h) ∈ Y)
    {q : Ordinal.{0}} (hq : SC q) (hqμ : q ≤ upsilon μ) :
    ZkPS (zkPc S l μ f Y) (zkPf S l μ f Y)
      (.add (.lc Uc.ucB) (.add (.old (.sg h (upsilon (l + h)))) (.old (.lo (upsilon l))))) := by
  refine ZkPS.addC (ZkPS.pre ⟨0, Or.inl rfl, ?_, ?_, ?_⟩) (zk_wit2 (S := S) H h0 hτY).1
  · show Uc.ucB < ConjT.th S ∧ ∃ q, SC q ∧ q ≤ upsilon (μ + f 0) ∧ Vd.vdD S 0 Uc.ucB < q
    rw [H.f0, add_zero]
    exact ⟨Vd.vd_B_lt_th, q, hq, hqμ, Ww.ww_B_dat hq⟩
  · show Om1 ∣ Uc.ucB
    have hOB : (Om1 : Ordinal.{0}) < Uc.ucB := Rj.rj_Om1_lt_E.trans Uv.uv_E_lt_B
    exact ⟨Uc.ucB, (Zf.zf_Om1_mul_eps Yv.yv_B_eps hOB).symm⟩
  · show (Om1 : Ordinal.{0}) ≤ Uc.ucB
    exact (Rj.rj_Om1_lt_E.trans Uv.uv_E_lt_B).le

end Googology.Trans.PoR.InaccPsi.R2.Zk
