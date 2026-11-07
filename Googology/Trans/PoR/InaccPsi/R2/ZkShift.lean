import Googology.Trans.PoR.InaccPsi.R2.ZkNode

/-!
# The shift from the level image off the mixed sum trees and the mixed prefix levels

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Zk.ZkImgP4` asks the level image off the one-segment levels, the segment sums of one-segment pieces and the prefix
levels; `Zf.zfShift2` adds the sum trees of nested nodes by induction on the size.  Here one induction does all of it
and more: the pieces of a sum tree or of the countable rests of a prefix level may be one-segment pieces (`zkPc`),
nested nodes (`Zf.ZfNodeOK`) and low pieces (`ZkLow`: value below `υ_λ`, fixed by `D`), mixed (`zkMx`).  The exponent map is `D` itself on the configuration, enlarged by the
Cantor exponents of its points (`zkExps`): a one-segment piece has image `zkCnf zkG val` and `zkG = D` on its exponents
(`zk_DG`); a node is an `ε`-number, its own only exponent, with image `D(val)` (the node clause at it, a smaller term).

* `zkExps`, `zkExps_le`, `zkEx_of_exps` (**the exponents of the Cantor normal form**);
* `zk_lev_psD` (`zk_lev_ps` with the exponent map `D` and any pieces);
* `zkCnf_id`, `ZkLow` (**low pieces**), `zkMx` (**mixed pieces**), `ZkImgHi5`, `ZkImgP5` (statements: `ZkImgHi4`, `ZkImgP4` off the mixed sum trees and the
  mixed prefix levels);
* `zkShift2_P5` (**`ZkImgP5 S ⇒ Yq.XoShift2 S`**).

No new axiom.  New definitions: `zkExps`, `ZkLow`, `zkMx` (predicates), `ZkImgHi5`, `ZkImgP5` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv
  Googology.Trans.PoR.InaccPsi.R2.Zf

variable {S : InaccSeq.{0}}

/-- The exponents of the Cantor normal form of `v` (base `ω`). -/
noncomputable def zkExps (v : Ordinal.{0}) : Finset Ordinal.{0} := ((Ordinal.CNF ω v).map Prod.fst).toFinset

theorem zkExps_le (v : Ordinal.{0}) {e : Ordinal.{0}} (he : e ∈ zkExps v) : e ≤ v := by
  unfold zkExps at he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
  exact (Ordinal.CNF.fst_le_log hx).trans (Ordinal.log_le_self _ _)

/-- **A property of all the Cantor exponents** gives `ZkEx`. -/
theorem zkEx_of_exps (P : Ordinal.{0} → Prop) : ∀ v, (∀ e ∈ zkExps v, P e) → ZkEx P v := by
  intro v
  induction v using WellFoundedLT.induction with
  | _ v IH =>
  intro h
  rcases eq_or_ne v 0 with rfl | hv
  · exact zkEx_zero P
  · rw [zkEx_ne P hv]
    have hC : zkExps v = insert (log ω v) (zkExps (v % ω ^ log ω v)) := by
      unfold zkExps; rw [Ordinal.CNF.ne_zero hv]; simp
    rw [hC] at h
    exact ⟨h _ (Finset.mem_insert_self _ _),
      IH _ (mod_opow_log_lt_self ω hv) fun e he => h e (Finset.mem_insert_of_mem he)⟩

/-- **The level image at a prefix level with any pieces of exponent map `D`.** -/
theorem zk_lev_psD {l μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    {A : Set Ordinal.{0}} {Pc : XoE → Prop}
    (H : ZkSegH l μ f Y) (hl1 : upsilon l < Om1) (hX : ∀ x ∈ X, x < upsilon l) (hXγ : ∀ x ∈ X, x < γ)
    (hγμ : γ < upsilon μ) (hid : ∀ x, x < γ → D x = x) (hγ0 : 0 < γ) (hYl : ∀ y ∈ Y, upsilon l ≤ y)
    (hbelow : ∀ y ∈ Y, D y < upsilon l)
    (hres : ∀ g, upsilon (l + g) ∈ Y → D (upsilon (l + g)) = upsilon (μ + f g))
    (hpi : ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y)
    (hmv : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y)
    (hDA : StrictMonoOn D A) (hDA1 : ∀ p ∈ A, D p < Om1)
    (hPc : ∀ P, Pc P → xoVal S l P < Om1 ∧ ZkEx (· ∈ A) (xoVal S l P) ∧ xoImg S l μ f P = zkCnf D (xoVal S l P))
    (L : XoE) (hL : ZkPS Pc (zkPf S l μ f Y) L) (hθ : Om1 * xoVal S l L < ConjT.th S)
    (hLv : YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L)) :
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L := by
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
  obtain ⟨P, c, hP, hc1, -, hv, hi⟩ := zk_ps_inv hDA hDA1 hPc hPf L hL
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
  have hbb : yvSub S D (Om1 * c) = Om1 * zkCnf D c := zk_yvSub_mul D hD0 hc1
  rw [hadd, ha, hbb, hi, mul_add]

/-- The Cantor map of the identity is the identity. -/
theorem zkCnf_id : ∀ v, zkCnf (fun x => x) v = v :=
  zk_ind (zkCnf_zero _) fun _ _ _ hk0 hk hr IH => by rw [zkCnf_step _ hk0 hk hr, IH]

/-- **A low piece**: value below `υ_λ`, an `old` / `th` / `add` term or a constant (fixed by the shift). -/
def ZkLow (S : InaccSeq.{0}) (l : Ordinal.{0}) (P : XoE) : Prop :=
  xoVal S l P < upsilon l ∧ (XoTopF P ∨ ∃ M, P = .lc M)

/-- **Mixed pieces**: one-segment pieces, nested nodes and low pieces. -/
def zkMx (S : InaccSeq.{0}) (l μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (Y : Finset Ordinal.{0}) (P : XoE) :
    Prop :=
  zkPc S l μ f Y P ∨ ZfNodeOK S l P ∨ ZkLow S l P

/-- **The level image off the mixed sum trees and the mixed prefix levels** (statement). -/
def ZkImgHi5 (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L → ¬ XoPi S l μ L →
    (∀ h', 0 < h' → upsilon (l + h') ∈ Y → ¬ Zf.XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L) →
    ¬ ZkSS (zkMx S l μ f Y) L → ¬ ZkPS (zkMx S l μ f Y) (zkPf S l μ f Y) L →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The shift with the level image off the mixed sum trees and the mixed prefix levels** (statement). -/
def ZkImgP5 (S : InaccSeq.{0}) : Prop :=
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
      Za.ZaHiD S l μ γ f D X Y ∧ ZkImgHi5 S l β μ γ f D X Y

/-- **`ZkImgP5 S ⇒ Yq.XoShift2 S`**: one induction on the size gives the level image at every node: one-segment
levels (`Zf.zf_img_pi`), one-base levels at a segment (`Zf.zf_img_piG`), mixed sum trees (`zk_ss_lev` with the map
`D`), mixed prefix levels (`zk_lev_psD`), the rest from `ZkImgHi5`; the node clauses at the inner nodes by `Zf.zfDCl`
at the smaller size. -/
theorem zkShift2_P5 (hP : ZkImgP5 S) : XoShift2 S := by
  classical
  intro l β Q hl hl1 hν hνβ hsup hstd hlL X Y hX hY
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  obtain ⟨Z, hZb, hZ⟩ := zf_enl S hl0 hb1 Y (fun y hy => (hY y hy).2)
  set C := (X ∪ Y).biUnion zkExps with hCdef
  set X' := insert ω X ∪ (Z ∪ C).filter (· < upsilon l) with hX'def
  set Y' := Y ∪ (Z ∪ C).filter (fun z => upsilon l ≤ z) with hY'def
  have hXX' : X ⊆ X' := fun x hx => Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
  have hYY' : Y ⊆ Y' := Finset.subset_union_left
  have hωX' : ω ∈ X' := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hZCXY : ∀ z ∈ Z ∪ C, z ∈ X' ∪ Y' := by
    intro z hz
    rcases lt_or_ge z (upsilon l) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hz, h⟩))
  have hZXY : ∀ z ∈ Z, z ∈ X' ∪ Y' := fun z hz => hZCXY z (Finset.mem_union_left _ hz)
  have hCXY : ∀ v ∈ X ∪ Y, ∀ e ∈ zkExps v, e ∈ X' ∪ Y' := fun v hv e he =>
    hZCXY e (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, he⟩))
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · rcases Finset.mem_insert.1 h with rfl | h
      · exact omega0_lt_inE hlE
      · exact hX x h
    · exact (Finset.mem_filter.1 h).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact hY y h
    · obtain ⟨hzC, hly⟩ := Finset.mem_filter.1 h
      refine ⟨hly, ?_⟩
      rcases Finset.mem_union.1 hzC with hz | hc
      · exact hZb y hz
      · obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.1 hc
        refine lt_of_le_of_lt (zkExps_le v he) ?_
        rcases Finset.mem_union.1 hv with hx | hy
        · exact (hX v hx).trans_le (upsilon_normal.strictMono.monotone le_self_add)
        · exact (hY v hy).2
  obtain ⟨D, μ, f, B, γ, Os, ⟨⟨hQ, hSl⟩, hXγ, hγμ, hLs, hres, hYB, ⟨hμl, hpi⟩, hmv, hub, hun, hLC, hid, hγU⟩,
    hZa, hImg⟩ := hP l β (fun μ f B γ Os => Q μ f B γ Os ∧ Sl.SlOff f Os B) hl hl1 hν hνβ
      (fun γ hγ Os hOs => by
        obtain ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsup γ hγ Os hOs
        exact ⟨μ, f, B, h1, h2, h3, h4, h5, h6, h7, h8, h7⟩)
      hstd hlL X' Y' hX' hY'
  have hsubXY : ∀ z, z ∈ X ∪ Y → z ∈ X' ∪ Y' := fun z hz => Finset.union_subset_union hXX' hYY' hz
  refine ⟨D, μ, f, B, γ, Os, ⟨hQ, fun x hx => hXγ x (hXX' hx), hγμ, zf_lsMapW_mono hLs hXX' hYY',
    fun g hg => hres g (hYY' hg), fun y hy => hYB y (hYY' hy), ⟨hμl, fun y hy => hpi y (hYY' hy)⟩,
    fun y hy => hmv y (hYY' hy),
    fun y hy g h1 h2 t hA hW hL => hub y (hYY' hy) g h1 h2 t hA hW (Ub.UbT.Lv_mono hsubXY t hL),
    fun y hy g h1 h2 t hZW hWF hL hZL => hun y (hYY' hy) g h1 h2 t hZW hWF (UnT.Lv_mono hsubXY t hL)
      (ZL_mono (fun p hp => hp.elim (fun h => Or.inl (hsubXY p h)) Or.inr) t hZL),
    vl_lc_mono (fun p hp => hp.elim (fun h => Or.inl (hsubXY p h)) Or.inr) hLC, hid, hγU⟩, ?_⟩
  intro h L e hW hF hR hp
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hW.2.1
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hLs.rng.1.1
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hBμ : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE, hμl, hl1⟩
  have hold := fun E hWE hp' =>
    (Vr.vrD_eq hl0 hb1 hX' hY' hLs.fix hLs.add hXγ hγμ hBμ hres hpi hmv hub hun hid E hWE hp').1
  have hyYof : ∀ y, y ∈ X ∪ Y → ∀ h', upsilon (l + h') ≤ y → y ∈ Y := by
    intro y hyP h' h1
    rcases Finset.mem_union.1 hyP with hx | hy
    · exact absurd (hX y hx) (not_lt.2 ((upsilon_normal.monotone le_self_add).trans h1))
    · exact hy
  have hLv' : ∀ y, y ∈ X ∪ Y → y ∈ Y' → ∀ h' M η, upsilon (l + h') ≤ y → y < upsilon (succ (l + h')) →
      1 ≤ M → η < Om1 → Om1 * M + η ∈ Tset (upsilon (l + h')) → Om1 * M + η < OmTwo →
      vt (upsilon (l + h')) (Om1 * M + η) = y → YvLv S (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * M) := by
    intro y hyP _ h' M η h1 h2 hM1 hη1 hT h2' hval
    have hyY := hyYof y hyP h' h1
    have hξ1 : Om1 ≤ Om1 * M + η := (le_mul_left Om1 (zero_lt_one.trans_le hM1)).trans le_self_add
    obtain ⟨hA, -⟩ := hZ y hyY h' (Om1 * M + η) h1 h2 hT h2' hval
    have hdiv : (Om1 * M + η) / Om1 = M := by
      rw [Ordinal.mul_add_div M Rj.rj_Om1_pos.ne' η, Ordinal.div_eq_zero_of_lt hη1, add_zero]
    have hA' := hA hξ1
    rw [hdiv] at hA'
    exact hA'.mono fun p hp => Or.inl (hZXY p hp.1)
  have hPr' : ∀ y, y ∈ X ∪ Y → y ∈ Y' → ∀ h' η, upsilon (l + h') ≤ y → y < upsilon (succ (l + h')) →
      1 ≤ η → η < Om1 → η ∈ Tset (upsilon (l + h')) → vt (upsilon (l + h')) η = y → η - 1 ∈ X' ∪ Y' := by
    intro y hyP _ h' η h1 h2 h1η hη1 hT hval
    have hyY := hyYof y hyP h' h1
    obtain ⟨-, hB'⟩ := hZ y hyY h' η h1 h2 hT (hη1.trans tqc_Om1_lt_OmTwo) hval
    exact hZXY _ (hB' h1η hη1).1
  have hm := upsilon_normal.strictMono
  have hbU : UpsPt (upsilon (l + β)) := upsPt_upsilon (hl0.trans_le le_self_add)
  have hθ2 : ConjT.th S < OmTwo := by rw [← Ui.ui_one_W]; exact (InaccSeq.psiS_bounds (S := S) _ 1).2
  have hIndec : Indec (OmTwo : Ordinal.{0}) := Lq.lq_SC_indec Uc.uc_SC_Om2
  have H : ZkSegH l μ f Y' := zkSegH_of hl0 hl1 hb1 hY' hLs hμl hres hSl
  have hDA1 : ∀ p ∈ (↑(X' ∪ Y') : Set Ordinal.{0}), D p < Om1 := by
    intro p hp
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hp) with hx | hy
    · rw [hLs.fix _ hx]; exact (hX' _ hx).trans hl1
    · exact (hLs.below _ hy).trans hl1
  -- the level image at every node, by induction on the size (the nested node levels from the inner nodes)
  have hImgAll : ∀ n : ℕ, ∀ h₁ : Ordinal.{0}, ∀ L₁ e₁ : XoE, xoSize (.th h₁ L₁ e₁) ≤ n →
      XoWF S l β (.th h₁ L₁ e₁) → XoTopF e₁ → XoR S l μ (.th h₁ L₁ e₁) →
      (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁), z ∈ X' ∪ Y') →
      (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁), z ∈ X ∪ Y) → 1 ≤ xoVal S l L₁ →
      YvLv S (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * xoVal S l L₁) →
      yvSub S D (Om1 * xoVal S l L₁) = Om1 * xoImg S l μ f L₁ := by
    intro n
    induction n with
    | zero =>
      intro h₁ L₁ e₁ hsz
      simp only [xoSize] at hsz
      omega
    | succ n ih =>
      intro h₁ L₁ e₁ hsz hW₁ hF₁ hR₁ hp₁ hq₁ hM1₁ hlv
      have hW₁c := hW₁
      obtain ⟨-, hh₁β, hWL₁, -, -, hξT₁, hξ2₁, hby₁, hys₁⟩ := hW₁c
      have hszL : xoSize L₁ ≤ n := by simp only [xoSize] at hsz; omega
      have hsubL : xoPts S l (upsilon (l + β)) L₁ ⊆ xoPts S l (upsilon (l + β)) (.th h₁ L₁ e₁) :=
        yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)))
      have hτ₁U : UpsPt (upsilon (l + h₁)) := upsPt_upsilon (hl0.trans_le le_self_add)
      have hτ₁1 : upsilon (l + h₁) < Om1 :=
        (hby₁.trans_lt hys₁).trans_le ((upsilon_normal.monotone (Order.succ_le_of_lt
          ((add_lt_add_iff_left l).2 hh₁β))).trans hb1)
      have hθ₁ : Om1 * xoVal S l L₁ < ConjT.th S :=
        le_self_add.trans_lt (uzTBound (S := S) _ (upsPt_inE hτ₁U) hτ₁1 _ hξT₁ hξ2₁)
      -- (1) one-segment levels
      by_cases hPi : XoPi S l μ L₁
      · have hβ1 : 1 ≤ β := Order.one_le_iff_ne_zero.2 hβ0.ne'
        have hs1 : upsilon (succ l) ≤ Om1 := by
          have : upsilon (succ l) ≤ upsilon (l + β) := by
            rw [Order.succ_eq_add_one]; exact upsilon_normal.monotone (add_le_add_right hβ1 l)
          exact this.trans hb1
        exact zf_img_pi hl0 hBμ hs1 hpi hid hXγ hγμ L₁ hPi hWL₁ hθ₁ hlv
      -- (2) one-base levels at a segment
      by_cases hG : ∃ h', 0 < h' ∧ upsilon (l + h') ∈ Y' ∧
          XoPiG S l μ (upsilon (μ + f h')) (upsilon (l + h')) f L₁
      · obtain ⟨h', h'0, hτY, hPG⟩ := hG
        have hσE : InE (upsilon (μ + f h')) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
        have hγσ : γ ≤ upsilon (μ + f h') := hγμ.le.trans (upsilon_normal.monotone le_self_add)
        obtain ⟨hB', hD'⟩ := zf_seg_D hl0 hl1 hX' (fun y hy => (hY' y hy).1) hXγ (hγμ.trans hμl) hid hLs.below
          hmv hτY (hres h' hτY).2 hσE hγσ ((hY' _ hτY).2.trans_le hb1)
        exact zf_img_piG hB' hD' L₁ hPG hθ₁ hlv
      push Not at hG
      -- the mixed pieces: their values, exponents and images
      have key : ∀ L₀ : XoE, ZkSS (zkMx S l μ f Y') L₀ → xoSize L₀ ≤ n → XoWF S l β L₀ → XoR S l μ L₀ →
          (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X' ∪ Y') →
          (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X ∪ Y) →
          ZkSS (fun N => xoVal S l N < Om1 ∧ ZkEx (· ∈ (↑(X' ∪ Y') : Set Ordinal.{0})) (xoVal S l N) ∧
            xoImg S l μ f N = zkCnf D (xoVal S l N)) L₀ := by
        intro L₀ hN₀
        induction hN₀ with
        | @piece P hPm =>
          intro hsz' hWL0 hRL hpL hqL
          rcases hPm with hpc | hOK | hlow
          · -- a one-segment piece: the segment map is `D` on its exponents
            obtain ⟨h1, hEx, himg⟩ := zk_pc_cnf H P hpc
            obtain ⟨-, g, hg, -, hTμ⟩ := hpc
            have hτg : upsilon (l + g) < upsilon (l + β) := by
              rcases hg with rfl | ⟨-, hgY⟩
              · rw [add_zero]; exact hm ((lt_add_iff_pos_right l).2 hβ0)
              · exact (hY' _ hgY).2
            have hgE : InE (upsilon (l + g)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
            have hvb : xoVal S l P < upsilon (l + β) :=
              Za.za_lt_next hgE (hτg.trans_le hb1) hTμ.1 h1 hτg hbU
            have hvXY : xoVal S l P ∈ X ∪ Y := hqL _ (xoVal_mem P hvb)
            have hExA : ZkEx (· ∈ (↑(X' ∪ Y') : Set Ordinal.{0})) (xoVal S l P) :=
              zkEx_of_exps _ _ (fun e he => Finset.mem_coe.2 (hCXY _ hvXY e he))
            refine ZkSS.piece ⟨h1, hExA, ?_⟩
            rw [himg]
            refine zkCnf_congr _ (zkEx_mono (fun x hx => (zk_DG H hXγ hγμ hid (fun y hy => (hY' y hy).1) hmv x
              hx.1 (Or.inl (Finset.mem_coe.1 hx.2))).symm) _ (zkEx_and _ hEx hExA))
          rotate_left
          · -- a low piece: fixed by `D`
            obtain ⟨hvl, hform⟩ := hlow
            have hvb : xoVal S l P < upsilon (l + β) := hvl.trans_le (upsilon_normal.monotone le_self_add)
            have hvXY : xoVal S l P ∈ X ∪ Y := hqL _ (xoVal_mem P hvb)
            have hvX' : xoVal S l P ∈ X' := by
              rcases Finset.mem_union.1 (hsubXY _ hvXY) with h | h
              · exact h
              · exact absurd (hY' _ h).1 (not_le.2 hvl)
            have himg : xoImg S l μ f P = xoVal S l P := by
              rcases hform with hT | ⟨M, rfl⟩
              · have hDP := zfDCl (Pt := fun z => z ∈ X ∪ Y) hl0 hβ0 hb1 hX' hY' hBμ hμ0 hLs.mono hLs.add
                  hLs.below hres hold hun hLC hid hγU hZa n ih hLv' hPr' (Finset.mem_union_left _ hωX') P hsz'
                  hWL0 hT hRL hpL hqL hvb
                rw [← hDP, hLs.fix _ hvX']
              · rfl
            have hExA : ZkEx (· ∈ (↑(X' ∪ Y') : Set Ordinal.{0})) (xoVal S l P) :=
              zkEx_of_exps _ _ (fun e he => Finset.mem_coe.2 (hCXY _ hvXY e he))
            refine ZkSS.piece ⟨hvl.trans hl1, hExA, ?_⟩
            have hfixE : ZkEx (fun x => D x = x) (xoVal S l P) := by
              refine zkEx_of_exps _ _ (fun e he => hLs.fix _ ?_)
              rcases Finset.mem_union.1 (hCXY _ hvXY e he) with h | h
              · exact h
              · exact absurd (hY' _ h).1 (not_le.2 ((zkExps_le _ he).trans_lt hvl))
            rw [himg, zkCnf_congr _ hfixE, zkCnf_id]
          · -- a nested node
            obtain ⟨h', L', e', rfl, hF', hM1'⟩ := hOK
            have hWL := hWL0
            obtain ⟨-, hh'β, -, -, hη1, hξT, hξ2, hby, hys⟩ := hWL
            have hsb' : upsilon (succ (l + h')) ≤ upsilon (l + β) :=
              upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hh'β))
            have hvL : xoVal S l (.th h' L' e') < upsilon (l + β) := hys.trans_le hsb'
            -- the node clause at the inner node
            have hDL : D (xoVal S l (.th h' L' e')) = xoImg S l μ f (.th h' L' e') :=
              zfDCl (Pt := fun z => z ∈ X ∪ Y) hl0 hβ0 hb1 hX' hY' hBμ hμ0 hLs.mono hLs.add hLs.below hres hold hun
                hLC hid hγU hZa n ih hLv' hPr' (Finset.mem_union_left _ hωX') (.th h' L' e') hsz' hWL0 hF'
                hRL hpL hqL hvL
            -- the inner value is an `ε`-number, and so is its image
            have hτU : UpsPt (upsilon (l + h')) := upsPt_upsilon (hl0.trans_le le_self_add)
            have hτE : InE (upsilon (l + h')) := upsPt_inE hτU
            have hv1 : xoVal S l (.th h' L' e') < Om1 := hvL.trans_le hb1
            have hτ1 : upsilon (l + h') < Om1 := hby.trans_lt hv1
            have hτb : upsilon (l + h') < upsilon (l + β) := hm ((add_lt_add_iff_left l).2 hh'β)
            have hηT : xoVal S l e' ∈ Tset (upsilon (l + h')) :=
              vzRem_T hτE hτ1 hξT hξ2 rfl (dvd_mul_right Om1 _) hη1
            have hηb : xoVal S l e' < upsilon (l + β) := Za.za_lt_next hτE hτ1 hηT hη1 hτb hbU
            have hyXY : xoVal S l (.th h' L' e') ∈ X ∪ Y := hqL _ (xoVal_mem _ hvL)
            have hyY : xoVal S l (.th h' L' e') ∈ Y := hyYof _ hyXY h' hby
            have hyY' : xoVal S l (.th h' L' e') ∈ Y' := hYY' hyY
            have hpe : xoPts S l (upsilon (l + β)) e' ⊆ xoPts S l (upsilon (l + β)) (.th h' L' e') :=
              yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)))
            have hηXY : xoVal S l e' ∈ X' ∪ Y' := hpL _ (hpe (xoVal_mem e' hηb))
            have hτXY : upsilon (l + h') ∈ X' ∪ Y' :=
              hpL _ (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hτb⟩)
            have hτY' : upsilon (l + h') ∈ Y' := by
              rcases Finset.mem_union.1 hτXY with hx | hy
              · exact absurd (hX' _ hx) (not_lt.2 (upsilon_normal.monotone le_self_add))
              · exact hy
            have hDτ := (hres h' hτY').2
            have hτ'1 : upsilon (μ + f h') < Om1 := (hDτ ▸ hLs.below _ hτY').trans hl1
            have hτ'E : InE (upsilon (μ + f h')) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
            have hDη1 : D (xoVal S l e') < Om1 := by
              rcases Finset.mem_union.1 hηXY with hx | hy
              · rw [hLs.fix _ hx]; exact (hX' _ hx).trans hl1
              · exact (hLs.below _ hy).trans hl1
            have hlvF := hLv' _ hyXY hyY' h' (xoVal S l L') (xoVal S l e') hby hys hM1' hη1 hξT hξ2 rfl
            have hlvT : YvLv S (· ∈ Tset (upsilon (l + h'))) (Om1 * xoVal S l L') :=
              (zf_lv_T S hτE hτ1 hM1' hη1 hξT hξ2 hbU hτb).mono fun p hp => hp.1
            have hξθ : Om1 * xoVal S l L' + xoVal S l e' < ConjT.th S := uzTBound (S := S) _ hτE hτ1 _ hξT hξ2
            have hMθ : Om1 * xoVal S l L' < ConjT.th S := le_self_add.trans_lt hξθ
            have hDE : InE (D (xoVal S l (.th h' L' e'))) := by
              rcases lt_or_ge (xoVal S l L') Uc.ucB with hMB | hMB
              · -- a level below `B₂`: the term `thc M (par η)`
                have hqB : Om1 * xoVal S l L' < Uc.ucB := Xe.xe_mul_lt_B hMB
                have hVT : Vc.VcLv (· ∈ Tset (upsilon (l + h'))) (Om1 * xoVal S l L') := by
                  cases hlvT with
                  | low _ hV => exact hV
                  | om hs _ heq => exact absurd hqB (not_lt.2 (heq ▸ yv_Om_ge_B hs))
                  | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                  | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                  | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                have hVF : Vc.VcLv (fun p => p ∈ X' ∪ Y' ∨ p < γ) (Om1 * xoVal S l L') := by
                  cases hlvF with
                  | low _ hV => exact hV
                  | om hs _ heq => exact absurd hqB (not_lt.2 (heq ▸ yv_Om_ge_B hs))
                  | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                  | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                  | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
                have hGT : Om1 * xoVal S l L' ∈ Tset (upsilon (l + h')) := vl_lv_mem hτE hτ1 hM1' hqB hVT
                have hZW : ZW (upsilon (l + h')) (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) :=
                  ⟨⟨hM1', hqB, hGT, hξT, Za.za_lt_vt_all hτE hτ1 hM1' hMθ hηT hη1 hξT⟩, trivial⟩
                have hWF : WFr (upsilon (l + h')) (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) := ⟨trivial, hη1⟩
                obtain ⟨e1, -, hZW'⟩ := hun _ hyY' h' hby hys (UnT.thc (xoVal S l L') (UnT.par (xoVal S l e'))) hZW hWF
                  hηXY ⟨hVF, trivial⟩ hηT ⟨hVT, trivial⟩ rfl
                obtain ⟨hN', -⟩ := hZW'
                rw [e1]
                refine ((vt_E_iff hτ'E hτ'1 hN'.mem ?_).2 ?_).2
                · exact hIndec.add_lt (hN'.qB.trans Uc.ucB_lt_Om2) (hDη1.trans Uc.uc_Om1_lt_Om2)
                · exact (le_mul_left Om1 (zero_lt_one.trans_le hN'.q1)).trans le_self_add
              · -- a level `≥ B₂`: the moving-level clause
                obtain ⟨q', -, hq'1, -, hq'θ, -, -, hmemT, hDy, -⟩ := hZa _ hyY' h' hby hys (xoVal S l L')
                  (UnT.par (xoVal S l e')) hM1' hMB hMθ hlvF hlvT trivial trivial hη1 hηXY trivial hηT trivial rfl
                rw [hDy]
                refine ((vt_E_iff hτ'E hτ'1 hmemT ?_).2 ?_).2
                · exact hIndec.add_lt (hq'θ.trans hθ2) (hDη1.trans Uc.uc_Om1_lt_Om2)
                · exact (le_mul_left Om1 (zero_lt_one.trans_le hq'1)).trans le_self_add

            have hξ1 : Om1 ≤ Om1 * xoVal S l L' + xoVal S l e' :=
              (le_mul_left Om1 (zero_lt_one.trans_le hM1')).trans le_self_add
            have hvE : InE (xoVal S l (.th h' L' e')) := ((vt_E_iff hτE hτ1 hξT hξ2).2 hξ1).2
            have hyA : xoVal S l (.th h' L' e') ∈ (↑(X' ∪ Y') : Set Ordinal.{0}) :=
              Finset.mem_coe.2 (hpL _ (xoVal_mem _ hvL))
            have hpos : (0 : Ordinal.{0}) < ω ^ xoVal S l (.th h' L' e') := opow_pos _ omega0_pos
            refine ZkSS.piece ⟨hv1, ?_, ?_⟩
            · have := (zkEx_step (· ∈ (↑(X' ∪ Y') : Set Ordinal.{0})) one_ne_zero zk_one_lt_omega hpos).2
                ⟨hyA, zkEx_zero _⟩
              rwa [mul_one, add_zero, hvE] at this
            · have hc := zkCnf_step D one_ne_zero zk_one_lt_omega hpos
              rw [mul_one, add_zero, hvE, zkCnf_zero, add_zero, mul_one] at hc
              rw [hc, hDL]
              exact (hDL ▸ hDE).symm
        | add _ _ ihs iht =>
          rename_i s t _ _
          intro hsz' hWL0 hRL hpL hqL
          have hszs : xoSize s ≤ n := by simp only [xoSize] at hsz'; omega
          have hszt : xoSize t ≤ n := by simp only [xoSize] at hsz'; omega
          have hps : xoPts S l (upsilon (l + β)) s ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
          have hpt : xoPts S l (upsilon (l + β)) t ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
          exact ZkSS.add (ihs hszs hWL0.1 hRL.1 (fun z hz => hpL z (hps hz)) (fun z hz => hqL z (hps hz)))
            (iht hszt hWL0.2 hRL.2.1 (fun z hz => hpL z (hpt hz)) (fun z hz => hqL z (hpt hz)))
      have keyPS : ∀ L₀ : XoE, ZkPS (zkMx S l μ f Y') (zkPf S l μ f Y') L₀ → xoSize L₀ ≤ n → XoWF S l β L₀ →
          XoR S l μ L₀ → (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X' ∪ Y') →
          (∀ z ∈ xoPts S l (upsilon (l + β)) L₀, z ∈ X ∪ Y) →
          ZkPS (fun N => xoVal S l N < Om1 ∧ ZkEx (· ∈ (↑(X' ∪ Y') : Set Ordinal.{0})) (xoVal S l N) ∧
            xoImg S l μ f N = zkCnf D (xoVal S l N)) (zkPf S l μ f Y') L₀ := by
        intro L₀ hN₀
        induction hN₀ with
        | pre h => intro _ _ _ _ _; exact ZkPS.pre h
        | addC _ ht ih =>
          rename_i s t _
          intro hsz' hWL0 hRL hpL hqL
          have hszs : xoSize s ≤ n := by simp only [xoSize] at hsz'; omega
          have hszt : xoSize t ≤ n := by simp only [xoSize] at hsz'; omega
          have hps : xoPts S l (upsilon (l + β)) s ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
          have hpt : xoPts S l (upsilon (l + β)) t ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
          exact ZkPS.addC (ih hszs hWL0.1 hRL.1 (fun z hz => hpL z (hps hz)) (fun z hz => hqL z (hps hz)))
            (key t ht hszt hWL0.2 hRL.2.1 (fun z hz => hpL z (hpt hz)) (fun z hz => hqL z (hpt hz)))
        | addL hs _ ih =>
          rename_i s t _
          intro hsz' hWL0 hRL hpL hqL
          have hszs : xoSize s ≤ n := by simp only [xoSize] at hsz'; omega
          have hszt : xoSize t ≤ n := by simp only [xoSize] at hsz'; omega
          have hps : xoPts S l (upsilon (l + β)) s ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
          have hpt : xoPts S l (upsilon (l + β)) t ⊆ xoPts S l (upsilon (l + β)) (.add s t) :=
            yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
          exact ZkPS.addL (key s hs hszs hWL0.1 hRL.1 (fun z hz => hpL z (hps hz)) (fun z hz => hqL z (hps hz)))
            (ih hszt hWL0.2 hRL.2.1 (fun z hz => hpL z (hpt hz)) (fun z hz => hqL z (hpt hz)))
      have hpL₁ : ∀ z ∈ xoPts S l (upsilon (l + β)) L₁, z ∈ X' ∪ Y' := fun z hz => hp₁ z (hsubL hz)
      have hqL₁ : ∀ z ∈ xoPts S l (upsilon (l + β)) L₁, z ∈ X ∪ Y := fun z hz => hq₁ z (hsubL hz)
      -- (3) sum trees of mixed pieces
      by_cases hSS : ZkSS (zkMx S l μ f Y') L₁
      · exact zk_ss_lev (G := D) (A := (↑(X' ∪ Y') : Set Ordinal.{0})) hLs.mono (fun _ hN => hN) (hid 0 hγU.1)
          (hid 0 hγU.1) (fun _ _ _ => rfl) L₁ (key L₁ hSS hszL hWL₁ hR₁.1 hpL₁ hqL₁) hlv
      -- (4) prefix levels with mixed pieces
      by_cases hPS : ZkPS (zkMx S l μ f Y') (zkPf S l μ f Y') L₁
      · exact zk_lev_psD H hl1 hX' hXγ hγμ hid hγU.1 (fun y hy => (hY' y hy).1) hLs.below
          (fun g hg => (hres g hg).2) hpi hmv hLs.mono hDA1 (fun _ hN => hN) L₁
          (keyPS L₁ hPS hszL hWL₁ hR₁.1 hpL₁ hqL₁) hθ₁ hlv
      -- (5) the rest
      exact hImg h₁ L₁ e₁ hW₁ hF₁ hR₁ hp₁ hM1₁ hPi hG hSS hPS hlv
  have hsb : upsilon (succ (l + h)) ≤ upsilon (l + β) :=
    upsilon_normal.monotone (Order.succ_le_of_lt ((add_lt_add_iff_left l).2 hW.2.1))
  have hv : xoVal S l (.th h L e) < upsilon (l + β) := hW.2.2.2.2.2.2.2.2.trans_le hsb
  exact zfDCl (Pt := fun z => z ∈ X ∪ Y) hl0 hβ0 hb1 hX' hY' hBμ hμ0 hLs.mono hLs.add hLs.below hres hold hun
    hLC hid hγU hZa _ (hImgAll (xoSize (.th h L e))) hLv' hPr' (Finset.mem_union_left _ hωX')
    (.th h L e) le_rfl hW hF hR (fun z hz => hsubXY z (hp z hz)) hp hv


end Googology.Trans.PoR.InaccPsi.R2.Zk
