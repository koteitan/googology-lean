import Googology.Trans.PoR.InaccPsi.R2.ZfLeaf

/-!
# The node clause of the moving-leaf shift at every node, levels `0` included, from the level image

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Za.zaDCl` proves `D(value) = image` at decompositions all of whose `ϑ`-nodes have good levels (`Za.ZaLevOK`), which
asks `1 ≤ val L`; a node of level `0` is never good (`Zf.zfNodesAll_false`).  Here the induction is redone with:

* nodes of level `0`: `ϑᵗ(0) = τ` (moved by the `υ`-clause of the shift) and `ϑᵗ(η) = ϑᵗ(1 + (η − 1))` (the term
  `th1 (par (η − 1))` of `Un.UnC`, moved by the term clause), the level term has image `0` (`zf_img_zero`);
* nodes of level `≥ 1`: as in `Za.zaDCl` (the term `thc M (par η)` below `B₂`, `Za.ZaHiD` from `B₂` on), with the
  leaves of the level in the configuration (hypothesis `hLv`), in `T^{υ_{λ+h}}` (`Zf.zf_lv_T`), and the **level
  image** `yvSub D (Ω₁·val L) = Ω₁·img L` (`ZfImgCl`, a statement).

* `zf_psi_zero`, `zf_psi_eq_zero`, `zf_vr_zero`, `zf_img_zero` (**a level term of value `0` has image `0`**);
* `ZfImgCl` (**the level-image clause**, a statement);
* `zfDCl` (**`D(value) = image` at every restricted well-formed decomposition with an `old` / `th` / `add` skeleton**,
  given the clauses of the shift, `ZfImgCl`, the leaves of every node level in the configuration (`hLv`), the
  predecessor `η − 1` of the countable part of every node of level `0` in the configuration (`hPr`), and `ω` in it).

No new axiom.  New definition: `ZfImgCl` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Un
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- `ψ_0(a) = 0`. -/
theorem zf_psi_zero (a : Ordinal.{0}) : S.psi a 0 = 0 := by
  rw [InaccSeq.psi_eq]
  refine le_antisymm (csInf_le' ⟨InaccSeq.CSet.zero_mem a 0, fun x _ hx => absurd hx (not_lt.2 zero_le)⟩) zero_le

/-- `ψ_p(a) = 0 ⇒ p = 0`. -/
theorem zf_psi_eq_zero {a p : Ordinal.{0}} (h : S.psi a p = 0) : p = 0 := by
  by_contra hp
  rw [InaccSeq.psi_eq] at h
  have hne : {b | p ∈ S.CSet a b ∧ ∀ x ∈ S.CSet a b, x < p → x < b}.Nonempty :=
    ⟨p + 1, InaccSeq.CSet.of_lt (Order.lt_add_one_iff.2 le_rfl), fun x _ hx => hx.trans (Order.lt_add_one_iff.2 le_rfl)⟩
  have hmem := csInf_mem hne
  rw [h] at hmem
  exact absurd (hmem.2 0 (InaccSeq.CSet.zero_mem a 0) (pos_iff_ne_zero.2 hp)) (lt_irrefl 0)

theorem zf_ups_pos {l h : Ordinal.{0}} (hl0 : 0 < l) : 0 < upsilon (l + h) :=
  lt_of_le_of_lt zero_le (upsilon_normal.strictMono (hl0.trans_le le_self_add))

/-- An old decomposition of value `0` has image `0`. -/
theorem zf_vr_zero {l β μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hl0 : 0 < l)
    (hB : Bases (upsilon μ) (upsilon l)) :
    ∀ E : Vr.VrE, Vr.VrWF l β E → Vr.vrVal l E = 0 → Vr.vrImg l μ f E = 0
  | .lo c, _, hv => by
    show pi (upsilon μ) (upsilon l) c = 0
    have hc : c = 0 := hv
    rw [hc]; exact pi_lt hB (lt_of_le_of_lt zero_le (omega0_lt_inE hB.1))
  | .sg h y, hW, hv => by
    have hy : y = 0 := hv
    exact absurd (hW.2.2.1.trans_eq hy) (not_le.2 (zf_ups_pos hl0))
  | .ub h t, hW, hv => by
    have hy : Ub.UbT.ev (upsilon (l + h)) t = 0 := hv
    exact absurd (hW.2.2.2.2.2.1.trans_eq hy) (not_le.2 (zf_ups_pos hl0))
  | .tm h t Lf δ, hW, hv => by
    have hy : UnT.ev (upsilon (l + h)) t = 0 := hv
    exact absurd (hW.2.2.2.2.2.2.2.2.1.trans_eq hy) (not_le.2 (zf_ups_pos hl0))
  | .add s t, hW, hv => by
    have hv' : Vr.vrVal l s + Vr.vrVal l t = 0 := hv
    obtain ⟨hs, ht⟩ := Ordinal.add_eq_zero_iff.1 hv'
    show Vr.vrImg l μ f s + Vr.vrImg l μ f t = 0
    rw [zf_vr_zero f hl0 hB s hW.1 hs, zf_vr_zero f hl0 hB t hW.2 ht, add_zero]

/-- **A level term of value `0` has image `0`.** -/
theorem zf_img_zero {l β μ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) (hl0 : 0 < l)
    (hB : Bases (upsilon μ) (upsilon l)) :
    ∀ L : XoE, XoWF S l β L → xoVal S l L = 0 → xoImg S l μ f L = 0 := by
  intro L
  induction L with
  | old E => exact fun hW hv => zf_vr_zero f hl0 hB E hW hv
  | th h L e _ _ =>
    intro hW hv
    exact absurd (hW.2.2.2.2.2.2.2.1.trans_eq hv) (not_le.2 (zf_ups_pos hl0))
  | add s t ihs iht =>
    intro hW hv
    have hv' : xoVal S l s + xoVal S l t = 0 := hv
    obtain ⟨hs, ht⟩ := Ordinal.add_eq_zero_iff.1 hv'
    show xoImg S l μ f s + xoImg S l μ f t = 0
    rw [ihs hW.1 hs, iht hW.2 ht, add_zero]
  | lc M => intro _ hv; exact hv
  | phi a b _ _ =>
    intro _ hv
    exact absurd hv veblen_pos.ne'
  | om a iha =>
    intro hW hv
    have hv' : Om (xoVal S l a) = 0 := hv
    have ha : xoVal S l a = 0 := by
      by_contra ha; exact absurd hv' (Om_pos ha).ne'
    show Om (xoImg S l μ f a) = 0
    rw [iha hW ha, Om_zero]
  | coll p e ihp _ =>
    intro hW hv
    have hv' : S.psi (xoVal S l e) (xoVal S l p) = 0 := hv
    have hp : xoVal S l p = 0 := zf_psi_eq_zero hv'
    show S.psi (xoImg S l μ f e) (xoImg S l μ f p) = 0
    rw [ihp hW.1 hp, zf_psi_zero]

/-- **The level-image clause** (statement): at every restricted well-formed node of the configuration whose level has
value `≥ 1` and leaves in `X ∪ Y ∪ γ`, the leaf substitution of the level value is the image of the level term. -/
def ZfImgCl (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) (f D : Ordinal.{0} → Ordinal.{0})
    (X Y : Finset Ordinal.{0}) : Prop :=
  ∀ h : Ordinal.{0}, ∀ L e : XoE, XoWF S l β (.th h L e) → XoTopF e → XoR S l μ (.th h L e) →
    (∀ z ∈ xoPts S l (upsilon (l + β)) (.th h L e), z ∈ X ∪ Y) → 1 ≤ xoVal S l L →
    YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * xoVal S l L) →
    yvSub S D (Om1 * xoVal S l L) = Om1 * xoImg S l μ f L

/-- **The node clause at every decomposition** (levels `0` included), from the clauses of the shift, the level image,
the leaves of the node levels in the configuration, the predecessors of the countable parts of the level-`0` nodes,
and `ω` in the configuration. -/
theorem zfDCl {l β μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {X Y : Finset Ordinal.{0}}
    {Os : Finset Ordinal.{0}} {Pt : Ordinal.{0} → Prop}
    (hl0 : 0 < l) (hβ0 : 0 < β) (hb1 : upsilon (l + β) ≤ Om1) (hXl : ∀ x ∈ X, x < upsilon l)
    (hYl : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) (hB : Bases (upsilon μ) (upsilon l)) (hμ0 : 0 < μ)
    (hmono : StrictMonoOn D ↑(X ∪ Y))
    (hadd : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z))
    (hbelow : ∀ y ∈ Y, D y < upsilon l)
    (hres : ∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g))
    (hold : ∀ E : Vr.VrE, Vr.VrWF l β E → (∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y) →
      D (Vr.vrVal l E) = Vr.vrImg l μ f E)
    (hUn : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UnC, ZW (upsilon (l + g)) t →
        WFr (upsilon (l + g)) t → UnT.Lv (· ∈ X ∪ Y) t → ZL (fun p => p ∈ X ∪ Y ∨ p < γ) t →
        UnT.Lv (· ∈ Tset (upsilon (l + g))) t → ZL (· ∈ Tset (upsilon (l + g))) t →
        UnT.ev (upsilon (l + g)) t = y →
        D y = UnT.ev (upsilon (μ + f g)) (vmap D t) ∧ WFr (upsilon (μ + f g)) (vmap D t) ∧
          ZW (upsilon (μ + f g)) (vmap D t))
    (hLC : VlLC (fun p => p ∈ X ∪ Y ∨ p < γ) D) (hid : ∀ x, x < γ → D x = x) (hγU : UpsPt γ)
    (hZa : Za.ZaHiD S l μ γ f D X Y) (hImg : ZfImgCl S l β μ γ f D X Y)
    (hLv : ∀ y, Pt y → y ∈ Y → ∀ h M η, upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) → 1 ≤ M → η < Om1 →
      Om1 * M + η ∈ Tset (upsilon (l + h)) → Om1 * M + η < OmTwo → vt (upsilon (l + h)) (Om1 * M + η) = y →
      YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * M))
    (hPr : ∀ y, Pt y → y ∈ Y → ∀ h η, upsilon (l + h) ≤ y → y < upsilon (succ (l + h)) → 1 ≤ η → η < Om1 →
      η ∈ Tset (upsilon (l + h)) → vt (upsilon (l + h)) η = y → η - 1 ∈ X ∪ Y)
    (hω : ω ∈ X ∪ Y) :
    ∀ E : XoE, XoWF S l β E → XoTopF E → XoR S l μ E → (∀ z ∈ xoPts S l (upsilon (l + β)) E, z ∈ X ∪ Y) →
      (∀ z ∈ xoPts S l (upsilon (l + β)) E, Pt z) →
      xoVal S l E < upsilon (l + β) → D (xoVal S l E) = xoImg S l μ f E := by
  have hm := upsilon_normal.strictMono
  have hωγ : ω < γ := omega0_lt_inE (upsPt_inE hγU)
  set b := upsilon (l + β) with hbdef
  intro E
  induction E with
  | old E =>
    intro hW _ _ hp _ _
    have hp' : ∀ z ∈ Vr.vrPts l E, z ∈ X ∪ Y := fun z hz =>
      hp z (Finset.mem_filter.2 ⟨hz, Vr.vrPts_lt hβ0 E hW z hz⟩)
    exact hold E hW hp'
  | th h L e _ ihe =>
    intro hW hF hR hp hq hv
    have hW0 := hW
    obtain ⟨h0, hhβ, hWL, hWe, hη1, hξT, hξ2, hby, hys⟩ := hW
    set M := xoVal S l L with hMdef
    set η := xoVal S l e with hηdef
    set τ := upsilon (l + h) with hτdef
    have hτU : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτE : InE τ := upsPt_inE hτU
    have hsb : upsilon (succ (l + h)) ≤ b := hm.monotone (Order.succ_le_of_lt (by
      exact (add_lt_add_iff_left l).2 hhβ))
    have hyb : vt τ (Om1 * M + η) < b := hys.trans_le hsb
    have hτ1 : τ < Om1 := (hby.trans_lt hyb).trans_le hb1
    have hηT : η ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 rfl (dvd_mul_right Om1 M) hη1
    have hτb : τ < b := hm ((add_lt_add_iff_left l).2 hhβ)
    have hbU : UpsPt b := upsPt_upsilon (hl0.trans_le le_self_add)
    have hηb : η < b := Za.za_lt_next hτE hτ1 hηT hη1 hτb hbU
    have hpe : xoPts S l b e ⊆ xoPts S l b (.th h L e) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)))
    have IHe := ihe hWe hF hR.2 (fun z hz => hp z (hpe hz)) (fun z hz => hq z (hpe hz)) hηb
    have hyP : Pt (vt τ (Om1 * M + η)) := hq _ (xoVal_mem (.th h L e) hyb)
    have hηXY : η ∈ X ∪ Y := hp _ (hpe (xoVal_mem e hηb))
    have hyXY : vt τ (Om1 * M + η) ∈ X ∪ Y := hp _ (xoVal_mem (.th h L e) hyb)
    have hlτ : upsilon l ≤ τ := hm.monotone le_self_add
    have hyY : vt τ (Om1 * M + η) ∈ Y := by
      rcases Finset.mem_union.1 hyXY with hx | hy
      · exact absurd (hXl _ hx) (not_lt.2 (hlτ.trans hby))
      · exact hy
    have hξθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτE hτ1 _ hξT hξ2
    have hMθ : Om1 * M < ConjT.th S := le_self_add.trans_lt hξθ
    have hτ'E : InE (upsilon (μ + f h)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
    show D (vt τ (Om1 * M + η)) = vt (upsilon (μ + f h)) (Om1 * xoImg S l μ f L + xoImg S l μ f e)
    rw [← IHe]
    rcases eq_or_ne M 0 with hM0 | hM0
    · -- a level `0`
      have hL0 : xoImg S l μ f L = 0 := zf_img_zero f hl0 hB L hWL hM0
      rw [hL0, mul_zero, zero_add]
      have hval : vt τ (Om1 * M + η) = vt τ η := by rw [hM0, mul_zero, zero_add]
      rcases eq_or_ne η 0 with hη0 | hη0
      · -- `ϑᵗ(0) = τ`
        have hτXY : τ ∈ X ∪ Y := hp _ (Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hτb⟩)
        have hτY : τ ∈ Y := by
          rcases Finset.mem_union.1 hτXY with hx | hy
          · exact absurd (hXl _ hx) (not_lt.2 hlτ)
          · exact hy
        have hDτ := (hres h hτY).2
        have hτ'1 : upsilon (μ + f h) < Om1 := (hDτ ▸ hbelow τ hτY).trans hB.2.2.2
        rw [hval, hη0, Si.siVt_zero hτE hτ1, hid 0 (lt_of_le_of_lt zero_le hωγ), Si.siVt_zero hτ'E hτ'1]
        exact hDτ
      · -- `ϑᵗ(η) = ϑᵗ(1 + (η − 1))`, the term `th1 (par (η − 1))`
        have h1η : 1 ≤ η := Order.one_le_iff_ne_zero.2 hη0
        have e1 : 1 + (η - 1) = η := Ordinal.add_sub_cancel_of_le h1η
        have hη'T : η - 1 ∈ Tset τ := zf_T_init hτE hτ1 hηT hη1 (Ordinal.sub_le_self _ _)
        have hη'1 : η - 1 < Om1 := (Ordinal.sub_le_self _ _).trans_lt hη1
        have hξT0 : η ∈ Tset τ := hηT
        have hη'XY : η - 1 ∈ X ∪ Y := hPr _ hyP hyY h η hby hys h1η hη1 hξT0 hval.symm
        obtain ⟨e2, -, -⟩ := hUn _ hyY h hby hys (UnT.th1 (UnT.par (η - 1)))
          (by simp [ZW]) (by simp [WFr, UnT.ev]; exact hη'1)
          (by simp only [UnT.Lv]; exact hη'XY) (by simp [ZL])
          (by simp only [UnT.Lv]; exact hη'T) (by simp [ZL]) (by show vt τ (1 + (η - 1)) = _; rw [e1, hval])
        rw [e2]
        show vt (upsilon (μ + f h)) (1 + D (η - 1)) = vt (upsilon (μ + f h)) (D η)
        congr 1
        rcases lt_or_ge η ω with hηω | hηω
        · have hη'ω : η - 1 < ω := (Ordinal.sub_le_self _ _).trans_lt hηω
          rw [hid _ (hη'ω.trans hωγ), hid _ (hηω.trans hωγ), e1]
        · have hinf : η - 1 = η := by
            have hη'ω : ω ≤ η - 1 := by
              by_contra hc
              push Not at hc
              have : 1 + (η - 1) < ω := by
                obtain ⟨n, hn⟩ := lt_omega0.1 hc
                rw [hn]; exact_mod_cast natCast_lt_omega0 (1 + n)
              rw [e1] at this; exact absurd hηω (not_le.2 this)
            have h2 : 1 + (η - 1) = η - 1 := Ordinal.one_add_of_omega0_le hη'ω
            rw [e1] at h2; exact h2.symm
          rw [hinf]
          have hDη : ω ≤ D η := by
            rcases lt_or_ge η γ with hηγ | hηγ
            · rw [hid η hηγ]; exact hηω
            · have hlt : D ω < D η := hmono hω hηXY (hωγ.trans_le hηγ)
              rw [hid ω hωγ] at hlt; exact hlt.le
          exact Ordinal.one_add_of_omega0_le hDη
    · -- a level `≥ 1`
      have hM1 : 1 ≤ M := Order.one_le_iff_ne_zero.2 hM0
      have hlvF : YvLv S (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * M) :=
        hLv _ hyP hyY h M η hby hys hM1 hη1 hξT hξ2 rfl
      have hlvT : YvLv S (· ∈ Tset τ) (Om1 * M) :=
        (zf_lv_T S hτE hτ1 hM1 hη1 hξT hξ2 hbU hτb).mono fun p hp => hp.1
      have hsubeq := hImg h L e hW0 hF hR hp hM1 hlvF
      rw [← hsubeq]
      rcases lt_or_ge M Uc.ucB with hMB | hMB
      · -- a level below `B₂`: the term `thc M (par η)`
        have hqB : Om1 * M < Uc.ucB := Xe.xe_mul_lt_B hMB
        have hVT : Vc.VcLv (· ∈ Tset τ) (Om1 * M) := by
          cases hlvT with
          | low _ hV => exact hV
          | om hs _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs))
          | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
          | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
          | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        have hVF : Vc.VcLv (fun p => p ∈ X ∪ Y ∨ p < γ) (Om1 * M) := by
          cases hlvF with
          | low _ hV => exact hV
          | om hs _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs))
          | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
          | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
          | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
        have hGT : Om1 * M ∈ Tset τ := vl_lv_mem hτE hτ1 hM1 hqB hVT
        have hZW : ZW τ (UnT.thc M (UnT.par η)) :=
          ⟨⟨hM1, hqB, hGT, hξT, Za.za_lt_vt_all hτE hτ1 hM1 hMθ hηT hη1 hξT⟩, trivial⟩
        have hWF : WFr τ (UnT.thc M (UnT.par η)) := ⟨trivial, hη1⟩
        obtain ⟨e1, -, -⟩ := hUn _ hyY h hby hys (UnT.thc M (UnT.par η)) hZW hWF hηXY ⟨hVF, trivial⟩ hηT
          ⟨hVT, trivial⟩ rfl
        obtain ⟨e2, -⟩ := hLC M hM1 hqB hVF
        rw [e1, yvSub_low D hqB, ← e2]
        rfl
      · -- a level `≥ B₂`: the moving-level clause at the term `par η`
        obtain ⟨q', e1, -, -, -, -, -, -, hnode, -⟩ := hZa _ hyY h hby hys M (UnT.par η) hM1 hMB hMθ hlvF hlvT
          trivial trivial hη1 hηXY trivial hηT trivial rfl
        rw [hnode, e1]
        rfl
  | add s t ihs iht =>
    intro hW hF hR hp hq hv
    have hv' : xoVal S l s + xoVal S l t < b := hv
    have hvs : xoVal S l s < b := le_self_add.trans_lt hv'
    have hvt : xoVal S l t < b := le_add_self.trans_lt hv'
    have hps : xoPts S l b s ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))
    have hpt : xoPts S l b t ⊆ xoPts S l b (.add s t) :=
      yq_pts_sub (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    have es := ihs hW.1 hF.1 hR.1 (fun z hz => hp z (hps hz)) (fun z hz => hq z (hps hz)) hvs
    have et := iht hW.2 hF.2 hR.2.1 (fun z hz => hp z (hpt hz)) (fun z hz => hq z (hpt hz)) hvt
    have hsum := (hadd _ (hp _ (hps (xoVal_mem s hvs))) _ (hp _ (hpt (xoVal_mem t hvt))) _
      (hp _ (xoVal_mem (.add s t) hv))).1 rfl
    show D (xoVal S l s + xoVal S l t) = xoImg S l μ f s + xoImg S l μ f t
    rw [← es, ← et, hsum]; rfl
  | lc _ => intro _ hF; exact hF.elim
  | phi _ _ _ _ => intro _ hF; exact hF.elim
  | om _ _ => intro _ hF; exact hF.elim
  | coll _ _ _ _ => intro _ hF; exact hF.elim

end Googology.Trans.PoR.InaccPsi.R2.Zf
