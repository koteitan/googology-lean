import Googology.Trans.PoR.InaccPsi.R2.WhGW

/-!
# WhSucc: THE SUCCESSOR STEP `ℓ ↦ ℓ + Ω₁` OF THE LEVEL-CODE INDUCTION, GENERIC IN `ℓ`

An ENTRY at a level `ℓ` (`WhAt ℓ K V`) is a package `K` (`Hn.HnPk`) at the level `ℓ`, read `rdc ℓ x` above its gate
`g ≤ gtc ℓ` (and every `ε`-number above `g` is above `gtc ℓ`), and a system `V` over `G` with the bound
`φ(ℓ, G+1)`, base gate `≤ gtc ℓ`, which is a START over `G` at `K` (`Hn.HnWShape (whGW K.Λ) 0 V`).  `WhExt` is the
extension statement of the skeleton (`Hn.HnkExt` of the packages, growing bound, readings and gates agree).

* `wh_rdc_add_Om1` (**`rdc (a + Ω₁) x = rdc a x + x`** for `Ω₁ ∣ a`), `wh_gtc_le_add_Om1`, `wh_gtc_add_Om1_lt`,
  `wh_lev_succ_le`, `wh_rdc_step` (**`rdc a x + x ≤ rdc b x`** for levels `a < b` with gates below `x`);
* `WhAt`, `WhExt`, `whAt_base` (**the entry at `Ω₁`**: `Hn.hnPk1`, `Hg.hgU`);
* `whSuccK`, `whSuccV`, `whStepSucc` (**THE SUCCESSOR STEP**: an entry at `ℓ'` gives an entry at `ℓ' + Ω₁` that
  extends it and everything it extends).

No new axiom.  New definitions: `WhAt`, `WhExt`, `whSuccV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wh

open Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Codes: adding `Ω₁` -/

theorem wh_log_ge_one {a : Ordinal.{0}} (h1 : Om1 ≤ a) : 1 ≤ log Om1 a :=
  (opow_le_iff_le_log wh_one_lt_Om1 (wh_Om1_pos.trans_le h1).ne').1 (by rw [opow_one]; exact h1)

/-- The parts of a nonzero multiple of `Ω₁`: the rest is a multiple of `Ω₁`, and `Ω₁ < Ω₁^L` when the rest is
nonzero. -/
theorem wh_mul_parts {a : Ordinal.{0}} (ha0 : a ≠ 0) (hd : Om1 ∣ a) :
    1 ≤ log Om1 a ∧ Om1 ∣ a % Om1 ^ log Om1 a := by
  have h1 : Om1 ≤ a := Ordinal.le_of_dvd ha0 hd
  have hL := wh_log_ge_one h1
  refine ⟨hL, ?_⟩
  have hdv : Om1 ∣ Om1 ^ log Om1 a * (a / Om1 ^ log Om1 a) := by
    refine Dvd.dvd.mul_right ?_ _
    have := opow_dvd_opow Om1 hL; rwa [opow_one] at this
  exact (Ordinal.dvd_add_iff hdv).1 (by rw [(parts ha0).2.2.2.1]; exact hd)

/-- **`rdc (a + Ω₁) x = rdc a x + x`** for a multiple `a` of `Ω₁` below `ε_{Ω₁+1}`. -/
theorem wh_rdc_add_Om1 : ∀ a, a < gfE → Om1 ∣ a → ∀ x, rdc (a + Om1) x = rdc a x + x ∧
    gtc a ≤ gtc (a + Om1) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW hd x
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add, rdc_zero, zero_add, gtc_zero]; exact ⟨(rdc_Om1 x).1, zero_le⟩
  obtain ⟨hd0, hdO, hr, hdec, hrl, _⟩ := parts ha0
  obtain ⟨hL1, hrd⟩ := wh_mul_parts ha0 hd
  have hLW : log Om1 a < gfE := (log_lt ha0 haW).trans haW
  set L := log Om1 a
  set d := a / Om1 ^ L
  set r := a % Om1 ^ L
  have hA := rdc_cnf hLW hd0.ne' hdO hr x
  rw [hdec] at hA
  rcases eq_or_ne r 0 with hr0 | hr0
  · rcases eq_or_ne L 1 with hL | hL
    · -- `a = Ω₁·d`, `a + Ω₁ = Ω₁·(d+1)`
      have hd1 : d + 1 < Om1 := gl_Om1_lim.add_one_lt hdO
      have hr1 : (0 : Ordinal.{0}) < Om1 ^ (1 : Ordinal.{0}) := opow_pos _ wh_Om1_pos
      have hB := rdc_cnf (l := 1) (q := d + 1) (r := 0) (by rw [← hL]; exact hLW) (by simp) hd1 hr1 x
      have e1 : a + Om1 = Om1 ^ (1 : Ordinal.{0}) * (d + 1) + 0 := by
        rw [← hdec, hr0, hL, add_zero, add_zero, opow_one, mul_add_one]
      rw [e1, hB.1, hB.2, hA.1, hA.2, hr0, hL]
      refine ⟨by rw [mul_add_one, rdc_zero, add_zero, add_zero, (rdc_const wh_one_lt_Om1 x).1, opow_one], ?_⟩
      exact max_le_max (max_le_max le_rfl (le_self_add)) le_rfl
    · have hL2 : Om1 < Om1 ^ L := by
        calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ < Om1 ^ L := (opow_lt_opow_iff_right wh_one_lt_Om1).2 (lt_of_le_of_ne hL1 (Ne.symm hL))
      have hB := rdc_cnf hLW hd0.ne' hdO hL2 x
      have e1 : a + Om1 = Om1 ^ L * d + Om1 := by rw [← hdec, hr0, add_zero]
      rw [e1, hB.1, hB.2, hA.1, hA.2, hr0, rdc_zero, add_zero, (rdc_Om1 x).1, gtc_zero]
      exact ⟨rfl, max_le_max le_rfl zero_le⟩
  · have hrO : Om1 ≤ r := Ordinal.le_of_dvd hr0 hrd
    have hrW : r < gfE := hrl.trans haW
    have hr2 : r + Om1 < Om1 ^ L := (Om1_pow_indec L).add_lt hr (hrO.trans_lt hr)
    have hB := rdc_cnf hLW hd0.ne' hdO hr2 x
    obtain ⟨i1, i2⟩ := IH r hrl hrW hrd x
    have e1 : a + Om1 = Om1 ^ L * d + (r + Om1) := by rw [← hdec, add_assoc]
    rw [e1, hB.1, hB.2, hA.1, hA.2, i1, add_assoc]
    exact ⟨rfl, max_le_max le_rfl i2⟩

/-- **`gtc (a + Ω₁) < Z`** from `gtc a < Z` at an additively closed `Z > 1`. -/
theorem wh_gtc_add_Om1_lt {Z a : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (h1 : 1 < Z)
    (haW : a < gfE) (hg : gtc a < Z) : gtc (a + Om1) < Z :=
  gtc_add hZ a Om1 haW Om1_lt_eW hg (by rw [(rdc_Om1 0).2]; exact h1)

theorem wh_gtc_add_Om1_ltE {x a : Ordinal.{0}} (hx : InE x) (haW : a < gfE) (hg : gtc a < x) :
    gtc (a + Om1) < x :=
  wh_gtc_add_Om1_lt (fun _ _ hu hv => (inE_indec hx).add_lt hu hv) (one_lt_omega0.trans (omega0_lt_inE hx)) haW hg

/-- **Levels increase by at least `Ω₁`.** -/
theorem wh_lev_succ_le {a b : Ordinal.{0}} (ha : Om1 ∣ a) (hb : Om1 ∣ b) (h : a < b) : a + Om1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have hmn : m < n := (mul_lt_mul_iff_right₀ wh_Om1_pos).1 h
  rw [← mul_add_one]; exact mul_le_mul_left' (Order.add_one_le_of_lt hmn) _

/-- **`rdc a x + x ≤ rdc b x`** for levels `a < b` with gates below the `ε`-number `x`. -/
theorem wh_rdc_step {a b x : Ordinal.{0}} (hx : InE x) (ha : Om1 ∣ a) (hb : Om1 ∣ b) (hab : a < b)
    (hbW : b < gfE) (hga : gtc a < x) (hgb : gtc b < x) : rdc a x + x ≤ rdc b x := by
  have haW := hab.trans hbW
  rw [← (wh_rdc_add_Om1 a haW ha x).1]
  exact rdc_le_mono hx hbW (wh_lev_succ_le ha hb hab) hgb (wh_gtc_add_Om1_ltE hx haW hga)

/-! ## Entries -/

/-- **AN ENTRY AT THE LEVEL `ℓ`**: the package `K` at `ℓ` (read `rdc ℓ x` above its gate `g ≤ gtc ℓ`, every
`ε`-number above `g` is above `gtc ℓ`) and a system `V` over `G` with the bound `φ(ℓ, G+1)` and base gate
`≤ gtc ℓ` that is a START over `G` at `K`. -/
def WhAt (ℓ : Ordinal.{0}) (K : HnPk) (V : HgVD) : Prop :=
  K.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → K.Λ.g < x → K.Λ.l x = rdc ℓ x) ∧
    V.B = veblen ℓ (gcG 0 + 1) ∧ V.γ ≤ gtc ℓ ∧ K.Λ.g ≤ gtc ℓ ∧
    (∀ x, InE x → x < Om1 → K.Λ.g < x → gtc ℓ < x) ∧ ∃ hN : WhNB K.Λ, HnWShape (whGW K.Λ hN) 0 V

/-- **The extension statement** (as in the skeleton): the packages extend, the bound grows, the readings and gates
of the systems agree below the smaller bound. -/
def WhExt (K' : HnPk) (V' : HgVD) (K : HnPk) (V : HgVD) : Prop :=
  HnkExt K' K ∧ V'.B < V.B ∧ ∀ c x, c < V'.B → V.R c x = V'.R c x ∧ V.g c = V'.g c

/-- **THE ENTRY AT THE LEVEL `Ω₁`**: `Hn.hnPk1` and `Hg.hgU`. -/
theorem whAt_base : WhAt Om1 hnPk1 hgU := by
  refine ⟨rfl, fun x _ _ _ => (rdc_Om1 x).1.symm, hgU_B, ?_, ?_, fun x hx _ _ => ?_, wh_hnL1_NB, whU_shape⟩
  · rw [hgU_γ]; exact zero_le
  · show (0 : Ordinal.{0}) ≤ _; exact zero_le
  · rw [(rdc_Om1 0).2]; exact one_lt_omega0.trans (omega0_lt_inE hx)

/-! ## The successor step -/

section Succ

variable {ℓ' : Ordinal.{0}} {K' : HnPk} {V' : HgVD}

theorem whS_W (h3 : ℓ' + Om1 < gfE) : ℓ' < gfE := (lt_add_of_pos_right _ wh_Om1_pos).trans h3

/-- The outer-field bound of the next level datum. -/
theorem whS_NB (h2 : Om1 ∣ ℓ') (h3 : ℓ' + Om1 < gfE) (hat : WhAt ℓ' K' V') : WhNB K'.Λ.succ :=
  fun x hx hx1 hg => by
  show K'.Λ.l x + x + x < eN x
  have hW := whS_W h3
  rw [hat.2.1 x hx hx1 hg, ← (wh_rdc_add_Om1 ℓ' hW h2 x).1]
  exact (inE_indec (eN_E x)).add_lt
    (rdc_lt_eN hx _ (wh_gtc_add_Om1_ltE hx hW (hat.2.2.2.2.2.1 x hx hx1 hg))) (lt_eN x)

/-- **The next system**: the union over `G` of the levels `ℓ' + κ`, `κ < Ω₁`, started at `V'`. -/
noncomputable def whSuccV (hat : WhAt ℓ' K' V') : HgVD :=
  hnwU (whGW K'.Λ hat.2.2.2.2.2.2.choose) K'.St0 K'.h0 V' hat.2.2.2.2.2.2.choose_spec

theorem whSuccV_B (hat : WhAt ℓ' K' V') : (whSuccV hat).B = veblen (ℓ' + Om1) (gcG 0 + 1) := by
  show hdNx (K'.Λ.L + Om1) (gcG 0) = _
  rw [hdNx_fixP (hnG_FP K'.Λ), hat.1]

/-- **The next entry is an entry at `ℓ' + Ω₁`.** -/
theorem whSucc_at (h2 : Om1 ∣ ℓ') (h3 : ℓ' + Om1 < gfE) (hat : WhAt ℓ' K' V') :
    WhAt (ℓ' + Om1) K'.succ (whSuccV hat) := by
  have hW := whS_W h3
  obtain ⟨e1, e2, e3, e4, e5, e6, hN, hsh⟩ := hat
  have hga := (wh_rdc_add_Om1 ℓ' hW h2 0).2
  refine ⟨by show K'.Λ.L + Om1 = _; rw [e1], fun x hx hx1 hg => ?_, whSuccV_B _, ?_, ?_,
    fun x hx hx1 hg => wh_gtc_add_Om1_ltE hx hW (e6 x hx hx1 hg), whS_NB h2 h3 ⟨e1, e2, e3, e4, e5, e6, hN, hsh⟩,
    whGU_shape K'.Λ _ _ K'.St0 K'.h0 V' _⟩
  · show K'.Λ.l x + x = _
    rw [e2 x hx hx1 hg, (wh_rdc_add_Om1 ℓ' hW h2 x).1]
  · show K'.Λ.g ≤ _; exact e5.trans hga
  · show K'.Λ.g ≤ _; exact e5.trans hga

/-- **The next entry extends the entry at `ℓ'`.** -/
theorem whSucc_ext (hat : WhAt ℓ' K' V') : WhExt K' V' K'.succ (whSuccV hat) := by
  set hsh := hat.2.2.2.2.2.2.choose_spec
  refine ⟨?_, ?_, fun c x hc => ⟨hnwU_R0 _ _ _ _ hsh hc x, hnwU_g0 _ _ _ _ hsh hc⟩⟩
  · intro hg' hL' hl' Q U hU c x hc
    have hsh' := hnw_shape_dn Q (K'.h0 Q.dn U hU)
    exact ⟨hnwU_R0 Q.toW K'.St0 K'.h0 _ hsh' hc x, hnwU_g0 Q.toW K'.St0 K'.h0 _ hsh' hc⟩
  · rw [whSuccV_B hat, hat.2.2.1]
    exact hd_veb_left_lt (lt_add_of_pos_right _ wh_Om1_pos) _

/-- **The next entry extends every entry that the entry at `ℓ'` extends.** -/
theorem whSucc_ext_lt (h2 : Om1 ∣ ℓ') (h3 : ℓ' + Om1 < gfE) (hat : WhAt ℓ' K' V') {ℓ'' : Ordinal.{0}}
    (hlt : ℓ'' < ℓ') (hd'' : Om1 ∣ ℓ'') {K'' : HnPk} {V'' : HgVD}
    (hat'' : WhAt ℓ'' K'' V'') (hext : WhExt K'' V'' K' V') : WhExt K'' V'' K'.succ (whSuccV hat) := by
  have hW := whS_W h3
  obtain ⟨n1, n2, -, -, -, n6, -⟩ := hat''
  obtain ⟨s1, s2, s3⟩ := whSucc_ext hat
  have e1 := hat.1
  have e2 := hat.2.1
  have e6 := hat.2.2.2.2.2.1
  obtain ⟨x1, x2, x3⟩ := hext
  refine ⟨?_, x2.trans s2, fun c x hc => ?_⟩
  · intro hg' hL' hl' Q U hU c x hc
    have hsh' := hnw_shape_dn Q (K'.h0 Q.dn U hU)
    have hLa : K''.Λ.L + Om1 ≤ K'.Λ.L := by rw [n1, e1]; exact wh_lev_succ_le hd'' h2 hlt
    have hla : ∀ x, InE x → x < Om1 → K'.Λ.g < x → K''.Λ.l x + x ≤ K'.Λ.l x := fun x hx hx1 hgx => by
      have hgx'' : K''.Λ.g < x := hg'.trans_lt hgx
      rw [n2 x hx hx1 hgx'', e2 x hx hx1 hgx]
      exact wh_rdc_step hx hd'' h2 hlt hW (n6 x hx hx1 hgx'') (e6 x hx hx1 hgx)
    have hc0 : c < (K'.St0 Q.dn U hU).B := by
      rw [(K'.h0 Q.dn U hU).B]
      rw [(K''.h0 _ U hU).B] at hc
      exact hc.trans_le (hdNx_mono (add_le_add (le_self_add.trans hLa) le_rfl) _)
    obtain ⟨r1, g1⟩ := x1 hg' hLa hla Q.dn U hU c x hc
    exact ⟨(hnwU_R0 Q.toW K'.St0 K'.h0 _ hsh' hc0 x).trans r1, (hnwU_g0 Q.toW K'.St0 K'.h0 _ hsh' hc0).trans g1⟩
  · obtain ⟨r1, g1⟩ := s3 c x (hc.trans x2)
    obtain ⟨r2, g2⟩ := x3 c x hc
    exact ⟨r1.trans r2, g1.trans g2⟩

end Succ

end Googology.Trans.PoR.InaccPsi.R2.Wh
