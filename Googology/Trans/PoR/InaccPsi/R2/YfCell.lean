import Googology.Trans.PoR.InaccPsi.R2.YfRel
import Googology.Trans.PoR.InaccPsi.R2.CpUp
import Googology.Trans.PoR.InaccPsi.R2.XtVz
import Googology.Trans.PoR.InaccPsi.R2.RzName
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# The transport along a cell `λ₀ < λ < λ₀ + ρ_{λ₀}`

For a restart index `λ₀` with a name, the restarts `λ₀ + z` (`0 < z < ρ_{λ₀}`, `ω² ∣ z`) are the restarts with
the names `η_{λ₀} + z` (`R2.CpName`), and none of them is a fixed point of `υ`.  The relative block induction
`R2.YfRel` with the offset `O(λ) = -1 + e(λ)` on the cell needs only constant terms, so it runs with no input
but the block structure at the base:

* `yfO O λ₀`: `O` up to `λ₀`, `-1 + e(λ)` above;
* `yfPkg_cst`, `yfRsStep_cst`: Lemma IMG and Lemma RS of a constant `c < ρ_λ` (from any term system);
* `yfSpec_cell` (**the cell specification**): the base data at `λ₀` and "no fixed point of `υ` in
  `(λ₀, B)`" give `YfSpec (yfO O λ₀) λ₀ B`;
* `yfCell_noFix`: no fixed point of `υ` in `(λ₀, λ₀ + ρ_{λ₀})`;
* `yfCell_UV` (**THE TRANSPORT THEOREM**): for every restart index `λ₀` with a name and the base data
  (`Good O` at every block boundary up to `λ₀ + ω²`, `O(λ₀) < δ_{λ₀}`), every `λ = λ₀ + z` (`0 < z < ρ_{λ₀}`,
  `ω² ∣ z`) has name `η_{λ₀} + z`, code `-1 + e(z)`, `r(λ) = δ_λ + (-1 + e(z)) = lh(ρ_λ)`, and UPPER, LOWER, CapV;
* `yfGrid_UV`: the same for every restart named `β + ζ` with `β` good, `ι(β)` a restart index, `0 < ζ < P(β)`
  (one theorem for every base `β` of the grid of region (B));
* `yfBase_wit` (**non-vacuity**): the base data hold at `λ₀ = Λ_B` with `O = VzOrec`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

open Classical in
/-- `O` up to `λ₀`, `-1 + e(λ)` above `λ₀`. -/
noncomputable def yfO (O : Ordinal.{0} → Ordinal.{0}) (l0 l : Ordinal.{0}) : Ordinal.{0} :=
  if l ≤ l0 then O l else cdOff (cdExp l)

theorem yfO_le {O : Ordinal.{0} → Ordinal.{0}} {l0 l : Ordinal.{0}} (h : l ≤ l0) : yfO O l0 l = O l := by
  unfold yfO; rw [if_pos h]

theorem yfO_gt {O : Ordinal.{0} → Ordinal.{0}} {l0 l : Ordinal.{0}} (h : l0 < l) :
    yfO O l0 l = cdOff (cdExp l) := by
  unfold yfO; rw [if_neg (not_le.2 h)]

/-- Lemma IMG of a constant `1 ≤ c < ρ_λ` (from any term system). -/
theorem yfPkg_cst (X : Xt.XtSys) {l c : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hc : c < upsilon l) (h1 : 1 ≤ c) (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (fun _ => c) := by
  have e : X.val (X.cst c) = fun _ => c := funext fun x => X.val_cst c x
  have h := X.pkg l hl hl1 (X.cst c) (X.cb_cstI c _ hc) (by rw [X.val_cst]; exact h1) R
  rwa [e] at h

/-- Lemma RS of a constant `c < ρ_λ` (from any term system). -/
theorem yfRsStep_cst (X : Xt.XtSys) {l c : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hc : c < upsilon l) : RsStep l (fun _ => c) := by
  have e : X.val (X.cst c) = fun _ => c := funext fun x => X.val_cst c x
  have h := X.rs l hl hl1 (X.cst c) (X.cb_cstI c _ hc)
  rwa [e] at h

theorem yf_le_of_lt_add {l0 μ : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hμ : IsRestartIdx μ)
    (h : μ < l0 + ω * ω) : μ ≤ l0 := by
  by_contra h'
  exact absurd h (not_lt.2 (next_mult (ri_iff.1 hl0).2 (ri_iff.1 hμ).2 (not_le.1 h')))

theorem yf_off_lt_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : l < upsilon l) :
    cdOff (cdExp l) < upsilon l :=
  ((cdOff_le _).trans (cpExp_le hl.1)).trans_lt hfix

theorem yf_exp_two {l : Ordinal.{0}} (hl : IsRestartIdx l) : 2 ≤ cdExp l :=
  cp_two_le_exp hl.1 (ri_iff.1 hl).2

/-- **The cell specification**: from the base data at `λ₀` and no fixed point of `υ` in `(λ₀, B)`. -/
theorem yfSpec_cell {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (hl0 : IsRestartIdx l0)
    (hB : ω * ω ∣ B) (hB1 : B < Om1) (hlB : l0 < B)
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) (hO0 : O l0 < upsilon (l0 + ω + 1))
    (hfix : ∀ l, IsRestartIdx l → l0 < l → l < B → l < upsilon l) :
    YfSpec (yfO O l0) l0 B where
  ri := hl0
  mult := hB
  cnt := hB1
  lt := hlB
  good := fun η hη => yfGood_congr (fun μ hμ hμl => yfO_le (yf_le_of_lt_add hl0 hμ (hμl.trans_le hη)))
    (hG η hη)
  le0 := by rw [yfO_le le_rfl]; exact hO0
  le := fun l hl hl0l hlB => by
    rw [yfO_gt hl0l]
    exact (((cdOff_le _).trans (cpExp_le hl.1)).trans upsilon_normal.strictMono.le_apply).trans_lt
      (cdRho_lt_delta l)
  one := fun l hl hl0l _ => by rw [yfO_gt hl0l]; exact cpOff_one_le (yf_exp_two hl)
  top := fun l hl hl0l hlB => by
    obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hl.1
    have hη0l : η0 < l := (lt_add_of_pos_right η0 (opow_pos _ omega0_pos)).trans_eq hdec.symm
    refine ⟨fun _ => cdOff (cdExp l), upsilon (max l0 η0), yfO_gt hl0l,
      upsilon_normal.strictMono (max_lt hl0l hη0l), ?_, ?_⟩
    · intro μ hμ hμl hx
      have hm : max l0 η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx
      rw [yfO_gt ((le_max_left _ _).trans_lt hm)]
      have hw := cdWin hdvd ((le_max_right _ _).trans_lt hm) (hμl.trans_eq hdec)
      exact cpOff_lt (one_le_two.trans (yf_exp_two hμ)) hw.1
    · intro R
      exact yfPkg_cst Xt.vzSys hl (hlB.trans hB1) (yf_off_lt_ups hl (hfix l hl hl0l hlB))
        (cpOff_one_le (yf_exp_two hl)) R
  succ := fun l hl hl0l _ h2 => by
    rw [yfO_gt hl0l]
    have he2 := yf_exp_two hl
    have he : cdExp l = 2 := by
      by_contra hne
      have h3 : 1 + 1 < cdExp l := by rw [one_add_one_eq_two]; exact lt_of_le_of_ne he2 (Ne.symm hne)
      have h4 : 1 < cdExp l - 1 := Ordinal.lt_sub.2 h3
      have h5 : (2 : Ordinal.{0}) ≤ cL l := by
        rw [Rz.rz_cL_eq hl, ← one_add_one_eq_two]; exact Order.add_one_le_of_lt h4
      exact absurd h2 (not_lt.2 h5)
    rw [he]
    have := cpOff_nat 2
    simpa using this
  rs := fun l hl hl0l hlB h2 => by
    intro w hw
    rw [yfO_gt hl0l] at hw
    have he3 : 2 < cdExp l := by
      rw [Rz.rz_cL_eq hl] at h2
      by_contra hle
      have h6 : cdExp l - 1 ≤ 1 := Ordinal.sub_le.2 (by rw [one_add_one_eq_two]; exact not_lt.1 hle)
      exact absurd (h2.trans h6) (not_le.2 one_lt_two)
    obtain ⟨a', ha'2, ha'e, hwa'⟩ := cpPick he3 hw
    obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hl.1
    have hη0l : η0 < l := (lt_add_of_pos_right η0 (opow_pos _ omega0_pos)).trans_eq hdec.symm
    have hwρ : w < upsilon l := hw.trans (yf_off_lt_ups hl (hfix l hl hl0l hlB))
    refine ⟨fun _ => w, le_rfl, yfRsStep_cst Xt.vzSys hl (hlB.trans hB1) hwρ, ?_⟩
    intro ν hν
    set ν' := max ν (max l0 η0) with hν'
    have hν'l : ν' < l := max_lt hν (max_lt hl0l hη0l)
    obtain ⟨w', hw'⟩ := exists_add_of_le ((le_max_right l0 η0).trans (le_max_right ν (max l0 η0)))
    have hwe : w' < ω ^ cdExp l := by
      have : η0 + w' < η0 + ω ^ cdExp l := by rw [← hw', ← hdec]; exact hν'l
      exact (add_lt_add_iff_left _).1 this
    have hpa : ω ^ a' ≠ 0 := (opow_pos _ omega0_pos).ne'
    set y := ω ^ a' * (w' / ω ^ a' + 1) with hy
    have hwy : w' < y := by rw [hy, mul_add_one]; exact lt_mul_div_add w' hpa
    have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hwy).ne'
    have hye : y < ω ^ cdExp l := by
      have h1 : y ≤ w' + ω ^ a' := by
        rw [hy, mul_add_one]; exact add_le_add (mul_div_le w' _) le_rfl
      exact h1.trans_lt (isPrincipal_add_omega0_opow _ hwe
        ((opow_lt_opow_iff_right one_lt_omega0).2 ha'e))
    have hey : a' ≤ cdExp y := cdExp_max hy0 (dvd_mul_right _ _)
    have hd0 : ω * ω ∣ η0 := by
      rw [← cp_ww_eq]; exact (opow_dvd_opow ω he3.le).trans hdvd
    have hdy : ω * ω ∣ y := cp_ww_of_exp hy0 (ha'2.trans hey)
    have hμ : IsRestartIdx (η0 + y) :=
      ri_iff.2 ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hy0) le_add_self).ne', dvd_add hd0 hdy⟩
    have hνμ : ν' < η0 + y := by rw [hν', hw']; exact (add_lt_add_iff_left _).2 hwy
    refine ⟨η0 + y, hμ, (le_max_left _ _).trans_lt hνμ,
      ((add_lt_add_iff_left _).2 hye).trans_eq hdec.symm, ?_⟩
    have hl0μ : l0 < η0 + y := ((le_max_left l0 η0).trans (le_max_right ν _)).trans_lt hνμ
    show w ≤ yfO O l0 (η0 + y)
    rw [yfO_gt hl0μ, cpExp_add η0 hy0]
    exact hwa'.trans (cpOff_mono hey)

/-- **No fixed point of `υ` in the cell** `(λ₀, λ₀ + ρ_{λ₀})`. -/
theorem yfCell_noFix {l0 l : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : l0 < l)
    (h2 : l < l0 + upsilon l0) : l < upsilon l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨-, hp, -⟩ := cp_fix_facts hl h.symm
    have hu : upsilon l0 < l := (upsilon_normal.strictMono h1).trans_eq h.symm
    exact absurd (hp h1 hu) (not_lt.2 h2.le)

theorem yf_ww_dvd_ups {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0) : ω * ω ∣ upsilon l0 := by
  have hU : UpsPt (upsilon l0) := upsPt_upsilon (pos_iff_ne_zero.2 hl0.1)
  have hE : ω ^ upsilon l0 = upsilon l0 := upsPt_inE hU
  have h2w : (2 : Ordinal.{0}) ≤ ω := le_of_lt (by exact_mod_cast natCast_lt_omega0 2)
  have h2 : (2 : Ordinal.{0}) ≤ upsilon l0 :=
    (h2w.trans (le_mul_left _ omega0_pos)).trans ((ri_ge hl0).trans upsilon_normal.strictMono.le_apply)
  rw [← hE, ← cp_ww_eq]; exact opow_dvd_opow ω h2

/-- `λ + ω + 2 < B` for restart indices `λ < B`, `ω² ∣ B`. -/
theorem yf_lt_add {l B : Ordinal.{0}} (hl : IsRestartIdx l) (hB : ω * ω ∣ B) (hlB : l < B) :
    l + ω + 1 + 1 < B := by
  have h1 : l + ω * ω ≤ B := next_mult (ri_iff.1 hl).2 hB hlB
  refine lt_of_lt_of_le ?_ h1
  rw [add_assoc, add_assoc]
  refine (add_lt_add_iff_left l).2 ?_
  have h2 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have h3 : ω + (1 + 1) < ω + ω := (add_lt_add_iff_left ω).2 h2
  calc ω + (1 + 1) < ω + ω := h3
    _ = ω * 2 := (Ordinal.mul_two ω).symm
    _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos

/-- **`δ_λ + x` is closed relative to `λ`** (`x < δ_λ`) at a restart index `λ₀ < λ < B` of a cell
specification. -/
theorem yfClosed {O : Ordinal.{0} → Ordinal.{0}} {l0 B l x : Ordinal.{0}} (Sp : YfSpec O l0 B)
    (hl : IsRestartIdx l) (hlB : l < B) (hx : x < cdDelta l) : cdClosed l (cdDelta l + x) := by
  have R := (yfRst Sp hl hlB).1
  refine ⟨le_self_add, fun a hρa hax g hg => ?_⟩
  rcases le_or_gt a (cdDelta l) with haδ | hδa
  · exact (not_lt.1 fun h => R.capδ a hρa haδ g h hg).trans le_self_add
  · have hnI : ¬ Indec a := decomp_mid hx hδa hax
    have hnU : ¬ UpsPt a := fun h => hnI (indec_of_upsPt h)
    have haB : a < upsilon B :=
      (hax.trans_lt (cp_delta_add_lt hx)).trans (upsilon_normal.strictMono (yf_lt_add hl Sp.mult hlB))
    have hR := (yfSk Sp a haB hnU g).1 hg
    exact ((Lh.lhDecomp hnI).2 g hR).trans hax

/-- **THE TRANSPORT THEOREM** (cell form): base data at `λ₀` ⇒ name, code, exact reach, UPPER, LOWER and CapV at
every `λ₀ + z`, `0 < z < ρ_{λ₀}`, `ω² ∣ z`. -/
theorem yfCell_UV (S : InaccSeq.{0}) {O : Ordinal.{0} → Ordinal.{0}} {l0 η1 z : Ordinal.{0}}
    (hl0 : IsRestartIdx l0) (hn : upsilon l0 < Pv S η1)
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) (hO0 : O l0 < upsilon (l0 + ω + 1))
    (hz0 : 0 < z) (hzρ : z < upsilon l0) (hzd : ω * ω ∣ z) :
    cdEta S (l0 + z) = cdEta S l0 + z ∧ cdCode S (l0 + z) = cdOff (cdExp z) ∧
      cdR S (l0 + z) = cdDelta (l0 + z) + cdOff (cdExp z) ∧
      IsReach R2C (upsilon (l0 + z)) (cdR S (l0 + z)) ∧
      CdUpper S (l0 + z) ∧ CdLower S (l0 + z) ∧ CdCapV S (l0 + z) := by
  have hρ1 : upsilon l0 < Om1 := by
    have h := Pv_lt_Om1 S η1
    rw [← Br.Om1_eq] at h
    exact hn.trans h
  have hl01 : l0 < Om1 := upsilon_normal.strictMono.le_apply.trans_lt hρ1
  have hpos : 0 < upsilon l0 := lt_of_le_of_lt zero_le hzρ
  have hB : ω * ω ∣ l0 + upsilon l0 := dvd_add (ri_iff.1 hl0).2 (yf_ww_dvd_ups hl0)
  have hB1 : l0 + upsilon l0 < Om1 := Om1_add_lt hl01 hρ1
  have hlB0 : l0 < l0 + upsilon l0 := lt_add_of_pos_right l0 hpos
  have Sp := yfSpec_cell hl0 hB hB1 hlB0 hG hO0 (fun l hl h1 h2 => yfCell_noFix hl h1 h2)
  set l := l0 + z with hl_def
  have hl : IsRestartIdx l :=
    ri_iff.2 ⟨(lt_of_lt_of_le hz0 le_add_self).ne', dvd_add (ri_iff.1 hl0).2 hzd⟩
  have h1 : l0 < l := lt_add_of_pos_right l0 hz0
  have h2 : l < l0 + upsilon l0 := (add_lt_add_iff_left l0).2 hzρ
  have hexp : cdExp l = cdExp z := cpExp_add l0 hz0.ne'
  have hreach := yfReach Sp hl h1 h2
  rw [yfO_gt h1, hexp] at hreach
  have hm : cdCode S l = cdOff (cdExp z) := cpCode_add hl0.1 hn hzρ hz0.ne'
  have hml : cdOff (cdExp z) ≤ l :=
    ((cdOff_le _).trans (cpExp_le hz0.ne')).trans le_add_self
  have hθ : cdTheta S l (cdCode S l) = cdOff (cdExp z) := by
    rw [hm]; exact cdTheta_small S (hml.trans upsilon_normal.strictMono.le_apply)
  have hmδ : cdOff (cdExp z) < cdDelta l :=
    (hml.trans upsilon_normal.strictMono.le_apply).trans_lt (cdRho_lt_delta l)
  have hR : cdR S l = cdDelta l + cdOff (cdExp z) := by
    show cdk l (cdTheta S l (cdCode S l)) = _
    rw [hθ]
    exact cdk_interval (fun y hy => Or.inl (yfClosed Sp hl h2 (hy.trans_lt hmδ))) _ le_rfl
  have hRe : IsReach R2C (upsilon l) (cdR S l) := by rw [hR]; exact hreach
  have hUL := cdExact_iff.2 hRe
  -- the name and the cap
  obtain ⟨heta, hg', hpv0⟩ := cpEta_add (S := S) hl0.1 hn hzρ
  obtain ⟨hg0, hι0, -, -⟩ := cdEta_pv_spec (S := S) hl0.1 hn
  have hz' : z < Pv S (cdEta S l0) := hpv0 ▸ hzρ
  have hι : iota S (cdEta S l) = l := by rw [heta, cpIota_add hg0 hz', hι0]
  have hgl : Bt.Good S (cdEta S l) := heta ▸ hg'
  have hpv : Pv S (cdEta S l) = upsilon l := by
    calc Pv S (cdEta S l) = upsilon (iota S (cdEta S l)) := (ups_iota S _).symm
      _ = upsilon l := by rw [hι]
  have hww : ω * ω < l := (ri_ge hl0).trans_lt h1
  have hw2 : (ω + 1 + 1 : Ordinal.{0}) < Pv S (cdEta S l) := by
    rw [hpv]
    have hU := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
    have hp := (indec_iff.1 (indec_of_upsPt hU)).2
    have hω : ω < upsilon l :=
      lt_of_le_of_lt (le_mul_left _ omega0_pos) (hww.trans_le upsilon_normal.strictMono.le_apply)
    have h1' : (1 : Ordinal.{0}) < upsilon l := one_lt_omega0.trans hω
    exact hp (hp hω h1') h1'
  have hP : Pv S (cdEta S l + (ω + 1 + 1)) = upsilon (l + ω + 1 + 1) := by
    calc Pv S (cdEta S l + (ω + 1 + 1))
        = upsilon (iota S (cdEta S l + (ω + 1 + 1))) := (ups_iota S _).symm
      _ = upsilon (l + ω + 1 + 1) := by rw [cpIota_add hgl hw2, hι]; simp only [add_assoc]
  have hexpη : cdExp (cdEta S l) = cdExp z := by rw [heta, cpExp_add _ hz0.ne']
  have he2 : 2 ≤ cdExp z := cp_two_le_exp hz0.ne' hzd
  have hle : ω + 1 + 1 ≤ ω ^ cdExp (cdEta S l) := by
    rw [hexpη]
    refine le_trans ?_ (opow_le_opow_right omega0_pos he2)
    rw [cp_ww_eq]
    refine le_of_lt ?_
    have h2' : (1 + 1 : Ordinal.{0}) < ω := by
      rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
    calc ω + 1 + 1 = ω + (1 + 1) := add_assoc _ _ _
      _ < ω + ω := (add_lt_add_iff_left ω).2 h2'
      _ = ω * 2 := (Ordinal.mul_two ω).symm
      _ < ω * ω := mul_lt_mul_of_pos_left (by exact_mod_cast natCast_lt_omega0 2) omega0_pos
  have hcap : CdCapV S l := by
    unfold CdCapV cdCapB
    rw [hR]
    calc cdDelta l + cdOff (cdExp z) < upsilon (l + ω + 1 + 1) := cp_delta_add_lt hmδ
      _ = Pv S (cdEta S l + (ω + 1 + 1)) := hP.symm
      _ ≤ Pv S (cdEta S l + ω ^ cdExp (cdEta S l)) := Pv_mono (add_le_add le_rfl hle)
  exact ⟨heta, hm, hR, hRe, hUL.1, hUL.2, hcap⟩

/-- **THE TRANSPORT THEOREM** (stretch form): with the base data at `λ₀` and no fixed point of `υ` in `(λ₀, B)`,
every restart index `λ₀ < λ < B` with a name has code `-1 + e(λ)`, `r(λ) = δ_λ + (-1 + e(λ))`, UPPER, LOWER,
CapV (re-based at the cell of `λ`, `R2.CpName`'s `cpDecomp`). -/
theorem yfStretch_UV (S : InaccSeq.{0}) {O : Ordinal.{0} → Ordinal.{0}} {l0 B l η1 : Ordinal.{0}}
    (hl0 : IsRestartIdx l0) (hB : ω * ω ∣ B) (hB1 : B < Om1) (hlB0 : l0 < B)
    (hG : ∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) (hO0 : O l0 < upsilon (l0 + ω + 1))
    (hfix : ∀ l, IsRestartIdx l → l0 < l → l < B → l < upsilon l)
    (hl : IsRestartIdx l) (h1 : l0 < l) (h2 : l < B) (hn : upsilon l < Pv S η1) :
    cdCode S l = cdOff (cdExp l) ∧ cdR S l = cdDelta l + cdOff (cdExp l) ∧
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have Sp := yfSpec_cell hl0 hB hB1 hlB0 hG hO0 hfix
  rcases lt_or_ge l (l0 + upsilon l0) with hc | hc
  · obtain ⟨z, rfl⟩ := exists_add_of_le h1.le
    have hz0 : 0 < z := (add_lt_add_iff_left l0).1 (by rwa [add_zero])
    have hzρ : z < upsilon l0 := (add_lt_add_iff_left l0).1 hc
    have hzd : ω * ω ∣ z := (dvd_add_iff (ri_iff.1 hl0).2).1 (ri_iff.1 hl).2
    have hn0 : upsilon l0 < Pv S η1 := (upsilon_normal.strictMono h1).trans hn
    obtain ⟨-, hm, hR, -, hU, hL, hV⟩ := yfCell_UV S hl0 hn0 hG hO0 hz0 hzρ hzd
    rw [cpExp_add l0 hz0.ne']
    exact ⟨hm, hR, hU, hL, hV⟩
  · have hww : ω * ω < l := (ri_ge hl0).trans_lt h1
    obtain ⟨l1, z, hl1, hz0, hzρ, hzd, rfl⟩ := cpDecomp hl hww (hfix _ hl h1 h2)
    have h01 : l0 ≤ l1 := by
      by_contra h
      have hlt : l1 < l0 := not_le.1 h
      have h3 : l1 + z < l0 + upsilon l0 :=
        calc l1 + z < l1 + upsilon l1 := (add_lt_add_iff_left l1).2 hzρ
          _ ≤ l0 + upsilon l0 := add_le_add hlt.le (upsilon_normal.strictMono.monotone hlt.le)
      exact absurd hc (not_le.2 h3)
    have hz1 : ω * ω ≤ z := le_of_dvd hz0.ne' hzd
    have hl1B : l1 + ω * ω ≤ B := (add_le_add le_rfl hz1).trans h2.le
    have hG' : ∀ η, ω * ω * η ≤ l1 + ω * ω → Good (yfO O l0) (ω * ω * η) :=
      fun η hη => yfGood_all Sp η (hη.trans hl1B)
    have hl1lt : l1 < B := (lt_add_of_pos_right l1 hz0).trans h2
    have hO1 : yfO O l0 l1 < upsilon (l1 + ω + 1) := by
      rcases eq_or_lt_of_le h01 with e | h
      · rw [← e]; exact Sp.le0
      · exact Sp.le l1 hl1 h hl1lt
    have hn1 : upsilon l1 < Pv S η1 :=
      (upsilon_normal.strictMono (lt_add_of_pos_right l1 hz0)).trans hn
    obtain ⟨-, hm, hR, -, hU, hL, hV⟩ := yfCell_UV S hl1 hn1 hG' hO1 hz0 hzρ hzd
    rw [cpExp_add l1 hz0.ne']
    exact ⟨hm, hR, hU, hL, hV⟩

/-- **The transport for the grid of region (B)**: for a good base name `β` with `ι(β)` a restart index and the
base data at `ι(β)`, every restart index `λ` named `β + ζ` with `0 < ζ < P(β)` has code `-1 + e(ζ)`, exact reach
`δ_λ + (-1 + e(ζ))`, UPPER, LOWER and CapV. -/
theorem yfGrid_UV (S : InaccSeq.{0}) {O : Ordinal.{0} → Ordinal.{0}} {β η1 ζ l : Ordinal.{0}}
    (hβ : Bt.Good S β) (hri : IsRestartIdx (iota S β)) (hn : upsilon (iota S β) < Pv S η1)
    (hG : ∀ η, ω * ω * η ≤ iota S β + ω * ω → Good O (ω * ω * η))
    (hO0 : O (iota S β) < upsilon (iota S β + ω + 1))
    (hl : IsRestartIdx l) (hι : iota S (cdEta S l) = l) (hname : cdEta S l = β + ζ)
    (hζ0 : ζ ≠ 0) (hζ : ζ < Pv S β) :
    cdCode S l = cdOff (cdExp ζ) ∧ cdR S l = cdDelta l + cdOff (cdExp ζ) ∧
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hlz : l = iota S β + ζ := by rw [← hι, hname, cpIota_add hβ hζ]
  have hζρ : ζ < upsilon (iota S β) := by rw [ups_iota S β]; exact hζ
  have hζd : ω * ω ∣ ζ := (dvd_add_iff (ri_iff.1 hri).2).1 (hlz ▸ (ri_iff.1 hl).2)
  obtain ⟨-, hm, hR, -, hU, hL, hV⟩ :=
    yfCell_UV S hri hn hG hO0 (pos_iff_ne_zero.2 hζ0) hζρ hζd
  rw [hlz]
  exact ⟨hm, hR, hU, hL, hV⟩

/-- **Non-vacuity of the base data**: at `λ₀ = Λ_B` with `O = VzOrec` (`R2.CpFront`), the base data hold and
`λ₀` has a name. -/
theorem yfBase_wit (S : InaccSeq.{0}) :
    IsRestartIdx VzLam ∧ upsilon VzLam < Pv S (Om ω + Nc.ncPp S * 0) ∧
      (∀ η, ω * ω * η ≤ VzLam + ω * ω → Good VzOrec (ω * ω * η)) ∧
      VzOrec VzLam < upsilon (VzLam + ω + 1) := by
  have hlt : VzLam < cpB1 := lt_of_le_of_lt le_self_add cpB0_lt
  refine ⟨vzLam_ri, ?_, fun η hη => good_allGen cpSpec η (hη.trans cpB0_lt.le), cpSpec.le _ vzLam_ri hlt⟩
  rw [← Lw.lw_L_eq S 0]
  exact (upsilon_normal.strictMono hlt).trans (Ph.phFr_vz (S := S)).2.2.2.2

end Googology.Trans.PoR.InaccPsi.R2.Yf
