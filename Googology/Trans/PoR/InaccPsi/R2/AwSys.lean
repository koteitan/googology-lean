import Googology.Trans.PoR.InaccPsi.R2.AwAt
import Googology.Trans.PoR.InaccPsi.R2.ZbLoc
import Googology.Trans.PoR.InaccPsi.R2.XiLay

/-!
# AwSys: THE TERM SYSTEM OF A CODE BOUND `T ≤ K_ω`, FROM LEMMA IMG AND LEMMA RS AT THE READINGS

`Xi.xiSys` is the term system of a code bound `T < θ`: constants and the codes below `T`, read by `R_x`.  Its values lie
in `seg(x)`, and it is a `Gd.GdLay`.  Above `θ` the readings leave `seg(x)` (`Θ(θ) = x⁺`, the next `υ`-point), so there is
no layer; but the block theorem `Xt.XtSys` asks only `top < δ`.  Here: for a code bound `T ≤ K_ω` the term system with the
readings `gxTh x (awAt S x)`, given (a hypothesis `AwH`) the bound `top(ρ) < δ`, the IMG packages and Lemma RS at the
readings.  Every `υ`-point is strongly critical (`aw_ups_SC`), so no gate is needed.  With the generic `Zb` lemmas:

* `AwH`, `awP`, `awCs`, `awVal`, `awCB`, `awTop`, `awSys` (**THE TERM SYSTEM OF `T`**);
* `aw_poly`, `aw_topPkg`, `aw_topE`;
* `awLoc` (**`Λ⁺ = ι(ω^T·ω)`**), `awFix` (THEOREM UNI), `awEnum`, `awCapV`, `awUV` (**UPPER ∧ LOWER ∧ CapV at every range
  restart below `ι(ω^T·ω)`**).

No new axiom.  New definitions: `AwH`, `awP`, `awCs`, `awVal`, `awCB`, `awTop`, `awSys`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Ph

variable (S : InaccSeq.{0}) (T : Ordinal.{0})

/-- **What the term system of the code bound `T` asks**: the code `T` over every base, the bound of its readings, and
Lemma IMG and Lemma RS at the readings of the codes. -/
structure AwH : Prop where
  V : T ≤ awV S
  gE : Gg.ggE < T
  lt : ∀ l, IsRestartIdx l → l < Om1 → gxTh (upsilon l) (awAt S (upsilon l)) T < upsilon (l + ω + 1)
  pkg : ∀ l, IsRestartIdx l → l < Om1 → ∀ c, Om 1 ≤ c → c < T → GxCl (upsilon l) (awAt S (upsilon l)) c →
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (fun x => gxTh x (awAt S x) c)
  top : ∀ l, IsRestartIdx l → l < Om1 → RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (fun x => gxTh x (awAt S x) T)
  rs : ∀ l, IsRestartIdx l → l < Om1 → ∀ c, Om 1 ≤ c → c < T → GxCl (upsilon l) (awAt S (upsilon l)) c →
    RsStep l (fun x => gxTh x (awAt S x) c)

/-- The least `q` with `c` a code over `q + 1`. -/
noncomputable def awP (c : Ordinal.{0}) : Ordinal.{0} := sInf {q | GxCl (q + 1) (awAt S (q + 1)) c}

open Classical in
/-- The constants of a term: `[c]` for the constant `c`; the largest constant of a code `Ω₁ ≤ c < T`. -/
noncomputable def awCs : Ordinal.{0} ⊕ Ordinal.{0} → List Ordinal.{0}
  | Sum.inl c => [c]
  | Sum.inr c => if Om 1 ≤ c ∧ c < T ∧ ∃ q, GxCl (q + 1) (awAt S (q + 1)) c then [awP S c] else [Om 1]

/-- The value of a term: the constant, or the reading of the code. -/
noncomputable def awVal : Ordinal.{0} ⊕ Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  | Sum.inl c => fun _ => c
  | Sum.inr c => fun x => gxTh x (awAt S x) c

/-- A term is visible at `x` when its constants are below `x`. -/
def awCB (t : Ordinal.{0} ⊕ Ordinal.{0}) (x : Ordinal.{0}) : Prop := ∀ p ∈ awCs S T t, p < x

open Classical in
/-- The top: the reading of `T` at a strongly critical base. -/
noncomputable def awTop (x : Ordinal.{0}) : Ordinal.{0} :=
  if SC x then gxTh x (awAt S x) T else eN x + 1

variable {S T}

/-- **Every `υ`-point is strongly critical.** -/
theorem aw_ups_SC (S : InaccSeq.{0}) {u : Ordinal.{0}} (hu : UpsPt u) (hu1 : u < Om1) : SC u :=
  Qc.qc_ups_SC u hu hu1 ε₀ (omega0_opow_epsilon 0)
    ((epsilon_zero_le_of_omega0_opow_le (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC 0)).le).trans_lt
      ((Gr.gr_gam0_lt_tdK S).trans_le (Gr.gr_tdK_le_ups S hu)))

open Classical in
theorem awCs_inr (c : Ordinal.{0}) : awCs S T (Sum.inr c) =
    if Om 1 ≤ c ∧ c < T ∧ ∃ q, GxCl (q + 1) (awAt S (q + 1)) c then [awP S c] else [Om 1] := rfl

theorem awCB_inl {c x : Ordinal.{0}} : awCB S T (Sum.inl c) x ↔ c < x := by
  simp [awCB, awCs]

/-- A visible code is a code over `x`. -/
theorem awCB_code {c x : Ordinal.{0}} (hx1 : x ≤ Om 1) (h : awCB S T (Sum.inr c) x) :
    Om 1 ≤ c ∧ c < T ∧ GxCl x (awAt S x) c := by
  classical
  unfold awCB at h
  rw [awCs_inr] at h
  by_cases hc : Om 1 ≤ c ∧ c < T ∧ ∃ q, GxCl (q + 1) (awAt S (q + 1)) c
  · rw [if_pos hc] at h
    have hp : awP S c < x := h _ (List.mem_singleton.2 rfl)
    have hm : GxCl (awP S c + 1) (awAt S (awP S c + 1)) c := by
      have := csInf_mem (s := {q | GxCl (q + 1) (awAt S (q + 1)) c}) hc.2.2
      exact this
    have hle : awP S c + 1 ≤ x := Order.add_one_le_of_lt hp
    exact ⟨hc.1, hc.2.1, hm.mono hle ((awU S).mono _ _ hle)⟩
  · rw [if_neg hc] at h
    exact absurd (h _ (List.mem_singleton.2 rfl)) (not_lt.2 hx1)

/-- A code `Ω₁ ≤ c < T` over a strongly critical `x` is visible at `x`. -/
theorem awCB_of_code {c x : Ordinal.{0}} (hx : SC x) (h1 : Om 1 ≤ c) (hcT : c < T) (hc : GxCl x (awAt S x) c) :
    awCB S T (Sum.inr c) x := by
  classical
  obtain ⟨Z', hZ', hc'⟩ := (awU S).support hx hc
  have hc'' : GxCl (Z' + 1) (awAt S (Z' + 1)) c :=
    hc'.mono le_self_add ((awU S).mono _ _ le_self_add)
  have hex : ∃ q, GxCl (q + 1) (awAt S (q + 1)) c := ⟨Z', hc''⟩
  unfold awCB
  rw [awCs_inr, if_pos ⟨h1, hcT, hex⟩]
  intro p hp
  rw [List.mem_singleton.1 hp]
  exact (show awP S c ≤ Z' from csInf_le' (show Z' ∈ {q | GxCl (q + 1) (awAt S (q + 1)) c} from hc'')).trans_lt hZ'

section Facts

variable (H : AwH S T)
include H

theorem aw_Om1_lt_T : Om 1 < T := Gg.ggE_spec.2.trans H.gE

theorem awTop_SC {x : Ordinal.{0}} (hx : SC x) : awTop S T x = gxTh x (awAt S x) T := if_pos hx

/-- At a strongly critical `y < Ω₁` the base lies below the reading of `T`. -/
theorem aw_y_lt {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : y < gxTh y (awAt S y) T := by
  have hOT := aw_Om1_lt_T H
  have := gxTh_lt (Z := y) (At := awAt S y) GxCl.om hOT
  have h2 : gxTh y (awAt S y) (Om 1) = y := gxTh_Om1 hy hy1 ((awU S).gxAt y)
  rwa [h2] at this

/-- **`ε_{y+1}` lies below the reading of `T`.** -/
theorem aw_eN_lt {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : eN y < gxTh y (awAt S y) T := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hEc : GxCl y (awAt S y) Gg.ggE :=
    GxCl.of_gg (Sp.spE_cl (Lu.lu_one_lt_E (Low.opow_eq_self_of_SC hy)))
  have hpE := gxTh_opow hy hAt hEc
  rw [Gg.ggE_spec.1] at hpE
  have hOE : gxTh y (awAt S y) (Om 1) < gxTh y (awAt S y) Gg.ggE := gxTh_lt GxCl.om Gg.ggE_spec.2
  rw [gxTh_Om1 hy hy1 hAt] at hOE
  exact (eN_le hOE hpE.symm).trans_lt (gxTh_lt hEc H.gE)

end Facts

theorem aw_val_ge {x c : Ordinal.{0}} (hx1 : x ≤ Om 1) (hc1 : Om 1 ≤ c) : x ≤ gxTh x (awAt S x) c := by
  calc x = gxTh x (awAt S x) x := (gxTh_small le_rfl).symm
    _ ≤ _ := gxTh_mono (hx1.trans hc1)

theorem aw_le_iff {x c d : Ordinal.{0}} (hc : GxCl x (awAt S x) c) (hd : GxCl x (awAt S x) d) :
    gxTh x (awAt S x) c ≤ gxTh x (awAt S x) d ↔ c ≤ d := by
  constructor
  · intro h
    by_contra hdc
    push Not at hdc
    exact absurd (gxTh_lt hd hdc) (not_lt.2 h)
  · intro h
    exact gxTh_mono h

/-- A term visible at `σ` is visible at every `ρ ≥ σ`. -/
theorem awCB_mono {σ ρ : Ordinal.{0}} (h : σ ≤ ρ) {t : Ordinal.{0} ⊕ Ordinal.{0}} (ht : awCB S T t σ) :
    awCB S T t ρ := fun p hp => (ht p hp).trans_le h

section Sys

variable (H : AwH S T)
include H

theorem aw_uni_le {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (t u : Ordinal.{0} ⊕ Ordinal.{0})
    (ht : awCB S T t σ) (hu : awCB S T u σ) (hρ1 : ρ ≤ Om 1) :
    awVal S t ρ ≤ awVal S u ρ ↔ awVal S t σ ≤ awVal S u σ := by
  have hσ1 : σ ≤ Om 1 := hB.2.2.1.le.trans hρ1
  cases t with
  | inl a =>
    cases u with
    | inl b => exact Iff.rfl
    | inr d =>
      have ha : a < σ := awCB_inl.1 ht
      obtain ⟨hd1, -, -⟩ := awCB_code hσ1 hu
      refine iff_of_true ?_ ?_
      · exact (ha.trans hB.2.2.1).le.trans (aw_val_ge hρ1 hd1)
      · exact ha.le.trans (aw_val_ge hσ1 hd1)
  | inr c =>
    obtain ⟨hc1, -, hcσ⟩ := awCB_code hσ1 ht
    have hcρ := hcσ.mono hB.2.2.1.le ((awU S).mono _ _ hB.2.2.1.le)
    cases u with
    | inl b =>
      have hb : b < σ := awCB_inl.1 hu
      refine iff_of_false ?_ ?_
      · exact not_le.2 ((hb.trans hB.2.2.1).trans_le (aw_val_ge hρ1 hc1))
      · exact not_le.2 (hb.trans_le (aw_val_ge hσ1 hc1))
    | inr d =>
      obtain ⟨-, -, hdσ⟩ := awCB_code hσ1 hu
      have hdρ := hdσ.mono hB.2.2.1.le ((awU S).mono _ _ hB.2.2.1.le)
      show gxTh ρ (awAt S ρ) c ≤ gxTh ρ (awAt S ρ) d ↔ gxTh σ (awAt S σ) c ≤ gxTh σ (awAt S σ) d
      rw [aw_le_iff hcρ hdρ, aw_le_iff hcσ hdσ]

/-- **THE TERM SYSTEM OF THE CODE BOUND `T`.** -/
noncomputable def awSys : XtSys where
  Tm := Ordinal.{0} ⊕ Ordinal.{0}
  val := awVal S
  CB := awCB S T
  cs := awCs S T
  cst := Sum.inl
  top := awTop S T
  cb_cst := fun _ _ h => h
  cb_iff := fun _ _ _ _ hc => hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => awCB_inl.2 h
  lt_top := fun l hl hl1 t ht => by
    have hu := ups_ri hl
    have hu1 := ups_lt_Om1 l hl1
    have hSC := aw_ups_SC S hu hu1
    have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
    rw [awTop_SC H hSC]
    cases t with
    | inl c => exact (awCB_inl.1 ht).trans (aw_y_lt H hSC hu1')
    | inr c =>
      obtain ⟨-, hcT, hc⟩ := awCB_code hu1'.le ht
      exact gxTh_lt hc hcT
  one_le_top := fun l hl hl1 => by
    have hu := ups_ri hl
    have hu1 := ups_lt_Om1 l hl1
    have hSC := aw_ups_SC S hu hu1
    have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
    rw [awTop_SC H hSC]
    exact (Gg.gg_one_lt_of_SC hSC).le.trans (aw_y_lt H hSC hu1').le
  rep := fun l hl hl1 v hv => by
    have hu := ups_ri hl
    have hu1 := ups_lt_Om1 l hl1
    have hSC := aw_ups_SC S hu hu1
    have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
    rw [awTop_SC H hSC] at hv
    rcases lt_or_ge v (upsilon l) with hvu | huv
    · exact ⟨Sum.inl v, awCB_inl.2 hvu, rfl⟩
    obtain ⟨c, hc, hcT, rfl⟩ := gxTh_onto hv
    have hc1 : Om 1 ≤ c := by
      by_contra hlt
      push Not at hlt
      have hcu := GxCl.lt_of_lt_Om1 hSC ((awU S).gxAt _) hc hlt
      rw [gxTh_small hcu.le] at huv
      exact absurd hcu (not_lt.2 huv)
    exact ⟨Sum.inr c, awCB_of_code hSC hc1 hcT hc, rfl⟩
  top_lt := fun l hl hl1 => by
    have hSC := aw_ups_SC S (ups_ri hl) (ups_lt_Om1 l hl1)
    rw [awTop_SC H hSC]
    exact H.lt l hl hl1
  pkg := fun l hl hl1 t ht h1 R => by
    classical
    have hu1 := ups_lt_Om1 l hl1
    have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
    cases t with
    | inl c =>
      have hc : c < upsilon l := awCB_inl.1 ht
      refine ⟨h1, hc.trans (R.ρτ.trans R.τδ), ∅, {c}, WZ.empty.insZ hc,
        (show c ∈ (∅ : Finset Ordinal.{0}) ∪ {c} by simp), fun A f _ hZ C => ?_⟩
      have hcA : c ∈ A := hZ (by simp)
      show c ≤ f c
      rw [C.fix c hcA hc]
    | inr c =>
      obtain ⟨hc1, hcT, hc⟩ := awCB_code hu1'.le ht
      exact H.pkg l hl hl1 c hc1 hcT hc R
  rs := fun l hl hl1 t ht R htg => by
    have hu1 := ups_lt_Om1 l hl1
    have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
    cases t with
    | inl c => exact rs_rstT (t := OT.k c) R (show OT.CB (OT.k c) (upsilon l) from awCB_inl.1 ht) htg
    | inr c =>
      obtain ⟨hc1, hcT, hc⟩ := awCB_code hu1'.le ht
      exact H.rs l hl hl1 c hc1 hcT hc R htg
  uni_le := fun _ ρ _ hρ hB t u ht hu => aw_uni_le H hB t u ht hu (by
    rw [← Rj.rj_Om1]; exact hB.2.2.2.le)
  small := fun t => by
    cases t with
    | inl c => exact Or.inl fun _ _ => rfl
    | inr c =>
      refine Or.inr fun x _ hx1 ht => ?_
      have hx1' : x ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hx1.le
      exact aw_val_ge hx1' (awCB_code hx1' ht).1

theorem awSys_top {x : Ordinal.{0}} (hx : SC x) : (awSys H).top x = gxTh x (awAt S x) T := awTop_SC H hx

/-- **Terms for the codes below `T`.** -/
theorem aw_poly (κ : Ordinal.{0}) : ZbPoly (awU S) (awSys H) T κ := by
  intro Z c hc hcT
  by_cases hc1 : c < Om 1
  · refine ⟨Sum.inl c, fun y hy _ hZy _ => ?_⟩
    have hcy' : GxCl y (awAt S y) c := hc.mono hZy ((awU S).mono Z y hZy)
    have hcy : c < y := GxCl.lt_of_lt_Om1 hy ((awU S).gxAt y) hcy' hc1
    exact ⟨awCB_inl.2 hcy, (gxTh_small hcy.le).symm⟩
  · push Not at hc1
    refine ⟨Sum.inr c, fun y hy _ hZy _ => ?_⟩
    have hcy' : GxCl y (awAt S y) c := hc.mono hZy ((awU S).mono Z y hZy)
    exact ⟨awCB_of_code hy hc1 hcT hcy', rfl⟩

/-- **The top has an IMG package.** -/
theorem aw_topPkg : XtTopPkg (awSys H) := by
  intro l hl hl1 R
  have hu1 := ups_lt_Om1 l hl1
  have hu1' : upsilon l < Om 1 := by rw [← Rj.rj_Om1]; exact hu1
  have hSC := aw_ups_SC S (ups_ri hl) hu1
  obtain ⟨h1, h2, W, Z, w, hm, hI⟩ := H.top l hl hl1 R
  refine ⟨?_, ?_, W, Z, w, ?_, fun A f hW hZ C => ?_⟩
  · show 1 ≤ awTop S T (upsilon l)
    rw [awTop_SC H hSC]; exact h1
  · show awTop S T (upsilon l) < _
    rw [awTop_SC H hSC]; exact h2
  · show awTop S T (upsilon l) ∈ _
    rw [awTop_SC H hSC]; exact hm
  · have hfU := C.ups
    have hf1 : f (upsilon l) < Om1 := (C.low _ C.rho).trans hu1
    show awTop S T (f (upsilon l)) ≤ f (awTop S T (upsilon l))
    rw [awTop_SC H hSC, awTop_SC H (aw_ups_SC S hfU hf1)]
    exact hI A f hW hZ C

theorem aw_topE {x : Ordinal.{0}} (_ : InE x) (hx1 : x < Om1) : eN x < (awSys H).top x := by
  show eN x < awTop S T x
  by_cases hSC : SC x
  · rw [awTop_SC H hSC]
    exact aw_eN_lt H hSC (by rw [← Rj.rj_Om1]; exact hx1)
  · unfold awTop
    rw [if_neg hSC]
    exact lt_add_one _

variable (hTE : ω ^ T = T) (hcl : ∀ Z, GxCl Z (awAt S Z) T)

include hTE hcl in
/-- **WHERE THE FRONTIER LIES**: `Λ⁺ = ι(ω^T·ω)`. -/
theorem awLoc : xtB1 (awSys H) = iota S (ω ^ T * ω) ∧ upsilon (xtB1 (awSys H)) = Pv S (ω ^ T * ω) ∧
    Pv S (ω ^ T * ω) < Nc.ncL S 0 :=
  zbB1_eq (S := S) (A := awU S) (X := awSys H) (T := T) (κ := 0) (lt_of_le_of_lt zero_le (Gr.gr_gam0_lt_tdK S)) H.V (aw_poly H 0)
    (fun _ hy _ _ => awSys_top H hy) (fun Z _ _ => hcl Z) (aw_Om1_lt_T H).le
    (fun _ hx hx1 => aw_topE H hx hx1) (aw_topPkg H)

include hTE hcl in
/-- **THEOREM UNI.** -/
theorem awFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (awSys H)) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (awSys H) l := by
  have hlt : l < iota S (ω ^ T * ω) := by rw [← (awLoc H hTE hcl).1]; exact hl
  exact zbUniTh (S := S) (A := awU S) (lt_of_le_of_lt zero_le (Gr.gr_gam0_lt_tdK S)) H.V (aw_poly H 0) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem aw_nonfix : XtNonfix (xtOrec (awSys H)) (xtB1 (awSys H)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (aw_topPkg H)))

include hTE hcl in
/-- **ENUM-REACH at every range restart below `ι(ω^T·ω)`.** -/
theorem awEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (awLoc H hTE hcl).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (aw_topPkg H)) (aw_nonfix H) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (aw_topPkg H)) hr.1 hl).2 (awFix H hTE hcl hr hl hfx.symm)

include hTE hcl in
/-- **CapV at every range restart below `ι(ω^T·ω)`.** -/
theorem awCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (awLoc H hTE hcl).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (aw_topPkg H)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (aw_nonfix H l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (aw_topPkg H) hr hl' hfx.symm (awEnum H hTE hcl hr hl)

include hTE hcl in
/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(ω^T·ω)`.** -/
theorem awUV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (ω ^ T * ω)) :
    CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  ⟨(awEnum H hTE hcl hr hl).1, (awEnum H hTE hcl hr hl).2, awCapV H hTE hcl hr hl⟩

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Aw
