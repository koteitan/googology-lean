import Googology.Trans.PoR.InaccPsi.R2.GqRS
import Googology.Trans.PoR.InaccPsi.R2.TdVeb

/-!
# THE GATED LOCATION THEOREM: frontiers of codes whose gate lies in `[ε₀, Γ₀)`

`Ge.geLayX` turns a gated layer into a layer only when its gate lies below `ε₀` (then every `ε`-number base lies above
the gate).  A gate `g ∈ [ε₀, Γ₀)` lies below every strongly critical ordinal (`Γ₀ ≤ y`) and below every `υ`-point
(`gq_gam_le_ups`: a `υ`-point below `P(Ω_ω)` is a named point `P(η) ≥ ψ_{Ω₁}(Ω_ω) ≥ Γ₀`), but not below every
`ε`-number.  The PATCHED layer `gqLayP L` keeps the gated layer `L` at the bases above `g`, and at the bases
`x ≤ g` (none of them a `υ`-point or strongly critical) has only the constants as terms and the top `B(x)` of the base
layer `vzLay`.  Every field of `Xt.XtLay` holds, and at every `υ`-point and every strongly critical base the patched
layer is `L`, so the frontier lemma `Gm.gmB1_eq` applies unchanged.

* `gq_gam_le_ups` (**`Γ₀ ≤ u` for every `υ`-point `u`**), `GqPT`, `gqPV`, `gqPCB`, `gqPcs`, `gqSysP`, `gqLayP`
  (**THE PATCHED LAYER**), `gqLayP_top`;
* for a reading system `RS : GqRS` and a code `c ∈ [ε_{Ω₁+1}, B)` with gate below `Γ₀`: `GqRS.gqLX`, `GqRS.gqX`,
  `GqRS.gqLoc` (**`Λ⁺(gqX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of it `= P(…) < L(0)`**), `GqRS.gqFix`, `GqRS.gqEnum`
  (**ENUM-REACH at every range restart below it, fixed points included**), `GqRS.gqCapV`, `GqRS.gqBlk` (**BLK^O and the
  exact reaches below `υ` of it**), `GqRS.gqGood_mul`.

No new axiom.  New definitions: `GqPT`, `gqPV`, `gqPCB`, `gqPcs`, `gqSysP`, `gqLayP`, `GqRS.gqLX`, `GqRS.gqX`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gq

open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Every `υ`-point lies above `Γ₀` -/

/-- **`Γ₀ ≤ u` for every `υ`-point `u`**: a `υ`-point below `P(Ω_ω)` is `P(η) ≥ ψ_{Ω₁}(Ω_ω) ≥ Γ₀`. -/
theorem gq_gam_le_ups (S : InaccSeq.{0}) {u : Ordinal.{0}} (hu : UpsPt u) : gamma 0 ≤ u := by
  obtain ⟨ι, hι, rfl⟩ := upsPt_iff_upsilon.1 hu
  have hK : ∀ η, Td.tdK S ≤ Pv S η := fun η =>
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : Om ω ≤ Om ω + ConjT.th S * η)).1
  refine (Td.tdGam_le_K (S := S)).trans ?_
  rcases lt_or_ge (upsilon ι) (Pv S (Om ω)) with h | h
  · rw [← Cd.cdEta_pv (S := S) hι.ne' h]; exact hK _
  · exact (hK _).trans h

/-! ## The patched layer -/

variable {g : Ordinal.{0}}

/-- The terms of the patched system: the terms of `L` and the constants. -/
abbrev GqPT (X : GdSys g) : Type 1 := X.Tm ⊕ Ordinal.{0}

/-- The value of a patched term. -/
def gqPV (X : GdSys g) : GqPT X → Ordinal.{0} → Ordinal.{0}
  | .inl s, x => X.val s x
  | .inr c, _ => c

/-- A term of `L` is defined only above the gate; a constant `c` at the bases above `c`. -/
def gqPCB (X : GdSys g) : GqPT X → Ordinal.{0} → Prop
  | .inl s, x => g < x ∧ X.CB s x
  | .inr c, x => c < x

/-- The constants of a patched term (a term of `L` also counts the gate). -/
def gqPcs (X : GdSys g) : GqPT X → List Ordinal.{0}
  | .inl s => g :: X.cs s
  | .inr c => [c]

/-- The term of `L` of a patched term. -/
def gqPconv (X : GdSys g) : GqPT X → X.Tm
  | .inl s => s
  | .inr c => X.cst c

theorem gqPconv_val (X : GdSys g) (t : GqPT X) (x : Ordinal.{0}) : X.val (gqPconv X t) x = gqPV X t x := by
  cases t with
  | inl s => rfl
  | inr c => exact X.val_cst c x

theorem gqPconv_CB (X : GdSys g) {t : GqPT X} {x : Ordinal.{0}} (h : gqPCB X t x) : X.CB (gqPconv X t) x := by
  cases t with
  | inl s => exact h.2
  | inr c => exact X.cb_cstI c x h

theorem gqPconv_fun (X : GdSys g) (t : GqPT X) : X.val (gqPconv X t) = gqPV X t :=
  funext fun x => gqPconv_val X t x

/-- **THE PATCHED TERM SYSTEM** of a gated layer `L` whose gate lies below every `υ`-point. -/
noncomputable def gqSysP (L : GdLay g) (hgU : ∀ u, UpsPt u → g < u) : XtSys where
  Tm := GqPT L.sys
  val := gqPV L.sys
  CB := gqPCB L.sys
  cs := gqPcs L.sys
  cst := Sum.inr
  top := fun x => if g < x then L.sys.top x else vzSys.top x
  cb_cst := fun t s h c hc => by
    cases t with
    | inl t =>
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1
      · exact L.sys.cb_cst t s h.2 c hc
    | inr t => rw [List.mem_singleton.1 hc]; exact h
  cb_iff := fun t s s' h H => by
    cases t with
    | inl t => exact ⟨H g List.mem_cons_self, L.sys.cb_iff t s s' h.2 fun c hc => H c (List.mem_cons_of_mem _ hc)⟩
    | inr t => exact H t (List.mem_singleton.2 rfl)
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t ht => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    show gqPV L.sys t (upsilon l) < if g < upsilon l then _ else _
    rw [if_pos hg]
    cases t with
    | inl t => exact L.sys.lt_top l hl hl1 hg t ht.2
    | inr c => exact ht.trans (L.top_gt _ (ups_inE hl) (ups_lt_Om1 l hl1) hg)
  one_le_top := fun l hl hl1 => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    show 1 ≤ if g < upsilon l then _ else _
    rw [if_pos hg]; exact L.sys.one_le_top l hl hl1 hg
  rep := fun l hl hl1 v hv => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    have hv' : v < L.sys.top (upsilon l) := by
      have : (if g < upsilon l then L.sys.top (upsilon l) else vzSys.top (upsilon l)) = L.sys.top (upsilon l) :=
        if_pos hg
      exact this ▸ hv
    obtain ⟨s, hs, e⟩ := L.sys.rep l hl hl1 hg v hv'
    exact ⟨.inl s, ⟨hg, hs⟩, e⟩
  top_lt := fun l hl hl1 => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    show (if g < upsilon l then _ else _) < _
    rw [if_pos hg]; exact L.sys.top_lt l hl hl1 hg
  pkg := fun l hl hl1 t ht h1 hR => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    have h := L.sys.pkg l hl hl1 hg (gqPconv L.sys t) (gqPconv_CB L.sys ht)
      (by rw [gqPconv_val]; exact h1) hR
    rwa [gqPconv_fun] at h
  rs := fun l hl hl1 t ht => by
    have hg := hgU _ (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
    have h := L.sys.rs l hl hl1 hg (gqPconv L.sys t) (gqPconv_CB L.sys ht)
    rwa [gqPconv_fun] at h
  uni_le := fun σ ρ hσ hρ hB t u ht hu => by
    have h := L.sys.uni_le σ ρ hσ hρ hB (hgU σ hσ) (gqPconv L.sys t) (gqPconv L.sys u) (gqPconv_CB L.sys ht)
      (gqPconv_CB L.sys hu)
    rwa [gqPconv_val, gqPconv_val, gqPconv_val, gqPconv_val] at h
  small := fun t => by
    cases t with
    | inl t => exact (L.sys.small t).imp id fun h x hx hx1 hc => h x hx hx1 hc.1 hc.2
    | inr c => exact Or.inl fun _ _ => rfl

theorem gqSysP_top {L : GdLay g} {hgU : ∀ u, UpsPt u → g < u} {x : Ordinal.{0}} (hx : g < x) :
    (gqSysP L hgU).top x = L.sys.top x := if_pos hx

theorem gqSysP_top_low {L : GdLay g} {hgU : ∀ u, UpsPt u → g < u} {x : Ordinal.{0}} (hx : ¬ g < x) :
    (gqSysP L hgU).top x = vzSys.top x := if_neg hx

/-- **THE PATCHED LAYER** of a gated layer `L` whose gate lies below every `υ`-point: `L` above the gate, the
constants and the top of `vzLay` below it. -/
noncomputable def gqLayP (L : GdLay g) (hgU : ∀ u, UpsPt u → g < u) : XtLay where
  sys := gqSysP L hgU
  E := fun x => if g < x then L.E x else VzB x
  top_eq := fun x hx hx1 => by
    by_cases h : g < x
    · rw [gqSysP_top h, if_pos h]; exact L.top_eq x hx hx1 h
    · rw [gqSysP_top_low h, if_neg h]; exact vzLay.top_eq x hx hx1
  exp_dvd := fun x hx hx1 => by
    by_cases h : g < x
    · rw [if_pos h]; exact L.exp_dvd x hx hx1 h
    · rw [if_neg h]; exact vzLay.exp_dvd x hx hx1
  exp_lt := fun x hx hx1 => by
    by_cases h : g < x
    · rw [if_pos h]; exact L.exp_lt x hx hx1 h
    · rw [if_neg h]; exact vzLay.exp_lt x hx hx1
  top_gt := fun x hx hx1 => by
    by_cases h : g < x
    · rw [gqSysP_top h]; exact L.top_gt x hx hx1 h
    · rw [gqSysP_top_low h]; exact vzLay.top_gt x hx hx1
  top_lt_ups := fun x u hx hx1 hxu hu => by
    by_cases h : g < x
    · rw [gqSysP_top h]; exact L.top_lt_ups x u hx hx1 h hxu hu
    · rw [gqSysP_top_low h]; exact vzLay.top_lt_ups x u hx hx1 hxu hu
  lt_top_E := fun x hx hx1 t ht => by
    cases t with
    | inl t =>
      rw [gqSysP_top ht.1]; exact L.lt_top_E x hx hx1 ht.1 t ht.2
    | inr c =>
      refine (show c < x from ht).trans ?_
      by_cases h : g < x
      · rw [gqSysP_top h]; exact L.top_gt x hx hx1 h
      · rw [gqSysP_top_low h]; exact vzLay.top_gt x hx hx1
  exact := fun σ ρ hσ hρ hB t ht => by
    cases t with
    | inl t => exact L.exact σ ρ hσ hρ hB (hgU σ hσ) t ht.2
    | inr c => exact ⟨mem_TB_of_lt hB ht, pi_lt hB ht⟩
  exp_pi := fun σ ρ hσ hρ hB => by
    have h1 := hgU σ hσ
    have h2 := hgU ρ hρ
    show (if g < ρ then L.E ρ else VzB ρ) ∈ TB ρ σ ∧ pi σ ρ (if g < ρ then L.E ρ else VzB ρ) =
      if g < σ then L.E σ else VzB σ
    rw [if_pos h1, if_pos h2]; exact L.exp_pi σ ρ hσ hρ hB h1
  top_wit := fun ρ τ δ h => by
    classical
    have hgρ : g < ρ := hgU ρ h.ρU
    obtain ⟨W, Z, hw, hm, hI⟩ := L.top_wit ρ τ δ h hgρ
    refine ⟨W, insert g Z, hw.insZ hgρ, by rw [gqSysP_top hgρ]; exact hm, fun A f hW hZ C => ?_⟩
    have hgA : g ∈ A := hZ (by simp)
    have C' : GdCtx g ρ A f := ⟨C, hgA⟩
    have hgf : g < f ρ := C'.lt hgρ
    rw [gqSysP_top hgρ, gqSysP_top hgf]
    exact hI A f hW (fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))) C'

theorem gqLayP_top {L : GdLay g} {hgU : ∀ u, UpsPt u → g < u} {x : Ordinal.{0}} (hx : g < x) :
    (gqLayP L hgU).sys.top x = L.sys.top x := if_pos hx

/-! ## The location of a code with gate below `Γ₀` -/

namespace GqRS

variable (RS : GqRS)

theorem gqL_gU {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < gamma 0) (S : InaccSeq.{0}) :
    ∀ u, UpsPt u → (RS.gqL c h hc).g < u := fun u hu => by
  rw [RS.gqL_g]; exact hg.trans_le (gq_gam_le_ups S hu)

/-- **The layer of the code `c`** (gate below `Γ₀`), patched below the gate. -/
noncomputable def gqLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < gamma 0)
    (S : InaccSeq.{0}) : XtLay :=
  gqLayP (RS.gqL c h hc).K (RS.gqL_gU h hc hg S)

/-- Its term system. -/
noncomputable def gqX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < gamma 0)
    (S : InaccSeq.{0}) : XtSys :=
  (RS.gqLX c h hc hg S).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < gamma 0) (S : InaccSeq.{0})
include h hc hg

theorem gq_SC_gx {y : Ordinal.{0}} (hy : SC y) : RS.K.gt c < y := hg.trans_le (Ta.taGam_le_SC hy)

theorem gqX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : RS.K.gt c < x) :
    (RS.gqX c h hc hg S).top x = gq (RS.R c x) x := by
  have hgx' : (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
  rw [show (RS.gqX c h hc hg S).top x = (RS.gqL c h hc).K.sys.top x from gqSysP_top (hgU := RS.gqL_gU h hc hg S) hgx']
  exact RS.gqL_top h hc hx hx1 hgx

theorem gqX_pkg : XtTopPkg (RS.gqX c h hc hg S) := XtLay.topPkg (RS.gqLX c h hc hg S)

theorem gqT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem gqX_cl : ∀ Z, SC Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z hZ =>
  RS.gqL_atom hc (RS.gq_SC_gx c h hc hg hZ)

theorem gqX_poly : GmPoly RS.K (RS.gqX c h hc hg S) (gcG c) := by
  intro Z d hd hdE
  have hgZ : (RS.gqL c h hc).g < max Z (gamma 0) := by
    rw [RS.gqL_g]; exact hg.trans_le (le_max_right _ _)
  obtain ⟨s, hs⟩ := (RS.gqL_codes S c h hc).2 (max Z (gamma 0)) d hgZ
    (gmCl_mono (le_max_left _ _) hd) hdE
  refine ⟨.inl s, fun y hy hy1 hZy => ?_⟩
  have hgy : (RS.gqL c h hc).g < y := by rw [RS.gqL_g]; exact RS.gq_SC_gx c h hc hg hy
  obtain ⟨h1, h2⟩ := hs y hy hy1 (max_le hZy (Ta.taGam_le_SC hy))
  exact ⟨⟨hgy, h1⟩, h2⟩

theorem gqX_topth : ∀ y, SC y → y < Om 1 → (RS.gqX c h hc hg S).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hgy := RS.gq_SC_gx c h hc hg hy
  rw [RS.gqX_top c h hc hg S hyE hy1' hgy, ← RS.gqL_E h hc hyE hy1' hgy]
  exact (RS.gqL_codes S c h hc).1 y hy hy1 hgy

theorem gqX_topE : ∀ x, InE x → x < Om1 → eN x < (RS.gqX c h hc hg S).top x := by
  intro x hx hx1
  by_cases hgx : RS.K.gt c < x
  · rw [RS.gqX_top c h hc hg S hx hx1 hgx]
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (RS.R_lt0' hx hx1 hc hgx)
    exact gmq_eN_lt hx hx1 hT h1
  · have hgx' : ¬ (RS.gqL c h hc).g < x := by rw [RS.gqL_g]; exact hgx
    rw [show (RS.gqX c h hc hg S).top x = vzSys.top x from gqSysP_top_low (hgU := RS.gqL_gU h hc hg S) hgx']
    exact gg_eN_lt_B hx hx1

/-- **WHERE THE FRONTIER OF A CODE WITH GATE BELOW `Γ₀` LIES**: `Λ⁺(RS.gqX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of it
`= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem gqLoc :
    xtB1 (RS.gqX c h hc hg S) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (RS.gqX c h hc hg S)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := gmB1_eq (S := S) (RS.gqT_le c h hc hg) (RS.gqX_poly c h hc hg S) (RS.gqX_topth c h hc hg S)
    (RS.gqX_cl c h hc hg) (gcG_Om1_lt _).le (RS.gqX_topE c h hc hg S) (RS.gqX_pkg c h hc hg S)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(RS.gqX c)`** (THEOREM UNI). -/
theorem gqFix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (RS.gqX c h hc hg S))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (RS.gqX c h hc hg S) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (RS.gqLoc c h hc hg S).1]; exact hl
  exact gmUniTh (RS.gqT_le c h hc hg) (RS.gqX_poly c h hc hg S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem gqX_nonfix : XtNonfix (xtOrec (RS.gqX c h hc hg S)) (xtB1 (RS.gqX c h hc hg S)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (RS.gqX_pkg c h hc hg S)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gqEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (RS.gqLoc c h hc hg S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (RS.gqX_pkg c h hc hg S)) (RS.gqX_nonfix c h hc hg S) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (RS.gqX_pkg c h hc hg S)) hr.1 hl).2 (RS.gqFix c h hc hg S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gqCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (RS.gqLoc c h hc hg S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (RS.gqX_pkg c h hc hg S)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (RS.gqX_nonfix c h hc hg S l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (RS.gqX_pkg c h hc hg S) hr hl' hfx.symm (RS.gqEnum c h hc hg S hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(RS.gqX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem gqBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (RS.gqX c h hc hg S)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (RS.gqX c h hc hg S) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (RS.gqX c h hc hg S) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (RS.gqX c h hc hg S) l)) ∧
    (∀ α < upsilon (xtB1 (RS.gqX c h hc hg S)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (RS.gqX_pkg c h hc hg S)

end Code

theorem gqGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (hgc : RS.K.gt c < gamma 0) (S : InaccSeq.{0}) :
    Bt.Good S (gcG c * ω) := by
  refine gm_good (K := RS.K) fun Z hZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gqL_atom hc (hgc.trans_le (Ta.taGam_le_SC hZ)))
    (GxCl.small (gg_one_lt_of_SC hZ)))

end GqRS

end Googology.Trans.PoR.InaccPsi.R2.Gq
