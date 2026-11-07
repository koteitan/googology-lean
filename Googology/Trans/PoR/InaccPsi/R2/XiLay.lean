import Googology.Trans.PoR.InaccPsi.R2.XiRd
import Googology.Trans.PoR.InaccPsi.R2.QdPast

/-!
# XiLay: ONE LAYER FOR EVERY CODE BOUND BELOW `θ`, FROM LEMMA IMG AT THE READINGS

With the reading `R_x` of `R2.XiRd` (Lemma EXACT for every code below `θ`, `gxTh y = R_y` at strongly critical `y`)
the layer of a code bound `T < θ` needs no digit systems: its terms are the countable constants and the codes
`Ω₁ ≤ c < T` themselves, a code `c` is visible at `x` when `P₀(c) ⊆ x`, and its value at `x` is `R_x(c)`.  Every field
of `Gd.GdSys`, `Gd.GdLay`, `Gd.GdB` follows from the order, the base change and the bounds of `R_x`, except the image
packages and the top witness, which ask Lemma IMG at the readings (`XiImg`).

* `XiImg` (**Lemma IMG at the readings of the codes up to `T`**, a hypothesis), `XiLH` (the hypotheses on the bound
  `T` and the gate `g ≥ ε₀`);
* `xi_eN_lt_SC`, `xi_next`, `xiE` (the top exponent), `xiE_facts`, `xiR_SC` (**at a strongly critical `y` above the
  gate, `R_y(T) = gxTh y T` is an `ε`-number above `ε_{y+1}`**), `xiE_SC`;
* `xiCs`, `xiVal`, `xiCB`, `xiSys`, `xiLay`, `xiB` (**THE LAYER OF `T`**);
* `xi_layA` (**`Zm.ZmLayA (qtU S) S B` for every atom index `B` with `Γ(B) ≤ T`**).

No new axiom.  New definitions: `XiImg`, `XiLH`, `xiE`, `xiCs`, `xiVal`, `xiCB`, `xiSys`, `xiLay`, `xiB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gd

variable (S : InaccSeq.{0})

/-- **Lemma IMG at the readings** of the codes `Ω₁ ≤ c ≤ T` visible at a restart base above the gate `g`. -/
def XiImg (g T : Ordinal.{0}) : Prop :=
  ∀ ρ τ δ c : Ordinal.{0}, RstK ρ τ δ → g < ρ → WDom S ρ c → Om1 ≤ c → c ≤ T → Gn.GnI ρ δ (xiR ρ c)

/-- The hypotheses on the bound code `T` and the gate `g`. -/
structure XiLH (g T : Ordinal.{0}) : Prop where
  th : T < ConjT.th S
  eps : ω ^ T = T
  gE : Gg.ggE < T
  par : ∀ p ∈ wP T, p ≤ g
  ge : ε₀ ≤ g
  img : XiImg S g T

variable {S} {g T : Ordinal.{0}}

theorem xi_eN_lt_SC {m y : Ordinal.{0}} (hm : SC m) (hym : y < m) : eN y < m := by
  have h1m : (1 : Ordinal.{0}) < m := by
    have := hm.2 0 hm.1 0 hm.1
    rwa [veblen_zero_apply, opow_zero] at this
  have hy1 : y + 1 < m := hm.isSuccLimit.add_one_lt hym
  have hv : veblen 1 (y + 1) < m := hm.2 1 h1m (y + 1) hy1
  have hvE : InE (veblen 1 (y + 1)) := Lu.luP_E le_rfl (Lu.luP_veblen 1 (y + 1))
  have hyv : y < veblen 1 (y + 1) := (lt_add_one y).trans_le (right_le_veblen _ _)
  exact (eN_le hyv hvE).trans_lt hv

/-- `Tˣ ∩ Ω₁ = m` is a strongly critical `ε`-number, below every `υ`-point above `x`. -/
theorem xi_next {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∃ m, x < m ∧ InE m ∧ SC m ∧ (∀ u, x < u → UpsPt u → m ≤ u) ∧ (∀ a, a < Om1 → (a ∈ Tset x ↔ a < m)) ∧
      m < Om1 := by
  obtain ⟨m, hxm, hmL, hmin, hT, hm1⟩ := T_next (Or.inr hx) hx1
  have hmE : InE m := upsPt_inE ⟨lt_of_le_of_lt zero_le hxm, hmL⟩
  exact ⟨m, hxm, hmE, Qc.qc_m_SC hx hx1 hxm hT hm1 hmE, fun u hxu hu => hmin u hxu hu.2, hT, hm1⟩

theorem xiLH_dom (H : XiLH S g T) {x : Ordinal.{0}} (hgx : g < x) : WDom S x T := by
  have hO : (Om1 : Ordinal.{0}) ≤ T := by
    rw [Rj.rj_Om1]; exact (Gg.ggE_spec.2.trans H.gE).le
  exact Or.inr ⟨hO, H.th, fun p hp => (H.par p hp).trans_lt hgx⟩

theorem xiLH_Om1_lt (H : XiLH S g T) : (Om1 : Ordinal.{0}) < T := by
  rw [Rj.rj_Om1]; exact Gg.ggE_spec.2.trans H.gE

open Classical in
/-- The top exponent: `R_x(T)` where it is an `ε`-number above `ε_{x+1}` (at every strongly critical base above the
gate), else the next `ε`-number above `max(R_x(T), ε_{x+1})`. -/
noncomputable def xiE (T x : Ordinal.{0}) : Ordinal.{0} :=
  if InE (xiR x T) ∧ eN x < xiR x T then xiR x T else eN (max (xiR x T) (eN x))

theorem xiE_facts (H : XiLH S g T) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : g < x) :
    InE (xiE T x) ∧ xiE T x ∈ Tset x ∧ xiE T x < Om1 ∧ eN x < xiE T x ∧ xiR x T ≤ xiE T x ∧
      ∀ u, x < u → UpsPt u → xiE T x < u := by
  obtain ⟨m, -, -, hmS, hmin, hT, hm1⟩ := xi_next hx hx1
  obtain ⟨hRT, hR1⟩ := xiR_T S hx hx1 T (xiLH_dom H hgx)
  have hRm : xiR x T < m := (hT _ hR1).1 hRT
  have heNm : eN x < m := (hT _ (lve_eN_T hx hx1).2).1 (lve_eN_T hx hx1).1
  by_cases hc : InE (xiR x T) ∧ eN x < xiR x T
  · rw [xiE, if_pos hc]
    exact ⟨hc.1, hRT, hR1, hc.2, le_rfl, fun u hxu hu => hRm.trans_le (hmin u hxu hu)⟩
  · rw [xiE, if_neg hc]
    have hMm : max (xiR x T) (eN x) < m := max_lt hRm heNm
    have hNm : eN (max (xiR x T) (eN x)) < m := xi_eN_lt_SC hmS hMm
    exact ⟨eN_E _, (hT _ (hNm.trans hm1)).2 hNm, hNm.trans hm1,
      (le_max_right _ _).trans_lt (lt_eN _), (le_max_left _ _).trans (lt_eN _).le,
      fun u hxu hu => hNm.trans_le (hmin u hxu hu)⟩

/-- **At a strongly critical `y` above the gate, `R_y(T) = gxTh y T` is an `ε`-number above `ε_{y+1}`.** -/
theorem xiR_SC (H : XiLH S g T) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hgy : g < y) :
    xiR y T = gxTh y (Qt.qtAt S y) T ∧ InE (xiR y T) ∧ eN y < xiR y T := by
  have hdom := xiLH_dom H hgy
  have e := (xiR_gx hy hy1 T hdom).symm
  have hAt : GxAt (Qt.qtAt S y) := (Qt.qtU S).gxAt y
  have hy1' : y < Om 1 := by rw [← Rj.rj_Om1]; exact hy1
  have hTc : GxCl y (Qt.qtAt S y) T := (xi_dom_codes hy hy1 H.th).2 hdom
  have hEc : GxCl y (Qt.qtAt S y) Gg.ggE :=
    GxCl.of_gg (Sp.spE_cl ((Lu.lu_one_lt_E (Low.opow_eq_self_of_SC hy))))
  have hpT := gxTh_opow hy hAt hTc
  rw [H.eps] at hpT
  have hpE := gxTh_opow hy hAt hEc
  rw [Gg.ggE_spec.1] at hpE
  have hOE : gxTh y (Qt.qtAt S y) (Om 1) < gxTh y (Qt.qtAt S y) Gg.ggE := gxTh_lt GxCl.om Gg.ggE_spec.2
  rw [gxTh_Om1 hy hy1' hAt] at hOE
  have hle : eN y ≤ gxTh y (Qt.qtAt S y) Gg.ggE := eN_le hOE hpE.symm
  refine ⟨e, ?_, ?_⟩
  · rw [e]; exact hpT.symm
  · rw [e]; exact hle.trans_lt (gxTh_lt hEc H.gE)

theorem xiE_SC (H : XiLH S g T) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hgy : g < y) :
    xiE T y = xiR y T := by
  obtain ⟨-, h1, h2⟩ := xiR_SC H hy hy1 hgy
  rw [xiE, if_pos ⟨h1, h2⟩]

theorem xi_ups_SC (H : XiLH S g T) {u : Ordinal.{0}} (hu : UpsPt u) (hu1 : u < Om1) (hgu : g < u) : SC u :=
  Qc.qc_ups_SC u hu hu1 ε₀ (omega0_opow_epsilon 0) (H.ge.trans_lt hgu)

/-! ## The term system -/

/-- The constants of a term: `[c]` for the constant `c`; `P₀(c)` for a code `Ω₁ ≤ c < T`. -/
noncomputable def xiCs (T : Ordinal.{0}) : Ordinal.{0} ⊕ Ordinal.{0} → List Ordinal.{0}
  | Sum.inl c => [c]
  | Sum.inr c => if Om1 ≤ c ∧ c < T then (wP c).toList else [Om1]

/-- The value of a term: the constant, or the reading of the code. -/
noncomputable def xiVal : Ordinal.{0} ⊕ Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  | Sum.inl c => fun _ => c
  | Sum.inr c => fun x => xiR x c

/-- A term is visible at `x` when its constants are below `x`. -/
def xiCB (T : Ordinal.{0}) (t : Ordinal.{0} ⊕ Ordinal.{0}) (x : Ordinal.{0}) : Prop := ∀ p ∈ xiCs T t, p < x

theorem xiCB_inl {c x : Ordinal.{0}} : xiCB T (Sum.inl c) x ↔ c < x := by
  simp [xiCB, xiCs]

theorem xiCB_inr {c x : Ordinal.{0}} (hx1 : x < Om1) :
    xiCB T (Sum.inr c) x ↔ Om1 ≤ c ∧ c < T ∧ ∀ p ∈ wP c, p < x := by
  show (∀ p ∈ (if Om1 ≤ c ∧ c < T then (wP c).toList else [Om1]), p < x) ↔ _
  split_ifs with h
  · simp only [Finset.mem_toList]
    exact ⟨fun h' => ⟨h.1, h.2, h'⟩, fun h' => h'.2.2⟩
  · simp only [List.mem_singleton, forall_eq]
    exact ⟨fun h' => absurd h' (not_lt.2 hx1.le), fun h' => absurd ⟨h'.1, h'.2.1⟩ h⟩

theorem xiCB_dom (H : XiLH S g T) {c x : Ordinal.{0}} (hx1 : x < Om1) (h : xiCB T (Sum.inr c) x) :
    WDom S x c ∧ Om1 ≤ c ∧ c < T := by
  obtain ⟨h1, h2, h3⟩ := (xiCB_inr hx1).1 h
  exact ⟨Or.inr ⟨h1, h2.trans H.th, h3⟩, h1, h2⟩

theorem xi_Om1_dom (x : Ordinal.{0}) : WDom S x Om1 := by
  refine Or.inr ⟨le_rfl, ?_, ?_⟩
  · rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th
  · rw [(wP_spec S).2.1]; simp

theorem xi_le_val {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : WDom S x c)
    (hc1 : Om1 ≤ c) : x ≤ xiR x c := by
  rcases hc1.lt_or_eq with hlt | heq
  · exact (xiR_Om1 S hx hx1).symm.trans_le (xiR_lt S hx hx1 _ _ (xi_Om1_dom x) hc hlt).le
  · rw [← heq]; exact (xiR_Om1 S hx hx1).ge

theorem xi_lt_top (H : XiLH S g T) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : g < x)
    (t : Ordinal.{0} ⊕ Ordinal.{0}) (ht : xiCB T t x) : xiVal t x < ω ^ xiE T x := by
  obtain ⟨-, -, -, heN, hRE, -⟩ := xiE_facts H hx hx1 hgx
  cases t with
  | inl c =>
    have hc : c < x := xiCB_inl.1 ht
    exact hc.trans ((lt_eN x).trans (heN.trans_le (right_le_opow _ one_lt_omega0)))
  | inr c =>
    obtain ⟨hd, -, hcT⟩ := xiCB_dom H hx1 ht
    exact (xiR_lt S hx hx1 c T hd (xiLH_dom H hgx) hcT).trans_le (hRE.trans (right_le_opow _ one_lt_omega0))

/-! ## The term system, the layer, the base package -/

section Sys

variable (H : XiLH S g T)
include H

/-- At a `υ`-point above the gate the top is `R_υ(T)`. -/
theorem xi_top_ups {u : Ordinal.{0}} (hu : UpsPt u) (hu1 : u < Om1) (hgu : g < u) :
    ω ^ xiE T u = xiR u T ∧ InE (xiR u T) := by
  have huS := xi_ups_SC H hu hu1 hgu
  obtain ⟨-, hE, -⟩ := xiR_SC H huS hu1 hgu
  rw [xiE_SC H huS hu1 hgu]
  exact ⟨hE, hE⟩

theorem xi_rep {u : Ordinal.{0}} (hu : UpsPt u) (hu1 : u < Om1) (hgu : g < u) :
    ∀ v < ω ^ xiE T u, ∃ t, xiCB T t u ∧ xiVal t u = v := by
  intro v hv
  have huE := upsPt_inE hu
  rw [(xi_top_ups H hu hu1 hgu).1] at hv
  rcases lt_or_ge v u with hvu | huv
  · exact ⟨Sum.inl v, xiCB_inl.2 hvu, rfl⟩
  obtain ⟨hRT, hR1⟩ := xiR_T S huE hu1 T (xiLH_dom H hgu)
  have hvT : v ∈ Tset u := vz_T_down huE hu1 hRT hR1 hv.le
  obtain ⟨c, hc, rfl⟩ := xiR_onto S huE hu1 v hvT (hv.trans hR1)
  rcases hc with hcu | ⟨h1, h2, h3⟩
  · rw [xiR_small S huE hu1 c hcu] at huv
    exact absurd hcu (not_lt.2 huv)
  · have hcT : c < T := by
      by_contra hTc
      push Not at hTc
      rcases hTc.lt_or_eq with hlt | heq
      · exact absurd (xiR_lt S huE hu1 T c (xiLH_dom H hgu) (Or.inr ⟨h1, h2, h3⟩) hlt) (not_lt.2 hv.le)
      · rw [heq] at hv; exact lt_irrefl _ hv
    exact ⟨Sum.inr c, (xiCB_inr hu1).2 ⟨h1, hcT, h3⟩, rfl⟩

omit H in
theorem xi_ups_of_gt {l : Ordinal.{0}} (hgl : g < upsilon l) : UpsPt (upsilon l) := by
  refine upsPt_upsilon (pos_iff_ne_zero.2 fun h => ?_)
  rw [h, upsilon_zero] at hgl
  exact absurd hgl (not_lt.2 zero_le)

theorem xi_top_lt_next {l : Ordinal.{0}} (hl1 : l < Om1) (hgl : g < upsilon l) :
    ω ^ xiE T (upsilon l) < upsilon (l + ω + 1) := by
  have hu := xi_ups_of_gt hgl
  have hu1 : upsilon l < Om1 := ups_lt_Om1 l hl1
  have huS := xi_ups_SC H hu hu1 hgl
  obtain ⟨-, -, -, -, -, hlt⟩ := xiE_facts H (upsPt_inE hu) hu1 hgl
  have hlu : upsilon l < upsilon (l + ω + 1) :=
    upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  rw [(xi_top_ups H hu hu1 hgl).1, ← xiE_SC H huS hu1 hgl]
  exact hlt _ hlu (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _)))

omit H in
theorem xi_le_iff {x c d : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : WDom S x c) (hd : WDom S x d) :
    xiR x c ≤ xiR x d ↔ c ≤ d := by
  constructor
  · intro h
    by_contra hdc
    push Not at hdc
    exact absurd (xiR_lt S hx hx1 d c hd hc hdc) (not_lt.2 h)
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact (xiR_lt S hx hx1 c d hc hd hlt).le
    · rw [heq]

theorem xi_pkg {l : Ordinal.{0}} (hl1 : l < Om1) (hgl : g < upsilon l) (t : Ordinal.{0} ⊕ Ordinal.{0})
    (ht : xiCB T t (upsilon l)) (h1 : 1 ≤ xiVal t (upsilon l))
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (xiVal t) := by
  classical
  have hρ1 : upsilon l < Om1 := ups_lt_Om1 l hl1
  have hρE : InE (upsilon l) := upsPt_inE R.ρU
  cases t with
  | inl c =>
    have hc : c < upsilon l := xiCB_inl.1 ht
    refine ⟨h1, hc.trans (R.ρτ.trans R.τδ), ∅, {c}, WZ.empty.insZ hc,
      (show c ∈ (∅ : Finset Ordinal.{0}) ∪ {c} by simp), fun A f _ hZ C => ?_⟩
    have hcA : c ∈ A := hZ (by simp)
    show c ≤ f c
    rw [C.fix c hcA hc]
  | inr c =>
    obtain ⟨hd, hc1, hcT⟩ := xiCB_dom H hρ1 ht
    have hPρ : ∀ p ∈ wP c, p < upsilon l := by
      rcases hd with h | ⟨-, -, h⟩
      · exact absurd (h.trans hρ1) (not_lt.2 hc1)
      · exact h
    have hI := H.img _ _ _ c R hgl hd hc1 hcT.le
    obtain ⟨W, Z, w, hm, hvT, hv1, b⟩ := Gn.gnI_use R hI
    have wzc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (wP c) :=
      ⟨by simp, fun z hz => hPρ z hz, by simp⟩
    have hw' := w.union wzc
    rw [Finset.union_empty] at hw'
    refine ⟨h1, Gn.gn_lt_δ R hvT hv1, W, Z ∪ wP c, hw', ?_, fun A f hW hZ C => ?_⟩
    · rcases Finset.mem_union.1 hm with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    have hZA : ↑Z ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
    obtain ⟨-, -, hle⟩ := b A f hW hZA C
    have hfρ : f (upsilon l) < upsilon l := C.low _ C.rho
    have hfE : InE (f (upsilon l)) := upsPt_inE C.ups
    have hdf : WDom S (f (upsilon l)) c := Or.inr ⟨hc1, hcT.trans H.th, fun p hp =>
      C.above p (hZ (Finset.mem_coe.2 (Finset.mem_union_right _ hp))) (hPρ p hp)⟩
    have e := (xiR_pi hfE hρE hfρ hρ1 c hdf).2
    show xiR (f (upsilon l)) c ≤ f (xiR (upsilon l) c)
    rw [← e]; exact hle

theorem xi_rs {l : Ordinal.{0}} (hl1 : l < Om1) (hgl : g < upsilon l) (t : Ordinal.{0} ⊕ Ordinal.{0})
    (ht : xiCB T t (upsilon l)) : RsStep l (xiVal t) := by
  intro R htg
  have hρ1 : upsilon l < Om1 := ups_lt_Om1 l hl1
  have hρE : InE (upsilon l) := upsPt_inE R.ρU
  cases t with
  | inl c =>
    exact rs_rstT (t := OT.k c) R (show OT.CB (OT.k c) (upsilon l) from xiCB_inl.1 ht) htg
  | inr c =>
    obtain ⟨hd, hc1, hcT⟩ := xiCB_dom H hρ1 ht
    have hPρ : ∀ p ∈ wP c, p < upsilon l := by
      rcases hd with h | ⟨-, -, h⟩
      · exact absurd (h.trans hρ1) (not_lt.2 hc1)
      · exact h
    have hdσ : ∀ σ, (∀ p ∈ wP c, p < σ) → WDom S σ c := fun σ hσ => Or.inr ⟨hc1, hcT.trans H.th, hσ⟩
    refine rs_rstF (T := xiVal (Sum.inr c)) (C := wP c) R hPρ (xi_le_val hρE hρ1 hd hc1) ?_ ?_ ?_ htg
    · obtain ⟨m, -, -, -, hmin, hTm, -⟩ := xi_next hρE hρ1
      obtain ⟨hRT, hR1⟩ := xiR_T S hρE hρ1 c hd
      have hnx := upsilon_isNext l
      exact ((hTm _ hR1).1 hRT).trans_le (hmin _ hnx.1 hnx.2.1)
    · intro σ _ hB hσ _
      exact (xiR_pi hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 c (hdσ σ hσ)).2
    · intro σ hσE hσρ _ hσ
      have hσ1 : σ < Om1 := hσρ.trans hρ1
      obtain ⟨m, -, -, -, hmin, hTm, -⟩ := xi_next hσE hσ1
      obtain ⟨hRT, hR1⟩ := xiR_T S hσE hσ1 c (hdσ σ hσ)
      exact ((hTm _ hR1).1 hRT).trans_le (hmin _ hσρ R.ρU)

theorem xi_uni_le {σ ρ : Ordinal.{0}} (_ : UpsPt σ) (_ : UpsPt ρ) (hB : Bases σ ρ) (hg : g < σ)
    (t u : Ordinal.{0} ⊕ Ordinal.{0}) (ht : xiCB T t σ) (hu : xiCB T u σ) :
    xiVal t ρ ≤ xiVal u ρ ↔ xiVal t σ ≤ xiVal u σ := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  cases t with
  | inl a =>
    cases u with
    | inl b => exact Iff.rfl
    | inr d =>
      have ha : a < σ := xiCB_inl.1 ht
      obtain ⟨hd, hd1, -⟩ := xiCB_dom H hσ1 hu
      refine iff_of_true ?_ ?_
      · exact (ha.trans hB.2.2.1).le.trans (xi_le_val hB.2.1 hB.2.2.2 (wDom_mono hB.2.2.1.le hd) hd1)
      · exact ha.le.trans (xi_le_val hB.1 hσ1 hd hd1)
  | inr c =>
    obtain ⟨hc, hc1, -⟩ := xiCB_dom H hσ1 ht
    cases u with
    | inl b =>
      have hb : b < σ := xiCB_inl.1 hu
      refine iff_of_false ?_ ?_
      · exact not_le.2 ((hb.trans hB.2.2.1).trans_le (xi_le_val hB.2.1 hB.2.2.2 (wDom_mono hB.2.2.1.le hc) hc1))
      · exact not_le.2 (hb.trans_le (xi_le_val hB.1 hσ1 hc hc1))
    | inr d =>
      obtain ⟨hd, -, -⟩ := xiCB_dom H hσ1 hu
      show xiR ρ c ≤ xiR ρ d ↔ xiR σ c ≤ xiR σ d
      rw [xi_le_iff hB.2.1 hB.2.2.2 (wDom_mono hB.2.2.1.le hc) (wDom_mono hB.2.2.1.le hd),
        xi_le_iff hB.1 hσ1 hc hd]

theorem xi_small (t : Ordinal.{0} ⊕ Ordinal.{0}) :
    (∀ x y, xiVal t x = xiVal t y) ∨ (∀ x, InE x → x < Om1 → g < x → xiCB T t x → x ≤ xiVal t x) := by
  cases t with
  | inl c => exact Or.inl fun _ _ => rfl
  | inr c =>
    refine Or.inr fun x hx hx1 _ ht => ?_
    obtain ⟨hd, hc1, -⟩ := xiCB_dom H hx1 ht
    exact xi_le_val hx hx1 hd hc1

/-- **The term system of the layer of `T`**: constants and the codes `Ω₁ ≤ c < T`, read by `R_x`. -/
noncomputable def xiSys : GdSys g where
  Tm := Ordinal.{0} ⊕ Ordinal.{0}
  val := xiVal
  CB := xiCB T
  cs := xiCs T
  cst := Sum.inl
  top := fun x => ω ^ xiE T x
  cb_cst := fun _ _ h => h
  cb_iff := fun _ _ _ _ hc => hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => xiCB_inl.2 h
  lt_top := fun l hl hl1 hg t ht => xi_lt_top H (ups_inE hl) (ups_lt_Om1 l hl1) hg t ht
  one_le_top := fun _ _ _ _ => one_le_iff_pos.2 (opow_pos _ omega0_pos)
  rep := fun l _ hl1 hg v hv => xi_rep H (xi_ups_of_gt hg) (ups_lt_Om1 l hl1) hg v hv
  top_lt := fun _ _ hl1 hg => xi_top_lt_next H hl1 hg
  pkg := fun _ _ hl1 hg t ht h1 R => xi_pkg H hl1 hg t ht h1 R
  rs := fun _ _ hl1 hg t ht => xi_rs H hl1 hg t ht
  uni_le := fun _ _ hσ hρ hB hg t u ht hu => xi_uni_le H hσ hρ hB hg t u ht hu
  small := xi_small H

theorem xi_exact {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (t : Ordinal.{0} ⊕ Ordinal.{0}) (ht : xiCB T t σ) :
    xiVal t ρ ∈ TB ρ σ ∧ pi σ ρ (xiVal t ρ) = xiVal t σ := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  cases t with
  | inl c =>
    have hc : c < σ := xiCB_inl.1 ht
    exact ⟨mem_TB_of_lt hB hc, pi_lt hB hc⟩
  | inr c =>
    obtain ⟨hd, -, -⟩ := xiCB_dom H hσ1 ht
    exact xiR_pi hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 c hd

theorem xi_exp_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : g < σ) :
    xiE T ρ ∈ TB ρ σ ∧ pi σ ρ (xiE T ρ) = xiE T σ := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  rw [xiE_SC H (xi_ups_SC H hρ hB.2.2.2 (hg.trans hB.2.2.1)) hB.2.2.2 (hg.trans hB.2.2.1),
    xiE_SC H (xi_ups_SC H hσ hσ1 hg) hσ1 hg]
  exact xiR_pi hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 T (xiLH_dom H hg)

theorem xi_top_wit {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hg : g < ρ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ xiE T ρ ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx g ρ A f →
        (∃ e', f (ω ^ xiE T ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ ω ^ xiE T (f ρ) ≤ f (ω ^ xiE T ρ) := by
  have hρE := upsPt_inE h.ρU
  obtain ⟨htop, hRE⟩ := xi_top_ups H h.ρU h.ρ1 hg
  rw [htop]
  have hρR : ρ < xiR ρ T := (xiR_Om1 S hρE h.ρ1).symm.trans_lt
    (xiR_lt S hρE h.ρ1 _ _ (xi_Om1_dom ρ) (xiLH_dom H hg) (xiLH_Om1_lt H))
  have hI := H.img ρ τ δ T h hg (xiLH_dom H hg) (xiLH_Om1_lt H).le le_rfl
  obtain ⟨W, Z, w, hTW, hb⟩ := Yw.ywTopWit_of_GnI h hRE hρR hI
  refine ⟨W, Z, w, hTW, fun A f hW hZ C => ?_⟩
  obtain ⟨h1, h2⟩ := hb A f hW hZ C.1
  refine ⟨h1, ?_⟩
  have hfρ := C.lt hg
  have hfU : UpsPt (f ρ) := C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  rw [(xi_top_ups H hfU hfρ1 hfρ).1, ← (xiR_pi (upsPt_inE hfU) hρE (C.low ρ C.rho) h.ρ1 T (xiLH_dom H hfρ)).2]
  exact h2

/-- **THE LAYER OF THE CODE BOUND `T`.** -/
noncomputable def xiLay : GdLay g where
  sys := xiSys H
  E := xiE T
  top_eq := fun _ _ _ _ => rfl
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (xiE_facts H hx hx1 hg).1
    ((lt_eN x).trans (xiE_facts H hx hx1 hg).2.2.2.1).le
  exp_lt := fun x hx hx1 hg => (xiE_facts H hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (lt_eN x).trans ((xiE_facts H hx hx1 hg).2.2.2.1.trans_le
    (right_le_opow _ one_lt_omega0))
  top_lt_ups := fun x u hx hx1 hg hxu hu => by
    show ω ^ xiE T x < u
    rw [show ω ^ xiE T x = xiE T x from (xiE_facts H hx hx1 hg).1]
    exact (xiE_facts H hx hx1 hg).2.2.2.2.2 u hxu hu
  lt_top_E := fun x hx hx1 hg t ht => xi_lt_top H hx hx1 hg t ht
  exact := fun _ _ _ _ hB _ t ht => xi_exact H hB t ht
  exp_pi := fun _ _ hσ hρ hB hg => xi_exp_pi H hσ hρ hB hg
  top_wit := fun _ _ _ h hg => xi_top_wit H h hg

/-- **The base package of the layer of `T`.** -/
noncomputable def xiB : GdB where
  g := g
  K := xiLay H
  ek := fun x hx hx1 hg => (xiE_facts H hx hx1 hg).1
  mem := fun x hx hx1 hg => (xiE_facts H hx hx1 hg).2.1

theorem xiB_g : (xiB H).g = g := rfl

theorem xiB_E (x : Ordinal.{0}) : (xiB H).K.E x = xiE T x := rfl

/-- **`Zm.ZmLayA (qtU S) S B` for every atom index `B` with `Γ(B) ≤ T`** (the gate below `tdK S`). -/
theorem xi_layA (hgK : g < Td.tdK S) {B : Ordinal.{0}} (hB : Gc.gcG B ≤ T) : Zm.ZmLayA (Qt.qtU S) S B := by
  have hO1T : Om 1 ≤ T := by rw [← Rj.rj_Om1]; exact (xiLH_Om1_lt H).le
  refine ⟨xiB H, T, hB, hgK, H.th.le, hO1T, H.eps, ?_, ?_, ?_, ?_⟩
  · intro y hy hy1 hgy
    have hy1' : y < Om1 := by rw [Rj.rj_Om1]; exact hy1
    rw [xiB_E, xiE_SC H hy hy1' hgy]
    exact (xiR_SC H hy hy1' hgy).1
  · intro Z c hgZ hc hcT
    have hcθ : c < ConjT.th S := hcT.trans H.th
    by_cases hc1 : c < Om1
    · refine ⟨Sum.inl c, fun y hy hy1 hZy => ?_⟩
      have hcy' : GxCl y (Qt.qtAt S y) c := hc.mono hZy ((Qt.qtU S).mono Z y hZy)
      have hcy : c < y := GxCl.lt_of_lt_Om1 hy ((Qt.qtU S).gxAt y) hcy' (by rw [← Rj.rj_Om1]; exact hc1)
      exact ⟨xiCB_inl.2 hcy, (gxTh_small hcy.le).symm⟩
    · push Not at hc1
      refine ⟨Sum.inr c, fun y hy hy1 hZy => ?_⟩
      have hy1' : y < Om1 := by rw [Rj.rj_Om1]; exact hy1
      have hcy' : GxCl y (Qt.qtAt S y) c := hc.mono hZy ((Qt.qtU S).mono Z y hZy)
      have hd : WDom S y c := (xi_dom_codes hy hy1' hcθ).1 hcy'
      have hPy : ∀ p ∈ wP c, p < y := by
        rcases hd with h | ⟨-, -, h⟩
        · exact absurd (h.trans hy1') (not_lt.2 hc1)
        · exact h
      exact ⟨(xiCB_inr hy1').2 ⟨hc1, hcT, hPy⟩, (xiR_gx hy hy1' c hd).symm⟩
  · intro Z hZ hKZ
    have hO : GxCl (Om 1) ((Qt.qtU S).At (Om 1)) T :=
      (Qt.qt_codes (SC_Om (by norm_num)) le_rfl H.th).2 (Vd.vd_K_th T H.th)
    rcases lt_or_ge Z (Om 1) with hZ1 | hZ1
    · have hZ1' : Z < Om1 := by rw [Rj.rj_Om1]; exact hZ1
      exact (xi_dom_codes hZ hZ1' H.th).2 (xiLH_dom H (hgK.trans_le hKZ))
    · exact hO.mono hZ1 ((Qt.qtU S).mono _ _ hZ1)
  · intro x hx hx1 hgx
    exact (xiE_facts H hx hx1 hgx).2.2.2.1

end Sys

end Googology.Trans.PoR.InaccPsi.R2.Xi
