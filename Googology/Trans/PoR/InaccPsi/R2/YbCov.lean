import Googology.Trans.PoR.InaccPsi.R2.XoRef
import Googology.Trans.PoR.InaccPsi.R2.XaRep

/-!
# The covering lemma for the repaired restriction `Xo.XoR`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Xo.XoCarry` asks the image bound only of decompositions with `Xo.XoR S λ μ`.  A reach point with no such
decomposition would make the carry silent there.  Here every countable `x < υ_{λ+β}` gets ONE well-formed moving-leaf
decomposition that is restricted at every `μ` in a TAIL (`γ < υ_μ < υ_λ` for some `γ < υ_λ`), by the induction of
`Xa.xaRep`:

* `ybFin_tail`, `ybOld_tail` (an old decomposition is restricted above the finitely many points and low parameters it
  has below `υ_λ`; `Wf.wfR_of`);
* `YbK S x` (**the inacc-free visibility closure with small members below `x`**: the clauses of `Vd.VdK` without
  `inacc` / `inaccW`, `0` small, plus fixed atoms `v` with `Vd.VdLtIn v Γ₀`) and `ybK_cov` (**every member is the
  value of a restricted, non-closed level term**: small members by the induction hypothesis, a fixed atom by the
  padded constant `lo 0 + lc v` (same value and image, not closed), the operations by the level constructors; no
  closed sub-term occurs above an atom, and a collapse `ψ_π(e)` with `π ≠ Ω₁` is uncountable, `yb_psi_ge`);
  `ybLtIn_mono`, `yb_mu_pos`;
* `YbLevK S λ β` (**the open level statement**: every uncountable level `M` of a `ϑ`-node `x = ϑ^{υ_{λ+h}}(Ω₁·M+η)`
  below `υ_{λ+β}` whose data is NOT below `υ_λ` lies in `YbK S x`);
* `ybCover` (**the covering lemma**: under `YbLevK`, every countable `x < υ_{λ+β}` is `YbCov`): leaves `lo x`
  (`x < υ_{λ+1}`), `sg h x` (`x = υ_{λ+h}`), sums, and `ϑ`-nodes whose level is the term of a countable level (below
  `x`: `CitedLv.lvLevel_lt_vt`), the constant `lc M` (data below `υ_λ`), or the `YbK` term;
* `ybLow_uc`, `ybLow_th` (the data tests that make `lc M` restricted on a tail);
* the witnesses: `ybTail_lam` (`λ`), `ybTail_Xj` (`E′`, value `r(λ+X′)`), `ybTail_wwX` (the gap witness
  `ϑ^{u₁}(Ω₁·B₂+λ)`), `ybCov_wit` (λ, `r(λ+X′)`, `wwX` are `YbCov` with no level hypothesis).

No new axiom.  New definitions: `YbTail`, `YbOs`, `YbCov`, `YbK`, `YbLevK` (statements and an inductive predicate;
no repo definition is changed).  Offsets: `ybOs_lo` … `ybOs_th` (every covered term has a finite offset set below
`β`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **Restricted on a tail**: some `γ < υ_λ` such that `E` is restricted at every `μ` with `γ < υ_μ < υ_λ`. -/
def YbTail (S : InaccSeq.{0}) (l : Ordinal.{0}) (E : Xo.XoE) : Prop :=
  ∃ γ < upsilon l, ∀ μ, γ < upsilon μ → Bases (upsilon μ) (upsilon l) → Xo.XoR S l μ E

/-- **Finitely many offsets**: a finite set of offsets below `β` such that `E` has its offsets in every larger set. -/
def YbOs (l β : Ordinal.{0}) (E : Xo.XoE) : Prop :=
  ∃ O : Finset Ordinal.{0}, (∀ d ∈ O, d < β) ∧ ∀ Os : Finset Ordinal.{0}, O ⊆ Os → Xo.XoOs l Os E

/-- **Covered**: a well-formed, non-closed decomposition with value `x`, restricted on a tail, with finitely many
offsets. -/
def YbCov (S : InaccSeq.{0}) (l β x : Ordinal.{0}) : Prop :=
  ∃ E : Xo.XoE, Xo.XoWF S l β E ∧ Xo.xoVal S l E = x ∧ ¬ Xo.XoCl E ∧ YbTail S l E ∧ YbOs l β E

/-- **The inacc-free visibility closure with small members below `x`** (`Vd.VdK` at `s = 0` without the
inaccessibles), with fixed atoms: every level whose data is below `Γ₀` (`Vd.VdLtIn v Γ₀`; for example a value with a
derivation without small members, which may use inaccessibles) may be taken as an atom. -/
inductive YbK (S : InaccSeq.{0}) (x : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {y : Ordinal.{0}} : y < x → YbK S x y
  | fix {v : Ordinal.{0}} : Vd.VdLtIn v (gamma 0) → YbK S x v
  | add {a b : Ordinal.{0}} : YbK S x a → YbK S x b → YbK S x (a + b)
  | phi {a b : Ordinal.{0}} : YbK S x a → YbK S x b → YbK S x (veblen a b)
  | om {a : Ordinal.{0}} : YbK S x a → YbK S x (Om a)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om 1 → YbK S x π → YbK S x e → YbK S x (S.psi e π)

/-- **The open level statement**: the uncountable levels of `ϑ`-nodes below `υ_{λ+β}` whose data is not below
`υ_λ` lie in the inacc-free closure with small members below the node value. -/
def YbLevK (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ h M η : Ordinal.{0}, 0 < h → h < β → Om1 ≤ M → η < Om1 → η ∈ Tset (upsilon (l + h)) →
    Om1 * M + η ∈ Tset (upsilon (l + h)) →
    Om1 * M + η < OmTwo → upsilon (l + h) ≤ vt (upsilon (l + h)) (Om1 * M + η) →
    vt (upsilon (l + h)) (Om1 * M + η) < upsilon (l + β) →
    (¬ ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ)) →
    YbK S (vt (upsilon (l + h)) (Om1 * M + η)) M

variable {S : InaccSeq.{0}}

/-! ## Tails -/

theorem yb_ups_pos {l : Ordinal.{0}} (hl0 : 0 < l) : 0 < upsilon l := InE.pos (upsPt_inE (upsPt_upsilon hl0))

/-- A finite set below `υ_λ` has a bound below `υ_λ`. -/
theorem ybFin_tail {l : Ordinal.{0}} (hl0 : 0 < l) (F : Finset Ordinal.{0}) (hF : ∀ q ∈ F, q < upsilon l) :
    ∃ γ < upsilon l, ∀ q ∈ F, q ≤ γ :=
  ⟨F.sup id, (Finset.sup_lt_iff (yb_ups_pos hl0)).2 hF, fun q hq => Finset.le_sup (f := id) hq⟩

/-- **An old decomposition is restricted on a tail** (above its low points and low parameters). -/
theorem ybOld_tail {l β : Ordinal.{0}} (hl0 : 0 < l) (E : Vr.VrE) (hW : Vr.VrWF l β E) :
    ∃ γ < upsilon l, ∀ μ, γ < upsilon μ → Bases (upsilon μ) (upsilon l) → Wf.WfR l μ E := by
  obtain ⟨γ, hγ, hle⟩ := ybFin_tail hl0 ((Vr.vrPts l E).filter (· < upsilon l) ∪ Wf.wfPrm l E) (by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact (Finset.mem_filter.1 h).2
    · exact Wf.wfPrm_lt l E q h)
  refine ⟨γ, hγ, fun μ hμ hB => Wf.wfR_of hl0 hB E hW (fun z hz hzl => ?_) (fun q hq => ?_)⟩
  · exact (hle z (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hz, hzl⟩))).trans_lt hμ
  · exact (hle q (Finset.mem_union_right _ hq)).trans_lt hμ

theorem ybCov_old {l β x : Ordinal.{0}} (hl0 : 0 < l) (E : Vr.VrE) (hW : Vr.VrWF l β E)
    (hv : Vr.vrVal l E = x) (hO : YbOs l β (.old E)) : YbCov S l β x := by
  obtain ⟨γ, hγ, hR⟩ := ybOld_tail hl0 E hW
  exact ⟨.old E, hW, hv, fun h => h, ⟨γ, hγ, hR⟩, hO⟩

/-! ## Offsets -/

theorem ybOs_lo (l β c : Ordinal.{0}) : YbOs l β (.old (.lo c)) := ⟨∅, by simp, fun _ _ => trivial⟩

theorem ybOs_sg {l β h y : Ordinal.{0}} (hβ : h < β) : YbOs l β (.old (.sg h y)) :=
  ⟨{h}, by simpa using hβ, fun _ hs => hs (Finset.mem_singleton_self h)⟩

theorem ybOs_lc (l β M : Ordinal.{0}) : YbOs l β (.lc M) := ⟨∅, by simp, fun _ _ => trivial⟩

theorem ybOs_union {l β : Ordinal.{0}} {E F : Xo.XoE} (hE : YbOs l β E) (hF : YbOs l β F) :
    ∃ O : Finset Ordinal.{0}, (∀ d ∈ O, d < β) ∧
      ∀ Os : Finset Ordinal.{0}, O ⊆ Os → Xo.XoOs l Os E ∧ Xo.XoOs l Os F := by
  obtain ⟨A, hA, hA'⟩ := hE
  obtain ⟨B, hB, hB'⟩ := hF
  refine ⟨A ∪ B, fun d hd => ?_, fun Os hs => ⟨hA' Os (Finset.union_subset_left hs),
    hB' Os (Finset.union_subset_right hs)⟩⟩
  rcases Finset.mem_union.1 hd with h | h
  · exact hA d h
  · exact hB d h

theorem ybOs_add {l β : Ordinal.{0}} {E F : Xo.XoE} (hE : YbOs l β E) (hF : YbOs l β F) :
    YbOs l β (.add E F) := by
  obtain ⟨O, hO, h⟩ := ybOs_union hE hF
  exact ⟨O, hO, fun Os hs => h Os hs⟩

theorem ybOs_phi {l β : Ordinal.{0}} {E F : Xo.XoE} (hE : YbOs l β E) (hF : YbOs l β F) :
    YbOs l β (.phi E F) := by
  obtain ⟨O, hO, h⟩ := ybOs_union hE hF
  exact ⟨O, hO, fun Os hs => h Os hs⟩

theorem ybOs_coll {l β : Ordinal.{0}} {E F : Xo.XoE} (hE : YbOs l β E) (hF : YbOs l β F) :
    YbOs l β (.coll E F) := by
  obtain ⟨O, hO, h⟩ := ybOs_union hE hF
  exact ⟨O, hO, fun Os hs => h Os hs⟩

theorem ybOs_om {l β : Ordinal.{0}} {E : Xo.XoE} (hE : YbOs l β E) : YbOs l β (.om E) := hE

theorem ybOs_th {l β h : Ordinal.{0}} {E F : Xo.XoE} (hβ : h < β) (hE : YbOs l β E) (hF : YbOs l β F) :
    YbOs l β (.th h E F) := by
  obtain ⟨O, hO, hc⟩ := ybOs_union hE hF
  refine ⟨insert h O, fun d hd => ?_, fun Os hs => ⟨hs (Finset.mem_insert_self h O),
    (hc Os ((Finset.subset_insert h O).trans hs)).1, (hc Os ((Finset.subset_insert h O).trans hs)).2⟩⟩
  rcases Finset.mem_insert.1 hd with rfl | h'
  · exact hβ
  · exact hO d h'

theorem ybTail_mono {l : Ordinal.{0}} {E : Xo.XoE} {γ : Ordinal.{0}} (hγ : γ < upsilon l)
    (h : ∀ μ, γ < upsilon μ → Bases (upsilon μ) (upsilon l) → Xo.XoR S l μ E) : YbTail S l E := ⟨γ, hγ, h⟩

/-- Two tails give one. -/
theorem ybTail_two {l : Ordinal.{0}} {E F : Xo.XoE} (hE : YbTail S l E) (hF : YbTail S l F) :
    ∃ γ < upsilon l, ∀ μ, γ < upsilon μ → Bases (upsilon μ) (upsilon l) → Xo.XoR S l μ E ∧ Xo.XoR S l μ F := by
  obtain ⟨a, ha, hA⟩ := hE
  obtain ⟨b, hb, hB⟩ := hF
  exact ⟨max a b, max_lt ha hb, fun μ hμ hBs =>
    ⟨hA μ ((le_max_left a b).trans_lt hμ) hBs, hB μ ((le_max_right a b).trans_lt hμ) hBs⟩⟩

/-! ## The inacc-free closure gives restricted level terms -/

theorem yb_mu_pos {μ : Ordinal.{0}} (h : upsilon 0 < upsilon μ) : 0 < μ :=
  pos_iff_ne_zero.2 fun e => by rw [e] at h; exact lt_irrefl _ h

/-- `Vd.VdLtIn` is monotone in the bound. -/
theorem ybLtIn_mono {M a b : Ordinal.{0}} (h : Vd.VdLtIn M a) (hab : a ≤ b) : Vd.VdLtIn M b := by
  rcases h with ⟨h1, h2⟩ | ⟨S', h1, h2, q, hq, hqa, hd⟩
  · exact Or.inl ⟨h1, h2.trans_le hab⟩
  · exact Or.inr ⟨S', h1, h2, q, hq, hqa.trans hab, hd⟩

/-- **A collapse at `π ≠ Ω₁` is uncountable.** -/
theorem yb_psi_ge {π e : Ordinal.{0}} (hπ : S.InR π) (hπ1 : π ≠ Om 1) : Om1 ≤ S.psi e π := by
  have hO1 : Om1 = Om 1 := Br.Om1_eq
  rw [hO1]
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact (InaccSeq.Om_one_lt_psiI e n).le
  · have hs : s ≠ 0 := fun h => hπ1 (by rw [h, zero_add])
    have h1 : (1 : Ordinal.{0}) ≤ s := Order.one_le_iff_ne_zero.2 hs
    exact ((Om_le_Om.2 h1).trans_lt (InaccSeq.psiS_bounds e s).1).le

/-- **Every member of `YbK S x` is the value of a well-formed, non-closed level term restricted on a tail**, given
that every countable `y < x` is covered. -/
theorem ybK_cov {l β x : Ordinal.{0}} (hl0 : 0 < l) (IH : ∀ y, y < x → YbCov S l β y) :
    ∀ M, YbK S x M → YbCov S l β M := by
  intro M hM
  induction hM with
  | small h => exact IH _ h
  | @fix v hv =>
    -- the padded constant `lo 0 + lc v` (same value, not closed)
    refine ⟨.add (.old (.lo 0)) (.lc v), ⟨(yb_ups_pos (l := succ l) (lt_of_le_of_lt zero_le (lt_succ l))), trivial⟩,
      by show (0 : Ordinal.{0}) + v = v; rw [zero_add], fun h => h.1,
      ⟨upsilon 0, upsilon_normal.strictMono hl0, fun μ hμ hB => ⟨?_, ?_, fun h => h.1.elim⟩⟩,
      ybOs_add (ybOs_lo l β 0) (ybOs_lc l β v)⟩
    · exact (Wf.wfR_lo_iff hB (yb_ups_pos hl0)).2 (InE.pos hB.1)
    · exact ybLtIn_mono hv (Gq.gq_gam_le_ups S (upsPt_upsilon (yb_mu_pos hμ)))
  | add _ _ ih1 ih2 =>
    obtain ⟨L1, w1, v1, c1, t1, o1⟩ := ih1
    obtain ⟨L2, w2, v2, c2, t2, o2⟩ := ih2
    obtain ⟨γ, hγ, hR⟩ := ybTail_two t1 t2
    refine ⟨.add L1 L2, ⟨w1, w2⟩, by show Xo.xoVal S l L1 + Xo.xoVal S l L2 = _; rw [v1, v2],
      fun h => c1 h.1, ⟨γ, hγ, fun μ hμ hB => ⟨(hR μ hμ hB).1, (hR μ hμ hB).2, fun h => absurd h.1 c1⟩⟩,
      ybOs_add o1 o2⟩
  | phi _ _ ih1 ih2 =>
    obtain ⟨L1, w1, v1, c1, t1, o1⟩ := ih1
    obtain ⟨L2, w2, v2, c2, t2, o2⟩ := ih2
    obtain ⟨γ, hγ, hR⟩ := ybTail_two t1 t2
    refine ⟨.phi L1 L2, ⟨w1, w2⟩, by show veblen (Xo.xoVal S l L1) (Xo.xoVal S l L2) = _; rw [v1, v2],
      fun h => c1 h.1, ⟨γ, hγ, fun μ hμ hB => ⟨(hR μ hμ hB).1, (hR μ hμ hB).2, fun h => absurd h.1 c1⟩⟩,
      ybOs_phi o1 o2⟩
  | om _ ih =>
    obtain ⟨L1, w1, v1, c1, ⟨γ, hγ, hR⟩, o1⟩ := ih
    exact ⟨.om L1, w1, by show Om (Xo.xoVal S l L1) = _; rw [v1], c1, ⟨γ, hγ,
      fun μ hμ hB => ⟨hR μ hμ hB, fun h => absurd h c1⟩⟩, ybOs_om o1⟩
  | @coll π e hπ hπ1 _ _ ihp ihe =>
    obtain ⟨Lp, wp, vp, cp, tp, op⟩ := ihp
    obtain ⟨Le, we, ve, ce, te, oe⟩ := ihe
    obtain ⟨γ, hγ, hR⟩ := ybTail_two tp te
    have hval : S.psi (Xo.xoVal S l Le) (Xo.xoVal S l Lp) = S.psi e π := by rw [vp, ve]
    refine ⟨.coll Lp Le, ⟨wp, we⟩, hval, fun h => cp h.1, ⟨γ, hγ, fun μ hμ hB =>
      ⟨(hR μ hμ hB).1, (hR μ hμ hB).2, fun h => absurd h.1 cp, fun h => ?_⟩⟩, ybOs_coll op oe⟩
    rw [hval] at h
    exact absurd h (not_lt.2 (yb_psi_ge hπ hπ1))

/-! ## Constant levels with low data -/

/-- `lc M` is restricted on a tail if its data is below some `c < υ_λ`. -/
theorem ybLc_tail {l M : Ordinal.{0}} (hlow : ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ)) :
    YbTail S l (.lc M) := by
  obtain ⟨c, hc, h⟩ := hlow
  exact ⟨c, hc, fun μ hμ _ => h μ hμ⟩

/-- **Low data below `B₂`**: `ucDat M < υ_λ`. -/
theorem ybLow_uc {l M : Ordinal.{0}} (hM : M < Uc.ucB) (hd : Uc.ucDat M < upsilon l) :
    ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ) :=
  ⟨Uc.ucDat M, hd, fun _ hμ => Or.inl ⟨hM, hμ⟩⟩

/-- **Low data on `[B₂, θ)`**: the `K⁽⁰⁾`-datum below a strongly critical `q < υ_λ`. -/
theorem ybLow_th {l M q : Ordinal.{0}} (hB : Uc.ucB ≤ M) (hθ : M < ConjT.th S) (hq : SC q) (hql : q < upsilon l)
    (hd : Vd.vdD S 0 M < q) : ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ) :=
  ⟨q, hql, fun _ hμ => Or.inr ⟨S, hB, hθ, q, hq, hμ.le, hd⟩⟩

/-! ## The covering lemma -/

/-- **The covering lemma**: under `YbLevK`, every countable `x < υ_{λ+β}` (`0 < λ`) is the value of a well-formed,
non-closed moving-leaf decomposition that is restricted (`Xo.XoR`) at every `μ` in a tail `γ < υ_μ < υ_λ`. -/
theorem ybCover {l β : Ordinal.{0}} (hl0 : 0 < l) (hK : YbLevK S l β) :
    ∀ x, x < upsilon (l + β) → x < Om1 → YbCov S l β x := by
  have hm := upsilon_normal.strictMono
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxβ hx1
  rcases lt_or_ge x (upsilon (succ l)) with hxl | hxl
  · exact ybCov_old hl0 (.lo x) hxl rfl (ybOs_lo l β x)
  by_cases hI : Indec x
  · obtain ⟨γ, hγx, hxγ⟩ := Xa.xa_seg_ex ((hm.monotone (zero_le : (0 : Ordinal.{0}) ≤ succ l)).trans hxl)
    have hlγ : l < γ := by
      by_contra hc
      push Not at hc
      exact absurd (hxγ.trans_le (hm.monotone (Order.succ_le_succ hc))) (not_lt.2 hxl)
    obtain ⟨h, rfl⟩ : ∃ h, l + h = γ := ⟨γ - l, Ordinal.add_sub_cancel_of_le hlγ.le⟩
    have h0 : 0 < h := pos_iff_ne_zero.2 fun e => by rw [e, add_zero] at hlγ; exact lt_irrefl l hlγ
    have hβ : h < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hγx.trans_lt hxβ))
    have hτP : UpsPt (upsilon (l + h)) := upsPt_upsilon (hl0.trans_le le_self_add)
    have hτ1 : upsilon (l + h) < Om1 := hγx.trans_lt hx1
    have hτE : InE (upsilon (l + h)) := upsPt_inE hτP
    have hlτ : upsilon l < upsilon (l + h) := hm (lt_add_of_pos_right l h0)
    obtain ⟨m, hn, hT⟩ := exists_next hτP hτ1
    have hm2 : m = upsilon (succ (l + h)) := hn.unique (upsilon_isNext (l + h))
    have hxT : x ∈ Tset (upsilon (l + h)) := (hT x hx1).2 (hm2 ▸ hxγ)
    rcases eq_or_lt_of_le hγx with hτx | hτx
    · refine ybCov_old hl0 (.sg h x) ⟨h0, hβ, hγx, hxγ, ?_⟩ rfl (ybOs_sg hβ)
      rw [← hτx]
      exact Ww.ww_par_self hlE hlτ hτE hτ1
    · obtain ⟨ξ, hξT, hξ2, hv⟩ := vt_rep hτE hτ1 hxT hγx hx1 hI
      obtain ⟨hηT, hηx⟩ := Xa.xa_arg S hτE hτ1 hξT hξ2
      rw [hv] at hηx
      have hηO : ξ % Om1 < Om1 := mod_lt ξ Rj.rj_Om1_inE.pos.ne'
      obtain ⟨e, he, hev, hec, het, heo⟩ := IH (ξ % Om1) hηx (hηx.trans hxβ) hηO
      have hdec0 : Om1 * (ξ / Om1) + ξ % Om1 = ξ := div_add_mod ξ Om1
      -- the level term
      obtain ⟨L, hLW, hLv, hLt, hLo⟩ : ∃ L : Xo.XoE, Xo.XoWF S l β L ∧ Xo.xoVal S l L = ξ / Om1 ∧
          YbTail S l L ∧ YbOs l β L := by
        set M := ξ / Om1 with hMdef
        set η := ξ % Om1 with hηdef
        rcases lt_or_ge M Om1 with hMΩ | hΩM
        · -- a countable level lies below `x`
          have hMx : M < x := by
            rcases lt_or_ge M (upsilon (l + h)) with hMτ | hτM
            · exact hMτ.trans_le hγx
            · have h' : Om1 * (Om1 * 0 + M) + η ∈ Tset (upsilon (l + h)) := by
                rw [mul_zero, zero_add, hdec0]; exact hξT
              have hMT : M ∈ Tset (upsilon (l + h)) :=
                (Rk.rkArg_T hτE hτ1 Rj.rj_Om1_inE.pos hMΩ hηO h').2
              have := (lvLevel_lt_vt hτE hτ1 hMT hτM hMΩ hηT hηO).1
              rw [hdec0, hv] at this
              exact this
          obtain ⟨L, hLW, hLv, -, hLt, hLo⟩ := IH M hMx (hMx.trans hxβ) hMΩ
          exact ⟨L, hLW, hLv, hLt, hLo⟩
        · by_cases hlow : ∃ c < upsilon l, ∀ μ, c < upsilon μ → Vd.VdLtIn M (upsilon μ)
          · exact ⟨.lc M, trivial, rfl, ybLc_tail hlow, ybOs_lc l β M⟩
          · have hYK := hK h M η h0 hβ hΩM hηO hηT (by rw [hdec0]; exact hξT) (by rw [hdec0]; exact hξ2)
              (by rw [hdec0, hv]; exact hγx) (by rw [hdec0, hv]; exact hxβ) hlow
            rw [hdec0, hv] at hYK
            obtain ⟨L, hLW, hLv, -, hLt, hLo⟩ := ybK_cov (S := S) (l := l) (β := β) (x := x) hl0
              (fun y hy => IH y hy (hy.trans hxβ) (hy.trans hx1)) M hYK
            exact ⟨L, hLW, hLv, hLt, hLo⟩
      have hdec : Om1 * Xo.xoVal S l L + Xo.xoVal S l e = ξ := by rw [hLv, hev]; exact hdec0
      obtain ⟨γ, hγ, hR⟩ := ybTail_two hLt het
      refine ⟨.th h L e, ⟨h0, hβ, hLW, he, ?_⟩, ?_, fun hc => hc, ⟨γ, hγ, fun μ hμ hB => hR μ hμ hB⟩,
        ybOs_th hβ hLo heo⟩
      · rw [hdec, hv, hev]; exact ⟨hηO, hξT, hξ2, hγx, hxγ⟩
      · show vt (upsilon (l + h)) (Om1 * Xo.xoVal S l L + Xo.xoVal S l e) = x
        rw [hdec, hv]
  · have hD : DecompR0 x := not_not.1 hI
    rcases hD with h0 | ⟨y, z, hy, hz, hyz⟩
    · rw [h0] at hxl
      exact absurd hxl (not_le.2 (zero_le.trans_lt (hm (lt_succ l))))
    obtain ⟨Ey, wy, vy, cy, ty, oy⟩ := IH y hy (hy.trans hxβ) (hy.trans hx1)
    obtain ⟨Ez, wz, vz, cz, tz, oz⟩ := IH z hz (hz.trans hxβ) (hz.trans hx1)
    obtain ⟨γ, hγ, hR⟩ := ybTail_two ty tz
    refine ⟨.add Ey Ez, ⟨wy, wz⟩, ?_, fun h => cy h.1, ⟨γ, hγ, fun μ hμ hB =>
      ⟨(hR μ hμ hB).1, (hR μ hμ hB).2, fun h => absurd h.1 cy⟩⟩, ybOs_add oy oz⟩
    show Xo.xoVal S l Ey + Xo.xoVal S l Ez = x
    rw [vy, vz, hyz]

/-- **The covering lemma for every reach below `υ_{λ+β} ≤ Ω₁`**: each inner reach `r(λ+g)` is big or has a covered
decomposition. -/
theorem ybCover_reach {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hK : YbLevK S l β)
    (g : Ordinal.{0}) : upsilon (l + β) ≤ cdR S (l + g) ∨ YbCov S l β (cdR S (l + g)) := by
  rcases le_or_gt (upsilon (l + β)) (cdR S (l + g)) with h | h
  · exact Or.inl h
  · exact Or.inr (ybCover hl0 hK _ h (h.trans_le hb1))

/-! ## The witnesses -/

theorem yb_lam_facts (k : ℕ) :
    0 < Nc.ncL S (k : Ordinal.{0}) ∧ upsilon 0 < upsilon (Nc.ncL S (k : Ordinal.{0})) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  exact ⟨hl0, upsilon_normal.strictMono hl0⟩

/-- **`λ` is restricted on a tail** (`lo λ`). -/
theorem ybTail_lam (k : ℕ) :
    YbTail S (Nc.ncL S (k : Ordinal.{0})) (.old (.lo (Nc.ncL S (k : Ordinal.{0})))) :=
  ⟨upsilon 0, (yb_lam_facts (S := S) k).2, fun μ hμ hB => Xo.xo_lo_R k (yb_mu_pos hμ) hB.2.2.1⟩

/-- **`E′` (value `r(λ+X′)`) is restricted on a tail.** -/
theorem ybTail_Xj (k : ℕ)
    (hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1) :
    YbTail S (Nc.ncL S (k : Ordinal.{0})) (Xo.xoXjE S k) :=
  ⟨upsilon 0, (yb_lam_facts (S := S) k).2, fun μ hμ hB => Xo.xoXj_R k (yb_mu_pos hμ) hB.2.2.1 hτO⟩

/-- The constant `B₂` passes the `lc` clause at every `μ > 0`. -/
theorem yb_B_low (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ0 : 0 < μ) : Vd.VdLtIn Uc.ucB (upsilon μ) :=
  Or.inr ⟨S, le_rfl, Vd.vd_B_lt_th, gamma 0, Lq.lq_gamma_SC 0,
    Gq.gq_gam_le_ups S (upsPt_upsilon hμ0), Ww.ww_B_dat (S := S) (Lq.lq_gamma_SC 0)⟩

/-- The gap witness `wwX = ϑ^{u₁}(Ω₁·B₂ + λ)` as a moving-leaf decomposition. -/
noncomputable def ybWwXE (S : InaccSeq.{0}) (k : ℕ) : Xo.XoE :=
  .th 1 (.lc Uc.ucB) (.old (.lo (Nc.ncL S (k : Ordinal.{0}))))

theorem ybWwXE_val (k : ℕ) : Xo.xoVal S (Nc.ncL S (k : Ordinal.{0})) (ybWwXE S k) = Ww.wwX S k := by
  show vt (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) (Om1 * Uc.ucB + Nc.ncL S (k : Ordinal.{0})) = _
  rw [Uf.uf_Om1_mul_B]; rfl

/-- **The gap witness is restricted on a tail.** -/
theorem ybTail_wwX (k : ℕ) : YbTail S (Nc.ncL S (k : Ordinal.{0})) (ybWwXE S k) :=
  ⟨upsilon 0, (yb_lam_facts (S := S) k).2, fun μ hμ hB =>
    ⟨yb_B_low S (yb_mu_pos hμ), Xo.xo_lo_R k (yb_mu_pos hμ) hB.2.2.1⟩⟩

/-- **The covering at the witnesses, with no level hypothesis**: `λ`, `r(λ+X′)` (given `L(k+1) ≤ ν_C`,
`X′ + ω + 1 < β`, `υ_{λ+β} ≤ Ω₁`) are covered; the audit's spellings `F_k`, `F′_k`, `E″`, `E‴` have these values
(`Xo.xoFk_val`, `Xo.xoFkA_val`, `Xo.xoE2_val`, `Xo.xoE3_val`), so their values are covered by restricted terms. -/
theorem ybCov_wit (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : Xj.xjX S k + ω + 1 < β) (hb1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Om1) :
    YbCov S (Nc.ncL S (k : Ordinal.{0})) β (Nc.ncL S (k : Ordinal.{0})) ∧
      YbCov S (Nc.ncL S (k : Ordinal.{0})) β (cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k)) := by
  obtain ⟨hl0, -, -, -, -, -, -, -, -⟩ := Vr.vr_facts (S := S) k
  obtain ⟨-, hu1O, hlu1, hlfix, -, -⟩ := Ww.ww_seg (S := S) k
  have hm := upsilon_normal.strictMono
  have hτO : upsilon (Nc.ncL S (k : Ordinal.{0}) + (Xj.xjX S k + ω + 1)) < Om1 :=
    (hm ((add_lt_add_iff_left _).2 hβ)).trans_le hb1
  have h1β : (1 : Ordinal.{0}) < β :=
    lt_of_le_of_lt (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one _))) hβ
  refine ⟨⟨.old (.lo _), ?_, rfl, fun h => h, ybTail_lam k, ybOs_lo _ _ _⟩,
    ⟨Xo.xoXjE S k, Xo.xoXj_WF k hβ hb1, Xo.xoXj_val k hν, fun h => h.1, ybTail_Xj k hτO,
      ybOs_add (ybOs_sg hβ) (ybOs_th h1β (ybOs_add (ybOs_lc _ _ _) (ybOs_lo _ _ _)) (ybOs_lo _ _ _))⟩⟩
  show Nc.ncL S (k : Ordinal.{0}) < upsilon (succ (Nc.ncL S (k : Ordinal.{0})))
  rw [succ_eq_add_one]; exact hlu1

end Googology.Trans.PoR.InaccPsi.R2.Yb
