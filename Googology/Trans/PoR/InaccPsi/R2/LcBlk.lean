import Googology.Trans.PoR.InaccPsi.R2.RmNamed
import Googology.Trans.PoR.InaccPsi.R2.RlEq
import Googology.Trans.PoR.InaccPsi.R2.BaseC

/-!
# The realizer maps on the first block above `a`: the base change `π_{ρ_μ, a}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`a` is a countable `υ`-point, `a^∞` the least `υ`-point above `a` (`IsNext a m`), `ρ_μ = υ_μ`, Range =
`Cd.CdRange`, `RlReal` = `Rl.RlReal`, `RmCof S a` = Range restarts cofinal below `a` (`Rm.RmCof`).
`Rm.rmReal_lin` gives `RlReal S a t` for `t ≤ a·ω^ω` (there no point of `(a, t)` is `≤₁` a larger one).
Above `a·ω^ω` the first `≤₁`-left ends `ω^{a+λ}` appear, and the clause `≤₁` of a realizer is no longer
vacuous.  Here the map is Wilken's base change `π_{ρ_μ, a} : Tᵃ[ρ_μ] → T^{ρ_μ}` ([W07a] Def 5.1,
Lemma 5.3), and the clause `≤₁` comes from `lh(π(α)) = π(lh(α))` ([W07b] Cor 5.7, axiom `lh_pi`, through
`R2.down_le1R`) and `Rl.rlD1_nonups` (below `ν_C`, `≤₁` of `R₂^C` at a non-`υ`-point is `≤₁` of `R₁⁺`).

* `lcReal_blk` (**`RlReal S a t` for every `t ≤ min(a^∞, ν_C)`**, given `RmCof S a`): the configuration
  `Y` lies in `Tᵃ[ρ_μ]` once `ρ_μ` is above `X` and the parameters `Parᵃ(y)` (`y ∈ Y`, [W07a] Def 3.28,
  axiom `Par_sub`); the images lie in `[ρ_μ, ρ_μ^∞) ⊆ [ρ_μ, δ_μ]`, so the bound by `r(μ)` holds; no
  `<₂`-pair below `ν_C` has a left end in `(a, a^∞)` (the pairs are standard, `std_of_lt_nuC`);
* `lcRealCof_blk` (**`RlRealCof S a a^∞`** when `a^∞ ≤ ν_C`), `lcLe1_blk` (`a ≤₁ a^∞` from LOWER and
  `CvNoPair a a^∞`);
* `lcTB_gap` (**the base change does not cross `a^∞`**): for a base `σ ≤ a`, no point of `[a, a^∞)` is in
  `T^{a^∞}[σ]`; a realizer for a target above `a^∞` must move the parameters in `[a, a^∞)` of the points
  above `a^∞`, which `π_{σ,τ}` (identity on its parameters `< σ`) does not do;
* the named points: `lcNext` (the least `υ`-point above `a`), `lcNext_spec`, `lc_named_ups`,
  `lcNamed_blk` (**`ρ_{B₀} < m*` and `L(ω) ≤ ν_C` give `RlRealCof` at `m*` and every `L(n+1)` up to their
  next `υ`-points**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Rm

variable {S : InaccSeq.{0}}

/-- A point of `(a, a^∞)` that is the left end of a `<₂`-pair below `ν_C` would be a `υ`-point. -/
theorem lc_not_le2_gap {a m y y' : Ordinal.{0}} (hm : IsNext a m) (hay : a < y) (hym : y < m)
    (hy' : y' < nuC) (hyy : y < y') : ¬ le2 y y' := by
  intro h2
  obtain ⟨L, hL, -, e, -⟩ := (std_of_lt_nuC hy' hyy h2).parts
  have hU : UpsPt y := by rw [e]; exact upsPt_upsilon (pos_iff_ne_zero.2 hL.ne_bot)
  exact not_upsPt_gap hm hay hym hU

/-- **The realizer maps on the first block above `a`** (`t ≤ a^∞`, `t ≤ ν_C`). -/
theorem lcReal_blk {a m t : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1) (hc : RmCof S a)
    (hm : IsNext a m) (htm : t ≤ m) (htν : t ≤ nuC) : RlReal S a t := by
  classical
  have haE := upsPt_inE ha
  have hapos : 0 < a := ha.1
  have ht1 : t ≤ Om1 := htν.trans nuC_le_Om1
  obtain ⟨m', hm', hTa⟩ := exists_next ha ha1
  rw [hm'.unique hm] at hTa
  have hμ : ∀ i : Shrink.{0} (Iio a), ∃ μ, CdRange S μ ∧ ((equivShrink (Iio a)).symm i).1 < upsilon μ ∧
      upsilon μ < a := fun i => hc _ ((equivShrink (Iio a)).symm i).2
  choose μf hμr hμlo hμhi using hμ
  have hσU : ∀ i, UpsPt (upsilon (μf i)) := fun i => upsPt_upsilon (pos_iff_ne_zero.2 (hμr i).1.1)
  have hB : ∀ i, Bases (upsilon (μf i)) a := fun i => ⟨upsPt_inE (hσU i), haE, hμhi i, ha1⟩
  have hnx : ∀ i, ∃ mσ, IsNext (upsilon (μf i)) mσ ∧
      ∀ x, x < Om1 → (x ∈ Tset (upsilon (μf i)) ↔ x < mσ) := fun i =>
    exists_next (hσU i) ((hμhi i).trans ha1)
  choose mσ hmσ hTσ using hnx
  have hmσa : ∀ i, mσ i ≤ a := fun i => (hmσ i).2.2 a (hμhi i) ha
  have hmσr : ∀ i, mσ i ≤ cdR S (μf i) := by
    intro i
    have h1 : mσ i ≤ upsilon (μf i + 1) :=
      (hmσ i).2.2 _ (upsilon_normal.strictMono (lt_add_one _))
        (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _)))
    refine h1.trans ((upsilon_normal.strictMono.monotone ?_).trans (cdR_ge S (μf i)))
    exact add_le_add le_self_add le_rfl
  -- the domains and the maps
  set E : Shrink.{0} (Iio a) → Set Ordinal.{0} :=
    fun i => {y | a ≤ y ∧ y < t ∧ y ∈ TB a (upsilon (μf i))} with hEdef
  have hEsub : ∀ i, E i ⊆ TB a (upsilon (μf i)) := fun i y hy => hy.2.2
  have hDsub : ∀ i, RlDom (upsilon (μf i)) (E i) ⊆ TB a (upsilon (μf i)) := by
    intro i x hx
    rcases hx with hx | hx
    · exact (TB_inter_lt (hB i) (hx.trans (hμhi i))).2 hx
    · exact hx.2.2
  have hy1 : ∀ i, ∀ y ∈ E i, y < Om1 := fun i y hy => lt_of_lt_of_le hy.2.1 ht1
  -- the window `ρ_μ ≤ π y < ρ_μ^∞ ≤ a`
  have hwin : ∀ i, ∀ y ∈ E i, upsilon (μf i) ≤ pi (upsilon (μf i)) a y ∧
      pi (upsilon (μf i)) a y < mσ i := by
    intro i y hy
    have hyT := hEsub i hy
    refine ⟨down_ge (hB i) hyT hy.1, ?_⟩
    exact (hTσ i _ (down_lt_Om1 (hB i) hyT (hy1 i y hy))).1 ((pi_bijOn (hB i)).1.mapsTo hyT)
  refine ⟨Shrink.{0} (Iio a), fun i => upsilon (μf i), E, fun i => pi (upsilon (μf i)) a, μf,
    hμhi, fun i y hy => ⟨hy.1, hy.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- exhaustion: `ρ_μ` above `X` and above the parameters of `Y`
    intro X Y hX hY _
    have hYT : ∀ y ∈ Y, y ∈ Tset a := fun y hy =>
      (hTa y (lt_of_lt_of_le (hY y hy).2 ht1)).2 (lt_of_lt_of_le (hY y hy).2 htm)
    set K : Finset Ordinal.{0} := X ∪ Y.biUnion (fun y => Par a y)
    have hK : ∀ k ∈ K, k < a := by
      intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · exact hX k hk
      · obtain ⟨y, hy, hky⟩ := Finset.mem_biUnion.1 hk
        exact Par_sub haE ha1 (hYT y hy) (Finset.mem_coe.2 hky)
    have hγ : K.sup id < a := (Finset.sup_lt_iff hapos).2 hK
    have hlo : K.sup id < upsilon (μf (equivShrink (Iio a) ⟨K.sup id, hγ⟩)) := by
      have h := hμlo (equivShrink (Iio a) ⟨K.sup id, hγ⟩)
      rwa [Equiv.symm_apply_apply] at h
    refine ⟨equivShrink (Iio a) ⟨K.sup id, hγ⟩, fun x hx => ?_, fun y hy => ⟨(hY y hy).1, (hY y hy).2,
      hYT y hy, fun p hp => ?_⟩⟩
    · exact lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_union_left _ hx)) hlo
    · have hpK : p ∈ K := Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_coe.1 hp⟩)
      exact lt_of_le_of_lt (Finset.le_sup (f := id) hpK) hlo
  · -- strictly increasing
    intro i
    exact down_mono (hB i) (hEsub i)
  · -- `+` kept and reflected on `[0, ρ_μ) ∪ E`
    intro i x hx y hy z hz
    exact down_add (hB i) (hDsub i) x hx y hy z hz
  · -- decomposability reflected (`π` keeps indecomposability)
    intro i y hy hdec
    by_contra hnd
    exact down_indec (hB i) (hEsub i hy) (hy1 i y hy) hnd hdec
  · -- identity below `ρ_μ`
    intro i x hx
    exact pi_lt (hB i) hx
  · -- the window
    intro i y hy
    exact ⟨(hwin i y hy).1, lt_of_lt_of_le (hwin i y hy).2 (hmσa i)⟩
  · -- `π(a) = ρ_μ` and the bound by `r(μ)`
    intro i
    exact ⟨hμr i, fun _ => (pi_base (hB i)).2, fun y hy => ((hwin i y hy).2.trans_le (hmσr i)).le⟩
  · -- `≤₁` and `≤₂` on the pairs `a < y < y'`
    intro i y hy y' hy' hay hyy
    have hym : y < m := lt_of_lt_of_le hy.2.1 htm
    have hyν : y < nuC := lt_of_lt_of_le hy.2.1 htν
    have hy'ν : y' < nuC := lt_of_lt_of_le hy'.2.1 htν
    refine ⟨fun h1 => ?_, fun h2 => absurd h2 (lc_not_le2_gap hm hay hym hy'ν hyy)⟩
    have hyT := hEsub i hy
    have hpy : upsilon (μf i) < pi (upsilon (μf i)) a y := down_gt (hB i) hyT hay
    have hpyν : pi (upsilon (μf i)) a y < nuC :=
      lt_of_lt_of_le ((hwin i y hy).2.trans_le (hmσa i)) (lt_of_le_of_lt hy.1 hyν).le
    refine rlD1_nonups hyν (not_upsPt_gap hm hay hym) hpyν
      (not_upsPt_gap (hmσ i) hpy (hwin i y hy).2) ?_ h1
    exact (down_le1R (hσU i) ha (hB i) hyT (hEsub i hy') (hy1 i y hy)).1

/-- **`RlRealCof S a a^∞`** (`a^∞ ≤ ν_C`, `RmCof S a`). -/
theorem lcRealCof_blk {a m : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1) (hc : RmCof S a)
    (hm : IsNext a m) (hmν : m ≤ nuC) : RlRealCof S a m := fun _ _ hym =>
  ⟨m, hym, le_rfl, lcReal_blk ha ha1 hc hm le_rfl hmν⟩

/-- **`a ≤₁ a^∞` from the block realizers**, LOWER and `CvNoPair a a^∞`. -/
theorem lcLe1_blk (hL : CdLOWER S) {a m : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1)
    (hc : RmCof S a) (hm : IsNext a m) (hmν : m ≤ nuC) (hP : Cv.CvNoPair a m) : le1 a m :=
  rlLe1_of_realCof hL hm.1.le hP (lcRealCof_blk ha ha1 hc hm hmν)

/-- **The base change does not cross `a^∞`**: for `σ ≤ a < a^∞ = m`, no point of `[a, m)` is in
`T^m[σ]` ([W07a] proof of Lemma 5.3: `T^m[σ] ∩ m = σ`, axiom `TB_inter_lt`). -/
theorem lcTB_gap {σ a m x : Ordinal.{0}} (hB : Bases σ m) (hσa : σ ≤ a) (hax : a ≤ x) (hxm : x < m) :
    x ∉ TB m σ := fun hx =>
  absurd (lt_of_lt_of_le ((TB_inter_lt hB hxm).1 hx) (hσa.trans hax)) (lt_irrefl _)

/-! ## The named points -/

/-- The least `υ`-point above `a`. -/
noncomputable def lcNext (a : Ordinal.{0}) : Ordinal.{0} := sInf {u | a < u ∧ UpsPt u}

theorem lcNext_spec {a : Ordinal.{0}} (ha : UpsPt a) (ha1 : a < Om1) : IsNext a (lcNext a) := by
  obtain ⟨m, hm, -⟩ := exists_next ha ha1
  have e : lcNext a = m :=
    le_antisymm (csInf_le' ⟨hm.1, hm.2.1⟩) (le_csInf ⟨m, hm.1, hm.2.1⟩ fun u hu => hm.2.2 u hu.1 hu.2)
  rw [e]; exact hm

theorem lc_L_lt_Om1 (ξ : Ordinal.{0}) : Nc.ncL S ξ < Om1 := by
  rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _

/-- `m*` and every `L(n+1)` are `υ`-points. -/
theorem lc_named_ups : UpsPt (Nc.ncL S 0) ∧ ∀ n : ℕ, UpsPt (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    rw [e]; exact upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    rw [e]; exact upsPt_upsilon (pos_iff_ne_zero.2 hl.1)

/-- `m*^∞ ≤ L(1)` and `L(n+1)^∞ ≤ L(n+2)`. -/
theorem lc_named_next :
    lcNext (Nc.ncL S 0) ≤ Nc.ncL S 1 ∧
      ∀ n : ℕ, lcNext (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤ Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨h0, hn⟩ := lc_named_ups (S := S)
  refine ⟨?_, fun n => ?_⟩
  · have h1 : UpsPt (Nc.ncL S 1) := by simpa using (lc_named_ups (S := S)).2 0
    exact (lcNext_spec h0 (lc_L_lt_Om1 0)).2.2 _ rlM_lt_L1 h1
  · have h2 := (lc_named_ups (S := S)).2 (n + 1)
    have e2 : ((n + 1 + 1 : ℕ) : Ordinal.{0}) = ((n + 2 : ℕ) : Ordinal.{0}) := rfl
    rw [e2] at h2
    exact (lcNext_spec (hn n) (lc_L_lt_Om1 _)).2.2 _ (Pp.ppL_lt_succ n) h2

/-- **`ρ_{B₀} < m*` and `L(ω) ≤ ν_C` give the block realizers at `m*` and at every `L(n+1)`.** -/
theorem lcNamed_blk (hB : upsilon cdB0 < Nc.ncL S 0) (hlow : Nc.ncL S ω ≤ nuC) :
    RlRealCof S (Nc.ncL S 0) (lcNext (Nc.ncL S 0)) ∧
      ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (lcNext (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) := by
  obtain ⟨c0, cn, -⟩ := rmNamed_cof_iff.1 hB
  obtain ⟨u0, un⟩ := lc_named_ups (S := S)
  obtain ⟨x0, xn⟩ := lc_named_next (S := S)
  refine ⟨lcRealCof_blk u0 (lc_L_lt_Om1 0) c0 (lcNext_spec u0 (lc_L_lt_Om1 0)) ?_, fun n =>
    lcRealCof_blk (un n) (lc_L_lt_Om1 _) (cn n) (lcNext_spec (un n) (lc_L_lt_Om1 _)) ?_⟩
  · exact x0.trans ((Pp.ppL_mono one_lt_omega0.le).trans hlow)
  · exact (xn n).trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)

end Googology.Trans.PoR.InaccPsi.R2.Lc
