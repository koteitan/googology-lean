import Googology.Trans.PoR.InaccPsi.R2.NestC

/-!
# Theorem NU-CT in `R₂^C`: `ν_C = T_C`, and the first non-standard pair starts at a restart

`ν_C` is the least right end of a non-standard `<₂`-pair of `R₂^C`, `T_C` the least top of a pair with a
pair nested inside; `ν_C ≤ T_C` (`nuC_le_TnestC`) and `T_C < Ω₁` (`TnestC_lt_Om1`).  Here the other
direction, inside `R₂^C` (the `R₂^S` half of the project's Theorem NU-CT is not formalized):

Let `(c, ν_C)` be a non-standard pair.  `c` is a `υ`-point (LEFT); by SKEL⁺ below `ν_C` (`classify`) it is
a restart or a point of a block `(υ_{bot}, δ]` with `δ = υ_{μ+ω(j+1)+1}`.

* In a block, `ν_C ≤ δ` (D1), and `c = υ_ξ` with `ξ ≤ μ + ω(j+1)`.  If `ξ` is a successor `ξ' + 1`, the
  `≤₁`-predecessors of `c` (cofinal below `c`, clause 1 of `c ≤₂ ν_C`, `pred1_cof`) would contain a point
  of `(υ_{ξ'}, υ_{ξ'+1})` that is `≤₁ υ_{ξ'+1}` in `R₁⁺`, hence `<₁ ∞`, hence a `υ`-point: impossible.
  If `ξ` is a limit, `c = τ = υ_{μ+ω(j+1)}` and `τ < ν_C < δ` (`ν_C = δ` would make the pair standard).
  Then (`no_tau_gap`) `K + 1` `υ`-points cofinal below `τ` form a `≤₁`-chain (SK1 in the block, `sk1F`),
  clause 2 of `τ ≤₂ ν_C` copies the chain into `(τ, ν_C)`, and there it is a chain of `R₁⁺` inside the gap
  `(τ, δ)`, against Lemma L (`chain_bound_gap`) for `K = ht_τ(ν_C) + 2`.
* So `c = ρ_L` is a restart.  Its `≤₁`-predecessors are cofinal below it and are restarts
  (`pred_restart_C`), so the standard pairs `(τ_μ, δ_μ)` are cofinal below `ρ_L`; PI2-UP (`pairs_up`,
  [C09] Def 5.3 clause 2) puts a pair `p <₂ q` inside `(ρ_L, ν_C)`, and `(ρ_L, p, q, ν_C)` realizes PS.

Results: `nuC_attained`, `pred1_cof`, `pairs_cof_restart`, `cov_seq` (a covering of a `≤`-chain pattern
onto a `≤₁`-chain), `no_tau_gap`, `left_restart_nuC` (**the left end of every non-standard pair with
right end `ν_C` is a restart**), `nuC_eq_TnestC` (**`ν_C = T_C`**), `nuC_core` (`[0, ν_C] ⊆ Core(R₂^C)`),
`nuC_cap` (CAP at `ν_C`), `pairs_cof_nuC` (standard pairs are cofinal below `ν_C`).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- `ν_C` is attained by a non-standard pair. -/
theorem nuC_attained (hd1 : nuC < Om1) : ∃ c, c < nuC ∧ le2 c nuC ∧ ¬ IsStd c nuC := by
  rcases csInf_mem (s := insert Om1 {d | ∃ c, c < d ∧ le2 c d ∧ ¬ IsStd c d})
    ⟨Om1, Set.mem_insert _ _⟩ with h | h
  · exact absurd (h ▸ hd1 : Om1 < Om1) (lt_irrefl _)
  · exact h

/-- The `≤₁`-predecessors of a `<₂`-left end are cofinal below it ([C09] Def 5.3, clause 1 (d), with
`Y = {c}`). -/
theorem pred1_cof {c d : Ordinal.{0}} (h : le2 c d) (hcd : c < d) :
    ∀ z < c, ∃ y, z < y ∧ y < c ∧ le1 y c := by
  intro z hz
  have hI := indec_of_lt1 (le2_le1 h) hcd
  obtain ⟨_, H1, _⟩ := le2_iff.1 h
  obtain ⟨Yt, hYt, -, -, f, -, -, hY⟩ := cof_core hz (fun y w => le1 y d → le1 w c)
    (fun X Y hX hY hXY => H1 X Y hX hY hXY) ∅ {c} (by simp) (by simp [hcd])
    (closed_singleton_of_indec hI)
  obtain ⟨hfY, hq⟩ := hY c (by simp)
  exact ⟨f c, (hYt _ hfY).1, (hYt _ hfY).2, hq (le2_le1 h)⟩

/-- Below a restart `ρ_L ≤ ν_C` that is a `<₂`-left end, `<₂`-pairs are cofinal. -/
theorem pairs_cof_restart {l d : Ordinal.{0}} (hl : IsRestartIdx l) (h : le2 (upsilon l) d)
    (hld : upsilon l < d) (hC : upsilon l ≤ nuC) :
    ∀ z < upsilon l, ∃ p q, z < p ∧ p < q ∧ q < upsilon l ∧ le2 p q := by
  intro z hz
  obtain ⟨y, hzy, hyl, hy1⟩ := pred1_cof h hld z hz
  obtain ⟨μ, hμ, rfl⟩ := pred_restart_C hl hC hyl hy1
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  have hidx : μ + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1 < l :=
    lt_of_lt_of_le (pidx_lt μ 0) (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl)
  have hq : upsilon (μ + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon l :=
    upsilon_normal.strictMono hidx
  have hpos : (0 : Ordinal.{0}) < ω * ((0 + 1 : ℕ) : Ordinal.{0}) :=
    mul_pos omega0_pos (by exact_mod_cast Nat.succ_pos 0)
  refine ⟨upsilon (μ + ω * ((0 + 1 : ℕ) : Ordinal.{0})),
    upsilon (μ + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1),
    hzy.trans (upsilon_normal.strictMono (lt_add_of_pos_right _ hpos)),
    upsilon_normal.strictMono (lt_add_one _), hq,
    pair_std (Or.inr hμ) 0 (lt_of_lt_of_le hq hC)⟩

/-! ## A covering of a chain pattern -/

/-- The chain pattern: `≤₁` is `≤`, `≤₂` is `=`. -/
def Pch : Str := ⟨fun x y => x ≤ y, fun x y => x = y⟩

/-- The universe of the chain pattern of length `n`: `{ω^1, …, ω^n}`. -/
noncomputable def Zch (n : ℕ) : Finset Ordinal.{0} :=
  (Finset.range n).image (fun i : ℕ => ω ^ ((i : Ordinal.{0}) + 1))

theorem lt_of_add_one_lt {x y : Ordinal.{0}} (h : x + 1 < y + 1) : x < y := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.2 (add_le_add hle le_rfl))

theorem zz_lt_iff {i i' : ℕ} :
    ω ^ ((i : Ordinal.{0}) + 1) < ω ^ ((i' : Ordinal.{0}) + 1) ↔ i < i' := by
  rw [opow_lt_opow_iff_right one_lt_omega0]
  constructor
  · intro h
    exact_mod_cast lt_of_add_one_lt h
  · intro h
    have : ((i + 1 : ℕ) : Ordinal.{0}) < ((i' + 1 : ℕ) : Ordinal.{0}) := by
      exact_mod_cast Nat.succ_lt_succ h
    simpa using this

theorem zz_le_iff {i i' : ℕ} :
    ω ^ ((i : Ordinal.{0}) + 1) ≤ ω ^ ((i' : Ordinal.{0}) + 1) ↔ i ≤ i' := by
  rw [← not_lt, zz_lt_iff, not_lt]

theorem Zch_closed (n : ℕ) : Closed (↑(Zch n) : Set Ordinal.{0}) := by
  refine closed_of_indec fun w hw => ?_
  simp only [Zch, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
  obtain ⟨i, -, rfl⟩ := hw
  exact indec_opow _

/-- **A covering of the chain pattern of length `n` onto a `≤₁`-chain** `w_0 < ⋯ < w_{n-1}` of
indecomposables of `R₂^C`. -/
theorem cov_seq (n : ℕ) (ws : ℕ → Ordinal.{0}) (hmono : ∀ i i', i < i' → i' < n → ws i < ws i')
    (hI : ∀ i < n, Indec (ws i)) (h1 : ∀ i i', i ≤ i' → i' < n → le1 (ws i) (ws i')) :
    ∃ h, Cov Pch R2C ↑(Zch n) ↑((Finset.range n).image ws) h := by
  classical
  set zz : ℕ → Ordinal.{0} := fun i => ω ^ ((i : Ordinal.{0}) + 1) with hzz
  have hmem : ∀ t, t ∈ (↑(Zch n) : Set Ordinal.{0}) ↔ ∃ i, i < n ∧ zz i = t := by
    intro t; simp [Zch, hzz]
  have zinj : ∀ i i', zz i = zz i' → i = i' := by
    intro i i' e
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd e (zz_lt_iff.2 h).ne
    · exact h
    · exact absurd e.symm (zz_lt_iff.2 h).ne
  set f : Ordinal.{0} → Ordinal.{0} := fun t =>
    if h : ∃ i, i < n ∧ zz i = t then ws (Classical.choose h) else 0 with hfdef
  have hfz : ∀ i < n, f (zz i) = ws i := by
    intro i hi
    have hex : ∃ i', i' < n ∧ zz i' = zz i := ⟨i, hi, rfl⟩
    simp only [hfdef, dif_pos hex]
    rw [zinj _ _ (Classical.choose_spec hex).2]
  have hext : ∀ i < n, ext f (zz i) = ws i := fun i hi => by
    rw [ext_indec (indec_opow _)]; exact hfz i hi
  have hf : StrictMonoOn f (IndecIn ↑(Zch n)) := by
    intro a ha c hc hac
    obtain ⟨i, hi, rfl⟩ := (hmem a).1 ha.1
    obtain ⟨i', hi', rfl⟩ := (hmem c).1 hc.1
    rw [hfz i hi, hfz i' hi']
    exact hmono i i' (zz_lt_iff.1 hac) hi'
  have hfI : ∀ a ∈ IndecIn (↑(Zch n) : Set Ordinal.{0}), Indec (f a) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := (hmem a).1 ha.1
    rw [hfz i hi]; exact hI i hi
  have himg : ext f '' ↑(Zch n) = ↑((Finset.range n).image ws) := by
    ext w
    simp only [Set.mem_image, Finset.coe_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (hmem t).1 ht
      exact ⟨i, hi, (hext i hi).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨zz i, (hmem _).2 ⟨i, hi, rfl⟩, hext i hi⟩
  refine ⟨ext f, ?_⟩
  rw [← himg]
  refine ⟨ext_arithIso (Zch_closed n) hf hfI, ?_, ?_⟩
  · intro a ha c hc hac
    obtain ⟨i, hi, rfl⟩ := (hmem a).1 ha
    obtain ⟨i', hi', rfl⟩ := (hmem c).1 hc
    change zz i ≤ zz i' at hac
    change le1 (ext f (zz i)) (ext f (zz i'))
    rw [hext i hi, hext i' hi']
    exact h1 i i' (zz_le_iff.1 hac) hi'
  · intro a _ c _ hac
    change a = c at hac
    change le2 (ext f a) (ext f c)
    rw [hac]; exact le2_refl _

/-! ## No `<₂`-pair from `τ` into its gap -/

/-- **No `<₂`-successor of `τ = υ_{a+ω}` strictly inside its gap below `ν_C`**: if `τ <₂ ν_C` then
`ν_C ≥ υ_{a+ω+1}` (Lemma L against a chain copied by clause 2). -/
theorem no_tau_gap {a : Ordinal.{0}} (hd1 : nuC < Om1) (h2 : le2 (upsilon (a + ω)) nuC)
    (h1 : upsilon (a + ω) < nuC) (hβ : nuC < upsilon (a + ω + 1)) : False := by
  classical
  set τ := upsilon (a + ω) with hτdef
  have hlimω : IsSuccLimit (a + ω) := isSuccLimit_add a isSuccLimit_omega0
  have ha0 : 0 < a + ω := lt_of_lt_of_le omega0_pos le_add_self
  have hτU : UpsPt τ := upsPt_upsilon ha0
  have hτE : InE τ := upsPt_inE hτU
  have hτ1 : τ < Om1 := h1.trans hd1
  -- no `<₂`-pair has its right end in `(υ_{a+1}, ν_C)`
  have hno : ∀ c d, c < d → upsilon (a + 1) < d → d < nuC → ¬ le2 c d := by
    intro c d hcd hTd hdν h2'
    obtain ⟨μ, j, -, rfl, rfl⟩ := std_of_lt_nuC hdν hcd h2'
    set X := μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) with hX
    have hXlim : IsSuccLimit X := isSuccLimit_add μ
      (isSuccLimit_mul_left isSuccLimit_omega0 (by exact_mod_cast Nat.succ_pos j))
    have hlo : a + 1 < X + 1 := upsilon_normal.strictMono.lt_iff_lt.1 hTd
    have hhi : X + 1 < a + ω + 1 := upsilon_normal.strictMono.lt_iff_lt.1 (hdν.trans hβ)
    have hlo' : a < X := lt_of_add_one_lt hlo
    have hhi' : X < a + ω := lt_of_add_one_lt hhi
    exact absurd (limit_eq_add_omega hXlim hlo' hhi'.le) hhi'.ne
  have sk := sk1F hd1 hno
  -- the gap of `τ`
  obtain ⟨m, hm, hT⟩ := exists_next hτU hτ1
  have hmδ : m = upsilon (a + ω + 1) := by
    have := upsilon_isNext (a + ω); rw [succ_eq_add_one] at this
    exact hm.unique this
  set K := ht τ nuC + 2 with hK
  -- the chain pattern is realized cofinally below `τ`
  have hcofτ : CofCov R2C ∅ (Zch (K + 1)) Pch τ := by
    intro c' hc'
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcι⟩ := (lt_isLUB_iff (upsilon_limit hlimω)).1 hc'
    obtain ⟨e, he, hιe⟩ := (lt_add_iff_of_isSuccLimit isSuccLimit_omega0).1 hι
    obtain ⟨n, rfl⟩ := lt_omega0.1 he
    set ws : ℕ → Ordinal.{0} := fun i => upsilon (a + ((n + 2 + i : ℕ) : Ordinal.{0})) with hws
    have hwlt : ∀ i, ws i < τ := fun i => upsilon_normal.strictMono
      ((add_lt_add_iff_left a).2 (natCast_lt_omega0 _))
    have hwU : ∀ i, UpsPt (ws i) := fun i => upsPt_upsilon (lt_of_lt_of_le
      (by exact_mod_cast (show 0 < n + 2 + i by omega) :
        (0 : Ordinal.{0}) < ((n + 2 + i : ℕ) : Ordinal.{0}))
      le_add_self)
    have hwT : ∀ i, upsilon (a + 1) < ws i := fun i => upsilon_normal.strictMono
      ((add_lt_add_iff_left a).2 (by exact_mod_cast (by omega : 1 < n + 2 + i)))
    have hwmono : ∀ i i', i < i' → ws i < ws i' := fun i i' h => upsilon_normal.strictMono
      ((add_lt_add_iff_left a).2 (by exact_mod_cast (by omega : n + 2 + i < n + 2 + i')))
    have hw1 : ∀ i i', i ≤ i' → i' < K + 1 → le1 (ws i) (ws i') := by
      intro i i' hii _
      have hle : ws i ≤ ws i' := by
        rcases eq_or_lt_of_le hii with rfl | h
        · exact le_rfl
        · exact (hwmono i i' h).le
      exact (sk (ws i') ((hwlt i').le.trans h1.le) (ws i) (hwT i)).2 ((hwU i).2 _ hle)
    obtain ⟨h, hcov⟩ := cov_seq (K + 1) ws (fun i i' h _ => hwmono i i' h)
      (fun i _ => indec_of_upsPt (hwU i)) hw1
    refine ⟨(Finset.range (K + 1)).image ws, ?_, ?_, h, by rwa [Finset.empty_union]⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      refine ⟨hcι.trans (lt_of_lt_of_le (upsilon_normal.strictMono hιe) ?_), hwlt i⟩
      exact upsilon_normal.strictMono.monotone ((add_le_add_iff_left a).2
        (by exact_mod_cast (by omega : n ≤ n + 2 + i)))
    · rw [Finset.empty_union]
      refine closed_of_indec fun w hw => ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
      obtain ⟨i, -, rfl⟩ := hw
      exact indec_of_upsPt (hwU i)
  -- clause 2 of `τ ≤₂ ν_C` copies it into `(τ, ν_C)`
  obtain ⟨_, -, H2⟩ := le2_iff.1 h2
  obtain ⟨Y', hY', -, g, hg⟩ := H2 ∅ (by simp) (Zch (K + 1)) Pch (Zch_closed _) hcofτ τ h1
  rw [Finset.empty_union] at hg
  set zz : ℕ → Ordinal.{0} := fun i => ω ^ ((i : Ordinal.{0}) + 1) with hzz
  have hzmem : ∀ i < K + 1, zz i ∈ (↑(Zch (K + 1)) : Set Ordinal.{0}) := fun i hi => by
    simp only [Zch, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨i, hi, rfl⟩
  set z : ℕ → Ordinal.{0} := fun i => g (zz i) with hzdef
  have hzY : ∀ i < K + 1, τ < z i ∧ z i < nuC := fun i hi =>
    hY' _ (Finset.mem_coe.1 (hg.1.1.mapsTo (hzmem i hi)))
  have hch : ∀ i < K, z i < z (i + 1) ∧ le1R (z i) (z (i + 1)) := by
    intro i hi
    have hi1 : i < K + 1 := by omega
    have hi2 : i + 1 < K + 1 := by omega
    have hlt : zz i < zz (i + 1) := zz_lt_iff.2 (Nat.lt_succ_self i)
    refine ⟨hg.1.2.1 (hzmem i hi1) (hzmem (i + 1) hi2) hlt, ?_⟩
    have hle1 : le1 (z i) (z (i + 1)) := hg.2.1 _ (hzmem i hi1) _ (hzmem (i + 1) hi2) hlt.le
    refine (sk (z (i + 1)) (hzY (i + 1) hi2).2.le (z i) ?_).1 hle1
    exact lt_trans (upsilon_normal.strictMono (lt_of_lt_of_le
      ((add_lt_add_iff_left a).2 one_lt_omega0) le_rfl)) (hzY i hi1).1
  have hbound := chain_bound_gap hτE hτ1 hT (by rw [hmδ]; exact hβ) hd1 K z
    (hzY 0 (by omega)).1 (hzY K (by omega)).2.le hch
  omega

/-! ## The left end of the first non-standard pair -/

/-- **The left end of a non-standard pair with right end `ν_C` is a restart.** -/
theorem left_restart_nuC (hd1 : nuC < Om1) {c : Ordinal.{0}} (hc : c < nuC) (h2 : le2 c nuC)
    (hns : ¬ IsStd c nuC) : ∃ l, IsRestartIdx l ∧ c = upsilon l := by
  have hcU : UpsPt c := left h2 hc (hc.trans hd1)
  rcases classify hcU.1 with hR | ⟨μ, j, hμ, hc1, hc2⟩
  · exact hR
  exfalso
  set a := μ + ω * (j : Ordinal.{0}) with ha
  have hτidx : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) = a + ω := by
    rw [ha, Nat.cast_succ, mul_add_one, add_assoc]
  -- `ν_C ≤ δ` (D1 otherwise)
  have hνβ : nuC ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
    by_contra hlt
    push Not at hlt
    have := ((block_le1 hμ j hlt hc1 hc2) nuC).1 (le2_le1 h2)
    exact absurd this.1 (not_le.2 hlt)
  rw [hτidx] at hνβ hc2
  obtain ⟨ξ, rfl⟩ := enumOrd_surjective upsSet_unbounded (Or.inr hcU : c ∈ UpsSet)
  change upsilon ξ < nuC at hc
  change le2 (upsilon ξ) nuC at h2
  change upsilon (botI μ j) < upsilon ξ at hc1
  have hξ1 : ξ < a + ω + 1 := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_lt_of_le hc hνβ)
  have hbot : a ≤ botI μ j := by
    rcases j with _ | k
    · simp [ha, botI]
    · show a ≤ μ + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1
      exact le_self_add
  have haξ : a < ξ := lt_of_le_of_lt hbot (upsilon_normal.strictMono.lt_iff_lt.1 hc1)
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ξ', rfl⟩ | hlim
  · exact absurd (h0 ▸ haξ) (not_lt.2 zero_le)
  · -- a successor index: no `≤₁`-predecessor in `(υ_{ξ'}, υ_{ξ'+1})`
    have hξ'ξ : upsilon ξ' < upsilon (succ ξ') := upsilon_normal.strictMono (lt_succ ξ')
    obtain ⟨y, hzy, hyc, hy1⟩ := pred1_cof h2 hc _ hξ'ξ
    have hR := inc1 (hc.trans hd1) hy1
    have hyU : UpsPt y := ⟨lt_of_le_of_lt zero_le hzy, ltInf1_of_le1R hR (upsPt_upsilon
      (lt_of_le_of_lt zero_le (lt_succ ξ'))).2⟩
    exact absurd ((upsilon_isNext ξ').2.2 y hzy hyU) (not_le.2 hyc)
  · -- a limit index: `ξ = a + ω`, `c = τ`
    have hξe : ξ = a + ω := limit_eq_add_omega hlim haξ (Order.lt_add_one_iff.1 hξ1)
    subst hξe
    rcases eq_or_lt_of_le hνβ with he | hlt
    · exact hns ⟨μ, j, hμ, by rw [hτidx]; rfl, by rw [hτidx, he]⟩
    · exact no_tau_gap hd1 h2 hc hlt

/-! ## `ν_C = T_C` -/

/-- **Theorem NU-CT in `R₂^C`**: `ν_C = T_C`.  The first non-standard pair `(ρ_L, ν_C)` has a standard
pair nested inside. -/
theorem nuC_eq_TnestC : nuC = TnestC := by
  refine le_antisymm nuC_le_TnestC ?_
  rcases nuC_le_Om1.lt_or_eq with hd1 | hd1
  swap
  · rw [hd1]; exact TnestC_le_Om1
  obtain ⟨c, hc, h2, hns⟩ := nuC_attained hd1
  obtain ⟨l, hl, rfl⟩ := left_restart_nuC hd1 hc h2 hns
  have hcof := pairs_cof_restart hl h2 hc hc.le
  obtain ⟨p, q, hcp, hpq, hqν, hpq2⟩ := pairs_up h2 hc hcof (upsilon l) hc
  exact TnestC_le ⟨hcp, hpq, hqν, h2, hpq2⟩

/-- **`[0, ν_C] ⊆ Core(R₂^C)`**. -/
theorem nuC_core : Set.Iic nuC ⊆ Core R2C := by
  rw [nuC_eq_TnestC]; exact TC_lt_core

/-- **Lemma CAP at `ν_C`**: no `α ≤ ν_C` is `≤₁` a point above `ν_C`. -/
theorem nuC_cap : ∀ α ≤ nuC, ∀ g, nuC < g → ¬ le1 α g := by
  rw [nuC_eq_TnestC]; exact cap_TC

/-- The first non-standard pair: `ρ_L <₂ ν_C` with `ρ_L` a restart, and `<₂`-pairs are cofinal below
`ν_C`. -/
theorem pairs_cof_nuC : (∃ l, IsRestartIdx l ∧ upsilon l < nuC ∧ le2 (upsilon l) nuC ∧
    ¬ IsStd (upsilon l) nuC) ∧ ∀ z < nuC, ∃ p q, z < p ∧ p < q ∧ q < nuC ∧ le2 p q := by
  obtain ⟨c, hc, h2, hns⟩ := nuC_attained nuC_lt_Om1
  obtain ⟨l, hl, rfl⟩ := left_restart_nuC nuC_lt_Om1 hc h2 hns
  exact ⟨⟨l, hl, hc, h2, hns⟩, pairs_up h2 hc (pairs_cof_restart hl h2 hc hc.le)⟩

end Googology.Trans.PoR.InaccPsi.R2
