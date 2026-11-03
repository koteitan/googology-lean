import Googology.Trans.PoR.InaccPsi.R2.YsBlk

/-!
# Ys: the block structure relative to a base point `a` (nested long reaches allowed)

`R2.Good O l` describes `[0, υ_l)` and asks `below` (no crossing of `υ_l` at all).  Inside a window
`W_k = [L(k), L(k+1))` the point `a = L(k)` crosses every window point, and the supply restarts `μ` cross
far (`Yi.yiWinShort_ref`).  `YsGood a O l` describes `(a, υ_l)` only and replaces `below` by

* `cross`: a point `c ∈ (a, υ_l)` with `c ≤₁ g`, `g ≥ υ_l`, is `ρ_μ` for a restart `μ < l` and
  `g ≤ δ_μ + O(μ)` (the corrected crossing clause `Yi.YiCross`, the bound being the restart's own reach);

and keeps `land`, `caps`, `pairs`, `sk` above `a` and, at every restart `μ < l` with `a ≤ ρ_μ`, a restart
context with crossings (`Ys.YsRstK`) and Lemma TOP at `δ_μ + O(μ)`.  The offsets `O(μ)` may be long (a
supply restart: `O(μ) ≥ δ_μ`).

* `Good.toYs`: the old structure is the case `a = 0`;  `ysGood_base`: the empty structure at `a = ρ_{l₀}`;
* `ysRst_of`: the restart context at `ρ_l` from the landing blocks and the pair field `nostr` at `ρ_l`;
* `ysTop_short`: Lemma TOP at `ρ_l` with an offset term `x·m + k` from `YsGood` (relative `R2.top_of_good`);
* `ysT3_short` / `ysT3_long`: the closedness above the restart block, for a short offset (from TOP and no
  crossing of `ρ_l` from `(x₀, ρ_l)`) and for a long reach (`x₀ = ρ_l`, the chain starts at `δ_l`);
* **`ysGood_step`**: the step `YsGood a O l ⇒ YsGood a O (l + ω²)` at a restart `l` (both kinds), with the
  chain of `Ys.YsBlkCtx` after `δ_l + o`;
* **`ysGood_limit`**: the limit step.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **The block structure of `(a, υ_l)` with crossings.** -/
structure YsGood (a : Ordinal.{0}) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop where
  cross : ∀ c, a < c → c < upsilon l → ∀ g, upsilon l ≤ g → le1 c g →
    ∃ μ, IsRestartIdx μ ∧ μ < l ∧ c = upsilon μ ∧ g ≤ upsilon (μ + ω + 1) + O μ
  land : ∀ c', a ≤ c' → c' < upsilon l → ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  caps : ∀ c d, a < c → c < d → d < upsilon l → le2 c d → ∀ x, a < x → x ≤ c → ∀ g, le1 x g →
    g ≤ d ∨ ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x = upsilon μ ∧ upsilon (μ + ω + 1) ≤ d ∧
      g ≤ upsilon (μ + ω + 1) + O μ
  pairs : ∀ c d, c < d → a < d → d < upsilon l → (le2 c d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
      μ < l ∧ a ≤ upsilon μ ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))
  sk : ∀ α, a < α → α < upsilon l → ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ
  rst : ∀ μ, IsRestartIdx μ → μ < l → a ≤ upsilon μ →
    YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
    (∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g) ∧
    ∃ T0 x0, upsilon (μ + ω) ≤ T0 ∧
      ∀ j : ℕ, YsBlkCtx (topA (μ + ω) T0 j) (lpA (μ + ω) j) (topA (μ + ω) T0 (j + 1)) x0

/-- **The old block structure is the case `a = 0`.** -/
theorem _root_.Googology.Trans.PoR.InaccPsi.R2.Good.toYs {O : Ordinal.{0} → Ordinal.{0}}
    {l : Ordinal.{0}} (G : Good O l) : YsGood 0 O l where
  cross := fun c _ hc g hg h => absurd h (G.below c hc g hg)
  land := fun c' _ hc' => by
    have hl : 0 < l := by
      rcases eq_or_ne l 0 with rfl | h
      · rw [upsilon_zero] at hc'; exact absurd hc' (not_lt.2 zero_le)
      · exact pos_iff_ne_zero.2 h
    exact G.land hl c' hc'
  caps := fun c d _ hcd hd h2 x _ hx g hg => G.caps c d hcd hd h2 x hx g hg
  pairs := fun c d hcd _ hd => by
    rw [G.pairs c d hcd hd]
    constructor
    · rintro ⟨μ, j, h1, h2, h3⟩; exact ⟨μ, j, h1, h2, zero_le, h3⟩
    · rintro ⟨μ, j, h1, h2, -, h3⟩; exact ⟨μ, j, h1, h2, h3⟩
  sk := fun α _ hα hnu γ => G.sk α hα hnu γ
  rst := fun μ hμ hμl _ => ⟨(G.rst μ hμ hμl).1.toYs, (G.rst μ hμ hμl).2.1,
    upsilon (μ + ω + 1) + O μ, 0, (G.rst μ hμ hμl).1.next.1.le.trans le_self_add,
    fun j => ((G.rst μ hμ hμl).2.2 j).toYs 0⟩

/-- **The empty relative structure** at the base `a = ρ_{l₀}`. -/
theorem ysGood_base (O : Ordinal.{0} → Ordinal.{0}) (l0 : Ordinal.{0}) :
    YsGood (upsilon l0) O l0 where
  cross := fun c hc hc' => absurd (hc.trans hc') (lt_irrefl _)
  land := fun c' hc hc' => absurd (lt_of_le_of_lt hc hc') (lt_irrefl _)
  caps := fun c d hc hcd hd => absurd ((hc.trans hcd).trans hd) (lt_irrefl _)
  pairs := fun c d _ hd hd' => absurd (hd.trans hd') (lt_irrefl _)
  sk := fun α hα hα' => absurd (hα.trans hα') (lt_irrefl _)
  rst := fun μ _ hμ ha => absurd (upsilon_normal.strictMono hμ) (not_lt.2 ha)

/-- The landing blocks below `υ_l` for every `c'`, from `YsGood` and `a < υ_l`. -/
theorem YsGood.land_all {a : Ordinal.{0}} {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (G : YsGood a O l) (ha : a < upsilon l) : ∀ c' < upsilon l, ∃ σ σ', UpsPt σ ∧ c' < σ ∧
      IsNext σ σ' ∧ σ' < upsilon l ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d) := by
  intro c' hc'
  obtain ⟨σ, σ', h1, h2, h3⟩ := G.land (max c' a) (le_max_right _ _) (max_lt hc' ha)
  exact ⟨σ, σ', h1, (le_max_left _ _).trans_lt h2, h3⟩

/-- **The restart context with crossings at `ρ_l`** from the landing blocks below `ρ_l` and the pair field
`nostr` at `ρ_l` (no pair from a point `≤ ρ_l` ends in `[ρ_l, δ_l]`). -/
theorem ysRst_of {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hland : ∀ c' < upsilon l, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l ∧
      (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
      (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d))
    (hnostr : ∀ c d, c < d → c ≤ upsilon l → upsilon l ≤ d → d ≤ upsilon (l + ω + 1) → ¬ le2 c d)
    (hc : upsilon (l + ω + 1) < Om1) :
    YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hlim : IsSuccLimit (l + ω) := isSuccLimit_add _ isSuccLimit_omega0
  refine ⟨upsPt_upsilon hl0, upsilon_normal.strictMono (lt_add_of_pos_right l omega0_pos),
    upsPt_upsilon (lt_of_lt_of_le hl0 le_self_add), ?_, hc, hnostr, hland, ?_, ?_⟩
  · have := upsilon_isNext (l + ω); rwa [succ_eq_add_one] at this
  · intro l' hl' hρl hlτ
    have h1 : l < l' := upsilon_normal.strictMono.lt_iff_lt.1 hρl
    have h2 : l' ≤ l + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
    rw [limit_eq_add_omega hl' h1 h2]
  · intro c' hc'
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
    refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
      hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
    exact upsilon_normal.strictMono (hlim.succ_lt hι)

/-- **Lemma TOP at `ρ_l` with a short offset term** `t = x·m + k`, from the relative structure: if
`a ≤ x₀ < ρ_l`, `O(l) = t(ρ_l)` and no restart `ρ_μ ∈ (x₀, ρ_l)` realizes `t` (`O(μ) < t(ρ_μ)`), then
`ρ_l` is not `≤₁` any `g > δ_l + O(l)`.  (Relative `R2.top_of_good`.) -/
theorem ysTop_short {a : Ordinal.{0}} {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (G : YsGood a O l) (R : YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    {m : ℕ} {k x0 : Ordinal.{0}} (hoff : O l = tm m k (upsilon l)) (hk : k < upsilon l)
    (hk1 : m = 0 → 1 ≤ k) (hax : a ≤ x0) (hx0 : x0 < upsilon l)
    (hreal : ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tm m k (upsilon μ)) :
    ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g := by
  rw [hoff]
  refine R.top_gen hk hk1 hx0 ?_
  intro c d hx0c hcd hd h2 x hx0x hxc e he1 hte hxe
  rcases G.caps c d (lt_of_le_of_lt hax hx0c) hcd hd h2 x (lt_of_le_of_lt hax hx0x) hxc (d + e) hxe with
    hle | ⟨μ, hμ, hμl, rfl, hδd, hg⟩
  · exact absurd hle (not_le.2 (lt_add_of_pos_right d (lt_of_lt_of_le zero_lt_one he1)))
  · have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have h1 := hreal μ hμ hμl hx0x
    have h2' := hte (upsPt_upsilon hμ0)
    have : upsilon (μ + ω + 1) + O μ < d + e :=
      lt_of_lt_of_le ((add_lt_add_iff_left _).2 (lt_of_lt_of_le h1 h2')) (add_le_add hδd le_rfl)
    exact absurd hg (not_le.2 this)

/-- **No crossing of `ρ_l` from `(x₀, ρ_l)`** when no restart `ρ_μ ∈ (x₀, ρ_l)` reaches `ρ_l`. -/
theorem ysBel_of {a : Ordinal.{0}} {O : Ordinal.{0} → Ordinal.{0}} {l x0 : Ordinal.{0}}
    (G : YsGood a O l) (hax : a ≤ x0)
    (hx : ∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → upsilon (μ + ω + 1) + O μ < upsilon l) :
    ∀ c, x0 < c → c < upsilon l → ∀ g, upsilon l ≤ g → ¬ le1 c g := by
  intro c hxc hc g hg hcg
  obtain ⟨μ, hμ, hμl, rfl, hgμ⟩ := G.cross c (lt_of_le_of_lt hax hxc) hc g hg hcg
  exact absurd (hg.trans hgμ) (not_le.2 (hx μ hμ hμl hxc))

/-- **The closedness after the restart block, short offset**: from TOP at `δ_l + o` and no crossing of
`ρ_l` from `(x₀, ρ_l)`. -/
theorem ysT3_short {l x0 o : Ordinal.{0}}
    (R : YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) (ho : o < upsilon (l + ω + 1))
    (htop : ∀ g, upsilon (l + ω + 1) + o < g → ¬ le1 (upsilon l) g)
    (hbel : ∀ c, x0 < c → c < upsilon l → ∀ g, upsilon l ≤ g → ¬ le1 c g) :
    ∀ c, x0 < c → c ≤ upsilon (l + ω + 1) + o → ∀ g, upsilon (l + ω + 1) + o < g → ¬ le1 c g :=
  R.T3off ho htop hbel

/-- **The closedness after the restart block, long reach** (`x₀ = ρ_l`, the chain starts at `δ_l`). -/
theorem ysT3_long {l : Ordinal.{0}}
    (R : YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ∀ c, upsilon l < c → c ≤ upsilon (l + ω + 1) + 0 → ∀ g, upsilon (l + ω + 1) + 0 < g → ¬ le1 c g := by
  intro c hc hcδ g hg
  rw [add_zero] at hcδ hg
  exact R.capδ c hc hcδ g hg

/-- **The step at a restart `l`** (an ordinary restart with a short offset, or a supply restart with a long
reach): from `(a, υ_l)` to `(a, υ_{l+ω²})`.  Inputs: the restart context at `ρ_l` (`R`), Lemma TOP at
`δ_l + O(l)` (`htop`), the start `T₀ = δ_l + o` of the chain (`o < δ_l`, `o ≤ O(l)`), the crossing bound `x₀`
of the chain (`a ≤ x₀ ≤ ρ_l`) with the closedness `hT3` above `x₀` at `T₀`, and for the points `c ≤ x₀`
crossing into a chain block: `hreach` (they reach its top) and `hnostrC` (no pair from them ends in it). -/
theorem ysGood_step {a : Ordinal.{0}} {O : Ordinal.{0} → Ordinal.{0}} {l o x0 : Ordinal.{0}}
    (hl : IsRestartIdx l) (G : YsGood a O l) (hal : a ≤ upsilon l)
    (R : YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (htop : ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g)
    (ho : o < upsilon (l + ω + 1)) (hoO : o ≤ O l) (hax : a ≤ x0) (hxl : x0 ≤ upsilon l)
    (hT3 : ∀ c, x0 < c → c ≤ upsilon (l + ω + 1) + o → ∀ g, upsilon (l + ω + 1) + o < g → ¬ le1 c g)
    (hreach : ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d →
      d < topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) → le1 c d →
      le1 c (topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1)))
    (hnostrC : ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA (l + ω) (upsilon (l + ω + 1) + o) j →
      ∀ d, topA (l + ω) (upsilon (l + ω + 1) + o) j < d →
      d ≤ topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) → ¬ le2 c d)
    (hcnt : l + ω * ω < Om1) : YsGood a O (l + ω * ω) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hll : l < l + ω * ω := lt_add_of_pos_right l hww
  set T0 := upsilon (l + ω + 1) + o with hT0def
  -- the chain after T₀
  have hT0 : T0 < lpA (l + ω) 0 := by
    have hU : UpsPt (lpA (l + ω) 0) := upsPt_upsilon (lpA_index_pos _ 0)
    have hδl : upsilon (l + ω + 1) < lpA (l + ω) 0 := by
      refine upsilon_normal.strictMono ?_
      simp only [Nat.cast_zero, mul_zero, add_zero]
      exact (add_lt_add_iff_left _).2 one_lt_omega0
    exact (indec_of_upsPt hU).add_lt hδl (ho.trans hδl)
  have hidx : ∀ l', IsSuccLimit l' → T0 < upsilon l' → l + ω < l' := by
    intro l' _ h
    have : upsilon (l + ω + 1) < upsilon l' := lt_of_le_of_lt le_self_add h
    exact lt_of_le_of_lt le_self_add (upsilon_normal.strictMono.lt_iff_lt.1 this)
  have C : ∀ j : ℕ, YsBlkCtx (topA (l + ω) T0 j) (lpA (l + ω) j) (topA (l + ω) T0 (j + 1)) x0 :=
    ysCtxA (l + ω) T0 x0 hT3 hreach hnostrC hT0 hidx
      (fun j n => ups_lt_Om1 _ ((idx_lt l j n).trans hcnt))
  have hTa : upsilon (l + ω) ≤ T0 := R.next.1.le.trans le_self_add
  have he : l + ω + ω * ω = l + ω * ω := by rw [add_assoc, w_add_ww]
  have hbelowC := ysChain_below C hT3 hTa
  have hlandC := ysChain_land C hTa
  rw [he] at hbelowC hlandC
  -- a pair whose right end is `≥ ρ_l` has its left end above `ρ_l`
  have hρc : ∀ c d, c < d → upsilon l ≤ d → d < upsilon (l + ω * ω) → le2 c d → upsilon l < c := by
    intro c d hcd hρd hd h2
    rcases lt_or_ge (upsilon l) c with h' | hcρ
    · exact h'
    exfalso
    rcases le_or_gt d (upsilon (l + ω + 1)) with hdδ | hδd
    · exact R.nostr c d hcd hcρ hρd hdδ h2
    rcases le_or_gt d T0 with hdT | hTd
    · exact (decomp_mid ho hδd hdT) (indec_of_lt2_right h2 hcd).1
    · obtain ⟨k, rfl, -⟩ := ysChain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
      have hTc : T0 < lpA (l + ω) k :=
        lt_of_le_of_lt ((ysChain_topMono C).monotone (Nat.zero_le k)) (C k).Tτ
      exact absurd (((R.ρτ.trans_le hTa).trans hTc).trans_le hcρ) (lt_irrefl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cross
    intro c hac hc g hg hcg
    have hlg : upsilon l ≤ g := (upsilon_normal.strictMono hll).le.trans hg
    rcases lt_trichotomy c (upsilon l) with hcρ | e | hρc'
    · obtain ⟨μ, hμ, hμl, h1, h2⟩ := G.cross c hac hcρ g hlg hcg
      exact ⟨μ, hμ, hμl.trans hll, h1, h2⟩
    · exact ⟨l, hl, hll, e, not_lt.1 fun h' => htop g h' (e ▸ hcg)⟩
    · exact absurd hcg (hbelowC c (lt_of_le_of_lt hxl hρc') hc g hg)
  · -- land
    intro c' _ hc'
    exact hlandC c' hc'
  · -- caps
    intro c d hac hcd hd h2 x hax' hxc g hg
    rcases lt_or_ge d (upsilon l) with hdρ | hρd
    · rcases G.caps c d hac hcd hdρ h2 x hax' hxc g hg with h | ⟨μ, hμ, hμl, hx, hδd, hg'⟩
      · exact Or.inl h
      · exact Or.inr ⟨μ, hμ, hμl.trans hll, hx, hδd, hg'⟩
    have hρc' := hρc c d hcd hρd hd h2
    have hρd' : upsilon l < d := hρc'.trans hcd
    -- a crossing point `x ≤ ρ_l` past `d ≥ ρ_l`
    have hcrossx : ∀ y, a < y → y ≤ upsilon l → upsilon l ≤ d → le1 y g → d < g →
        ∃ μ, IsRestartIdx μ ∧ μ < l + ω * ω ∧ y = upsilon μ ∧ upsilon (μ + ω + 1) ≤ d ∧
          g ≤ upsilon (μ + ω + 1) + O μ := by
      intro y hay hyl hld hyg hdg
      rcases eq_or_lt_of_le hyl with e | hylt
      · refine ⟨l, hl, hll, e, ?_, not_lt.1 fun h' => htop g h' (e ▸ hyg)⟩
        rcases le_or_gt (upsilon (l + ω + 1)) d with h | h
        · exact h
        · exact absurd h2 (R.noPairGap c d hcd hρd' h)
      · obtain ⟨μ, hμ, hμl, rfl, hgμ⟩ := G.cross y hay hylt g (hld.trans hdg.le) hyg
        have hδμ : upsilon (μ + ω + 1) < upsilon l :=
          upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
            (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
        exact ⟨μ, hμ, hμl.trans hll, rfl, (hδμ.trans_le hρd).le, hgμ⟩
    rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
    · exact absurd h2 (R.noPairGap c d hcd hρd' hdδ)
    · rcases le_or_gt g d with hgd | hdg
      · exact Or.inl hgd
      right
      rcases le_or_gt x (upsilon l) with hxρ | hρx
      · exact hcrossx x hax' hxρ hρd hg hdg
      · exact absurd hg (R.capδ x hρx ((hxc.trans hcd.le).trans e.le) g (by rw [← e]; exact hdg))
    · rcases le_or_gt d T0 with hdT | hTd
      · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid ho hδd hdT)
      · rcases le_or_gt g d with hgd | hdg
        · exact Or.inl hgd
        right
        rcases le_or_gt x x0 with hxx | hxx
        · exact hcrossx x hax' (hxx.trans hxl) hρd hg hdg
        · obtain ⟨k, rfl, rfl⟩ := ysChain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
          have hTc : T0 < lpA (l + ω) k :=
            lt_of_le_of_lt ((ysChain_topMono C).monotone (Nat.zero_le k)) (C k).Tτ
          exact absurd hg (ysChain_cap C hTa _ _ hTc hcd (by rw [he]; exact hd) h2 x hxx (hxc.trans hcd.le) g hdg)
  · -- pairs
    intro c d hcd had hd
    constructor
    · intro h2
      rcases lt_or_ge d (upsilon l) with hdρ | hρd
      · obtain ⟨μ, j, hμ, hμl, haμ, hc, hd'⟩ := (G.pairs c d hcd had hdρ).1 h2
        exact ⟨μ, j, hμ, hμl.trans hll, haμ, hc, hd'⟩
      have hρc' := hρc c d hcd hρd hd h2
      rcases lt_trichotomy d (upsilon (l + ω + 1)) with hdδ | e | hδd
      · exact absurd h2 (R.noPairGap c d hcd (hρc'.trans hcd) hdδ)
      · rw [e] at hcd h2 ⊢
        refine ⟨l, 0, Or.inr hl, hll, hal, ?_, ?_⟩
        · rw [idx_one]; exact R.pairs_at_top hcd h2
        · rw [idx_one]
      · rcases le_or_gt d T0 with hdT | hTd
        · exact absurd (indec_of_lt2_right h2 hcd).1 (decomp_mid ho hδd hdT)
        · obtain ⟨k, rfl, rfl⟩ := ysChain_pair C hTa hTd (by rw [he]; exact hd) hcd h2
          refine ⟨l, k + 1, Or.inr hl, hll, hal, ?_, ?_⟩
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω) = _
            rw [idx_chain]
          · show upsilon (l + ω + ω * (k : Ordinal.{0}) + ω + 1) = _
            rw [idx_chain]
    · rintro ⟨μ, j, hμ, hμl, haμ, rfl, rfl⟩
      rcases lt_trichotomy μ l with hμl' | e | hlμ
      · have hlt : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon l :=
          upsilon_normal.strictMono (lt_of_lt_of_le (pidx_lt μ j)
            (next_mult (mult_of hμ) (ri_iff.1 hl).2 hμl'))
        exact (G.pairs _ _ hcd had hlt).2 ⟨μ, j, hμ, hμl', haμ, rfl, rfl⟩
      · rw [e]
        rcases j with _ | k
        · rw [idx_one]; exact R.pair
        · have := (C k).pair
          simp only [lpA, topA] at this
          rw [idx_chain]; exact this
      · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (mult_of hμ) hlμ))
  · -- skeletal
    intro α haα hα hnu γ
    rcases lt_or_ge α (upsilon l) with hαρ | hρα
    · exact G.sk α haα hαρ hnu γ
    rcases eq_or_lt_of_le hρα with e | hρα'
    · exact absurd (e ▸ R.ρU) hnu
    rcases le_or_gt α (upsilon (l + ω + 1)) with hαδ | hδα
    · exact skel_block R.next.2.1 R.δ1 hρα' hαδ hnu R.lowδ γ
    rcases le_or_gt α T0 with hαT | hTα
    · exact sk_decomp (decomp_mid ho hδα hαT) γ
    · exact ysChain_sk C hTa hTα (by rw [he]; exact hα) hnu γ
  · -- restarts
    intro μ hμ hμl haμ
    rcases lt_trichotomy μ l with hμl' | e | hlμ
    · exact G.rst μ hμ hμl' haμ
    · rw [e]; exact ⟨R, htop, T0, x0, hTa, C⟩
    · exact absurd hμl (not_lt.2 (next_mult (ri_iff.1 hl).2 (ri_iff.1 hμ).2 hlμ))

/-- **The limit step** of the relative structure (base index `l₀`, `a = ρ_{l₀}`). -/
theorem ysGood_limit {O : Ordinal.{0} → Ordinal.{0}} {l0 η : Ordinal.{0}} (hη : IsSuccLimit η)
    (hl0 : l0 < ω * ω * η)
    (IH : ∀ η' < η, l0 ≤ ω * ω * η' → YsGood (upsilon l0) O (ω * ω * η')) :
    YsGood (upsilon l0) O (ω * ω * η) := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hlim : IsSuccLimit (ω * ω * η) := isSuccLimit_mul_right hww hη
  have hlt : ∀ η' < η, ω * ω * η' < ω * ω * η := fun η' h => (mul_lt_mul_iff_right₀ hww).2 h
  have hup : ∀ η' < η, upsilon (ω * ω * η') < upsilon (ω * ω * η) :=
    fun η' h => upsilon_normal.strictMono (hlt η' h)
  obtain ⟨η0, hη0, hl0η0⟩ := (lt_mul_iff_of_isSuccLimit hη).1 hl0
  have keyμ : ∀ μ < ω * ω * η, ∃ η' < η, l0 ≤ ω * ω * η' ∧ μ < ω * ω * η' := by
    intro μ hμ
    obtain ⟨η1, hη1, hμη1⟩ := (lt_mul_iff_of_isSuccLimit hη).1 hμ
    refine ⟨max η0 η1, max_lt hη0 hη1, hl0η0.le.trans (mul_le_mul_right (le_max_left _ _) _),
      hμη1.trans_le (mul_le_mul_right (le_max_right _ _) _)⟩
  have key : ∀ c < upsilon (ω * ω * η), ∃ η' < η, l0 ≤ ω * ω * η' ∧ c < upsilon (ω * ω * η') := by
    intro c hc
    obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc
    obtain ⟨η', hη', h1, h2⟩ := keyμ ι hι
    exact ⟨η', hη', h1, hcx.trans (upsilon_normal.strictMono h2)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hac hc g hg hcg
    obtain ⟨η', hη', h0, hcη⟩ := key c hc
    obtain ⟨μ, hμ, hμl, h1⟩ := (IH η' hη' h0).cross c hac hcη g ((hup η' hη').le.trans hg) hcg
    exact ⟨μ, hμ, hμl.trans (hlt η' hη'), h1⟩
  · intro c' hac hc'
    obtain ⟨η', hη', h0, hcη⟩ := key c' hc'
    obtain ⟨σ, σ', h1, h2, h3, h4, h5⟩ := (IH η' hη' h0).land c' hac hcη
    exact ⟨σ, σ', h1, h2, h3, h4.trans (hup η' hη'), h5⟩
  · intro c d hac hcd hd h2 x hax hx g hg
    obtain ⟨η', hη', h0, hdη⟩ := key d hd
    rcases (IH η' hη' h0).caps c d hac hcd hdη h2 x hax hx g hg with h | ⟨μ, hμ, hμl, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨μ, hμ, hμl.trans (hlt η' hη'), h3⟩
  · intro c d hcd had hd
    constructor
    · intro h2
      obtain ⟨η', hη', h0, hdη⟩ := key d hd
      obtain ⟨μ, j, hμ, hμl, h3⟩ := ((IH η' hη' h0).pairs c d hcd had hdη).1 h2
      exact ⟨μ, j, hμ, hμl.trans (hlt η' hη'), h3⟩
    · rintro ⟨μ, j, hμ, hμl, haμ, rfl, rfl⟩
      obtain ⟨η', hη', h0, hμη⟩ := keyμ μ hμl
      have hlt' : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < upsilon (ω * ω * η') :=
        upsilon_normal.strictMono (lt_of_lt_of_le (pidx_lt μ j)
          (next_mult (mult_of hμ) (dvd_mul_right _ _) hμη))
      exact ((IH η' hη' h0).pairs _ _ hcd had hlt').2 ⟨μ, j, hμ, hμη, haμ, rfl, rfl⟩
  · intro α haα hα hnu γ
    obtain ⟨η', hη', h0, hαη⟩ := key α hα
    exact (IH η' hη' h0).sk α haα hαη hnu γ
  · intro μ hμ hμl haμ
    obtain ⟨η', hη', h0, hμη⟩ := keyμ μ hμl
    exact (IH η' hη' h0).rst μ hμ hμη haμ

end Googology.Trans.PoR.InaccPsi.R2.Ys
