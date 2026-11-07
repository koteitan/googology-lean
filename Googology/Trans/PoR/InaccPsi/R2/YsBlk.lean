import Googology.Trans.PoR.InaccPsi.R2.YsRstW

/-!
# Ys: block contexts and chains of blocks when points below cross into them

`R2.BlkCtx T τ β` asks (T3): no `c ≤ T` is `≤₁` a point `> T`.  Inside a window (or inside the long reach of
a supply restart) the points `≤ x₀` (`L(k)`, the supply restarts covering the block) do cross.
`YsBlkCtx T τ β x₀` keeps (T3) only above `x₀` and asks for the crossing points `c ≤ min(x₀, T)`:

* `reach`: a crossing into `(T, β)` reaches `β` (`c ≤₁ d`, `T < d < β` ⇒ `c ≤₁ β`);
* `nostr`: no `<₂`-pair from `c` has its right end in `(T, β]`.

All the block lemmas hold again: `left_eq`, `no_pair_upto`, `le1_lowτ`, `chains`, `not_le2_gap`,
`no_pair_gap`, `le1_lowβ`, `le2_eq`, `toPair` (a `Ys.YsPairCtx`), **`pair`** (`τ <₂ β`), `T3_next` (above
`x₀`), `pairs_at_top`.  `R2.BlkCtx.toYs`: every old block context is one (any `x₀`).
`ysCtxA`: the chain of such contexts after `T₀` (the relative `R2.ctxA`), `ysChain_pairs`, `ysChain_below`
(no point of `(x₀, υ_{a+ω²})` crosses `υ_{a+ω²}`), `ysChain_land`, `ysChain_cap`, `ysChain_sk`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ys

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- A block context with crossings from the points `≤ x₀`. -/
structure YsBlkCtx (T τ β x0 : Ordinal.{0}) : Prop where
  τU : UpsPt τ
  next : IsNext τ β
  β1 : β < Om1
  Tτ : T < τ
  T3 : ∀ c, x0 < c → c ≤ T → ∀ g, T < g → ¬ le1 c g
  nostr : ∀ c, c ≤ x0 → c ≤ T → ∀ d, T < d → d ≤ β → ¬ le2 c d
  left : ∀ l, IsSuccLimit l → T < upsilon l → upsilon l ≤ τ → upsilon l = τ
  cof : ∀ c' < τ, ∃ u, UpsPt u ∧ c' < u ∧ u < τ

/-- An old block context is a block context with crossings, for every `x₀`. -/
theorem _root_.Googology.Trans.PoR.InaccPsi.R2.BlkCtx.toYs {T τ β : Ordinal.{0}} (h : BlkCtx T τ β)
    (x0 : Ordinal.{0}) : YsBlkCtx T τ β x0 :=
  ⟨h.τU, h.next, h.β1, h.Tτ, fun c _ hc g hg => h.T3 c hc g hg,
    fun c _ hc d hd _ h2 => h.T3 c hc d hd (le2_le1 h2), h.left, h.cof⟩

namespace YsBlkCtx

variable {T τ β x0 : Ordinal.{0}} (h : YsBlkCtx T τ β x0)
include h

theorem τ1 : τ < Om1 := h.next.1.trans h.β1

theorem τβ : τ < β := h.next.1

theorem T_iff : ∀ a, a < Om1 → (a ∈ Tset τ ↔ a < β) := by
  obtain ⟨m, hm, hT⟩ := exists_next h.τU h.τ1
  rw [← hm.unique h.next]; exact hT

/-- A `<₂`-left end in `(T, τ]` is `τ`. -/
theorem left_eq {c d : Ordinal.{0}} (h2 : le2 c d) (hcd : c < d) (hTc : T < c) (hcτ : c ≤ τ) :
    c = τ := by
  obtain ⟨l, hl, rfl⟩ := left_limit h2 hcd (lt_of_le_of_lt hcτ h.τ1)
  exact h.left l hl hTc hcτ

/-- No `<₂`-pair has its right end in `(T, τ]`. -/
theorem no_pair_upto : ∀ c d, c < d → T < d → d ≤ τ → ¬ le2 c d := by
  intro c d hcd hTd hdτ h2
  rcases le_or_gt c T with hcT | hTc
  · rcases le_or_gt c x0 with hcx | hxc
    · exact h.nostr c hcx hcT d hTd (hdτ.trans h.next.1.le) h2
    · exact h.T3 c hxc hcT d hTd (le2_le1 h2)
  · have := h.left_eq h2 hcd hTc (hcd.le.trans hdτ)
    rw [this] at hcd
    exact absurd (lt_of_lt_of_le hcd hdτ) (lt_irrefl _)

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, τ]`. -/
theorem le1_lowτ : ∀ a b, T < a → b ≤ τ → (le1 a b ↔ le1R a b) := fun a b ha hb =>
  ysBlk h.τ1 (fun c d hcd hTd hdτ => h.no_pair_upto c d hcd hTd hdτ.le) b hb a ha

/-- `≤₁`-chains of `υ`-points of `R₂^C`, cofinal below `τ` (above `T`). -/
theorem chains : ∀ c' < τ, ∃ g : ℕ → Ordinal.{0}, StrictMono g ∧ (∀ i, Indec (g i)) ∧
    (∀ i, c' < g i ∧ g i < τ) ∧ ∀ i k, i ≤ k → le1 (g i) (g k) := by
  classical
  intro c' hc'
  let F : Ordinal.{0} → Ordinal.{0} := fun x => if hx : x < τ then Classical.choose (h.cof x hx) else 0
  have hF : ∀ x < τ, UpsPt (F x) ∧ x < F x ∧ F x < τ := fun x hx => by
    simp only [F, dif_pos hx]; exact Classical.choose_spec (h.cof x hx)
  let g : ℕ → Ordinal.{0} := fun i => Nat.rec (motive := fun _ => Ordinal.{0}) (F (max c' T))
    (fun _ y => F y) i
  have hm : max c' T < τ := max_lt hc' h.Tτ
  have hg : ∀ i, UpsPt (g i) ∧ max c' T < g i ∧ g i < τ := by
    intro i
    induction i with
    | zero => exact hF _ hm
    | succ i ih =>
      have := hF (g i) ih.2.2
      exact ⟨this.1, ih.2.1.trans this.2.1, this.2.2⟩
  have hgs : ∀ i, g i < g (i + 1) := fun i => (hF (g i) (hg i).2.2).2.1
  have hmono : StrictMono g := strictMono_nat_of_lt_succ hgs
  refine ⟨g, hmono, fun i => indec_of_upsPt (hg i).1,
    fun i => ⟨lt_of_le_of_lt (le_max_left _ _) (hg i).2.1, (hg i).2.2⟩, fun i k hik => ?_⟩
  refine (h.le1_lowτ (g i) (g k) (lt_of_le_of_lt (le_max_right _ _) (hg i).2.1)
    (hg k).2.2.le).2 ?_
  exact (hg i).1.2 _ (hmono.monotone hik)

/-- `τ <₂ d` fails for `d ∈ (τ, β)`. -/
theorem not_le2_gap : ∀ d, τ < d → d < β → ¬ le2 τ d := by
  classical
  intro d hτd hdβ h2
  have hd1 : d < Om1 := hdβ.trans h.β1
  set K := ht τ d + 2 with hK
  obtain ⟨f, hfM, hfI, -, -⟩ := h.chains 0 (lt_of_le_of_lt zero_le h.Tτ)
  have hZc : Closed (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    closed_of_indec (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact hfI i)
  have hcof : CofCov R2C ∅ ((Finset.range (K + 1)).image f) chainP τ := by
    intro c' hc'
    obtain ⟨g, hgM, hgI, hgb, hg1⟩ := h.chains c' hc'
    obtain ⟨hh, hcov, -⟩ := cov_chain R2C K hfM hgM hfI hgI (fun i j hij _ => hg1 i j hij)
      le2_refl
    refine ⟨(Finset.range (K + 1)).image g, ?_, ?_, hh, ?_⟩
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hgb i
    · rw [Finset.empty_union]
      exact closed_of_indec (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hgI i)
    · rw [Finset.empty_union]; exact hcov
  obtain ⟨-, -, H2⟩ := le2_iff.1 h2
  have hcofd := H2 ∅ (by simp) _ chainP hZc hcof
  obtain ⟨Y, hY, -, hh, hcov⟩ := hcofd τ hτd
  have hmemZ : ∀ i ≤ K, f i ∈ (↑((Finset.range (K + 1)).image f) : Set Ordinal.{0}) :=
    fun i hi => Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
  have hzY : ∀ i ≤ K, τ < hh (f i) ∧ hh (f i) < d := by
    intro i hi
    have hm := hcov.1.1.mapsTo (hmemZ i hi)
    rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at hm
    exact hY _ (Finset.mem_coe.1 hm)
  have hch : ∀ i < K, hh (f i) < hh (f (i + 1)) ∧ le1R (hh (f i)) (hh (f (i + 1))) := by
    intro i hi
    refine ⟨hcov.1.2.1 (hmemZ i hi.le) (hmemZ (i + 1) hi) (hfM (Nat.lt_succ_self i)), ?_⟩
    have h1 : le1 (hh (f i)) (hh (f (i + 1))) :=
      hcov.2.1 _ (hmemZ i hi.le) _ (hmemZ (i + 1) hi) (hfM.monotone (Nat.le_succ i))
    exact inc1 ((hzY (i + 1) hi).2.trans hd1) h1
  have hbound := chain_bound_gap (upsPt_inE h.τU) h.τ1 h.T_iff hdβ hd1 K
    (fun i => hh (f i)) (hzY 0 (Nat.zero_le K)).1 (hzY K le_rfl).2.le hch
  omega

/-- No `<₂`-pair has its right end in `(T, β)`. -/
theorem no_pair_gap : ∀ c d, c < d → T < d → d < β → ¬ le2 c d := by
  intro c d hcd hTd hdβ h2
  rcases le_or_gt c T with hcT | hTc
  · rcases le_or_gt c x0 with hcx | hxc
    · exact h.nostr c hcx hcT d hTd hdβ.le h2
    · exact h.T3 c hxc hcT d hTd (le2_le1 h2)
  have hc1 : c < Om1 := (hcd.trans hdβ).trans h.β1
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hcd hc1
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd (lt_trans hcd hdβ) (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  have := h.left_eq h2 hcd hTc hcτ
  subst this
  exact h.not_le2_gap d hcd hdβ h2

/-- `≤₁` of `R₂^C` is `≤₁` of `R₁⁺` on `(T, β]`. -/
theorem le1_lowβ : ∀ a b, T < a → b ≤ β → (le1 a b ↔ le1R a b) := fun a b ha hb =>
  ysBlk h.β1 h.no_pair_gap b hb a ha

theorem le2_eq {c d : Ordinal.{0}} (h2 : le2 c d) (hTd : T < d) (hdβ : d < β) : c = d := by
  rcases eq_or_lt_of_le (le2_le h2) with e | hlt
  · exact e
  · exact absurd h2 (h.no_pair_gap c d hlt hTd hdβ)

/-- A block context with crossings is a pair context with crossings. -/
theorem toPair : YsPairCtx T τ β := by
  exact ⟨h.τU, h.next, h.β1, h.Tτ, h.cof, h.no_pair_gap, h.le1_lowβ⟩

/-- The pair of the block, from the pair context. -/
theorem pair : le2 τ β := h.toPair.pair

/-- (T3) at `β` above `x₀`: no `c ∈ (x₀, β]` is `≤₁` an ordinal `> β`. -/
theorem T3_next : ∀ c, x0 < c → c ≤ β → ∀ g, β < g → ¬ le1 c g := by
  classical
  intro c hxc hcβ g hg hcg
  have hτI := indec_of_upsPt h.τU
  have hβI := indec_of_upsPt h.next.2.1
  rcases le_or_gt c T with hcT | hTc
  · exact h.T3 c hxc hcT g (h.Tτ.trans (h.τβ.trans hg)) hcg
  rcases le_or_gt c τ with hcτ | hτc
  · have hmem : ∀ x ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}), x = τ ∨ x = β := by
      intro x hx; simpa using hx
    obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hcg hTc ∅ {τ, β} (by simp)
      (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ⟨hcτ, h.τβ.trans hg⟩
        · exact ⟨hcβ, hg⟩)
      (closed_of_indec (by
        intro x hx
        rcases hmem x hx with rfl | rfl
        · exact hτI
        · exact hβI))
    have hτm : τ ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have hβm : β ∈ (↑((∅ : Finset Ordinal.{0}) ∪ {τ, β} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f β) := hf.2.2 _ hτm _ hβm h.pair
    have hlt : f τ < f β := hf.1.2.1 hτm hβm h.τβ
    have hfβ := hYt _ (hmap β (by simp))
    exact h.no_pair_gap _ _ hlt hfβ.1 (lt_of_lt_of_le hfβ.2 (hcτ.trans h.τβ.le)) h2
  · obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hcg hτc {τ} {β} (by simpa using hτc)
      (by simpa using ⟨hcβ, hg⟩)
      (closed_of_indec (by
        intro x hx
        simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hτI
        · exact hβI))
    have hτm : τ ∈ (↑({τ} ∪ {β} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have hβm : β ∈ (↑({τ} ∪ {β} : Finset Ordinal.{0}) : Set Ordinal.{0}) := by simp
    have h2 : le2 (f τ) (f β) := hf.2.2 _ hτm _ hβm h.pair
    have hfβ := hYt _ (hmap β (by simp))
    rw [hfix τ (by simp)] at h2
    exact h.no_pair_gap _ _ hfβ.1 (h.Tτ.trans hfβ.1) (lt_of_lt_of_le hfβ.2 hcβ) h2

/-- `τ` is the only `<₂`-predecessor of `β`. -/
theorem pairs_at_top {c : Ordinal.{0}} (hc : c < β) (h2 : le2 c β) : c = τ := by
  rcases le_or_gt c T with hcT | hTc
  · rcases le_or_gt c x0 with hcx | hxc
    · exact absurd h2 (h.nostr c hcx hcT β (h.Tτ.trans h.τβ) le_rfl)
    · exact absurd (le2_le1 h2) (h.T3 c hxc hcT β (h.Tτ.trans h.τβ))
  have hcU := Googology.Trans.PoR.InaccPsi.R2.left h2 hc (hc.trans h.β1)
  have hcτ : c ≤ τ := by
    by_contra hlt
    exact absurd hc (not_lt.2 (h.next.2.2 c (not_le.1 hlt) hcU))
  exact h.left_eq h2 hc hTc hcτ

end YsBlkCtx


/-- The chain of block contexts after `T₀`. -/
theorem ysCtxA (a T0 x0 : Ordinal.{0})
    (hT3 : ∀ c, x0 < c → c ≤ T0 → ∀ g, T0 < g → ¬ le1 c g)
    (hnostr : ∀ j : ℕ, ∀ c, c ≤ x0 → c ≤ topA a T0 j → ∀ d, topA a T0 j < d → d ≤ topA a T0 (j + 1) →
      ¬ le2 c d)
    (hT0 : T0 < lpA a 0) (hidx : ∀ l, IsSuccLimit l → T0 < upsilon l → a < l)
    (hc : ∀ j n : ℕ, upsilon (a + ω * (j : Ordinal.{0}) + n) < Om1) :
    ∀ j : ℕ, YsBlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)) x0 := by
  have base : ∀ j : ℕ, (∀ c, x0 < c → c ≤ topA a T0 j → ∀ g, topA a T0 j < g → ¬ le1 c g) →
      (topA a T0 j < lpA a j) →
      (∀ l, IsSuccLimit l → topA a T0 j < upsilon l → a + ω * (j : Ordinal.{0}) < l) →
      YsBlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)) x0 := by
    intro j hT3' hTτ hidx'
    have hlim : IsSuccLimit (a + ω * (j : Ordinal.{0}) + ω) := isSuccLimit_add _ isSuccLimit_omega0
    have hnext : IsNext (lpA a j) (topA a T0 (j + 1)) := by
      have := upsilon_isNext (a + ω * (j : Ordinal.{0}) + ω)
      rwa [succ_eq_add_one] at this
    refine ⟨upsPt_upsilon (lpA_index_pos a j), hnext, ?_, hTτ, hT3', hnostr j, ?_, ?_⟩
    · show upsilon (a + ω * (j : Ordinal.{0}) + ω + 1) < Om1
      have := hc (j + 1) 1
      rwa [omega_mul_succ, ← add_assoc, Nat.cast_one] at this
    · intro l hl hTl hlτ
      have h1 := hidx' l hl hTl
      have h2 : l ≤ a + ω * (j : Ordinal.{0}) + ω := upsilon_normal.strictMono.le_iff_le.1 hlτ
      show upsilon l = upsilon (a + ω * (j : Ordinal.{0}) + ω)
      rw [limit_eq_add_omega hl h1 h2]
    · intro c' hc'
      obtain ⟨_, ⟨ι, hι, rfl⟩, hcx⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hc'
      refine ⟨upsilon (succ ι), upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι)),
        hcx.trans (upsilon_normal.strictMono (lt_succ ι)), ?_⟩
      exact upsilon_normal.strictMono (hlim.succ_lt hι)
  intro j
  induction j with
  | zero =>
    refine base 0 hT3 hT0 ?_
    intro l hl hTl
    simpa using hidx l hl hTl
  | succ j ih =>
    refine base (j + 1) ih.T3_next ?_ ?_
    · show upsilon (a + ω * (j : Ordinal.{0}) + ω + 1) <
        upsilon (a + ω * ((j + 1 : ℕ) : Ordinal.{0}) + ω)
      rw [omega_mul_succ, ← add_assoc]
      exact upsilon_normal.strictMono ((add_lt_add_iff_left _).2 one_lt_omega0)
    · intro l _ hTl
      have : a + ω * (j : Ordinal.{0}) + ω + 1 < l := upsilon_normal.strictMono.lt_iff_lt.1 hTl
      rw [omega_mul_succ, ← add_assoc]
      exact lt_of_le_of_lt le_self_add this

section YsChain

variable {a T0 x0 : Ordinal.{0}}
  (hctx : ∀ j : ℕ, YsBlkCtx (topA a T0 j) (lpA a j) (topA a T0 (j + 1)) x0)
include hctx

theorem ysChain_topMono : StrictMono (topA a T0) :=
  strictMono_nat_of_lt_succ fun j => lt_trans (hctx j).Tτ (hctx j).τβ

/-- The pairs with right end in `(T₀, topA j]`. -/
theorem ysChain_pairs : ∀ j : ℕ, ∀ c d, c < d → T0 < d → d ≤ topA a T0 j → le2 c d →
    ∃ k < j, c = lpA a k ∧ d = topA a T0 (k + 1) := by
  intro j
  induction j with
  | zero =>
    intro c d _ hTd hd _
    exact absurd (lt_of_lt_of_le hTd hd) (lt_irrefl _)
  | succ j ih =>
    intro c d hcd hTd hd h2
    rcases le_or_gt d (topA a T0 j) with hdj | hdj
    · obtain ⟨k, hk, hck, hdk⟩ := ih c d hcd hTd hdj h2
      exact ⟨k, Nat.lt_succ_of_lt hk, hck, hdk⟩
    rcases eq_or_lt_of_le hd with e | hlt
    · subst e
      exact ⟨j, Nat.lt_succ_self j, (hctx j).pairs_at_top hcd h2, rfl⟩
    · exact absurd h2 ((hctx j).no_pair_gap c d hcd hdj hlt)

theorem ysChain_top_lt (j : ℕ) : topA a T0 (j + 1) < upsilon (a + ω * ω) :=
  ((hctx (j + 1)).Tτ).trans (chainA_lp_lt (a := a) (j + 1))

/-- No point below `υ_{a+ω·ω}` is `≤₁` a point `≥ υ_{a+ω·ω}`. -/
theorem ysChain_below (hT3 : ∀ c, x0 < c → c ≤ T0 → ∀ g, T0 < g → ¬ le1 c g)
    (hTa : upsilon a ≤ T0) :
    ∀ c, x0 < c → c < upsilon (a + ω * ω) → ∀ g, upsilon (a + ω * ω) ≤ g → ¬ le1 c g := by
  intro c hxc hc g hg
  have hT0 : T0 < upsilon (a + ω * ω) := ((hctx 0).Tτ).trans (chainA_lp_lt (a := a) 0)
  rcases chainA_sup hTa hc with hcT | ⟨j, hcj⟩
  · exact hT3 c hxc hcT g (lt_of_lt_of_le hT0 hg)
  · exact (hctx (j + 1)).T3 c hxc hcj g (lt_of_lt_of_le (ysChain_top_lt hctx j) hg)

/-- Landing blocks below `υ_{a+ω·ω}`. -/
theorem ysChain_land (hTa : upsilon a ≤ T0) : ∀ c' < upsilon (a + ω * ω), ∃ σ σ', UpsPt σ ∧
    c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon (a + ω * ω) ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d) := by
  intro c' hc'
  have hj : ∃ j, c' < lpA a j := by
    rcases chainA_sup hTa hc' with hcT | ⟨j, hcj⟩
    · exact ⟨0, lt_of_le_of_lt hcT (hctx 0).Tτ⟩
    · exact ⟨j + 1, lt_of_le_of_lt hcj (hctx (j + 1)).Tτ⟩
  obtain ⟨j, hcj⟩ := hj
  have H := hctx j
  obtain ⟨σ, hσU, hσ, hστ⟩ := H.cof (max c' (topA a T0 j)) (max_lt hcj H.Tτ)
  obtain ⟨σ', hσn, -⟩ := exists_next hσU (hστ.trans H.τ1)
  have hσ'τ : σ' ≤ lpA a j := hσn.2.2 _ hστ H.τU
  have hTσ : topA a T0 j < σ := lt_of_le_of_lt (le_max_right _ _) hσ
  refine ⟨σ, σ', hσU, lt_of_le_of_lt (le_max_left _ _) hσ, hσn,
    lt_of_le_of_lt hσ'τ (chainA_lp_lt (a := a) j), ?_, ?_, ?_⟩
  · intro a' b ha' hb
    exact H.le1_lowτ a' b (hTσ.trans ha') (hb.le.trans hσ'τ)
  · intro b hb hbσ
    exact (H.le1_lowτ σ b hTσ (hbσ.le.trans hσ'τ)).2 (hσU.2 b hb)
  · intro c d hcd hσd hdσ
    exact H.no_pair_upto c d hcd (hTσ.trans hσd) (hdσ.le.trans hσ'τ)

/-- The pairs above `T₀` below `υ_{a+ω·ω}` end at block tops, which are closed. -/
theorem ysChain_cap (hTa : upsilon a ≤ T0) : ∀ c d, T0 < c → c < d → d < upsilon (a + ω * ω) →
    le2 c d → ∀ x, x0 < x → x ≤ d → ∀ g, d < g → ¬ le1 x g := by
  intro c d hTc hcd hd h2 x hxx hx g hg
  rcases chainA_sup hTa hd with hdT | ⟨j, hdj⟩
  · exact absurd (lt_of_lt_of_le (hTc.trans hcd) hdT) (lt_irrefl _)
  · obtain ⟨k, -, -, rfl⟩ := ysChain_pairs hctx (j + 1) c d hcd (hTc.trans hcd) hdj h2
    exact (hctx (k + 1)).T3 x hxx hx g hg


/-- Skeletal in the chain region. -/
theorem ysChain_sk (hTa : upsilon a ≤ T0) {α : Ordinal.{0}} (hTα : T0 < α)
    (hα : α < upsilon (a + ω * ω)) (hnu : ¬ UpsPt α) : ∀ γ, le1 α γ ↔ le1R α γ := by
  classical
  have hex : ∃ j, α ≤ topA a T0 j := by
    rcases chainA_sup hTa hα with hαT | ⟨j, hαj⟩
    · exact absurd hTα (not_lt.2 hαT)
    · exact ⟨j + 1, hαj⟩
  set j := Nat.find hex with hj
  have hαj : α ≤ topA a T0 j := Nat.find_spec hex
  rcases j with _ | j
  · exact absurd hTα (not_lt.2 hαj)
  have hTj : topA a T0 j < α := not_le.1 (Nat.find_min hex (show j < Nat.find hex by omega))
  have H := hctx j
  exact skel_block H.next.2.1 H.β1 hTj hαj hnu H.le1_lowβ

/-- The pair below `υ_{a+ω²}` above `T₀` is a chain pair. -/
theorem ysChain_pair (hTa : upsilon a ≤ T0) {c d : Ordinal.{0}} (hT0d : T0 < d)
    (hd : d < upsilon (a + ω * ω)) (hcd : c < d) (h2 : le2 c d) :
    ∃ k : ℕ, c = lpA a k ∧ d = topA a T0 (k + 1) := by
  rcases chainA_sup hTa hd with hdT | ⟨j, hdj⟩
  · exact absurd hT0d (not_lt.2 hdT)
  obtain ⟨k, -, rfl, rfl⟩ := ysChain_pairs hctx (j + 1) c d hcd hT0d hdj h2
  exact ⟨k, rfl, rfl⟩

end YsChain


end Googology.Trans.PoR.InaccPsi.R2.Ys
