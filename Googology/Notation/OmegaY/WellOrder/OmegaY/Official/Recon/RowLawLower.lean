/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawLower.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRun

set_option backward.do.legacy false

/-!
# The lower part of a new column

The lower part of `Official.copyColumn` processes the first items `L_{k,j}` (notes/03 §2.3):
the regions of level `k + 1` with base `slot (k + 2) τ j`, `j < τ_k`, for `k` from the top
down. Their bases form a chain of adjacent regions from `0` to `τ` (`lowerItems_chainTo`):
every row of a region bumps at `level - 1` to the base of the next region, and the rows of
the last region bump to `τ`.

`lower_flatten` joins the emitted lists of these items into one chain of bump steps, and
proves the seam with the upper part: the last emitted row `a'` and a row `b = bump a₀ e ≥ τ`,
where `a₀` is the highest row of the source column below `τ`, are a bump step. The last
nonempty item is the region of `a₀` (the column cannot jump over the base of the next
region), and `e` is at least the level of that region, so `bump a' e = bump a₀ e`.
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

/-! ## Chains of adjacent regions -/

/-- Every row of the region `p = (d, b)` bumps at `d - 1` to `γ`. -/
def EndsAt (γ : Row) (p : Nat × Row) : Prop :=
  ∀ r, inRegion p.1 p.2 r = true → Row.bump r (p.1 - 1) = γ

/-- The region `q` follows the region `p`. -/
def Adj (p q : Nat × Row) : Prop := EndsAt q.2 p

/-- A chain of adjacent regions from the base `β` to the row `γ`. -/
structure ChainTo (β γ : Row) (l : List (Nat × Row)) : Prop where
  nil : l = [] → β = γ
  head : ∀ p ∈ l.head?, p.2 = β
  chain : l.IsChain Adj
  last : ∀ p ∈ l.getLast?, EndsAt γ p

theorem ChainTo.append {β γ δ : Row} {l₁ l₂ : List (Nat × Row)} (h₁ : ChainTo β γ l₁)
    (h₂ : ChainTo γ δ l₂) : ChainTo β δ (l₁ ++ l₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨e1, e2⟩ := List.append_eq_nil_iff.mp h
    exact (h₁.nil e1).trans (h₂.nil e2)
  · intro p hp
    cases l₁ with
    | nil =>
      rw [h₁.nil rfl]
      exact h₂.head p (by simpa using hp)
    | cons a l =>
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      subst hp
      exact h₁.head a (by simp)
  · refine List.IsChain.append h₁.chain h₂.chain ?_
    intro x hx y hy
    have := h₁.last x hx
    show EndsAt y.2 x
    rw [h₂.head y hy]
    exact this
  · intro p hp
    cases l₂ with
    | nil =>
      rw [← h₂.nil rfl]
      simp only [List.append_nil] at hp
      exact h₁.last p hp
    | cons a l =>
      rw [List.getLast?_append_of_ne_nil _ (by simp)] at hp
      exact h₂.last p hp

theorem ChainTo.tail {β γ : Row} {p : Nat × Row} {l : List (Nat × Row)}
    (h : ChainTo β γ (p :: l)) : ChainTo (Row.bump p.2 (p.1 - 1)) γ l := by
  refine ⟨?_, ?_, h.chain.tail, ?_⟩
  · rintro rfl
    exact (h.last p (by simp)) p.2 (self_inRegion _ _)
  · intro q hq
    cases l with
    | nil => cases hq
    | cons a l =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      have hadj : Adj p a := (List.isChain_cons_cons.mp h.chain).1
      exact ((hadj p.2 (self_inRegion _ _))).symm
  · intro q hq
    cases l with
    | nil => cases hq
    | cons a l =>
      apply h.last q
      rw [List.getLast?_cons_cons]
      exact hq

theorem ChainTo.head_eq {β γ : Row} {p : Nat × Row} {l : List (Nat × Row)}
    (h : ChainTo β γ (p :: l)) : p.2 = β := h.head p (by simp)

theorem ChainTo.singleton {d : Nat} {b : Row} :
    ChainTo b (Row.bump b (d - 1)) [(d, b)] := by
  refine ⟨by simp, by simp, List.IsChain.singleton _, ?_⟩
  intro p hp
  simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hp
  subst hp
  intro r hr
  exact bump_of_inRegion hr

/-- The bases increase along a chain of adjacent regions. -/
theorem chainTo_base_le {β γ : Row} : ∀ {l : List (Nat × Row)}, ChainTo β γ l →
    ∀ p ∈ l, β ≤ p.2
  | [], _, p, hp => by cases hp
  | q :: l, h, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [h.head_eq]
    · have ih := chainTo_base_le h.tail p hp
      rw [← h.head_eq]
      exact (Row.lt_bump _ _).le.trans ih

/-! ## The first items form a chain of adjacent regions -/

/-- The regions `L_{k, j}`, `j < n`. -/
def group (τ : Row) (k n : Nat) : List (Nat × Row) :=
  (List.range n).map fun j => (k + 1, slot (k + 2) τ j)

theorem group_chainTo (τ : Row) (k : Nat) :
    ∀ n, ChainTo (slot (k + 2) τ 0) (slot (k + 2) τ n) (group τ k n)
  | 0 => ⟨fun _ => rfl, by simp [group], by simp [group], by simp [group]⟩
  | n + 1 => by
    have h := group_chainTo τ k n
    have hs : ChainTo (slot (k + 2) τ n) (slot (k + 2) τ (n + 1)) [(k + 1, slot (k + 2) τ n)] := by
      have := ChainTo.singleton (d := k + 1) (b := slot (k + 2) τ n)
      rw [show k + 1 - 1 = k by omega, bump_slot] at this
      exact this
    have := h.append hs
    unfold group
    rw [List.range_succ, List.map_append]
    exact this

theorem slot_top_coeff (τ : Row) (k : Nat) : slot (k + 2) τ (τ.coeff k) = slot (k + 1) τ 0 := by
  apply row_ext
  intro q
  rw [coeff_slot, coeff_slot]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem slot_one_zero (τ : Row) : slot 1 τ 0 = τ := by
  apply row_ext
  intro q
  rw [coeff_slot, if_neg (by omega), if_neg (by omega)]

/-- The regions `L_{k, j}` for `k < K`, from the top down. -/
def lowK (τ : Row) (K : Nat) : List (Nat × Row) :=
  (List.range K).reverse.flatMap fun k => group τ k (τ.coeff k)

theorem lowK_chainTo (τ : Row) : ∀ K, ChainTo (slot (K + 1) τ 0) τ (lowK τ K)
  | 0 => by
    rw [slot_one_zero]
    exact ⟨fun _ => rfl, by simp [lowK], by simp [lowK], by simp [lowK]⟩
  | K + 1 => by
    have hg := group_chainTo τ K (τ.coeff K)
    rw [slot_top_coeff] at hg
    have := hg.append (lowK_chainTo τ K)
    unfold lowK
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons]
    exact this

theorem lowerItems_map (τ : Row) :
    (lowerItems τ).map (fun p => (p.1, p.2.target)) = lowK τ (len τ) := by
  unfold lowerItems lowK group
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map]
  rfl

theorem lowerItems_chainTo (τ : Row) :
    ChainTo 0 τ ((lowerItems τ).map (fun p => (p.1, p.2.target))) := by
  rw [lowerItems_map]
  have := lowK_chainTo τ (len τ)
  rw [slot_top_zero] at this
  exact this

theorem mem_lowerItems {τ : Row} {p : Nat × Item} (hp : p ∈ lowerItems τ) :
    ∃ k j, k < len τ ∧ j < τ.coeff k ∧
      p = (k + 1, ⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩) := by
  unfold lowerItems at hp
  obtain ⟨k, hk, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact ⟨k, j, by simpa using hk, List.mem_range.mp hj, rfl⟩

/-! ## Joining the lists of the first items -/

/-- The facts on one first item used by `lower_flatten`. -/
structure LowerOK (ctx : Context) (τ : Row) (x : Nat × Row × List Emit) : Prop where
  good : Good x.1 x.2.1 x.2.2
  has : Has ctx x.1 x.2.1 ↔ x.2.2 ≠ []
  zero : ZeroBelow (x.1 - 1) x.2.1
  agree : ∀ q, x.1 - 1 < q → τ.coeff q = x.2.1.coeff q
  below : ∀ r, inRegion x.1 x.2.1 r = true → r < τ

/-- The highest row of the source column below `τ`. -/
structure TopBelow (ctx : Context) (τ a₀ : Row) : Prop where
  mem : ∃ p ∈ realNodes ctx.source ctx.x, official p.2.row = a₀
  lt : a₀ < τ
  max : ∀ p ∈ realNodes ctx.source ctx.x, official p.2.row < τ → official p.2.row ≤ a₀

theorem flatten_ne_nil_iff {Ls : List (List Emit)} : Ls.flatten ≠ [] ↔ ∃ L ∈ Ls, L ≠ [] := by
  rw [ne_eq, List.flatten_eq_nil_iff]
  push Not
  rfl

/-- **The lower part.** The emitted lists of a chain of adjacent regions join into a chain of
bump steps, and the last emitted row is a bump step below every `bump a₀ e ≥ τ`. -/
theorem lower_flatten {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {τ : Row} :
    ∀ (xs : List (Nat × Row × List Emit)) (β : Row),
      ChainTo β τ (xs.map fun x => (x.1, x.2.1)) → (∀ x ∈ xs, LowerOK ctx τ x) →
      EChain (xs.map fun x => x.2.2).flatten ∧
        (∀ a₀, TopBelow ctx τ a₀ → ∀ e, τ ≤ Row.bump a₀ e →
          ∀ em ∈ (xs.map fun x => x.2.2).flatten.getLast?, BumpStep em.row (Row.bump a₀ e))
  | [], _, _, _ => by simp [EChain]
  | x :: rest, β, hch, hok => by
    obtain ⟨d, b, L⟩ := x
    have hx := hok (d, b, L) List.mem_cons_self
    have hrest := fun y hy => hok y (List.mem_cons_of_mem _ hy)
    have hch' := ChainTo.tail (p := (d, b)) hch
    obtain ⟨ihc, ihs⟩ := lower_flatten hb rest _ hch' hrest
    simp only [List.map_cons, List.flatten_cons]
    -- if the rest emits something, its first list does
    have hfirst : (rest.map fun x => x.2.2).flatten ≠ [] →
        ∃ y rest', rest = y :: rest' ∧ y.2.2 ≠ [] := by
      intro hne
      obtain ⟨L', hL', hne'⟩ := flatten_ne_nil_iff.mp hne
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hL'
      cases rest with
      | nil => cases hz
      | cons y rest' =>
        refine ⟨y, rest', rfl, ?_⟩
        have hz' := hok z (List.mem_cons_of_mem _ hz)
        obtain ⟨p, hp, hin⟩ := hz'.has.mpr hne'
        have hy := hok y (List.mem_cons_of_mem _ List.mem_cons_self)
        -- the base of `y` is at most the base of `z`
        have hby : y.2.1 = Row.bump b (d - 1) := by
          have := hch'.head_eq (p := (y.1, y.2.1)) (l := rest'.map fun x => (x.1, x.2.1))
          simpa using this
        have hle : y.2.1 ≤ z.2.1 := by
          rcases List.mem_cons.mp hz with rfl | hz2
          · exact le_rfl
          · -- bases increase along the chain
            have hchy : ChainTo y.2.1 τ ((y :: rest').map fun x => (x.1, x.2.1)) := by
              rw [← hby] at hch'
              exact hch'
            exact chainTo_base_le hchy (z.1, z.2.1) (List.mem_map.mpr ⟨z, List.mem_cons_of_mem _ hz2, rfl⟩)
        have hzle : z.2.1 ≤ official p.2.row := base_le_of_inRegion hz'.zero hin
        obtain ⟨p', hp', hrow⟩ := node_of_between hb hy.zero hy.agree hp (hle.trans hzle)
          (hz'.below _ hin)
        exact hy.has.mp ⟨p', hp', by rw [hrow]; exact self_inRegion _ _⟩
    refine ⟨?_, ?_⟩
    · refine List.IsChain.append hx.good.1 ihc ?_
      intro a ha c hc
      obtain ⟨y, rest', rfl, hyne⟩ := hfirst (by
        intro h; rw [h] at hc; cases hc)
      have hby : y.2.1 = Row.bump b (d - 1) := by
        have := hch'.head_eq (p := (y.1, y.2.1)) (l := rest'.map fun x => (x.1, x.2.1))
        simpa using this
      have hy := hok y (List.mem_cons_of_mem _ List.mem_cons_self)
      -- the head of the rest is the base of `y`
      have hc' : c ∈ y.2.2.head? := by
        simp only [List.map_cons, List.flatten_cons] at hc
        cases hy2 : y.2.2 with
        | nil => exact absurd hy2 hyne
        | cons c0 l0 =>
          rw [hy2, List.cons_append, List.head?_cons] at hc
          rw [List.head?_cons]
          exact hc
      have hcrow := hy.good.2.2 c hc'
      have hain := hx.good.2.1 a (List.mem_of_getLast? ha)
      refine ⟨d - 1, ?_⟩
      rw [hcrow, hby]
      exact (bump_of_inRegion hain).symm
    · intro a₀ htop e hτe em hem
      by_cases hre : (rest.map fun x => x.2.2).flatten = []
      · rw [hre, List.append_nil] at hem
        -- the last emitted row is in the region `(d, b)`, and so is `a₀`
        have hLne : L ≠ [] := by intro h; rw [h] at hem; cases hem
        have hemin := hx.good.2.1 em (List.mem_of_getLast? hem)
        obtain ⟨p, hp, hin⟩ := hx.has.mpr hLne
        have hple : official p.2.row ≤ a₀ := htop.max p hp (hx.below _ hin)
        have hba : b ≤ a₀ := (base_le_of_inRegion hx.zero hin).trans hple
        have ha₀in : inRegion d b a₀ = true := by
          by_contra hn
          have hge : Row.bump b (d - 1) ≤ a₀ := by
            by_contra hlt
            exact hn (inRegion_of_between hba (lt_of_not_ge hlt))
          cases rest with
          | nil =>
            have := hch.last (d, b) (by simp)
            rw [this b (self_inRegion _ _)] at hge
            exact absurd htop.lt (not_lt.mpr hge)
          | cons y rest' =>
            have hby : y.2.1 = Row.bump b (d - 1) := by
              have := hch'.head_eq (p := (y.1, y.2.1)) (l := rest'.map fun x => (x.1, x.2.1))
              simpa using this
            have hy := hok y (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain ⟨q, hq, hqrow⟩ := htop.mem
            obtain ⟨p', hp', hrow⟩ := node_of_between hb hy.zero hy.agree hq
              (by rw [hqrow, hby]; exact hge) (by rw [hqrow]; exact htop.lt)
            have hyne := hy.has.mp ⟨p', hp', by rw [hrow]; exact self_inRegion _ _⟩
            apply hyne
            simp only [List.map_cons, List.flatten_cons] at hre
            exact (List.append_eq_nil_iff.mp hre).1
        -- the bump exponent is at least `d - 1`
        have hed : d - 1 ≤ e := by
          by_contra hlt
          have hin' : inRegion d b (Row.bump a₀ e) = true := by
            rw [inRegion_iff'] at ha₀in ⊢
            intro k hk
            rw [bump_coeff_high (by omega)]
            exact ha₀in k hk
          exact absurd (hx.below _ hin') (not_lt.mpr hτe)
        refine ⟨e, ?_⟩
        apply Row.bump_eq_of_jump_le
        rw [Row.jump_le_iff]
        intro k hk
        rw [inRegion_iff'.mp hemin k (by omega), inRegion_iff'.mp ha₀in k (by omega)]
      · rw [List.getLast?_append_of_ne_nil _ hre] at hem
        exact ihs a₀ htop e hτe em hem

end OmegaY.Official.Recon.RowLaw
