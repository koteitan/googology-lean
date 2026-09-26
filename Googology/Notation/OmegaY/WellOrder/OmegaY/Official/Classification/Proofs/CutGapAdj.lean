/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapAdj.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapPairStep
import Mathlib.Data.List.Chain

set_option backward.do.legacy false

/-!
# Consecutive emits of a column (`CutGap`), and `CutBump`

`emitsT_adj`: in a copied column of a block `i ≥ 1`, two consecutive emits `p`, `q` with `q`
not a gap copy and different origin rows `σ_p ≠ σ_q` satisfy
`jump(row p, row q) ≤ jump(σ_p, σ_q)` (`AdjR`).

## The argument

By induction over the items. Inside one child the induction hypothesis applies. For the last
emit `p` of a child `a` and the first emit `q` of a later child `b` of an item of level `d + 2`:
both rows lie in the target region, so `jump(row p, row q) ≤ d + 1`. If the two children have
different source slots, `σ_p` and `σ_q` differ at the coefficient `d`, so
`jump(σ_p, σ_q) = d + 1`. Two different children with the same source slot (the slot `h_ρ` of
the root top `ρ`) never have a non-cut first emit after a nonempty earlier child
(`sameSlot_head_cut`):

* a later child that copies the root row with `b = 1` emits only gap copies (`runItemT_ibCut`);
* the other later child skips the bottom of its region; the earlier child copies `row ρ`, so
  the column has a node at `row ρ` (`clean_node`), and then an item that skips the bottom of its
  region starts with a gap copy of `row ρ` (`runItemT_cbFirst`).

For the first items and the upper part the regions of the two rows are the regions of the two
origin rows, and the jumps are equal (`jump_congr_high`).

`cutBump`: the open statement `CutBump` of `CutPartsTop.lean` is the case `p` a gap copy and
`q` the non-cut copy of the node above its origin. **Proved without any hypothesis.**
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-! ## Rows -/

theorem jump_le_of_region {d : Nat} {T r r' : Row} (h : inRegion (d + 2) T r = true)
    (h' : inRegion (d + 2) T r' = true) : Row.jump r r' ≤ d + 1 := by
  rw [Row.jump_le_iff]
  intro e he
  rw [Recon.RowLaw.inRegion_iff'.mp h e (by omega), Recon.RowLaw.inRegion_iff'.mp h' e (by omega)]

theorem jump_ge_of_ne {a b : Row} {e : Nat} (h : a.coeff e ≠ b.coeff e) : e + 1 ≤ Row.jump a b := by
  by_contra hn
  have : Row.jump a b ≤ e := by omega
  exact h (Row.coeff_eq_of_jump_le this le_rfl)

/-- Rows that agree at and above `m` in pairs have the same jump, if they differ at or above
`m`. -/
theorem jump_congr_high {m : Nat} {r1 r2 r3 r4 : Row} (h12 : ∀ e, m ≤ e → r1.coeff e = r2.coeff e)
    (h34 : ∀ e, m ≤ e → r3.coeff e = r4.coeff e) {e0 : Nat} (he0 : m ≤ e0)
    (hd : r1.coeff e0 ≠ r3.coeff e0) : Row.jump r1 r3 = Row.jump r2 r4 := by
  have h1 := jump_ge_of_ne hd
  have hd' : r2.coeff e0 ≠ r4.coeff e0 := by rw [← h12 e0 he0, ← h34 e0 he0]; exact hd
  have h2 := jump_ge_of_ne hd'
  apply Nat.le_antisymm
  · rw [Row.jump_le_iff]
    intro e he
    have hm : m ≤ e := by omega
    show r1.coeff e = r3.coeff e
    rw [h12 e hm, h34 e hm]
    exact Row.coeff_eq_of_jump_le le_rfl he
  · rw [Row.jump_le_iff]
    intro e he
    have hm : m ≤ e := by omega
    show r2.coeff e = r4.coeff e
    rw [← h12 e hm, ← h34 e hm]
    exact Row.coeff_eq_of_jump_le le_rfl he

/-! ## Lists -/

theorem head?_flatten_mem {α : Type} :
    ∀ {L : List (List α)} {y : α}, y ∈ L.flatten.head? → ∃ b, ∃ hb : b < L.length, y ∈ L[b].head?
  | [], y, h => by simp at h
  | l :: L, y, h => by
      rw [List.flatten_cons, List.head?_append] at h
      cases hl : l with
      | nil =>
          rw [hl] at h
          simp only [List.head?_nil, Option.none_or] at h
          obtain ⟨b, hb, hy⟩ := head?_flatten_mem h
          exact ⟨b + 1, by simp; omega, by simpa using hy⟩
      | cons a l' =>
          rw [hl] at h
          simp only [List.head?_cons, Option.some_or] at h
          exact ⟨0, by simp, by simp [hl]; simpa using h⟩

theorem isChain_flatten {α : Type} {R : α → α → Prop} :
    ∀ (L : List (List α)), (∀ l ∈ L, List.IsChain R l) →
      (∀ a b (ha : a < L.length) (hb : b < L.length), a < b →
        ∀ x ∈ L[a].getLast?, ∀ y ∈ L[b].head?, R x y) → List.IsChain R L.flatten
  | [], _, _ => by simp
  | l :: L, hin, hac => by
      rw [List.flatten_cons, List.isChain_append]
      refine ⟨hin l (by simp), isChain_flatten L (fun l' hl' => hin l' (by simp [hl']))
        (fun a b ha hb hab x hx y hy => hac (a + 1) (b + 1) (by simp; omega) (by simp; omega)
          (by omega) x (by simpa using hx) y (by simpa using hy)), ?_⟩
      intro x hx y hy
      obtain ⟨b, hb, hyb⟩ := head?_flatten_mem hy
      exact hac 0 (b + 1) (by simp) (by simp; omega) (by omega) x (by simpa using hx) y
        (by simpa using hyb)

theorem filter_ge_range (h n : Nat) (hh : h ≤ n) :
    (List.range n).filter (fun j => decide (h ≤ j)) = List.range' h (n - h) := by
  rw [List.range_eq_range']
  obtain ⟨m, rfl⟩ : ∃ m, n = h + m := ⟨n - h, by omega⟩
  rw [show h + m - h = m by omega, ← List.range'_append_1, Nat.zero_add, List.filter_append]
  have h1 : (List.range' 0 h).filter (fun j => decide (h ≤ j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp [List.mem_range'_1] at ha
    simp; omega
  have h2 : (List.range' h m).filter (fun j => decide (h ≤ j)) = List.range' h m := by
    apply List.filter_eq_self.mpr
    intro a ha
    simp [List.mem_range'_1] at ha
    simp; omega
  rw [h1, h2, List.nil_append]

/-! ## Children lists with a known length -/

/-- The children of an item that skips the bottom of its region: there are at least
`h_top + 1` indices before filtering. -/
theorem childItems_cb_len {ctx : Context} {R : Mountain} {B d : Nat} {it : Item} {cs : List Item}
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx d it = .ok cs) (hcl : it.clean = none) (hcb : it.cutBottom = true)
    {aR : Ref} {aC : Cell} (htop : topIn ctx.source ctx.x d it.source = some (aR, aC)) :
    ∃ n, cs = kidList ctx.source ctx.rootColumn ctx.lastColumn ctx.block R B d it true n ∧
      height d (official aC.row) + 1 ≤ n := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure, hbnd, htop, hcl, hcb, Option.isSome_none,
    Bool.false_eq_true, or_true, not_true_eq_false, ite_false, ↓reduceIte] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hvt
      have hv1 : v = true := by simpa using hvt
      subst hv1
      obtain rfl := Except.ok.inj h
      refine ⟨?n, ?eq, ?le⟩
      case eq =>
        simp only [kidList, hcl, hcb, not_true_eq_false, ite_false, ↓reduceIte]
        rfl
      case le => split <;> omega

/-- The children of a gap-copy item with offset `0` in a block `i ≥ 1`: at least one. -/
theorem childItems_ib_len {ctx : Context} {R : Mountain} {B d : Nat} {it : Item} {cs : List Item}
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx d it = .ok cs) {C : Row} (hcl : it.clean = some C)
    (hcb : it.cutBottom = true) (ho : it.offset = 0) (hi : ctx.block ≠ 0)
    {aR : Ref} {aC : Cell} (htop : topIn ctx.source ctx.x d it.source = some (aR, aC)) :
    ∃ n, cs = kidList ctx.source ctx.rootColumn ctx.lastColumn ctx.block R B d it true n ∧
      1 ≤ n := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure, hbnd, htop, hcl, hcb,
    Option.isSome_some, true_or, not_true_eq_false, ite_false, ↓reduceIte, if_neg hi,
    false_and] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hvt
      have hv1 : v = true := by simpa using hvt
      subst hv1
      split at h
      · cases h
      · rename_i q hq
        split at h
        · cases h
        · rename_i g hg
          obtain rfl := Except.ok.inj h
          refine ⟨?n, ?eq, ?le⟩
          case eq =>
            simp only [kidList, hcl, not_true_eq_false, ite_false, ↓reduceIte]
            congr 1
            · funext j
              simp only [kidC4, hcb, ↓reduceIte, hRootOf]
            · rfl
          case le => rw [ho]; omega

/-! ## Nonempty items and their first emits -/

theorem flatten_head?_of_ne {α : Type} {L : List (List α)} (h0 : 0 < L.length)
    (hne : L[0] ≠ []) : L.flatten.head? = L[0].head? := by
  cases L with
  | nil => simp at h0
  | cons l L =>
      simp only [List.flatten_cons, List.head?_append, List.getElem_cons_zero]
      cases l with
      | nil => simp at hne
      | cons a l' => simp

theorem flatten_ne_nil_of {α : Type} {L : List (List α)} (h0 : 0 < L.length) (hne : L[0] ≠ []) :
    L.flatten ≠ [] := by
  cases L with
  | nil => simp at h0
  | cons l L =>
      simp only [List.flatten_cons, List.getElem_cons_zero] at hne ⊢
      intro h
      exact hne (List.append_eq_nil_iff.mp h).1

/-- A clean item that emits something has a node of the column at its copied row. -/
theorem runItemT_clean_node (ctx : Context) {C : Row} :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      it.clean = some C → ps ≠ [] → ∃ q, nodeAt ctx.source ctx.x C = some q
  | 0, it, ps, h, hcl, hne => by
      have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      unfold levelOneT at h'
      cases hsrc : nodeAt ctx.source ctx.x it.source with
      | none => simp [hsrc, pure, Except.pure] at h'; subst h'; exact absurd rfl hne
      | some q =>
          simp only [hsrc, hcl] at h'
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h'
          | some q' => exact ⟨q', rfl⟩
  | d + 1, it, ps, h, hcl, hne => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          unfold childItems at hch
          simp only [bind, Except.bind, pure, Except.pure, hcl, Option.isSome_some, true_or,
            not_true_eq_false, ite_false, ↓reduceIte] at hch
          split at hch
          · obtain rfl := Except.ok.inj hch
            simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at houts
            subst houts
            exact absurd (by simp) hne
          · split at hch
            · cases hch
            · rename_i v hv
              split at hch
              · simp [throw, throwThe, MonadExceptOf.throw] at hch
              · split at hch
                · cases hch
                · rename_i q hq
                  exact ⟨_, hq⟩

/-- **A gap-copy item with offset `0` whose source contains its copied row `C`, in a column
with a node at `C`, emits something** (block `i ≥ 1`). -/
theorem runItemT_ib_ne (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T) (hi : ctx.block ≠ 0)
    {C : Row} :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      it.clean = some C → it.cutBottom = true → it.offset = 0 →
      inRegion (d + 1) it.source C = true → (∃ q, nodeAt ctx.source ctx.x C = some q) →
      ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it → ps ≠ []
  | 0, it, ps, h, hcl, hcb, ho, hin, ⟨q, hq⟩, _ => by
      have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      have hsrcC : it.source = C := by
        ext k
        exact ((Recon.RowLaw.inRegion_iff'.mp hin k (by omega))).symm
      unfold levelOneT at h'
      rw [hsrcC, hq] at h'
      simp only [hcl, hq, bind, Except.bind, pure, Except.pure] at h'
      split at h'
      · cases h'
      · cases h'
        simp
  | d + 1, it, ps, h, hcl, hcb, ho, hin, hnode, hinv => by
      obtain ⟨q, hq⟩ := hnode
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      rename_i children hch
      split at h
      · cases h
      rename_i outs houts
      cases h
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
      obtain ⟨hqcol, hq1, hqcell, hqrow⟩ := Classification.nodeAt_spec hq
      have htop := topIn_ne_none_of_node hqcol hq1 hqcell (by rw [hqrow]; exact hin)
      obtain ⟨⟨aR, aC⟩, htop'⟩ := Option.ne_none_iff_exists'.mp htop
      obtain ⟨n, hkid, hn⟩ := childItems_ib_len hbnd hch hcl hcb ho hi htop'
      have h0 : 0 < children.length := by subst hkid; simp [kidList, hcl]; omega
      have h0' : 0 < outs.length := by omega
      obtain ⟨hinvc, _, _⟩ := ChainCorr.Inner.childItems_order hch hinv
      have hrun0 := hall 0 h0 h0'
      have hIc := hinvc _ (List.getElem_mem h0)
      -- the first child
      obtain ⟨r, ρc, hρ, hρrow⟩ := hinv C hcl
      have hhR : heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) =
          C.coeff d := by
        rw [hρ, ← hρrow]; simp [heightOf, Recon.RowLaw.height_eq]
      have hc0 : children[0] = ⟨slot (d + 2) it.source (C.coeff d), slot (d + 2) it.target 0,
          some C, 0, true⟩ := by
        subst hkid
        simp only [kidList, hcl, not_true_eq_false, ite_false, ↓reduceIte, List.getElem_map,
          List.getElem_range, kidC4, hcb, hRootOf, hhR, ho]
        try simp
      rw [hc0] at hrun0 hIc
      have hne0 := runItemT_ib_ne ctx R B hbnd hi d _ _ hrun0 rfl rfl rfl
        (Recon.RowLaw.inRegion_slot_iff.mpr ⟨hin, rfl⟩) ⟨q, hq⟩ hIc
      exact flatten_ne_nil_of h0' hne0

/-- **An item that skips the bottom of its region, in a column with a node at the row of the
root top `ρ`, starts with a gap copy** (block `i ≥ 1`). -/
theorem runItemT_cbFirst (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hV : MountainValid ctx.source) (hi : ctx.block ≠ 0) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 2) it = .ok ps →
      it.clean = none → it.cutBottom = true → ∀ ρr ρc,
      topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      (∃ q, nodeAt ctx.source ctx.x (official ρc.row) = some q) →
      ps ≠ [] ∧ ∀ y ∈ ps.head?, ChainCorr.cutOrigin y.2 = true := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro it ps h hcl hcb ρr ρc hρ ⟨q, hq⟩
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i children hch
  split at h
  · cases h
  rename_i outs houts
  cases h
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  obtain ⟨hqcol, hq1, hqcell, hqrow⟩ := Classification.nodeAt_spec hq
  have hρin := topIn_inRegion hρ
  have htop := topIn_ne_none_of_node hqcol hq1 hqcell (by rw [hqrow]; exact hρin)
  obtain ⟨⟨aR, aC⟩, htop'⟩ := Option.ne_none_iff_exists'.mp htop
  obtain ⟨n, hkid, hn⟩ := childItems_cb_len hbnd hch hcl hcb htop'
  have hhR : hRootOf ctx.source ctx.rootColumn (d + 2) it = (official ρc.row).coeff d := by
    simp [hRootOf, hρ, heightOf, Recon.RowLaw.height_eq]
  -- the top of the column is at or above `row ρ`
  have hle := le_top_of_node hV hqcol hq1 hqcell (by rw [hqrow]; exact hρin) htop'
  rw [hqrow] at hle
  have hRtop : (official ρc.row).coeff d ≤ height (d + 2) (official aC.row) := by
    rw [Recon.RowLaw.height_eq]
    exact Recon.RowLaw.coeff_le_of_inRegion hρin (topIn_inRegion htop') hle
  have hRn : (official ρc.row).coeff d ≤ n := by omega
  have hfil := filter_ge_range _ n hRn
  have hkid' : children = (List.range' ((official ρc.row).coeff d)
      (n - (official ρc.row).coeff d)).map (kidC3 ctx.source ctx.rootColumn R B (d + 2) it) := by
    rw [hkid]
    simp only [kidList, hcl, hcb, not_true_eq_false, ite_false, ↓reduceIte, hhR]
    rw [← hfil]
  have h0 : 0 < children.length := by
    rw [hkid', List.length_map, List.length_range']; omega
  have h0' : 0 < outs.length := by omega
  have hrun0 := hall 0 h0 h0'
  have hc0 : children[0] = kidC3 ctx.source ctx.rootColumn R B (d + 2) it
      ((official ρc.row).coeff d) := by
    simp only [hkid', List.getElem_map, List.getElem_range']
    try simp
  rw [hc0] at hrun0
  unfold kidC3 at hrun0
  have hhR' : heightOf (d + 2) (some (ρr, ρc)) = (official ρc.row).coeff d := by
    simp [heightOf, Recon.RowLaw.height_eq]
  simp only [hRootOf, rhoRowOf, hρ, hhR'] at hrun0
  generalize heightOf (d + 2) (topIn R B (d + 2) it.target) = hB at hrun0
  have he : ((if d + 2 = 2 then 1 else 0 : Int) = 1 ∧ d = 0) ∨
      ((if d + 2 = 2 then 1 else 0 : Int) = 0 ∧ 1 ≤ d) := by
    by_cases hd : d = 0
    · left; simp [hd]
    · right; simp [hd]; omega
  generalize (if d + 2 = 2 then 1 else 0 : Int) = e at hrun0 he
  have hne0 : outs[0] ≠ [] ∧ ∀ y ∈ outs[0].head?, ChainCorr.cutOrigin y.2 = true := by
    split_ifs at hrun0 with h1
    · -- a gap copy of `row ρ` first
      have hne := runItemT_ib_ne ctx R B hbnd hi d _ _ hrun0 rfl rfl rfl
        (Recon.RowLaw.inRegion_slot_iff.mpr ⟨hρin, rfl⟩) ⟨q, hq⟩
        (fun C hC => ⟨ρr, ρc, ChainCorr.Inner.topIn_slot hρ, (Option.some.inj hC).symm ▸ rfl⟩)
      refine ⟨hne, fun y hy => runItemT_ibCut ctx R B hbnd d _ _ hrun0 rfl rfl y
        (List.mem_of_mem_head? hy)⟩
    · -- no gap copy before: the item skips the bottom of its region again
      have hB0 : hB = 0 := by rcases he with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      have hd : 1 ≤ d := by rcases he with ⟨_, _⟩ | ⟨_, h⟩ <;> omega
      subst hB0
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.sub_zero, Nat.sub_self, Nat.zero_add, decide_true] at hrun0
      exact ih d' (by omega) _ _ hrun0 rfl rfl ρr ρc (ChainCorr.Inner.topIn_slot hρ) ⟨q, hq⟩
  refine ⟨flatten_ne_nil_of h0' hne0.1, ?_⟩
  rw [flatten_head?_of_ne h0' hne0.1]
  exact hne0.2

/-! ## The children, case by case -/

theorem slot_idx {d : Nat} {S r : Row} {j : Nat} (h : inRegion (d + 1) (slot (d + 2) S j) r = true) :
    r.coeff d = j := (Recon.RowLaw.inRegion_slot_iff.mp h).2

theorem kidC2_cases (M : Mountain) (cr x0 i d : Nat) (it : Item) (j : Nat) :
    (j < hRootOf M cr d it ∧ kidC2 M cr x0 i d it j = kidC1 d it j) ∨
    (hRootOf M cr d it ≤ j ∧
      (j : Int) < hRootOf M cr d it + liftOf M cr x0 i d it + (if d = 2 then 1 else 0) ∧
      kidC2 M cr x0 i d it j = ⟨slot d it.source (hRootOf M cr d it), slot d it.target j,
        some (rhoRowOf M cr d it), 0, decide (hRootOf M cr d it < j)⟩) ∨
    (hRootOf M cr d it ≤ j ∧
      ¬ (j : Int) < hRootOf M cr d it + liftOf M cr x0 i d it + (if d = 2 then 1 else 0) ∧
      kidC2 M cr x0 i d it j = ⟨slot d it.source ((j : Int) - liftOf M cr x0 i d it).toNat,
        slot d it.target j, none, 0,
        decide (i ≠ 0 ∧ (j : Int) = hRootOf M cr d it + liftOf M cr x0 i d it)⟩) := by
  unfold kidC2
  by_cases h1 : j < hRootOf M cr d it
  · left; exact ⟨h1, by rw [if_pos h1]⟩
  · right
    by_cases h2 : (j : Int) < hRootOf M cr d it + liftOf M cr x0 i d it + (if d = 2 then 1 else 0)
    · left; exact ⟨by omega, h2, by rw [if_neg h1, if_pos h2]⟩
    · right; exact ⟨by omega, h2, by rw [if_neg h1, if_neg h2]⟩

theorem kidC3_cases (M : Mountain) (cr : Nat) (R : Mountain) (B d : Nat) (it : Item) (j : Nat) :
    ((j : Int) < (heightOf d (topIn R B d it.target) : Int) + (hRootOf M cr d it : Int) +
        (if d = 2 then 1 else 0) ∧
      kidC3 M cr R B d it j = ⟨slot d it.source (hRootOf M cr d it),
        slot d it.target (j - hRootOf M cr d it), some (rhoRowOf M cr d it), 0, true⟩) ∨
    (¬ (j : Int) < (heightOf d (topIn R B d it.target) : Int) + (hRootOf M cr d it : Int) +
        (if d = 2 then 1 else 0) ∧
      kidC3 M cr R B d it j = ⟨slot d it.source (j - heightOf d (topIn R B d it.target)),
        slot d it.target (j - hRootOf M cr d it), none, 0,
        decide (j = heightOf d (topIn R B d it.target) + hRootOf M cr d it)⟩) := by
  unfold kidC3
  by_cases h1 : (j : Int) < (heightOf d (topIn R B d it.target) : Int) + (hRootOf M cr d it : Int) +
      (if d = 2 then 1 else 0)
  · left; exact ⟨h1, by rw [if_pos h1]⟩
  · right; exact ⟨h1, by rw [if_neg h1]⟩

theorem kid_three {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item} {n j : Nat}
    (hcl : it.clean = none) (hcb : it.cutBottom = true)
    (hj : j < (kidList M cr x0 i R B d it true n).length) :
    (kidList M cr x0 i R B d it true n)[j] = kidC3 M cr R B d it (hRootOf M cr d it + j) := by
  have hform : kidList M cr x0 i R B d it true n =
      ((List.range n).filter (fun j => decide (hRootOf M cr d it ≤ j))).map
        (kidC3 M cr R B d it) := by
    simp only [kidList, hcl, hcb, not_true_eq_false, ite_false, ↓reduceIte]
  by_cases hn : hRootOf M cr d it ≤ n
  · have hL : kidList M cr x0 i R B d it true n =
        (List.range' (hRootOf M cr d it) (n - hRootOf M cr d it)).map (kidC3 M cr R B d it) := by
      rw [hform, filter_ge_range _ n hn]
    simp only [hL, List.getElem_map, List.getElem_range']
    try simp
  · exfalso
    have : (List.range n).filter (fun j => decide (hRootOf M cr d it ≤ j)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp at ha
      simp; omega
    rw [hform, this] at hj
    simp at hj

/-! ## The same source slot -/

/-- **Two different children with the same source slot**: after a nonempty child, a later
child with the same source slot starts with a gap copy. -/
theorem sameSlot_head_cut (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hV : MountainValid ctx.source) (hi : ctx.block ≠ 0) {d : Nat} {it : Item}
    {children : List Item} {outs : List (List (Emit × Origin))}
    (hch : childItems ctx (d + 2) it = .ok children) {a b : Nat} (ha : a < children.length)
    (hb : b < children.length) (hab : a < b) (hoa : a < outs.length) (hob : b < outs.length)
    (hruna : runItemT ctx (d + 1) children[a] = .ok outs[a])
    (hrunb : runItemT ctx (d + 1) children[b] = .ok outs[b])
    {x y : Emit × Origin} (hx : x ∈ outs[a]) (hy : y ∈ outs[b].head?)
    (hxO : ChainCorr.Inner.EmitOK ctx.source ctx.rootColumn (d + 1) children[a] x)
    (hyO : ChainCorr.Inner.EmitOK ctx.source ctx.rootColumn (d + 1) children[b] y)
    {c c' : Cell} (hc : cell? ctx.source x.2.src = some c) (hc' : cell? ctx.source y.2.src = some c')
    (heqc : (official c.row).coeff d = (official c'.row).coeff d) :
    ChainCorr.cutOrigin y.2 = true := by
  have hxne : outs[a] ≠ [] := List.ne_nil_of_mem hx
  have hymem := List.mem_of_mem_head? hy
  have ibCut_b : children[b].clean.isSome = true → children[b].cutBottom = true →
      ChainCorr.cutOrigin y.2 = true :=
    fun h1 h2 => runItemT_ibCut ctx R B hbnd d _ _ hrunb h1 h2 y hymem
  rcases childItems_kid hbnd hch with hnil | ⟨asc, n, hasc, hkid, hasc'⟩
  · subst hnil; simp at ha
  subst hkid
  cases asc with
  | false =>
      exfalso
      rw [kid_false ha] at hxO
      rw [kid_false hb] at hyO
      have ea := slot_idx (emitOK_reg hxO hc)
      have eb := slot_idx (emitOK_reg hyO hc')
      omega
  | true =>
      obtain ⟨ρr, ρc, hρ⟩ := rho_of_asc hasc
      have hhR := hRoot_eq (it := it) hρ
      have hrr := rhoRow_eq (it := it) hρ
      have he : ((if d + 2 = 2 then 1 else 0 : Int) = 1 ∧ d = 0) ∨
          ((if d + 2 = 2 then 1 else 0 : Int) = 0 ∧ 1 ≤ d) := by
        by_cases hd : d = 0
        · left; simp [hd]
        · right; simp [hd]; omega
      cases hcl : it.clean with
      | none =>
          cases hcb : it.cutBottom with
          | false =>
              rw [kid_two hcl hcb ha] at hxO hruna
              rw [kid_two hcl hcb hb] at hyO hrunb ibCut_b
              rcases kidC2_cases ctx.source ctx.rootColumn ctx.lastColumn ctx.block (d + 2) it a
                with ⟨ha1, hka⟩ | ⟨ha1, ha2, hka⟩ | ⟨ha1, ha2, hka⟩ <;>
              rcases kidC2_cases ctx.source ctx.rootColumn ctx.lastColumn ctx.block (d + 2) it b
                with ⟨hb1, hkb⟩ | ⟨hb1, hb2, hkb⟩ | ⟨hb1, hb2, hkb⟩ <;>
              rw [hka] at hxO hruna <;> rw [hkb] at hyO hrunb ibCut_b <;>
              have ea := slot_idx (emitOK_reg hxO hc) <;> have eb := slot_idx (emitOK_reg hyO hc') <;>
              rcases he with ⟨he1, hd0⟩ | ⟨he1, hd1⟩ <;>
              first
                | (exfalso; omega)
                | (exact ibCut_b rfl (by simp; omega))
                | skip
              -- the remaining case: `b` skips the bottom of the slot of `ρ`, `a` copies `row ρ`
              all_goals
                have hbL : (b : Int) = (hRootOf ctx.source ctx.rootColumn (d + 2) it : Int) +
                    liftOf ctx.source ctx.rootColumn ctx.lastColumn ctx.block (d + 2) it := by omega
                have hs : ((b : Int) - liftOf ctx.source ctx.rootColumn ctx.lastColumn ctx.block
                    (d + 2) it).toNat = (official ρc.row).coeff d := by omega
                have hcbb : decide (ctx.block ≠ 0 ∧ (b : Int) =
                    (hRootOf ctx.source ctx.rootColumn (d + 2) it : Int) +
                      liftOf ctx.source ctx.rootColumn ctx.lastColumn ctx.block (d + 2) it) = true := by
                  simp only [decide_eq_true_eq]; exact ⟨hi, hbL⟩
                rw [hcbb] at hrunb
                rw [hrr] at hruna
                obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
                have hnode := runItemT_clean_node ctx (d' + 1) _ _ hruna rfl hxne
                exact (runItemT_cbFirst ctx R B hbnd hV hi d' _ _ hrunb rfl rfl ρr ρc
                  (by rw [hs]; exact ChainCorr.Inner.topIn_slot hρ) hnode).2 y hy
          | true =>
              rw [kid_three hcl hcb ha] at hxO hruna
              rw [kid_three hcl hcb hb] at hyO hrunb ibCut_b
              rcases kidC3_cases ctx.source ctx.rootColumn R B (d + 2) it (hRootOf ctx.source
                  ctx.rootColumn (d + 2) it + a) with ⟨ha1, hka⟩ | ⟨ha1, hka⟩ <;>
              rcases kidC3_cases ctx.source ctx.rootColumn R B (d + 2) it (hRootOf ctx.source
                  ctx.rootColumn (d + 2) it + b) with ⟨hb1, hkb⟩ | ⟨hb1, hkb⟩ <;>
              rw [hka] at hxO hruna <;> rw [hkb] at hyO hrunb ibCut_b <;>
              have ea := slot_idx (emitOK_reg hxO hc) <;> have eb := slot_idx (emitOK_reg hyO hc') <;>
              rcases he with ⟨he1, hd0⟩ | ⟨he1, hd1⟩ <;>
              first
                | (exfalso; omega)
                | (exact ibCut_b rfl rfl)
                | skip
              all_goals
                have hs : hRootOf ctx.source ctx.rootColumn (d + 2) it + b -
                    heightOf (d + 2) (topIn R B (d + 2) it.target) = (official ρc.row).coeff d := by
                  omega
                have hcbb : decide (hRootOf ctx.source ctx.rootColumn (d + 2) it + b =
                    heightOf (d + 2) (topIn R B (d + 2) it.target) +
                      hRootOf ctx.source ctx.rootColumn (d + 2) it) = true := by
                  simp only [decide_eq_true_eq]; omega
                rw [hcbb] at hrunb
                rw [hrr] at hruna
                obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
                have hnode := runItemT_clean_node ctx (d' + 1) _ _ hruna rfl hxne
                exact (runItemT_cbFirst ctx R B hbnd hV hi d' _ _ hrunb rfl rfl ρr ρc
                  (by rw [hs]; exact ChainCorr.Inner.topIn_slot hρ) hnode).2 y hy
      | some C =>
          rw [kid_four hcl ha] at hxO hruna
          rw [kid_four hcl hb] at hyO hrunb ibCut_b
          unfold kidC4 at hxO hruna hyO hrunb ibCut_b
          cases hcb : it.cutBottom with
          | true =>
              simp only [hcb, ↓reduceIte] at ibCut_b
              exact ibCut_b (by simp) (by simp)
          | false =>
              simp only [hcb, Bool.false_eq_true, ↓reduceIte] at hxO hyO ibCut_b
              by_cases hb1 : b < hRootOf ctx.source ctx.rootColumn (d + 2) it
              · exfalso
                have ha1 : a < hRootOf ctx.source ctx.rootColumn (d + 2) it := by omega
                rw [if_pos ha1] at hxO
                rw [if_pos hb1] at hyO
                have ea := slot_idx (emitOK_reg hxO hc)
                have eb := slot_idx (emitOK_reg hyO hc')
                omega
              · rw [if_neg hb1] at ibCut_b
                by_cases ha1 : a < hRootOf ctx.source ctx.rootColumn (d + 2) it
                · exfalso
                  rw [if_pos ha1] at hxO
                  rw [if_neg hb1] at hyO
                  have ea := slot_idx (emitOK_reg hxO hc)
                  have eb := slot_idx (emitOK_reg hyO hc')
                  omega
                · exact ibCut_b rfl (by simp; omega)

/-! ## Consecutive emits -/

/-- Two consecutive emits: if the second is not a gap copy and the origin rows differ, the jump
of the rows is at most the jump of the origin rows. -/
def AdjR (M : Mountain) (p q : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin q.2 = false → ∀ c c' : Cell, cell? M p.2.src = some c →
    cell? M q.2.src = some c' → official c.row ≠ official c'.row →
      Row.jump p.1.row q.1.row ≤ Row.jump (official c.row) (official c'.row)

theorem levelOneT_short {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ps = [] ∨ ∃ a, ps = [a] := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; exact Or.inl h
  | some q =>
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h; exact Or.inr ⟨_, rfl⟩
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            exact Or.inr ⟨_, h.symm⟩
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h; exact Or.inr ⟨_, rfl⟩

/-- **Consecutive emits of an item.** -/
theorem runItemT_adj (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hV : MountainValid ctx.source) (hi : ctx.block ≠ 0) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
      List.IsChain (AdjR ctx.source) ps
  | 0, it, ps, h, _ => by
      have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      rcases levelOneT_short h' with rfl | ⟨a, rfl⟩
      · exact List.IsChain.nil
      · exact List.IsChain.singleton a
  | d + 1, it, ps, h, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      rename_i children hch
      split at h
      · cases h
      rename_i outs houts
      cases h
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
      obtain ⟨hinvc, _, _⟩ := ChainCorr.Inner.childItems_order hch hinv
      apply isChain_flatten
      · intro l hl
        obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
        exact runItemT_adj ctx R B hbnd hV hi d _ _ (hall a (by omega) ha)
          (hinvc _ (List.getElem_mem _))
      · intro a b ha hb hab x hx y hy hyn c c' hc hc' hne
        have hax : a < children.length := by omega
        have hbx : b < children.length := by omega
        have hruna := hall a hax ha
        have hrunb := hall b hbx hb
        have hxm := List.mem_of_mem_getLast? hx
        have hym := List.mem_of_mem_head? hy
        have hxO := (ChainCorr.Inner.runItemT_order ctx (d + 1) _ _ hruna
          (hinvc _ (List.getElem_mem hax))).2 x hxm
        have hyO := (ChainCorr.Inner.runItemT_order ctx (d + 1) _ _ hrunb
          (hinvc _ (List.getElem_mem hbx))).2 y hym
        -- the rows lie in the target region
        have hxT := runItemT_inTarget ctx d _ _ hruna x hxm
        have hyT := runItemT_inTarget ctx d _ _ hrunb y hym
        obtain ⟨ja, hja⟩ := Dimension.childItems_targets ctx (d + 2) it children hch _
          (List.getElem_mem hax)
        obtain ⟨jb, hjb⟩ := Dimension.childItems_targets ctx (d + 2) it children hch _
          (List.getElem_mem hbx)
        rw [hja] at hxT
        rw [hjb] at hyT
        have hjr := jump_le_of_region (Recon.RowLaw.inRegion_of_slot hxT)
          (Recon.RowLaw.inRegion_of_slot hyT)
        by_cases hcd : (official c.row).coeff d = (official c'.row).coeff d
        · exfalso
          have := sameSlot_head_cut ctx R B hbnd hV hi hch hax hbx hab ha hb hruna hrunb hxm hy
            hxO hyO hc hc' hcd
          rw [this] at hyn
          cases hyn
        · have := jump_ge_of_ne hcd
          omega

/-- The first items: a row of a region and a row that differs from it at or above the level of
the region. -/
theorem lowerItems_rows {τ : Row} {p : Nat × Item} (hp : p ∈ lowerItems τ) :
    ∃ k j, j < τ.coeff k ∧ p = (k + 1, ⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩) ∧
      ∀ r, inRegion (k + 1) (slot (k + 2) τ j) r = true →
        r.coeff k = j ∧ ∀ e, k < e → r.coeff e = τ.coeff e := by
  obtain ⟨k, j, _, hj, rfl⟩ := Recon.RowLaw.mem_lowerItems hp
  refine ⟨k, j, hj, rfl, fun r hr => ?_⟩
  have h1 := Recon.RowLaw.inRegion_iff'.mp hr
  refine ⟨?_, fun e he => ?_⟩
  · rw [h1 k (by omega)]
    exact Recon.RowLaw.slot_coeff_at k τ j
  · rw [h1 e (by omega)]
    exact Recon.RowLaw.slot_coeff_high he

/-- **Consecutive emits of a copied column** (block `i ≥ 1`). -/
theorem emitsT_adj (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hV : MountainValid ctx.source) (hi : ctx.block ≠ 0) {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : List.IsChain (AdjR ctx.source) es := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i low hlow
  split at h
  · cases h
  rename_i up hup
  cases h
  unfold lowerT at hlow
  simp only [bind, Except.bind, pure, Except.pure] at hlow
  split at hlow
  · cases hlow
  rename_i outs houts
  cases hlow
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  -- facts on an emit of a first item
  have hfirst : ∀ a (ha : a < outs.length) (x : Emit × Origin), x ∈ outs[a] →
      ∃ k j, j < τ.coeff k ∧ (∀ c, cell? ctx.source x.2.src = some c →
        (official c.row).coeff k = j ∧ ∀ e, k < e → (official c.row).coeff e = τ.coeff e) ∧
        x.1.row.coeff k = j ∧ (∀ e, k < e → x.1.row.coeff e = τ.coeff e) ∧
        ((lowerItems τ)[a]'(by omega)) = (k + 1, ⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩) := by
    intro a ha x hx
    have hal : a < (lowerItems τ).length := by omega
    obtain ⟨k, j, hj, hk, hreg⟩ := lowerItems_rows (List.getElem_mem hal)
    have hrun := hall a hal ha
    rw [hk] at hrun
    have hO := (ChainCorr.Inner.runItemT_order ctx (k + 1) _ _ hrun
      (fun C hC => by cases hC)).2 x hx
    have hT := runItemT_inTarget ctx k _ _ hrun x hx
    obtain ⟨_, c0, hc0, hc0reg, _⟩ := hO
    refine ⟨k, j, hj, fun c hc => ?_, (hreg _ hT).1, (hreg _ hT).2, hk⟩
    rw [hc0] at hc
    cases hc
    exact hreg _ hc0reg
  -- consecutive emits of the upper part
  have hupper : ∀ q ∈ up, ∃ r : Ref × Cell, q.2 = .upper r.1 ∧ q.1.row = official r.2.row ∧
      cell? ctx.source r.1 = some r.2 ∧ τ ≤ official r.2.row := by
    intro q hq
    unfold upperT at hup
    obtain ⟨r, hr, hrq⟩ := mem_of_mapM hup hq
    obtain ⟨h1, h2⟩ := upper_emit hrq
    rw [List.mem_filter] at hr
    obtain ⟨_, _, hrc⟩ := mem_realNodes hr.1
    exact ⟨r, h1, h2, hrc, by simpa using hr.2⟩
  rw [List.isChain_append]
  refine ⟨?_, ?_, ?_⟩
  · apply isChain_flatten
    · intro l hl
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
      have hal : a < (lowerItems τ).length := by omega
      obtain ⟨k, j, _, hk, _⟩ := lowerItems_rows (List.getElem_mem hal)
      have hrun := hall a hal ha
      rw [hk] at hrun
      exact runItemT_adj ctx R B hbnd hV hi k _ _ hrun (fun C hC => by cases hC)
    · intro a b ha hb hab x hx y hy _ c c' hc hc' _
      have hxm := List.mem_of_mem_getLast? hx
      have hym := List.mem_of_mem_head? hy
      obtain ⟨k, j, hj, hcx, hx1, hx2, hka⟩ := hfirst a ha x hxm
      obtain ⟨k', j', hj', hcy, hy1, hy2, hkb⟩ := hfirst b hb y hym
      obtain ⟨hc1, hc2⟩ := hcx c hc
      obtain ⟨hc1', hc2'⟩ := hcy c' hc'
      -- the two regions differ
      have hsep := List.pairwise_iff_getElem.mp (ChainCorr.Inner.lowerItems_sep τ) a b
        (by omega) (by omega) hab
      rw [hka, hkb] at hsep
      have hne : (k, j) ≠ (k', j') := by
        intro heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hr : inRegion (k + 1) (slot (k + 2) τ j) x.1.row = true := by
          rw [Recon.RowLaw.inRegion_iff']
          intro e he
          have he' : k ≤ e := by omega
          rcases Nat.lt_or_eq_of_le he' with he'' | he''
          · rw [hx2 e he'', Recon.RowLaw.slot_coeff_high he'']
          · subst he''; rw [hx1, Recon.RowLaw.slot_coeff_at]
        exact lt_irrefl _ (hsep _ _ hr hr)
      apply le_of_eq
      rcases Nat.lt_trichotomy k k' with hkk | hkk | hkk
      · refine jump_congr_high (m := k') (e0 := k') (fun e he => ?_) (fun e he => ?_) le_rfl ?_
        · rw [hx2 e (by omega), hc2 e (by omega)]
        · rcases Nat.lt_or_eq_of_le he with he | he
          · rw [hy2 e he, hc2' e he]
          · subst he; rw [hy1, hc1']
        · rw [hx2 k' hkk, hy1]; omega
      · subst hkk
        have hjj : j ≠ j' := fun h => hne (by rw [h])
        refine jump_congr_high (m := k) (e0 := k) (fun e he => ?_) (fun e he => ?_) le_rfl ?_
        · rcases Nat.lt_or_eq_of_le he with he | he
          · rw [hx2 e he, hc2 e he]
          · subst he; rw [hx1, hc1]
        · rcases Nat.lt_or_eq_of_le he with he | he
          · rw [hy2 e he, hc2' e he]
          · subst he; rw [hy1, hc1']
        · rw [hx1, hy1]; exact hjj
      · refine jump_congr_high (m := k) (e0 := k) (fun e he => ?_) (fun e he => ?_) le_rfl ?_
        · rcases Nat.lt_or_eq_of_le he with he | he
          · rw [hx2 e he, hc2 e he]
          · subst he; rw [hx1, hc1]
        · rw [hy2 e (by omega), hc2' e (by omega)]
        · rw [hx1, hy2 k hkk]; omega
  · -- the upper part: rows are origin rows
    rw [List.isChain_iff_getElem]
    intro n hn _ c c' hc hc' _
    obtain ⟨r, hr1, hr2, hr3, _⟩ := hupper _ (List.getElem_mem (by omega : n < up.length))
    obtain ⟨r', hr1', hr2', hr3', _⟩ := hupper _ (List.getElem_mem hn)
    have hs : up[n].2.src = r.1 := by rw [hr1]; rfl
    have hs' : up[n + 1].2.src = r'.1 := by rw [hr1']; rfl
    rw [hs, hr3] at hc
    rw [hs', hr3'] at hc'
    cases hc
    cases hc'
    rw [hr2, hr2']
  · -- the last lower emit and the first upper emit
    intro x hx y hy _ c c' hc hc' _
    obtain ⟨a, ha, hxa⟩ : ∃ a, ∃ ha : a < outs.length, x ∈ outs[a] := by
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp (List.mem_of_mem_getLast? hx)
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
      exact ⟨a, ha, hxl⟩
    obtain ⟨k, j, hj, hcx, hx1, hx2, _⟩ := hfirst a ha x hxa
    obtain ⟨hc1, hc2⟩ := hcx c hc
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hupper y (List.mem_of_mem_head? hy)
    have hs : y.2.src = r.1 := by rw [hr1]; rfl
    rw [hs, hr3] at hc'
    cases hc'
    rw [hr2]
    apply le_of_eq
    -- `row y ≥ τ` differs from the region of `x` at or above `k`
    have hd : ∃ e, k ≤ e ∧ x.1.row.coeff e ≠ (official r.2.row).coeff e := by
      by_contra hn
      simp only [not_exists, not_and, not_not] at hn
      have hlt : official r.2.row < τ := by
        refine Row.lt_iff.mpr ⟨k, fun e he => ?_, ?_⟩
        · rw [← hn e (by omega), hx2 e he]
        · rw [← hn k le_rfl, hx1]; exact hj
      exact absurd hr4 (not_le.mpr hlt)
    obtain ⟨e0, he0, hne0⟩ := hd
    exact jump_congr_high (m := k) (fun e he => by
      rcases Nat.lt_or_eq_of_le he with he | he
      · rw [hx2 e he, hc2 e he]
      · subst he; rw [hx1, hc1]) (fun e _ => rfl) he0 hne0

open ChainCorr in
/-- **`CutBump` holds.** -/
theorem cutBump : ChainCorr.CutParts.CutBump := by
  intro s n D M out ρ R t X x i es hS hx j hj hcut hj1 hsrc1 hnc1 cv cv' cm cm' hcv hcv' hcm hcm'
  have hV := build_valid_of_success hS.splice.build
  have hipos := hS.iPos
  obtain ⟨hcx, _⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hbnd : ∀ d T, topIn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X).result
      (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X).boundary d T =
      topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    have := hS.Xeq
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < X; omega)
  have hchain := emitsT_adj _ (official t.row) R _ hbnd hV (by show i ≠ 0; omega) hS.emits
  have hadj := List.IsChain.getElem hchain j hj1
  -- the cells of the two emits
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨e1, he1, hr1⟩ := hcellsX j hj
  obtain ⟨e2, he2, hr2⟩ := hcellsX (j + 1) hj1
  rw [hcv] at he1
  cases he1
  rw [hcv'] at he2
  cases he2
  -- the origins
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  obtain ⟨hoc, ho1, _⟩ := src_of_inner (ne_of_lt hx) hbl j hj
  have hcm'' : cell? M es[j + 1].2.src = some cm' := by rw [hsrc1]; exact hcm'
  have hlt : cm.row < cm'.row := by
    have h1 : cell? M ⟨x, es[j].2.src.index⟩ = some cm := by rw [← hoc]; exact hcm
    have h2 : cell? M ⟨x, es[j].2.src.index + 1⟩ = some cm' := by
      rw [← hoc]; exact hcm'
    exact cell_row_lt hV h1 h2 (by omega)
  have hone : (1 : Row) ≤ cm.row := one_le_row hV hcm ho1
  have hoff := Recon.official_strictMono hone hlt
  have hle := hadj hnc1 cm cm' hcm hcm'' (ne_of_lt hoff)
  rw [hr1, hr2, Recon.JumpLaw.jump_stored]
  have e1 : cm.row = stored (official cm.row) := (Classification.stored_official hone).symm
  have e2 : cm'.row = stored (official cm'.row) :=
    (Classification.stored_official (le_trans hone hlt.le)).symm
  rw [e1, e2, Recon.JumpLaw.jump_stored]
  exact hle

end OmegaY.Official.Classification.Proofs.CutGap

#print axioms OmegaY.Official.Classification.Proofs.CutGap.emitsT_adj
#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutBump
