/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Execution.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Certificate

set_option backward.do.legacy false

/-!
# What a successful official run stores in a new column

`Official.copyColumn` emits nodes (`Emit`), turns every emitted node into a cell
with the stored row `stored em.row` and a left endpoint, and finishes the values with
`Expansion.finish` over the output so far (`Official.assemble`). This file records
what is known about such a column from the execution alone (`NewCol`):

* the cells come in strictly increasing rows, none of them the phantom row `0`;
* every cell has a left endpoint, which is either the phantom `⟨X - 1, 0⟩` of the
  previous column (for a bottom node with no source leg, stored row `1`) or the
  answer of `Expansion.below` in some existing column (the highest node strictly below
  the new row).

`expandDiagram_inv` shows that every successful run of `Official.expandDiagram` keeps
the columns left of `x₀` and satisfies `NewCol` in every later column.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Dimension

/-! ## Loops with postconditions -/

/-- A `for` loop whose body only yields and checks a property of each element. -/
theorem ok_forIn_check {ε α β : Type} (Q : α → Prop) :
    ∀ (xs : List α) (init : β) (f : α → β → Except ε (ForInStep β)),
      (∀ a ∈ xs, ∀ b r, f a b = .ok r → Q a ∧ ∃ b', r = .yield b') →
      Ok (forIn xs init f) (fun _ => ∀ a ∈ xs, Q a)
  | [], _, _, _ => ok_pure (by simp)
  | a :: as, init, f, hf => by
      rw [List.forIn_cons]
      intro r hr
      obtain ⟨y, hy, hr⟩ := Reconstruction.bind_ok hr
      obtain ⟨hQ, b', rfl⟩ := hf a List.mem_cons_self init y hy
      have := ok_forIn_check Q as b' f (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) r hr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hQ
      · exact this x hx

/-- `mapM` with a pointwise postcondition relating each input to its output. -/
theorem ok_mapM₂ {ε α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (f : α → Except ε β), (∀ a ∈ xs, Ok (f a) (P a)) →
      Ok (xs.mapM f) (fun ys => List.Forall₂ P xs ys)
  | [], _, _ => ok_pure List.Forall₂.nil
  | a :: as, f, hf => by
      rw [List.mapM_cons]
      refine ok_bind (hf a List.mem_cons_self) (fun b hb => ?_)
      refine ok_bind (ok_mapM₂ P as f (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')))
        (fun bs hbs => ok_pure (List.Forall₂.cons hb hbs))

theorem pairwise_of_zip_tail' {α : Type} {r : α → α → Prop} [IsTrans α r] {l : List α}
    (h : ∀ p ∈ l.zip l.tail, r p.1 p.2) : l.Pairwise r := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hl : ∀ p ∈ l.zip l.tail, r p.1 p.2 := by
        intro p hp
        cases l with
        | nil => simp at hp
        | cons b l' =>
            apply h
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hp
      have ihl := ih hl
      refine List.pairwise_cons.mpr ⟨?_, ihl⟩
      cases l with
      | nil => simp
      | cons b l' =>
          have hab : r a b := h (a, b) (by simp)
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hab
          · exact _root_.trans hab ((List.pairwise_cons.mp ihl).1 y hy)

theorem forall₂_map {α β γ : Type} {P : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, P a b → g b = f a) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ys.map g = xs.map f
  | _, _, .nil => rfl
  | _, _, .cons h rest => by
      simp only [List.map_cons, hfg _ _ h, forall₂_map hfg rest]

theorem forall₂_mem_right {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ y ∈ ys, ∃ x ∈ xs, P x y
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨x, hx, hxy⟩ := forall₂_mem_right rest y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

/-! ## A new column -/

/-- The left endpoint of a cell of a new column over the output `m` so far. -/
def LegOK (m : Mountain) (cell : Cell) : Prop :=
  ∃ ref, cell.left = some ref ∧
    ((cell.row = 1 ∧ ref = ⟨m.size - 1, 0⟩) ∨
      ∃ q nodes, m[q]? = some nodes ∧ Expansion.below m q cell.row = .ok ref)

/-- What the execution alone says about a new column `col` appended to `m`. -/
def NewCol (m : Mountain) (col : Column) : Prop :=
  ∃ cells : List Cell, Expansion.finish m (phantom :: cells) = .ok col ∧
    (cells.map Cell.row).Pairwise (· < ·) ∧ (∀ cell ∈ cells, cell.row ≠ 0) ∧
    ∀ cell ∈ cells, LegOK m cell

theorem below_nodes {m : Mountain} {q : Nat} {row : Row} {ref : Ref}
    (h : Expansion.below m q row = .ok ref) : ∃ nodes, m[q]? = some nodes := by
  unfold Expansion.below at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i nodes hn
    unfold Expansion.columnAt at hn
    split at hn
    · rename_i c hc
      exact ⟨c, hc⟩
    · cases hn

/-- The cell made from one emitted node. -/
theorem assemble_cell (ctx : Context) (em : Emit) :
    Ok (match em.leftColumn with
      | some p => do
        let q := if ctx.rootColumn ≤ p then p + ctx.width * ctx.block else p
        let ref ← liftE (Expansion.below ctx.result q (stored em.row))
        pure (⟨stored em.row, 0, some ref⟩ : Cell)
      | none =>
        if em.row = 0 then pure (⟨stored em.row, 0, some ⟨ctx.result.size - 1, 0⟩⟩ : Cell)
        else throw .missingParent)
      (fun cell => cell.row = stored em.row ∧ LegOK ctx.result cell) := by
  split
  · intro cell h
    obtain ⟨ref, href, h⟩ := Reconstruction.bind_ok h
    cases h
    obtain ⟨nodes, hn⟩ := below_nodes (Reconstruction.liftE_ok href)
    exact ⟨rfl, ref, rfl, Or.inr ⟨_, nodes, hn, Reconstruction.liftE_ok href⟩⟩
  · split
    · rename_i h0
      intro cell h
      cases h
      refine ⟨rfl, _, rfl, Or.inl ⟨?_, rfl⟩⟩
      rw [h0]
      exact stored_zero
    · exact ok_throw _

/-- **The column made by `assemble`.** -/
theorem assemble_newCol (ctx : Context) (emits : List Emit) :
    Ok (assemble ctx emits) (NewCol ctx.result) := by
  unfold assemble
  dsimp only
  split
  · exact ok_throw_bind _ _
  · refine ok_bind (ok_forIn_check (fun pair : Emit × Emit => pair.1.row < pair.2.row) _ _ _ ?_)
      (fun _ hrows => ?_)
    · intro a _ b r h
      by_cases hq : a.1.row < a.2.row
      · simp only [hq, not_true_eq_false, if_false] at h
        exact ⟨hq, by cases h; exact ⟨_, rfl⟩⟩
      · simp only [hq, not_false_eq_true, if_true] at h
        cases h
    · refine ok_bind (ok_mapM₂ (fun (em : Emit) (cell : Cell) =>
        cell.row = stored em.row ∧ LegOK ctx.result cell) emits _ (fun em _ => assemble_cell ctx em))
        (fun cells hcells => ?_)
      intro col hcol
      refine ⟨cells, Reconstruction.liftE_ok hcol, ?_, ?_, ?_⟩
      · have hmap : cells.map Cell.row = emits.map (fun em => stored em.row) :=
          forall₂_map (fun _ _ h => h.1) hcells
        rw [hmap, List.pairwise_map]
        have := pairwise_of_zip_tail' (r := fun a b : Emit => a.row < b.row) hrows
        exact this.imp stored_strictMono
      · intro cell hc
        obtain ⟨em, _, hem⟩ := forall₂_mem_right hcells cell hc
        rw [hem.1]
        exact stored_ne_zero _
      · intro cell hc
        obtain ⟨em, _, hem⟩ := forall₂_mem_right hcells cell hc
        exact hem.2

/-- **The column made by `copyColumn`.** -/
theorem copyColumn_newCol (ctx : Context) (τ : Row) :
    Ok (copyColumn ctx τ) (NewCol ctx.result) := by
  unfold copyColumn
  dsimp only
  refine ok_bind (ok_true _) (fun emits _ => ?_)
  refine ok_bind (ok_true _) (fun emits _ => ?_)
  exact assemble_newCol ctx emits

end OmegaY.Official.Recon

namespace OmegaY.Official.Recon

open Canonical Expansion Dimension

/-! ## The runs of `expandDiagram` -/

/-- The shape of the output of a run: it keeps the columns of `M` left of `x₀`, and every
later column is a `NewCol` over the columns before it. -/
def Inv (M : Mountain) (x0 : Nat) (R : Mountain) : Prop :=
  x0 ≤ R.size ∧ (∀ c, c < x0 → R[c]? = M[c]?) ∧
    ∀ c (hc : c < R.size), x0 ≤ c → 0 < c ∧ NewCol (R.extract 0 c) R[c]

theorem inv_push {M : Mountain} {x0 : Nat} {R : Mountain} (h : Inv M x0 R) {col : Column}
    (hpos : 0 < R.size) (hcol : NewCol R col) : Inv M x0 (R.push col) := by
  obtain ⟨hs, hpre, hnew⟩ := h
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro c hc
    rw [getElem_push_left (by omega)]
    exact hpre c hc
  · intro c hc hx
    by_cases he : c = R.size
    · subst he
      refine ⟨hpos, ?_⟩
      simp only [Array.getElem_push_eq]
      rw [show (R.push col).extract 0 R.size = R by
        apply Array.ext
        · simp
        · intro i h1 h2
          simp]
      exact hcol
    · have hOld : c < R.size := by simp only [Array.size_push] at hc; omega
      obtain ⟨hp, hn⟩ := hnew c hOld hx
      refine ⟨hp, ?_⟩
      simp only [Array.getElem_push_lt hOld]
      rw [show (R.push col).extract 0 c = R.extract 0 c by
        apply Array.ext
        · simp; omega
        · intro i h1 h2
          simp only [Array.size_extract, Array.size_push] at h1 h2
          simp only [Array.getElem_extract]
          rw [Array.getElem_push_lt (by omega)]]
      exact hn

theorem inv_extract {M : Mountain} {x0 : Nat} (hx : x0 ≤ M.size) : Inv M x0 (M.extract 0 x0) := by
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro c hc
    simp [hc, show c < M.size by omega]
  · intro c hc hx'
    simp at hc
    omega

theorem inv_pop {M : Mountain} : Inv M (M.size - 1) M.pop := by
  refine ⟨by simp, ?_, ?_⟩
  · intro c hc
    rw [Array.getElem?_pop, if_pos (by omega)]
  · intro c hc hx'
    simp at hc
    omega

/-- **Every successful run keeps the prefix and makes `NewCol` columns.** -/
theorem expandDiagram_inv {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    (copies : Nat) : Ok (Official.expandDiagram s copies) (Inv M (M.size - 1)) := by
  unfold Official.expandDiagram
  have hbuild : Ok (liftE ((Canonical.build s).mapError Expansion.Error.canonical))
      (fun M' => M' = M) := by
    intro M' h
    rw [hb] at h
    cases h
    rfl
  refine ok_bind hbuild (fun M' hM' => ?_)
  subst M'
  dsimp only
  split
  · rename_i hs
    have : s = [] := List.isEmpty_iff.mp hs
    subst this
    have hM0 : M = #[] := Except.ok.inj (hb.symm.trans rfl)
    subst hM0
    exact ok_pure ⟨le_refl _, fun c hc => by simp at hc, fun c hc => by simp at hc⟩
  · refine ok_bind (ok_true _) (fun lastCol _ => ?_)
    refine ok_bind (ok_true _) (fun t _ => ?_)
    split
    · exact ok_pure inv_pop
    · refine ok_bind (ok_true _) (fun root _ => ?_)
      split
      · exact ok_throw_bind _ _
      · rename_i hcr
        have hx0 : 1 ≤ M.size - 1 := by
          have := not_not.mp hcr
          omega
        let I : Mountain → Prop := fun R => Inv M (M.size - 1) R
        refine ok_bind (ok_forIn I _ _ _ (inv_extract (by omega))
          (fun i _ R hR => ?_)) (fun R hR => ok_pure hR)
        refine ok_bind (ok_forIn I _ _ _ hR (fun x _ R hR => ?_))
          (fun R hR => ok_pure hR)
        split
        · exact ok_throw_bind _ _
        · refine ok_bind (copyColumn_newCol _ _) (fun col hcol => ok_pure ?_)
          exact inv_push hR (by have := hR.1; omega) hcol

end OmegaY.Official.Recon
