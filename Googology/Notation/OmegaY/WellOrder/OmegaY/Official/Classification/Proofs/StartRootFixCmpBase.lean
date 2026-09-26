/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootFixCmpBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMD
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono

set_option backward.do.legacy false

/-!
# The copies keep their place among the rows of the root column (`RootCmp`)

For a copied column of a block `i ≥ 1` (any column `y` of the block, `x₀` included) and a row
`r` of a real node of the root column `c_r` (a *root row*):

* a non-gap emit with origin row `σ` is on the same side of `r` as `σ`:
  `r < σ → r < row`, `r = σ → row = σ`, `σ < r → row < r`;
* a gap copy (`b = 1`) with origin row `C` is above every root row `≤ C` and below every root
  row `> C`.

This replaces the row map `Φ` of `CopyShape.lean` (which needs (MA), false) where only the
comparison with the root rows is used (`PaLookup`, `StartRootFixPa.lean`). It uses no fact
about `M(s)` besides validity and (MD) (proved, `mdHolds`).

## The invariant

Write `Bl d S r` (`r` is below every row of the region `(d, S)`) and `Ab d S r` (above). For an
item `(S, T, C, o, b)` of level `d` (`CInv`):

* `C = ⊥`, `b = 0`: `S = T`, or every root row is below both regions or above both (`Sep`);
* `C = ⊥`, `b = 1`: `d ≥ 2`, and every root row is in or below `S` and below `T`, or above
  both (`SepUp`);
* `C ≠ ⊥`, `b = 0`: `S = T` and `C` is the row of the top of `c_r` in `S`;
* `C ≠ ⊥`, `b = 1`: every root row `≤ C` is below `T`, every root row `> C` above it
  (`GapSep`).

The lower items have `S = T`. The children (cases 1 to 4 of the rule) keep the invariant
(`childItems_cinv`); the only fact used beyond the regions is that the lift `(h_κ - h_ρ)·i`
of an ascending region is at least `1` (MD). At level `1` the invariant gives the comparison
of the emit (`levelOneT_cmp`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CopyMonoProof

/-! ## Rows of the root column, and the sides of a region -/

/-- `r` is the official row of a real node of column `cr`. -/
def RootRow (M : Mountain) (cr : Nat) (r : Row) : Prop :=
  ∃ q ∈ realNodes M cr, official q.2.row = r

/-- `r` is below every row of the region. -/
def Bl (d : Nat) (S r : Row) : Prop := ∀ a, inRegion d S a = true → r < a

/-- `r` is above every row of the region. -/
def Ab (d : Nat) (S r : Row) : Prop := ∀ a, inRegion d S a = true → a < r

def Sep (M : Mountain) (cr d : Nat) (S T : Row) : Prop :=
  S = T ∨ ∀ r, RootRow M cr r → (Bl d S r ∧ Bl d T r) ∨ (Ab d S r ∧ Ab d T r)

def SepUp (M : Mountain) (cr d : Nat) (S T : Row) : Prop :=
  ∀ r, RootRow M cr r → ((inRegion d S r = true ∨ Bl d S r) ∧ Bl d T r) ∨ (Ab d S r ∧ Ab d T r)

def GapSep (M : Mountain) (cr d : Nat) (T C : Row) : Prop :=
  ∀ r, RootRow M cr r → (r ≤ C → Bl d T r) ∧ (C < r → Ab d T r)

/-- The invariant of an item. -/
def CInv (ctx : Context) (d : Nat) (it : Item) : Prop :=
  (it.clean = none → it.cutBottom = false →
    Sep ctx.source ctx.rootColumn d it.source it.target) ∧
  (it.clean = none → it.cutBottom = true →
    2 ≤ d ∧ SepUp ctx.source ctx.rootColumn d it.source it.target) ∧
  (∀ C, it.clean = some C → it.cutBottom = false →
    it.source = it.target ∧ rootTop ctx d it.source = some C) ∧
  (∀ C, it.clean = some C → it.cutBottom = true →
    GapSep ctx.source ctx.rootColumn d it.target C)

/-- **The comparison of an emit with the root rows.** -/
def ECmp (M : Mountain) (cr : Nat) (p : Emit × Origin) : Prop :=
  ∀ c, cell? M p.2.src = some c → ∀ r, RootRow M cr r →
    (cutOrigin p.2 = false →
      (r < official c.row → r < p.1.row) ∧ (r = official c.row → p.1.row = r) ∧
        (official c.row < r → p.1.row < r)) ∧
    (cutOrigin p.2 = true → (r ≤ official c.row → r < p.1.row) ∧ (official c.row < r → p.1.row < r))

/-! ## Regions -/

theorem bl_slot {d : Nat} {S r : Row} {j : Nat} (h : Bl (d + 2) S r) :
    Bl (d + 1) (slot (d + 2) S j) r := fun a ha => h a (mem_of_slot ha)

theorem ab_slot {d : Nat} {S r : Row} {j : Nat} (h : Ab (d + 2) S r) :
    Ab (d + 1) (slot (d + 2) S j) r := fun a ha => h a (mem_of_slot ha)

/-- **A region is an interval**: a row is in it, below it or above it. -/
theorem trichotomy (d : Nat) (S r : Row) :
    inRegion d S r = true ∨ Bl d S r ∨ Ab d S r := by
  classical
  by_cases hin : inRegion d S r = true
  · exact Or.inl hin
  · right
    have hex : ∃ k, d - 1 ≤ k ∧ r.coeff k ≠ S.coeff k := by
      by_contra hn
      push Not at hn
      exact hin ((inRegion_iff d S r).mpr hn)
    let N := len r + len S + d
    have hbound : ∀ k, d - 1 ≤ k ∧ r.coeff k ≠ S.coeff k → k ≤ N := by
      intro k ⟨_, hk⟩
      by_contra hn
      apply hk
      rw [coeff_eq_zero_of_len_le (by omega), coeff_eq_zero_of_len_le (by omega)]
    obtain ⟨k1, hk1⟩ := hex
    let k0 := Nat.findGreatest (fun k => d - 1 ≤ k ∧ r.coeff k ≠ S.coeff k) N
    have hk0 : d - 1 ≤ k0 ∧ r.coeff k0 ≠ S.coeff k0 :=
      Nat.findGreatest_spec (P := fun k => d - 1 ≤ k ∧ r.coeff k ≠ S.coeff k) (hbound k1 hk1) hk1
    have habove : ∀ k, k0 < k → r.coeff k = S.coeff k := by
      intro k hk
      by_contra hne
      by_cases hkN : k ≤ N
      · exact Nat.findGreatest_is_greatest (P := fun k => d - 1 ≤ k ∧ r.coeff k ≠ S.coeff k) hk
          hkN ⟨by omega, hne⟩
      · exact hkN (hbound k ⟨by omega, hne⟩)
    rcases Nat.lt_or_gt_of_ne hk0.2 with hlt | hgt
    · left
      intro a ha
      have ha' := (inRegion_iff d S a).mp ha
      refine Row.lt_iff.mpr ⟨k0, fun j hj => ?_, ?_⟩
      · rw [habove j hj, ha' j (by omega)]
      · rw [ha' k0 hk0.1]; exact hlt
    · right
      intro a ha
      have ha' := (inRegion_iff d S a).mp ha
      refine Row.lt_iff.mpr ⟨k0, fun j hj => ?_, ?_⟩
      · rw [habove j hj, ha' j (by omega)]
      · rw [ha' k0 hk0.1]; exact hgt

theorem coeff_le_of_le {d : Nat} {S a b : Row} (ha : inRegion (d + 2) S a = true)
    (hb : inRegion (d + 2) S b = true) (hab : a ≤ b) : a.coeff d ≤ b.coeff d := by
  by_contra hn
  push Not at hn
  have ha' := (inRegion_iff (d + 2) S a).mp ha
  have hb' := (inRegion_iff (d + 2) S b).mp hb
  have : b < a := Row.lt_iff.mpr ⟨d, fun j hj => by rw [ha' j (by omega), hb' j (by omega)], hn⟩
  exact absurd hab (not_le.mpr this)

/-- A row of the region with height below `j` is below the slot `j`. -/
theorem bl_slot_of_lt {d : Nat} {S r : Row} {j : Nat} (hr : inRegion (d + 2) S r = true)
    (hj : r.coeff d < j) : Bl (d + 1) (slot (d + 2) S j) r :=
  fun a ha => lt_of_slot_lt (mem_slot_height hr) ha (by simpa [height] using hj)

theorem in_slot_of_eq {d : Nat} {S r : Row} {j : Nat} (hr : inRegion (d + 2) S r = true)
    (hj : r.coeff d = j) : inRegion (d + 1) (slot (d + 2) S j) r = true := by
  have := mem_slot_height hr
  simp only [height, show d + 2 - 2 = d by omega] at this
  rw [hj] at this
  exact this

/-! ## The top of the root column in a region -/

/-- The facts about the top `C0` of the root column in the region `(d + 2, S)`. -/
structure TopInfo (M : Mountain) (cr d : Nat) (S C0 : Row) : Prop where
  root : RootRow M cr C0
  mem : inRegion (d + 2) S C0 = true
  max : ∀ r, RootRow M cr r → inRegion (d + 2) S r = true → r ≤ C0

theorem topInfo {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {cr d : Nat}
    {S : Row} {ρr : Ref} {ρc : Cell} (h : topIn M cr (d + 2) S = some (ρr, ρc)) :
    TopInfo M cr d S (official ρc.row) := by
  obtain ⟨hmem, hin, _⟩ := Recon.RowLaw.topIn_spec h
  refine ⟨⟨_, hmem, rfl⟩, hin, ?_⟩
  rintro r ⟨q, hq, rfl⟩ hr
  exact Recon.RowLaw.topIn_row_max hb h hq hr

/-- The side of a root row with respect to the region of a top `C0`. -/
theorem side {M : Mountain} {cr d : Nat} {S C0 r : Row} (hT : TopInfo M cr d S C0)
    (hr : RootRow M cr r) :
    (inRegion (d + 2) S r = true ∧ r ≤ C0 ∧ r.coeff d ≤ C0.coeff d) ∨
      (Bl (d + 2) S r ∧ r < C0) ∨ (Ab (d + 2) S r ∧ C0 < r) := by
  rcases trichotomy (d + 2) S r with h | h | h
  · have hle := hT.max r hr h
    exact Or.inl ⟨h, hle, coeff_le_of_le h hT.mem hle⟩
  · exact Or.inr (Or.inl ⟨h, h C0 hT.mem⟩)
  · exact Or.inr (Or.inr ⟨h, h C0 hT.mem⟩)

/-- A slot above the top of the root column has root rows only below or above it. -/
theorem sep_above {M : Mountain} {cr d : Nat} {S T C0 : Row} (hT : TopInfo M cr d S C0)
    {σ j : Nat} (hσ : C0.coeff d < σ) (hj : C0.coeff d < j)
    (hST : ∀ r, RootRow M cr r → (inRegion (d + 2) S r = true ∨ Bl (d + 2) S r) → Bl (d + 2) T r ∨
      (inRegion (d + 2) T r = true ∧ r.coeff d ≤ C0.coeff d))
    (hST' : ∀ r, RootRow M cr r → Ab (d + 2) S r → Ab (d + 2) T r) :
    Sep M cr (d + 1) (slot (d + 2) S σ) (slot (d + 2) T j) := by
  right
  intro r hr
  rcases side hT hr with ⟨hin, _, hc⟩ | ⟨hbl, _⟩ | ⟨hab, _⟩
  · left
    refine ⟨bl_slot_of_lt hin (by omega), ?_⟩
    rcases hST r hr (Or.inl hin) with h | ⟨h, hc'⟩
    · exact bl_slot h
    · exact bl_slot_of_lt h (by omega)
  · left
    refine ⟨bl_slot hbl, ?_⟩
    rcases hST r hr (Or.inr hbl) with h | ⟨h, hc'⟩
    · exact bl_slot h
    · exact bl_slot_of_lt h (by omega)
  · right
    exact ⟨ab_slot hab, ab_slot (hST' r hr hab)⟩

/-- A gap slot above the top of the root column, with `S = T`. -/
theorem gap_above {M : Mountain} {cr d : Nat} {S C0 : Row} (hT : TopInfo M cr d S C0) {j : Nat}
    (hj : C0.coeff d < j) : GapSep M cr (d + 1) (slot (d + 2) S j) C0 := by
  intro r hr
  rcases side hT hr with ⟨hin, hle, hc⟩ | ⟨hbl, hlt⟩ | ⟨hab, hlt⟩
  · exact ⟨fun _ => bl_slot_of_lt hin (by omega), fun h => absurd hle (not_le.mpr h)⟩
  · exact ⟨fun _ => bl_slot hbl, fun h => absurd (lt_trans hlt h) (lt_irrefl _)⟩
  · exact ⟨fun h => absurd (lt_of_lt_of_le hlt h) (lt_irrefl _), fun _ => ab_slot hab⟩

/-- The slot of the top, with `S = T`, below a higher slot. -/
theorem up_at_top {M : Mountain} {cr d : Nat} {S C0 : Row} (hT : TopInfo M cr d S C0) {j : Nat}
    (hj : C0.coeff d < j) :
    SepUp M cr (d + 1) (slot (d + 2) S (C0.coeff d)) (slot (d + 2) S j) := by
  intro r hr
  rcases side hT hr with ⟨hin, _, hc⟩ | ⟨hbl, _⟩ | ⟨hab, _⟩
  · left
    refine ⟨?_, bl_slot_of_lt hin (by omega)⟩
    rcases Nat.lt_or_eq_of_le hc with h | h
    · exact Or.inr (bl_slot_of_lt hin h)
    · exact Or.inl (in_slot_of_eq hin h)
  · exact Or.inl ⟨Or.inr (bl_slot hbl), bl_slot hbl⟩
  · exact Or.inr ⟨ab_slot hab, ab_slot hab⟩

/-- A top that is a root row in `S` rules out the second form of `Sep`. -/
theorem eq_of_sep {M : Mountain} {cr d : Nat} {S T C0 : Row} (hT : TopInfo M cr d S C0)
    (h : Sep M cr (d + 2) S T) : S = T := by
  rcases h with h | h
  · exact h
  · exfalso
    rcases h C0 hT.root with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_irrefl _ (h1 C0 hT.mem)
    · exact lt_irrefl _ (h1 C0 hT.mem)

/-! ## The invariant for the four kinds of items -/

section Kinds

variable {ctx : Context} {d : Nat}

theorem cinv_plain {S T : Row} (h : Sep ctx.source ctx.rootColumn d S T) :
    CInv ctx d ⟨S, T, none, 0, false⟩ := by
  refine ⟨fun _ _ => h, ?_, ?_, ?_⟩
  · intro _ hb; cases hb
  · intro C hC; cases hC
  · intro C hC; cases hC

theorem cinv_up {S T : Row} (h2 : 2 ≤ d) (h : SepUp ctx.source ctx.rootColumn d S T) :
    CInv ctx d ⟨S, T, none, 0, true⟩ := by
  refine ⟨?_, fun _ _ => ⟨h2, h⟩, ?_, ?_⟩
  · intro _ hb; cases hb
  · intro C hC; cases hC
  · intro C hC; cases hC

theorem cinv_clean {S T C : Row} {o : Nat} (hST : S = T) (h : rootTop ctx d S = some C) :
    CInv ctx d ⟨S, T, some C, o, false⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h'; cases h'
  · intro h'; cases h'
  · intro C' hC _
    cases hC
    exact ⟨hST, h⟩
  · intro C' _ hb; cases hb

theorem cinv_gap {S T C : Row} {o : Nat} (h : GapSep ctx.source ctx.rootColumn d T C) :
    CInv ctx d ⟨S, T, some C, o, true⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h'; cases h'
  · intro h'; cases h'
  · intro C' _ hb; cases hb
  · intro C' hC _
    cases hC
    exact h

theorem sep_slot {M : Mountain} {cr : Nat} {S T : Row} (h : Sep M cr (d + 2) S T) (j : Nat) :
    Sep M cr (d + 1) (slot (d + 2) S j) (slot (d + 2) T j) := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · right
    intro r hr
    rcases h r hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨bl_slot h1, bl_slot h2⟩
    · exact Or.inr ⟨ab_slot h1, ab_slot h2⟩

theorem gapSep_slot {M : Mountain} {cr : Nat} {T C : Row} (h : GapSep M cr (d + 2) T C)
    (j : Nat) : GapSep M cr (d + 1) (slot (d + 2) T j) C := by
  intro r hr
  exact ⟨fun h' => bl_slot ((h r hr).1 h'), fun h' => ab_slot ((h r hr).2 h')⟩

end Kinds

/-! ## The children -/

theorem case2_cinv {ctx : Context} {d : Nat} {S C0 : Row} (hT : TopInfo ctx.source ctx.rootColumn d S C0)
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) S (C0.coeff d)) = some C0)
    {L e : Int} (hL : 1 ≤ L) (he : e = 0 ∨ e = 1) (he0 : e = 0 → 1 ≤ d) (hblk : ctx.block ≠ 0)
    (N : Nat) :
    ∀ c ∈ (List.range N).map (c2 S S C0 d (C0.coeff d) L e ctx.block), CInv ctx (d + 1) c := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  unfold c2
  by_cases h1 : j < C0.coeff d
  · rw [if_pos h1]
    exact cinv_plain (Or.inl rfl)
  · rw [if_neg h1]
    by_cases h2 : (j : Int) < (C0.coeff d : Int) + L + e
    · rw [if_pos h2]
      by_cases h3 : C0.coeff d < j
      · rw [show decide (C0.coeff d < j) = true by simpa using h3]
        exact cinv_gap (gap_above hT h3)
      · rw [show decide (C0.coeff d < j) = false by simpa using h3]
        have hj : j = C0.coeff d := by omega
        subst hj
        exact cinv_clean rfl hinvC0
    · rw [if_neg h2]
      by_cases h3 : (j : Int) = (C0.coeff d : Int) + L
      · have he' : e = 0 := by omega
        have hσ : ((j : Int) - L).toNat = C0.coeff d := by omega
        rw [hσ, show decide (ctx.block ≠ 0 ∧ (j : Int) = (C0.coeff d : Int) + L) = true by
          simpa using ⟨hblk, h3⟩]
        exact cinv_up (by have := he0 he'; omega) (up_at_top hT (by omega))
      · rw [show decide (ctx.block ≠ 0 ∧ (j : Int) = (C0.coeff d : Int) + L) = false by
          simp only [decide_eq_false_iff_not, not_and]; exact fun _ => h3]
        refine cinv_plain (sep_above hT (by omega) (by omega) ?_ (fun _ _ h => h))
        intro r hr hs
        rcases hs with hs | hs
        · exact Or.inr ⟨hs, (side hT hr).elim (fun h => h.2.2)
            (fun h => h.elim (fun h' => absurd (h'.1 r hs) (lt_irrefl _))
              (fun h' => absurd (h'.1 r hs) (lt_irrefl _)))⟩
        · exact Or.inl hs

/-- Case 2 in block `0` (no lift). -/
theorem case2_cinv0 {ctx : Context} {d : Nat} {S C0 : Row}
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) S (C0.coeff d)) = some C0) {e : Int}
    (he : e = 0 ∨ e = 1) (N : Nat) :
    ∀ c ∈ (List.range N).map (c2 S S C0 d (C0.coeff d) 0 e 0), CInv ctx (d + 1) c := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  unfold c2
  by_cases h1 : j < C0.coeff d
  · rw [if_pos h1]
    exact cinv_plain (Or.inl rfl)
  · rw [if_neg h1]
    by_cases h2 : (j : Int) < (C0.coeff d : Int) + 0 + e
    · rw [if_pos h2]
      by_cases h3 : C0.coeff d < j
      · rw [show decide (C0.coeff d < j) = true by simpa using h3]
        exfalso
        omega
      · rw [show decide (C0.coeff d < j) = false by simpa using h3]
        have hj : j = C0.coeff d := by omega
        subst hj
        exact cinv_clean rfl hinvC0
    · rw [if_neg h2]
      rw [show decide ((0 : Nat) ≠ 0 ∧ (j : Int) = (C0.coeff d : Int) + 0) = false by simp]
      have hσ : ((j : Int) - 0).toNat = j := by omega
      rw [hσ]
      exact cinv_plain (Or.inl rfl)

theorem case3_cinv {ctx : Context} {d : Nat} {S T C0 : Row}
    (hT : TopInfo ctx.source ctx.rootColumn d S C0)
    (hup : SepUp ctx.source ctx.rootColumn (d + 2) S T) {hB : Nat} {e : Int}
    (he : e = 0 ∨ e = 1) (he0 : e = 0 → 1 ≤ d) (N : Nat) :
    ∀ c ∈ ((List.range N).filter (fun x => decide (C0.coeff d ≤ x))).map
      (c3 S T C0 d (C0.coeff d) hB e), CInv ctx (d + 1) c := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hjR : C0.coeff d ≤ j := by simpa using (List.mem_filter.mp hj).2
  unfold c3
  by_cases h2 : (j : Int) < (hB : Int) + (C0.coeff d : Int) + e
  · rw [if_pos h2]
    refine cinv_gap ?_
    intro r hr
    rcases hup r hr with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · refine ⟨fun _ => bl_slot h2', fun hlt => ?_⟩
      exfalso
      rcases h1 with h1 | h1
      · exact absurd (hT.max r hr h1) (not_le.mpr hlt)
      · exact lt_irrefl _ (lt_trans hlt (h1 C0 hT.mem))
    · exact ⟨fun hle => absurd (lt_of_le_of_lt hle (h1 C0 hT.mem)) (lt_irrefl _),
        fun _ => ab_slot h2'⟩
  · rw [if_neg h2]
    by_cases h3 : j = hB + C0.coeff d
    · have he' : e = 0 := by omega
      have hσ : j - hB = C0.coeff d := by omega
      rw [hσ, show decide (j = hB + C0.coeff d) = true by simpa using h3]
      refine cinv_up (by have := he0 he'; omega) ?_
      intro r hr
      rcases hup r hr with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · left
        refine ⟨?_, bl_slot h2'⟩
        rcases h1 with h1 | h1
        · have hc := coeff_le_of_le h1 hT.mem (hT.max r hr h1)
          rcases Nat.lt_or_eq_of_le hc with h | h
          · exact Or.inr (bl_slot_of_lt h1 h)
          · exact Or.inl (in_slot_of_eq h1 h)
        · exact Or.inr (bl_slot h1)
      · exact Or.inr ⟨ab_slot h1, ab_slot h2'⟩
    · rw [show decide (j = hB + C0.coeff d) = false by simpa using h3]
      refine cinv_plain (Or.inr ?_)
      intro r hr
      rcases hup r hr with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · left
        refine ⟨?_, bl_slot h2'⟩
        rcases h1 with h1 | h1
        · exact bl_slot_of_lt h1 (by
            have := coeff_le_of_le h1 hT.mem (hT.max r hr h1)
            omega)
        · exact bl_slot h1
      · exact Or.inr ⟨ab_slot h1, ab_slot h2'⟩

theorem case4_cinv {ctx : Context} {d : Nat} {it : Item} {C C0 : Row} (hcl : it.clean = some C)
    (hT : TopInfo ctx.source ctx.rootColumn d it.source C0)
    (hinvC0 : rootTop ctx (d + 1) (slot (d + 2) it.source (C0.coeff d)) = some C0)
    (hI : CInv ctx (d + 2) it) (hCC : it.cutBottom = false → C = C0) {hB : Nat} (N : Nat) :
    ∀ c ∈ (List.range N).map (c4 it.source it.target C d (C0.coeff d) hB it.offset it.cutBottom),
      CInv ctx (d + 1) c := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  unfold c4
  cases hcb : it.cutBottom with
  | true =>
      simp only [if_true]
      exact cinv_gap (gapSep_slot (hI.2.2.2 C hcl hcb) j)
  | false =>
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨hST, _⟩ := hI.2.2.1 C hcl hcb
      have hC := hCC hcb
      subst hC
      by_cases h1 : j < C.coeff d
      · rw [if_pos h1]
        exact cinv_plain (Or.inl (by rw [hST]))
      · rw [if_neg h1]
        by_cases h3 : C.coeff d < j
        · rw [show decide (C.coeff d < j) = true by simpa using h3]
          rw [← hST]
          exact cinv_gap (gap_above hT h3)
        · rw [show decide (C.coeff d < j) = false by simpa using h3]
          have hj : j = C.coeff d := by omega
          subst hj
          exact cinv_clean (by rw [hST]) hinvC0

end OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp
