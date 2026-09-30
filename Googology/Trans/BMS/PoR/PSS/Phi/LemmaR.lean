import Googology.Trans.BMS.PoR.PSS.Phi.Nodes
import Googology.Trans.BMS.PoR.PSS.Phi.CNF
import Googology.Trans.BMS.PoR.PSS.Phi.LogMono

/-!
# Lemma R: `o(N) = ω^{o(𝓛 N)}`

`proof/COMB.md` §7.  For every standard term `N`,

```
o(N) = ω ^ o(𝓛 N),
```

where `o = pairOrdL` (`o(M) = 1 + val (pairTerm M)`, `o(()) = 0`) and `𝓛 N` is
`()` for `N = 1`, `(N)` for epsilon `N`, and `log N` otherwise.  So `o(N)` is an
epsilon number for epsilon `N`, and `o(N) = ω^{o(log N)}` otherwise.

The proof here does not follow the fundamental sequences of COMB §7.  It reads
the order types directly:

* the nodes below `(N)` are the non-increasing lists of standard terms below
  `N`, and `o(y_1 … y_m) = o(y_1) + ⋯ + o(y_m)` (Lemma 5 (a), `ordOf_append`);
* by induction `o(y_i) = ω^{o(𝓛 y_i)}`, and `𝓛` is strictly monotone and onto the
  nodes (`bigL_lt_bigL`, `exists_bigL_eq`), so the exponents `o(𝓛 y_i)` are
  exactly the ordinals below `o(𝓛 N)`;
* the Cantor normal form (`exists_sumOmega`) turns the sums
  `ω^{β_1} + ⋯ + ω^{β_m}` with `β_1 ≥ ⋯ ≥ β_m`, `β_i < o(𝓛 N)`, into exactly the
  ordinals below `ω^{o(𝓛 N)}`.
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Ordinal
open Bijectivity (CTPS)

theorem stdOrd_single' {t : Tm} (h : Std t) : StdOrd [t] := stdOrd_single h

theorem single_lt_single {y N : Tm} (h : y < N) : [y] < [N] :=
  List.cons_lt_cons_iff.mpr (Or.inl h)

/-- The ordinal of a node is the sum of the powers `ω^{o(𝓛 y)}`, given Lemma R
for its terms. -/
theorem ordOf_eq_sumOmega : ∀ {Y : List Tm}, StdOrd Y →
    (∀ y ∈ Y, ordOf [y] = ω ^ ordOf (bigL y)) →
    ordOf Y = sumOmega (Y.map (fun y => ordOf (bigL y)))
  | [], _, _ => by simp [ordOf_nil, sumOmega_nil]
  | y :: Y, hY, h => by
    rw [ordOf_cons hY, h y (by simp), List.map_cons, sumOmega_cons,
      ordOf_eq_sumOmega (stdOrd_of_append_right (A := [y]) hY) (fun y' hy' => h y' (by simp [hy']))]

theorem lt_of_mem_lt_single {Y : List Tm} {N : Tm} (hY : Desc Y) (h : Y < [N]) :
    ∀ y ∈ Y, y < N := by
  cases Y with
  | nil => simp
  | cons y1 Y =>
    have h1 : y1 < N := by
      rcases List.cons_lt_cons_iff.mp h with h | ⟨_, h⟩
      · exact h
      · simp at h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1
    · exact lt_of_le_of_lt ((List.pairwise_cons.mp hY).1 y hy) h1

/-- **Lemma R.**  `o(N) = ω^{o(𝓛 N)}` for every standard term `N`. -/
theorem lemmaR_ordOf (β : Ordinal.{0}) :
    ∀ N : Tm, Std N → ordOf [N] = β → ordOf [N] = ω ^ ordOf (bigL N) := by
  refine WellFoundedLT.induction (motive := fun β => ∀ N : Tm, Std N → ordOf [N] = β →
    ordOf [N] = ω ^ ordOf (bigL N)) β ?_
  intro β ih N hN hβ
  have hN1 := stdOrd_single hN
  have hLN := stdOrd_bigL hN
  -- Lemma R below `N`
  have ihN : ∀ y, Std y → y < N → ordOf [y] = ω ^ ordOf (bigL y) := fun y hy hyN =>
    ih _ (hβ ▸ (ordOf_lt_iff (stdOrd_single hy) hN1).mp (single_lt_single hyN)) y hy rfl
  apply le_antisymm
  · apply le_of_forall_lt
    intro γ hγ
    obtain ⟨Y, hY, rfl⟩ := exists_ordOf_eq hN1 hγ
    have hYN : Y < [N] := (ordOf_lt_iff hY hN1).mpr hγ
    have hY' := (stdOrd_iff Y).mp hY
    have hlt := lt_of_mem_lt_single hY'.1 hYN
    rw [ordOf_eq_sumOmega hY (fun y hy => ihN y (hY'.2 y hy) (hlt y hy))]
    apply sumOmega_lt
    intro b hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact (ordOf_lt_iff (stdOrd_bigL (hY'.2 y hy)) hLN).mp
      (bigL_lt_bigL (hY'.2 y hy) hN (hlt y hy))
  · apply le_of_forall_lt
    intro γ hγ
    obtain ⟨bs, hbs, hbα, rfl⟩ := exists_sumOmega hγ
    -- a node `Y` below `(N)` with exponents `bs`
    have key : ∀ bs : List Ordinal.{0}, bs.Pairwise (fun a b => b ≤ a) →
        (∀ b ∈ bs, b < ordOf (bigL N)) →
        ∃ Y, StdOrd Y ∧ (∀ y ∈ Y, y < N) ∧ Y.map (fun y => ordOf (bigL y)) = bs := by
      intro bs
      induction bs with
      | nil => exact fun _ _ => ⟨[], stdOrd_nil, by simp, rfl⟩
      | cons b bs ihb =>
        intro hp hb
        obtain ⟨Y', hY', hY'N, hY'm⟩ :=
          ihb (List.pairwise_cons.mp hp).2 (fun b' hb' => hb b' (by simp [hb']))
        obtain ⟨X, hX, hXb⟩ := exists_ordOf_eq hLN (hb b (by simp))
        obtain ⟨y, hy, rfl⟩ := exists_bigL_eq hX
        have hyN : y < N := by
          rcases lt_trichotomy y N with h | rfl | h
          · exact h
          · exfalso
            have := hb b (by simp)
            rw [← hXb] at this
            exact lt_irrefl _ this
          · have := (ordOf_lt_iff hLN hX).mp (bigL_lt_bigL hN hy h)
            rw [hXb] at this
            exact absurd (hb b (by simp)) (not_lt.mpr this.le)
        refine ⟨y :: Y', ?_, ?_, ?_⟩
        · rw [stdOrd_iff] at hY' ⊢
          refine ⟨List.pairwise_cons.mpr ⟨fun y' hy' => ?_, hY'.1⟩, fun t ht => ?_⟩
          · by_contra hlt
            push Not at hlt
            have h1 := (ordOf_lt_iff hX (stdOrd_bigL (hY'.2 y' hy'))).mp
              (bigL_lt_bigL hy (hY'.2 y' hy') hlt)
            have h2 : ordOf (bigL y') ∈ bs := by
              rw [← hY'm]; exact List.mem_map.mpr ⟨y', hy', rfl⟩
            have h3 := (List.pairwise_cons.mp hp).1 _ h2
            rw [hXb] at h1
            exact absurd h3 (not_le.mpr h1)
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact hy
            · exact hY'.2 t ht
        · intro y' hy'
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact hyN
          · exact hY'N y' hy'
        · rw [List.map_cons, hY'm, hXb]
    obtain ⟨Y, hY, hYN, hYm⟩ := key bs hbs hbα
    have hY' := (stdOrd_iff Y).mp hY
    rw [← hYm, ← ordOf_eq_sumOmega hY (fun y hy => ihN y (hY'.2 y hy) (hYN y hy))]
    apply (ordOf_lt_iff hY hN1).mp
    cases Y with
    | nil => simp
    | cons y Y => exact List.cons_lt_cons_iff.mpr (Or.inl (hYN y (by simp)))

/-- **Lemma R.**  For every standard term `N`, `o(N) = ω^{o(𝓛 N)}`. -/
theorem lemmaR {N : Tm} (hN : CTPS N.cols) : pairOrdL N.cols = ω ^ pairOrdL (mat (bigL N)) := by
  have := lemmaR_ordOf _ N hN rfl
  rwa [ordOf_single] at this

/-- **Lemma R, non-epsilon case.**  `o(N) = ω^{o(log N)}` for standard `N` that is not
epsilon. -/
theorem lemmaR_log {N : Tm} (hN : CTPS N.cols) (hne : isEps N = false) :
    pairOrdL N.cols = ω ^ pairOrdL (mat (log0 N)) := by
  rw [lemmaR hN]
  unfold bigL
  split_ifs with h1
  · -- `N = 1`: `log N = ()`
    have : log0 N = [] := by unfold log0; rw [h1]; rfl
    rw [this]
  · rw [hne] at *; simp_all
  · rfl

/-- **Lemma R, epsilon case.**  `o(N)` is an epsilon number: `o(N) = ω^{o(N)}`. -/
theorem lemmaR_eps {N : Tm} (hN : CTPS N.cols) (heps : isEps N = true) :
    pairOrdL N.cols = ω ^ pairOrdL N.cols := by
  have := lemmaR hN
  have hb : bigL N = [N] := by
    unfold bigL
    have h1 : N.cs ≠ [] := by
      intro h
      obtain ⟨y, cs⟩ := N
      simp only [Tm.cs_node] at h
      subst h
      rcases y with _ | y <;> simp [isEps] at heps
    simp [h1, heps]
  rw [hb, mat_cons, mat_nil, List.append_nil] at this
  exact this

/-- **`𝓛` is an order embedding** of the standard terms into the nodes (and it is
onto: `exists_bigL_eq`). -/
theorem bigL_lt_iff {s t : Tm} (hs : Std s) (ht : Std t) : s < t ↔ bigL s < bigL t := by
  constructor
  · exact bigL_lt_bigL hs ht
  · intro h
    rcases lt_trichotomy s t with h' | rfl | h'
    · exact h'
    · exact absurd h (lt_irrefl _)
    · exact absurd (lt_trans h (bigL_lt_bigL ht hs h')) (lt_irrefl _)

end Googology.Trans.PSS.Phi
