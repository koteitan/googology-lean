import Googology.Trans.DBMS.ThreeRowUpperRPShape

/-!
# `T3nRankDescRPInner`, reduced to one step of standard forms

`ThreeRowUpperNCLast.lean` reduces the upper bound
`rkL 2 (cgen 2 4) ≤ rkL 2 (bgen3 2)` to `RPLastShape` and
`T3nRankDescRPInner`; `ThreeRowUpperRPShape.lean` proves `RPLastShape`.
This file reduces `T3nRankDescRPInner`, a statement about ranks, to a
statement about the trio fragment only:

    T3nInnerStd :  for a reached C in the shape RaisedPar whose column n - 2 is
                   not raisable, if t3n C is in TrioStdL then so is every
                   t3n (C[N + 1]).

**What is proved.**

* `sReach_t3nStd`: under `T3nInnerStd`, `t3n C ∈ TrioStdL` for every reached
  `C`.  By induction on `SReach`: at the start `t3n` gives a trio generator;
  outside `RaisedPar`, `t3n (C[N]) = (t3n C)[N]`; when the raisable parent is
  the column `n - 2`, `t3n (C[N])` is `S₀[N + 1]` or `W[N]` with `W` a prefix of
  `S₀[1]`, `S₀ = (t3n C)[0]` (the equalities of `ThreeRowUpperNCLast.lean`, with
  `RPLastShape`), and the trio fragment is closed under prefixes
  (`trioStdL_prefix'`); at `N = 0`, `t3n (C[0]) = (t3n C)[0]`.
* `t3n_expand_lt_of_inner`: when the raisable parent `y` is not `n - 2`,
  `t3n (C[N + 1]) < t3n C` in the dictionary order.  The two agree on the first
  `n - 1` columns, and at column `n - 1` the expansion has the copy
  `(z₀, z₁, 0)` of `y` where `t3n C` has the last column `(z₀, z₁, z₂)`,
  `z₂ ≥ 1`.
* `t3nRankDescRPInner_of_innerStd`: `T3nInnerStd → T3nRankDescRPInner`, by the
  two facts and `rkL_lt_of_trio`.
* `rkL_cgen_two_four_eq_of_innerStd`: under `T3nInnerStd`,
  `rkL 2 (cgen 2 4) = rkL 2 (bgen3 2)`.

**Open.**  `T3nInnerStd`.  Numerically (scripts outside the library) every
`t3n C` with `C` reached (breadth-first from `lift 3 (trioGen v)`) has an
explicit path of expansions from a trio generator, which is more than
`T3nInnerStd` needs.
-/

namespace Googology.Trans.DBMS

open Ordinal Order
open Googology.Trans.BMS
open Googology.Trans.BMS.TrioCofinal (trioGen TrioStdL)
open Classical

/-! ### Prefixes of the trio fragment -/

/-- The trio fragment is closed under prefixes. -/
theorem trioStdL_prefix' : ∀ (m l : List (List Nat)), TrioStdL (l ++ m) → TrioStdL l := by
  intro m
  induction m with
  | nil => intro l h; rwa [List.append_nil] at h
  | cons c m ih =>
    intro l h
    have h1 : TrioStdL (l ++ [c]) := ih (l ++ [c]) (by rwa [List.append_assoc])
    have h2 := TrioStdL.step 0 h1
    rwa [expandRL_zero 3 _ (valid_trioStdL h1), List.dropLast_concat] at h2

theorem trioStdL_take {l : List (List Nat)} (h : TrioStdL l) (m : Nat) : TrioStdL (l.take m) :=
  trioStdL_prefix' (l.drop m) _ (by rwa [List.take_append_drop])

/-! ### The open step -/

/-- **Open.**  One expansion step of the shape `RaisedPar` with the raisable
parent before the column `n - 2` stays in the trio fragment after `t3n`. -/
def T3nInnerStd : Prop :=
  ∀ C, SReach C → RaisedPar C → ¬ Rz C (C.length - 2) → TrioStdL (t3n C) →
    ∀ N, TrioStdL (t3n (expandRL 3 (N + 1) C))

/-- Every `t3n C` of a reached matrix is in the trio fragment. -/
def T3nStd : Prop := ∀ C, SReach C → TrioStdL (t3n C)

/-! ### The raisable parent is the column before the last -/

/-- **When the raisable parent is the column `n - 2`, the trio fragment is
kept.** -/
theorem t3nStd_last {C : List (List Nat)} (hC : SReach C) (hy : Rz C (C.length - 2))
    (ih : TrioStdL (t3n C)) (N : Nat) : TrioStdL (t3n (expandRL 3 N C)) := by
  have hv := hC.valid
  have hl := hy.1
  have hvS := valid_t3n hv
  have hS0 : TrioStdL (t3n C).dropLast := by
    rw [← expandRL_zero 3 (t3n C) hvS]; exact TrioStdL.step 0 ih
  obtain ⟨x, hx⟩ := exists_ParR1_of_sReach hC (j := C.length - 2) (by omega)
    (by rw [hy.2.1]; omega)
  have hxy := ParR_lt hx
  obtain ⟨a, ha⟩ : ∃ a, (C[C.length - 2]!)[0]! = a := ⟨_, rfl⟩
  by_cases hx1 : x + 1 = C.length - 2
  · rw [t3n_expandRL_eq_dropLast_expand hC hy hx hx1 N]
    exact TrioStdL.step _ hS0
  · have hR : Rz C (x + 1) := (rPLastShape C hC hy x hx).resolve_left hx1
    obtain ⟨hWlen, hWlow, hWy, hWz⟩ :=
      take_dropLast_expand_one hC hy hx (by omega) hR ha
    obtain ⟨W, hW⟩ : ∃ W, W = (expandRL 3 1 (t3n C).dropLast).take C.length := ⟨_, rfl⟩
    rw [← hW] at hWlen hWlow hWy hWz
    have hvS0 : Valid 2 (t3n C).dropLast := valid_dropLast hvS
    have hvW : Valid 2 W := by rw [hW]; exact valid_take (valid_expandRL hvS0 1) _
    have hWstd : TrioStdL W := by rw [hW]; exact trioStdL_take (TrioStdL.step 1 hS0) _
    have hRz : Rz W (W.length - 2) := by
      rw [hWlen]
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hWy]; rfl
      · rw [hWy]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz, hWy]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz]; rfl
      · rw [show C.length - 2 + 1 = C.length - 1 from by omega, hWz]; rfl
    have hWa : (W[W.length - 2]!)[0]! = a := by rw [hWlen, hWy]; rfl
    have hWt : W.take (C.length - 2) = (t3n C).take (C.length - 2) := by
      apply ext_getElem!' (by rw [List.length_take, List.length_take, hWlen, t3n_length])
      intro i hi
      rw [List.length_take, hWlen] at hi
      rw [getElem!_take_of_lt _ (by omega), getElem!_take_of_lt _ (by omega),
        hWlow i (by omega)]
    have hWN : expandRL 3 N W = t3n (expandRL 3 N C) := by
      rw [t3n_expandRL_of_Rz_last hv hy ha N, expandRL_of_Rz_last hvW hRz N, hWa, hWlen, hWt]
    rw [← hWN]
    exact TrioStdL.step N hWstd

/-- **Under `T3nInnerStd`, every `t3n C` of a reached matrix is in the trio
fragment.** -/
theorem sReach_t3nStd (hI : T3nInnerStd) : T3nStd := by
  intro C h
  induction h with
  | gen v =>
    rw [expandRL_cgen_two_four, t3n_lift_trioGen]
    exact TrioStdL.gen _
  | @step C N hC ih =>
    by_cases hnp : RaisedPar C
    · by_cases hy : Rz C (C.length - 2)
      · exact t3nStd_last hC hy ih N
      · cases N with
        | zero =>
          have hv := hC.valid
          rw [expandRL_zero 3 C hv, t3n_dropLast hy,
            ← expandRL_zero 3 (t3n C) (valid_t3n hv)]
          exact TrioStdL.step 0 ih
        | succ N => exact hI C hC hnp hy ih N
    · rw [← expandRL_t3n_of_sReach hC hnp N]
      exact TrioStdL.step N ih

/-! ### The dictionary order -/

theorem lt_of_getElem! : ∀ (k : Nat) (l l' : List (List Nat)), k < l.length → k < l'.length →
    (∀ i, i < k → l[i]! = l'[i]!) → l[k]! < l'[k]! → l < l'
  | _, [], _, h1, _, _, _ => by simp at h1
  | _, _ :: _, [], _, h2, _, _ => by simp at h2
  | 0, a :: l, b :: l', _, _, _, h => List.cons_lt_cons_iff.mpr (Or.inl (by simpa using h))
  | k + 1, a :: l, b :: l', h1, h2, he, h => by
      have e0 := he 0 (by omega)
      simp only [List.getElem!_cons_zero] at e0
      subst e0
      refine List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt_of_getElem! k l l' (by simpa using h1)
        (by simpa using h2) (fun i hi => ?_) (by simpa using h)⟩)
      have := he (i + 1) (by omega)
      simpa using this

/-- The columns before `n - 1` of an expansion are those of the list. -/
theorem expandRL_get_low {C : List (List Nat)} {r : Nat} (hb : badRootR 3 C = some r) (N : Nat)
    {m k : Nat} (hm : m < C.length - 1) (hk : k < 3) :
    ((expandRL 3 N C)[m]!)[k]! = (C[m]!)[k]! := by
  rcases Nat.lt_or_ge m r with hmr | hmr
  · rw [expandRL_get_pre hb N hmr]
  · have e := expandRL_get_cpos (N := N) hb rfl (q := 0) (Nat.zero_le _) (s := m - r)
      (by omega) k hk
    rw [Nat.zero_mul, Nat.zero_add, show r + (m - r) = m from by omega] at e
    rw [e]; simp

/-- **When the raisable parent is not the column `n - 2`, `t3n` goes down in
the dictionary order with every expansion `[N + 1]`.** -/
theorem t3n_expand_lt_of_inner {C : List (List Nat)} (hC : SReach C) (hR : RaisedPar C)
    (hy : ¬ Rz C (C.length - 2)) (N : Nat) : t3n (expandRL 3 (N + 1) C) < t3n C := by
  obtain ⟨y, hyp, hyR⟩ := hR
  have hv := hC.valid
  have hL2 := low2_of_sReach hC
  have hyl := ParR_lt hyp
  have hne : C ≠ [] := by rintro rfl; simp at hyl
  have hm : m0L 3 C = 2 := by
    have hs : (parAtR C 2 (C.length - 1)).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨y, (parAtR_eq_some _ _ _ _).mpr hyp⟩
    rw [m0L]; exact Nat.findGreatest_eq hs
  have hb : badRootR 3 C = some y := by
    rw [badRootR, if_neg (by simpa [List.isEmpty_iff] using hne), hm]
    exact (parAtR_eq_some _ _ _ _).mpr hyp
  have hyn : y ≠ C.length - 2 := fun e => hy (e ▸ hyR)
  obtain ⟨_, hT1, hlt2, _⟩ := (ParR_two_iff' C y _).mp hyp
  have hz1 : (C[y]!)[1]! < (C[C.length - 1]!)[1]! := AncR_entry_lt hT1
  have hz0 : (C[y]!)[0]! < (C[C.length - 1]!)[0]! :=
    AncR_entry_lt (AncR_zero_of (k := 1) hT1)
  have hy2 : (C[y]!)[2]! = 0 := hyR.2.2.1
  have hz2 : 1 ≤ (C[C.length - 1]!)[2]! := by omega
  have hz1' : 2 ≤ (C[C.length - 1]!)[1]! := by
    by_contra hc; have := hL2 (C.length - 1) (by omega); omega
  set D := expandRL 3 (N + 1) C with hD
  have hlen : D.length = y + (N + 1 + 1) * (C.length - 1 - y) := expandRL_length_some hb _
  have hL2' : C.length - 1 - y ≤ (N + 1) * (C.length - 1 - y) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hDlen : C.length - 1 < D.length := by
    rw [hlen, Nat.add_mul, Nat.one_mul]; omega
  have hvD : Valid 2 D := valid_expandRL hv _
  -- the column `n - 1` of the expansion
  have hDz : ∀ k, k < 3 → (D[C.length - 1]!)[k]! =
      if k < 2 then (C[C.length - 1]!)[k]! else 0 := by
    intro k hk
    have e := expandRL_get_cpos (N := N + 1) hb rfl (q := 1) (by omega) (s := 0) (by omega) k hk
    simp only [Nat.one_mul, Nat.add_zero] at e
    rw [show y + (C.length - 1 - y) = C.length - 1 from by omega] at e
    rw [← hD] at e
    rw [e, hm]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    · rw [if_pos (by simp), if_pos (by omega)]; omega
    · rw [if_pos (by simp), if_pos (by omega)]; omega
    · rw [if_neg (by omega), if_neg (by omega), hy2]
  have hnRz : ¬ Rz D (C.length - 2) := by
    intro h
    have := h.2.2.2.2.2
    rw [show C.length - 2 + 1 = C.length - 1 from by omega, hDz 2 (by omega)] at this
    simp at this
  have hnRz' : ¬ Rz D (C.length - 1) := by
    intro h
    have := h.2.1
    rw [hDz 1 (by omega), if_pos (by omega)] at this
    omega
  apply lt_of_getElem! (C.length - 1) _ _ (by rw [t3n_length]; exact hDlen)
    (by rw [t3n_length]; omega)
  · intro i hi
    have hcol : D[i]! = C[i]! :=
      col_ext3 (hvD _ (getElem!_mem _ i (by omega))) (hv _ (getElem!_mem _ i (by omega)))
        (fun k hk => expandRL_get_low hb _ hi hk)
    rw [t3n_get (by omega), t3n_get (by omega), hcol]
    by_cases hi2 : i + 1 < C.length - 1
    · have hiff : Rz D i ↔ Rz C i :=
        Rz_congr (fun m k hm hk => expandRL_get_low hb _ (by omega) hk) (by omega) (by omega)
      by_cases hRi : Rz C i
      · rw [if_pos (hiff.mpr hRi), if_pos hRi]
      · rw [if_neg (fun h => hRi (hiff.mp h)), if_neg hRi]
    · rw [show i = C.length - 2 from by omega, if_neg hnRz, if_neg hy]
  · rw [t3n_get_of_not hnRz', t3n_get_of_not (not_Rz_last C)]
    have e1 : D[C.length - 1]! = [(C[C.length - 1]!)[0]!, (C[C.length - 1]!)[1]!, 0] := by
      apply col_ext3 (hvD _ (getElem!_mem _ _ hDlen)) rfl
      intro k hk
      rw [hDz k hk]
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl <;> rfl
    have e2 : C[C.length - 1]! = [(C[C.length - 1]!)[0]!, (C[C.length - 1]!)[1]!,
        (C[C.length - 1]!)[2]!] := by
      apply col_ext3 (hv _ (getElem!_mem _ _ (by omega))) rfl
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl <;> rfl
    rw [e1, e2]
    exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr
      (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl (by omega))⟩)⟩)

/-! ### The reduction -/

/-- **`T3nInnerStd` gives `T3nRankDescRPInner`.** -/
theorem t3nRankDescRPInner_of_innerStd (hI : T3nInnerStd) : T3nRankDescRPInner :=
  fun C hC hR hy N => rkL_lt_of_trio (sReach_t3nStd hI C hC)
    (sReach_t3nStd hI _ (hC.step (N + 1))) (t3n_expand_lt_of_inner hC hR hy N)

/-- **The upper bound at `n = 2` under `T3nInnerStd`**: the DBMS content
`(0,0,0)(1,1,0)(2,2,1)(3,3,2)` and the BMS matrix `(0,0,0)(1,1,1)(2,2,2)` have
the same rank. -/
theorem rkL_cgen_two_four_eq_of_innerStd (hI : T3nInnerStd) :
    rkL 2 (cgen 2 4) = rkL 2 (bgen3 2) :=
  rkL_cgen_two_four_eq_of_last rPLastShape (t3nRankDescRPInner_of_innerStd hI)

end Googology.Trans.DBMS

#print axioms Googology.Trans.DBMS.sReach_t3nStd
#print axioms Googology.Trans.DBMS.t3n_expand_lt_of_inner
#print axioms Googology.Trans.DBMS.t3nRankDescRPInner_of_innerStd
#print axioms Googology.Trans.DBMS.rkL_cgen_two_four_eq_of_innerStd
