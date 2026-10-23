import Googology.Trans.PoR.InaccPsi.R2.RyTail

/-!
# `L(ω+1) ≤ ν_C` and `T` from the base change `B_n` at its base point only

`L(ξ) = Nc.ncL S ξ`, `c_n = Bc.bcC S n = L(n+1)`, `B_n = Bc.bcB S n` (the base change on normal forms, defined on
`[0, L(n+2))`, `B_n(L(n+1)) = L(ω)`, `B_n(L(n+2)) = L(ω+1)`, strictly increasing below `L(ω)`, fixing `[0, L(n+1))`,
ONTO-FIN, all Lean-proved in `Bc`), `ν_C` the right end of the first non-standard `<₂`-pair, `T` is `Cx.CxT S`
(`L(ω) ≤₁ L(ω+1)`), CAP-0, CAP-1 as in `Cd.CdCAP0`, `Cd.CdCAP1`.

The SHIFT road (`Qq`, `Bc`) asks EMB₁ and EMB₂ (`B_n` keeps and reflects `≤₁` and `≤₂` on all of `[0, L(n+2))`).
Here only the pairs with the left end at the base point are used:

* `RyRefl2 S n` (**REFLECT-₂ at the base point**): `L(ω) ≤₂ B_n(y)` gives `L(n+1) ≤₂ y` for `L(n+1) < y < L(n+2)`;
* `ryNu_of_refl2` (**CAP-0, CAP-1 below `L(ω+1)` and `RyRefl2` for all `n ≥ N` give `L(ω+1) ≤ ν_C`**): a pair
  `L(ω) <₂ d < L(ω+1)` (from `Rg.rgNu_of_caps`) is pulled back by ONTO-FIN to `L(n+1) <₂ y < L(n+2) < L(ω) ≤ ν_C`
  (`Cd.cdLow`), a standard pair, so `L(n+1)` would be a `τ`-point, but it is a restart;
* `ryRefl2_of_nu`, `ryNu_iff_refl2` (**the converse: under the caps, `L(ω+1) ≤ ν_C ⇔ RyRefl2` from some `N` on**;
  given `L(ω+1) ≤ ν_C` the premise `L(ω) ≤₂ B_n(y)` never holds), `ryNu_road` (UPPER and CapV for the caps);
* `RyKeep1 S n` (**KEEP-₁ at the base point**): `L(n+1) ≤₁ y` gives `L(ω) ≤₁ B_n(y)` for `L(n+1) ≤ y < L(n+2)`;
* `ryT_of_keep1` (**`L(n+1) ≤₁ L(n+2)` and `RyKeep1` for all `n ≥ N` give `T`**: ONTO-FIN and `≤₁` at the limit
  `L(ω+1)`), `ryKeep1_of_T`, `ryT_iff_keep1` (**the converse**).

So the base-point halves of EMB₂ and EMB₁ are each exactly as strong as `L(ω+1) ≤ ν_C` and `T`: under the caps,
no hypothesis about `B_n` at the base point is weaker than the goal.

No new axiom.  New definitions (hypothesis names only): `RyRefl2`, `RyKeep1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ry

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **REFLECT-₂ at the base point** of `B_n`: `L(ω) ≤₂ B_n(y) ⇒ L(n+1) ≤₂ y` for `L(n+1) < y < L(n+2)`. -/
def RyRefl2 (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ y, Bc.bcC S n < y → y < Bc.bcC S (n + 1) → le2 (Nc.ncL S ω) (Bc.bcB S n y) → le2 (Bc.bcC S n) y

/-- **KEEP-₁ at the base point** of `B_n`: `L(n+1) ≤₁ y ⇒ L(ω) ≤₁ B_n(y)` for `L(n+1) ≤ y < L(n+2)`. -/
def RyKeep1 (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∀ y, Bc.bcC S n ≤ y → y < Bc.bcC S (n + 1) → le1 (Bc.bcC S n) y → le1 (Nc.ncL S ω) (Bc.bcB S n y)

/-- `B_n(L(n+1)) = L(ω)`. -/
theorem ryB_base (n : ℕ) : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base n

/-- `L(n+1) < y < L(n+2)` gives `L(ω) < B_n(y) < L(ω+1)`. -/
theorem ryB_window {n : ℕ} {y : Ordinal.{0}} (hy1 : Bc.bcC S n < y) (hy2 : y < Bc.bcC S (n + 1)) :
    Nc.ncL S ω < Bc.bcB S n y ∧ Bc.bcB S n y < Nc.ncL S (ω + 1) := by
  refine ⟨?_, Bc.bcB_bound' S n y hy2⟩
  have h := (Bc.bcB_lt_iff (S := S) (k := n) (Bc.bcC_lt S n) (hy2.trans (Bc.bcC_lt S (n + 1)))).2 hy1
  rwa [ryB_base] at h

/-- A preimage `y < L(n+2)` of a point `z ≥ L(ω)` is `≥ L(n+1)`, and `> L(n+1)` when `z > L(ω)`. -/
theorem ryB_pre {n : ℕ} {y : Ordinal.{0}} (hy2 : y < Bc.bcC S (n + 1)) :
    (Nc.ncL S ω ≤ Bc.bcB S n y → Bc.bcC S n ≤ y) ∧ (Nc.ncL S ω < Bc.bcB S n y → Bc.bcC S n < y) := by
  have hiff := Bc.bcB_lt_iff (S := S) (k := n) (hy2.trans (Bc.bcC_lt S (n + 1))) (Bc.bcC_lt S n)
  have hiff' := Bc.bcB_lt_iff (S := S) (k := n) (Bc.bcC_lt S n) (hy2.trans (Bc.bcC_lt S (n + 1)))
  rw [ryB_base] at hiff hiff'
  refine ⟨fun h => ?_, fun h => hiff'.1 h⟩
  by_contra hlt
  push Not at hlt
  exact absurd (hiff.2 hlt) (not_lt.2 h)

/-- CAP-1 below `X` gives CAP-1 below every `X' ≤ X`. -/
theorem ryCAP1_mono {X X' : Ordinal.{0}} (h : CdCAP1 S X) (hX : X' ≤ X) : CdCAP1 S X' :=
  fun l hl hB hm hl' hc => h l hl hB hm (hl'.trans_le hX) hc

/-- **CAP-0, CAP-1 below `L(ω+1)` and REFLECT-₂ at the base point from some `N` on give `L(ω+1) ≤ ν_C`.** -/
theorem ryNu_of_refl2 (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1)))
    (hR : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RyRefl2 S n) : Nc.ncL S (ω + 1) ≤ nuC := by
  by_contra hlt
  have hnp : ¬ Rg.RgLwPair S := fun hp => hlt (Rg.rgNu_of_caps h0 h1 hp)
  unfold Rg.RgLwPair at hnp
  push Not at hnp
  obtain ⟨d, hd1, hd2, hd2', -⟩ := hnp
  obtain ⟨N, hN⟩ := hR
  have hdY : ∀ y ∈ ({d} : Finset Ordinal.{0}), Nc.ncL S ω ≤ y ∧ y < Nc.ncL S (ω + 1) := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨hd1.le, hd2⟩
  obtain ⟨n, hNn, hY⟩ := Bc.bcOnto' S {d} hdY N
  obtain ⟨y, hy2, hyd⟩ := hY d (Finset.mem_singleton_self d)
  have hy1 : Bc.bcC S n < y := (ryB_pre hy2).2 (by rw [hyd]; exact hd1)
  have h2 : le2 (Bc.bcC S n) y := hN n hNn y hy1 hy2 (by rw [hyd]; exact hd2')
  have hLν : Nc.ncL S ω ≤ nuC := cdLow h0 (ryCAP1_mono h1 (Qq.qqL_lt_succ S).le)
  have hyν : y < nuC := (hy2.trans (Bc.bcC_lt S (n + 1))).trans_le hLν
  obtain ⟨l, hl, hle⟩ := Pp.ppL_succ_restart (S := S) n
  have htau : Nc.NcTauPt (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := Nc.ncStd_tau (std_of_lt_nuC hyν hy1 h2)
  rw [hle] at htau
  exact Nc.ncRestart_not_tau hl htau

/-- **`L(ω+1) ≤ ν_C` gives REFLECT-₂ at every base point** (its premise never holds). -/
theorem ryRefl2_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) (n : ℕ) : RyRefl2 S n := by
  intro y hy1 hy2 h2
  exfalso
  obtain ⟨hB1, hB2⟩ := ryB_window hy1 hy2
  exact Lw.lw_not_tau_L_omega S (Nc.ncStd_tau (std_of_lt_nuC (hB2.trans_le hν) hB1 h2))

/-- **Under CAP-0, CAP-1 below `L(ω+1)`: `L(ω+1) ≤ ν_C ⇔` REFLECT-₂ at the base point from some `N` on.** -/
theorem ryNu_iff_refl2 (h0 : CdCAP0 S) (h1 : CdCAP1 S (Nc.ncL S (ω + 1))) :
    Nc.ncL S (ω + 1) ≤ nuC ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RyRefl2 S n :=
  ⟨fun hν => ⟨0, fun n _ => ryRefl2_of_nu hν n⟩, ryNu_of_refl2 h0 h1⟩

/-- **`L(ω+1) ≤ ν_C` from UPPER, CapV and REFLECT-₂ at the base point.** -/
theorem ryNu_road (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hR : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RyRefl2 S n) : Nc.ncL S (ω + 1) ≤ nuC :=
  ryNu_of_refl2 (Rg.rgCAP_of_enum hU hV hVt).1 (Rg.rgCAP_of_enum hU hV hVt).2 hR

/-- **`L(n+1) ≤₁ L(n+2)` and KEEP-₁ at the base point from some `N` on give `T`.** -/
theorem ryT_of_keep1 (h12 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → le1 (Bc.bcC S n) (Bc.bcC S (n + 1)))
    (hK : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RyKeep1 S n) : Cx.CxT S := by
  obtain ⟨N1, h1⟩ := h12
  obtain ⟨N2, h2⟩ := hK
  refine le1_limit (Lw.lw_L_SC S _).isSuccLimit (Qq.qqL_lt_succ S) fun z hz1 hz2 => ?_
  have hzY : ∀ y ∈ ({z} : Finset Ordinal.{0}), Nc.ncL S ω ≤ y ∧ y < Nc.ncL S (ω + 1) := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨hz1, hz2⟩
  obtain ⟨n, hNn, hY⟩ := Bc.bcOnto' S {z} hzY (max N1 N2)
  obtain ⟨y, hy2, hyz⟩ := hY z (Finset.mem_singleton_self z)
  have hy1 : Bc.bcC S n ≤ y := (ryB_pre hy2).1 (by rw [hyz]; exact hz1)
  have hle1 : le1 (Bc.bcC S n) y := le1_of_le_of_le1 hy1 hy2.le (h1 n (le_of_max_le_left hNn))
  have h := h2 n (le_of_max_le_right hNn) y hy1 hy2 hle1
  rwa [hyz] at h

/-- **`T` gives KEEP-₁ at every base point.** -/
theorem ryKeep1_of_T (hT : Cx.CxT S) (n : ℕ) : RyKeep1 S n := by
  intro y hy1 hy2 _
  have hlo : Nc.ncL S ω ≤ Bc.bcB S n y := by
    rcases hy1.lt_or_eq with h | h
    · exact (ryB_window h hy2).1.le
    · rw [← h, ryB_base]
  exact le1_of_le_of_le1 hlo (Bc.bcB_bound' S n y hy2).le hT

/-- **Given `L(n+1) ≤₁ L(n+2)` from some `N` on: `T ⇔` KEEP-₁ at the base point from some `N` on.** -/
theorem ryT_iff_keep1 (h12 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cx.CxT S ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RyKeep1 S n :=
  ⟨fun hT => ⟨0, fun n _ => ryKeep1_of_T hT n⟩, ryT_of_keep1 h12⟩

end Googology.Trans.PoR.InaccPsi.R2.Ry
