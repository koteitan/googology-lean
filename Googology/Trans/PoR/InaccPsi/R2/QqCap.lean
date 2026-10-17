import Googology.Trans.PoR.InaccPsi.R2.QqShift
import Googology.Trans.PoR.InaccPsi.R2.SHDeep
import Googology.Trans.PoR.InaccPsi.R2.NcCPB

/-!
# (Q) and the reach of `a` from the data of SHIFT

Data of SHIFT as in `R2.QqShift` (`c`, `B`, (C1), (EMB), (ONTO-FIN)), with `a < b`.

* `qqNest_below`: every `k`-nest (`k ≥ 1`) with its points in `[a, b)` has a copy (a `k`-nest)
  with top below `a` (pull it back by `B n`; `B n` reflects `<` and `≤₂`);
* `qqTw_le`: if `a ≤₁ g` for some `g > b`, then `T_ω ≤ a`: by DEEP (`shDeep`) `(a, b)` is the outer
  pair of a `(k+1)`-nest for every `k`; its inner `k`-nest lies in `(a, b)` and is copied below `a`,
  so `T_k < a` for every `k`;
* `qqQ` (**(Q) from SHIFT, CAP form**): if `a < T_ω`, then no `g > b` has `a ≤₁ g`; `qqReach`:
  `lh(a) = b`; `qqCap`: for `g ≥ a`, `a ≤₁ g ⇔ g ≤ b`; `qqQ_succ`: (Q) `¬ a ≤₁ b + 1`;
* `qqQ_of_le_nuC`: the same when `a ≤ ν_C` (`ν_C = T₂ < T_ω`);
* `qqNu_le`: if `a` is not a `τ`-point, `ν_C ≤ b` (the pair `a <₂ b` is not standard);
  `qqNu_eq`: if moreover `a ≤ ν_C`, then `ν_C = b` (CAP at `ν_C`, `nuC_cap`).

No new axiom; the axioms are those of the repo lemmas on `T_k` (`C09_cor15_15`, `C09_nestk`,
`C09_thm14_10`) and, for `qqNu_le`, of `ncPair_bound`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Qq

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nc

/-- `ν_C < T_ω` (`ν_C = T₂`). -/
theorem qqNuC_lt_Tw : nuC < shTw := by
  have h := shTk_lt_Tw 1
  rwa [show Tk (1 + 1) = nuC from Tk_two] at h

section Cap

variable {a b : Ordinal.{0}} {c : ℕ → Ordinal.{0}} {B : ℕ → Ordinal.{0} → Ordinal.{0}}
  (hmono : Monotone c) (hca : ∀ n, c n < a) (hcof : ∀ γ < a, ∃ n, γ < c n)
  (hc1 : ∀ n, le1 (c (n + 1)) a) (hlt : a < b)
  (hBm : ∀ n, StrictMonoOn (B n) (Set.Iio (c (n + 1))))
  (hBb : ∀ n, ∀ x < c (n + 1), B n x < b)
  (hBadd : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), ∀ z < c (n + 1),
    (x + y = z ↔ B n x + B n y = B n z))
  (hB1 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le1 x y ↔ le1 (B n x) (B n y)))
  (hB2 : ∀ n, ∀ x < c (n + 1), ∀ y < c (n + 1), (le2 x y ↔ le2 (B n x) (B n y)))
  (hBcl : ∀ n, Closed (B n '' Set.Iio (c (n + 1))))
  (hfix : ∀ n, ∀ x < c n, B n x = x)
  (honto : ∀ Y : Finset Ordinal.{0}, (∀ y ∈ Y, a ≤ y ∧ y < b) → ∀ N, ∃ n, N ≤ n ∧
    ∀ y ∈ Y, ∃ y' < c (n + 1), B n y' = y)

include hca hBm hB2 honto in
/-- A `k`-nest in `[a, b)` has a copy with top below `a`. -/
theorem qqNest_below {k : ℕ} (hk : 1 ≤ k) {p q : ℕ → Ordinal.{0}} (hN : NestSeq k p q)
    (hin : ∀ z ∈ nestPts k p q, a ≤ z ∧ z < b) :
    ∃ p' q', NestSeq k p' q' ∧ q' 0 < a := by
  classical
  obtain ⟨n, -, hn⟩ := honto (nestPts k p q) hin 0
  let g : Ordinal.{0} → Ordinal.{0} := fun z =>
    if hz : ∃ y' < c (n + 1), B n y' = z then Classical.choose hz else 0
  have hg : ∀ z ∈ nestPts k p q, g z < c (n + 1) ∧ B n (g z) = z := by
    intro z hz
    have hex := hn z hz
    simp only [g, dif_pos hex]
    exact Classical.choose_spec hex
  have hgm : StrictMonoOn g (↑(nestPts k p q) : Set Ordinal.{0}) := by
    intro x hx y hy hxy
    refine ((hBm n).lt_iff_lt (Set.mem_Iio.2 (hg x hx).1) (Set.mem_Iio.2 (hg y hy).1)).1 ?_
    rw [(hg x hx).2, (hg y hy).2]; exact hxy
  have hg2 : ∀ x ∈ (↑(nestPts k p q) : Set Ordinal.{0}),
      ∀ y ∈ (↑(nestPts k p q) : Set Ordinal.{0}), le2 x y → le2 (g x) (g y) := by
    intro x hx y hy hr
    refine (hB2 n (g x) (hg x hx).1 (g y) (hg y hy).1).2 ?_
    rw [(hg x hx).2, (hg y hy).2]; exact hr
  exact ⟨_, _, hN.map hgm hg2, (hg (q 0) (hN.b_mem (by omega))).1.trans (hca (n + 1))⟩

include hca hBm hB2 honto in
/-- If `a <₂ b` and `a ≤₁ g` for some `g > b`, then `T_ω ≤ a`. -/
theorem qqTw_le (hab : a < b) (h2 : le2 a b) {g : Ordinal.{0}} (hbg : b < g) (hag : le1 a g) :
    shTw ≤ a := by
  refine ciSup_le fun m => ?_
  obtain ⟨p, q, hN, hp, hq⟩ := shDeep hab h2 hbg hag (m + 1)
  have hT := hN.tail
  have hp1 : a < p 1 := hp ▸ (hN.1 0 (by omega)).1
  have hq1 : q 1 < b := hq ▸ (hN.1 0 (by omega)).2
  have hin : ∀ z ∈ nestPts (m + 1) (fun i => p (i + 1)) (fun i => q (i + 1)), a ≤ z ∧ z < b :=
    fun z hz => ⟨hp1.le.trans (hT.bounds hz).1, lt_of_le_of_lt (hT.bounds hz).2 hq1⟩
  obtain ⟨p', q', hN', hq'⟩ := qqNest_below hca hBm hB2 honto (by omega) hT hin
  exact (Tk_le hN').trans hq'.le

include hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto

/-- **(Q) from SHIFT, CAP form**: if `a < T_ω`, no `g > b` has `a ≤₁ g`. -/
theorem qqQ (hTw : a < shTw) : ∀ g, b < g → ¬ le1 a g := by
  intro g hbg hag
  have h2 := qqShift hmono hca hcof hc1 hlt.le hBm hBb hBadd hB1 hB2 hBcl hfix honto
  exact absurd (qqTw_le hca hBm hB2 honto hlt h2 hbg hag) (not_le.2 hTw)

/-- `lh(a) = b` when `a < T_ω`. -/
theorem qqReach (hTw : a < shTw) : IsReach R2C a b :=
  ⟨qqShift_le1 hmono hca hcof hc1 hlt.le hBm hBb hBadd hB1 hB2 hBcl hfix honto, fun g hg =>
    not_lt.1 fun h => qqQ hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw g h hg⟩

/-- **CAP at `a`**: when `a < T_ω`, for `g ≥ a`, `a ≤₁ g ⇔ g ≤ b`. -/
theorem qqCap (hTw : a < shTw) {g : Ordinal.{0}} (hag : a ≤ g) : le1 a g ↔ g ≤ b := by
  have hr := qqReach hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw
  exact ⟨hr.2 g, fun hgb => le1_of_le_of_le1 hag hgb hr.1⟩

/-- **(Q)** at `(a, b)`: `¬ a ≤₁ b + 1`, when `a < T_ω`. -/
theorem qqQ_succ (hTw : a < shTw) : ¬ le1 a (b + 1) :=
  qqQ hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto hTw (b + 1)
    (Order.lt_add_one_iff.2 le_rfl)

/-- **(Q)** at `(a, b)` when `a ≤ ν_C`. -/
theorem qqQ_of_le_nuC (hν : a ≤ nuC) : ¬ le1 a (b + 1) :=
  qqQ_succ hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto
    (lt_of_le_of_lt hν qqNuC_lt_Tw)

/-- If `a` is not a `τ`-point, `ν_C ≤ b`. -/
theorem qqNu_le (hτ : ¬ NcTauPt a) : nuC ≤ b :=
  ncPair_bound hlt (qqShift hmono hca hcof hc1 hlt.le hBm hBb hBadd hB1 hB2 hBcl hfix honto) hτ

/-- If `a` is not a `τ`-point and `a ≤ ν_C`, then `ν_C = b`. -/
theorem qqNu_eq (hτ : ¬ NcTauPt a) (hν : a ≤ nuC) : nuC = b := by
  refine le_antisymm (qqNu_le hmono hca hcof hc1 hlt hBm hBb hBadd hB1 hB2 hBcl hfix honto hτ) ?_
  by_contra h
  exact nuC_cap a hν b (not_le.1 h)
    (qqShift_le1 hmono hca hcof hc1 hlt.le hBm hBb hBadd hB1 hB2 hBcl hfix honto)

end Cap

end Googology.Trans.PoR.InaccPsi.R2.Qq
