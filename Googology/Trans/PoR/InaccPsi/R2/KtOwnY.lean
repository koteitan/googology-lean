import Googology.Trans.PoR.InaccPsi.R2.KtOwn

/-!
# Kt: THE OWNERSHIP RELATIVE TO A TARGET `Y` (the plateau `Kg.kgPlat` with `G(κ)` replaced by any `Y`)

`KtGapY Y G C x`: every member `e ∈ C` below `Y` lies below `G(q + 1)` for some `q < x`.  With `Y = G(κ)` it is
`Kg.KgGap`; with `Y = sup_{v<κ} G(v)` it holds for contexts that are not continuous at `κ` (e.g. `φ(·, q + 1)`).

* `ktKeyY`, `ktPlatY` (**`ψ_κ(Y) ≤ sup_n x_n`**), `ktOwnY` (**every `u < ψ_κ(Y)` has `u < ψ_κ(G(u))`**),
  `ktGapY_of` (`KgGap` gives `KtGapY` below `G(κ)`).

No new axiom.  New definition: `KtGapY`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Kg

variable {S : InaccSeq.{0}}

/-- **The gap toward a target `Y`.** -/
def KtGapY (Y : Ordinal.{0}) (G : Ordinal.{0} → Ordinal.{0}) (C : Set Ordinal.{0}) (x : Ordinal.{0}) : Prop :=
  ∀ e ∈ C, e < Y → ∃ q, q < x ∧ e < G (q + 1)

theorem ktGapY_of {κ Y : Ordinal.{0}} {G : Ordinal.{0} → Ordinal.{0}} {C : Set Ordinal.{0}} {x : Ordinal.{0}}
    (hY : Y ≤ G κ) (hg : KgGap κ G C x) : KtGapY Y G C x :=
  fun e he hlt => hg e he (hlt.trans_le hY)

section Plat

variable {κ x0 Y : Ordinal.{0}} {G : Ordinal.{0} → Ordinal.{0}}
variable (hκ : S.InR κ) (hG : Monotone G) (h0 : x0 ≤ kgX S κ G x0 1) (hx0 : x0 < κ)
include hκ hG h0 hx0

/-- **Every member of `Cl(Y, sup_n x_n)` lies in a stage.** -/
theorem ktKeyY
    (hg : ∀ n, KtGapY Y G (S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1))) (kgX S κ G x0 (n + 1))) :
    ∀ y ∈ S.CSet Y (⨆ n : ℕ, kgX S κ G x0 n),
      ∃ n, y ∈ S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1)) := by
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt (hn.trans_le (kgX_mono hκ hG h0 n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (kgStage_mono hκ hG h0 (le_max_left i j) hi)
      (kgStage_mono hκ hG h0 (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (kgStage_mono hκ hG h0 (le_max_left i j) hi)
      (kgStage_mono hκ hG h0 (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    obtain ⟨q, hq, hqe⟩ := hg k _ hk e.2
    have hmono : Monotone (kgX S κ G x0) := monotone_nat_of_le_succ (kgX_mono hκ hG h0)
    set N := max (k + 1) i with hN
    have hltN : e.1 < G (kgX S κ G x0 N) :=
      hqe.trans_le (hG ((Order.add_one_le_of_lt hq).trans (hmono (le_max_left (k + 1) i))))
    have heN := kgStage_mono (S := S) (κ := κ) (G := G) (x0 := x0) hκ hG h0
      ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := kgStage_mono (S := S) (κ := κ) (G := G) (x0 := x0) hκ hG h0 (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU TOWARD `Y`**: `ψ_κ(Y) ≤ sup_n x_n`. -/
theorem ktPlatY (hκC : ∀ a b : Ordinal.{0}, κ ∈ S.CSet a b)
    (hg : ∀ n, KtGapY Y G (S.CSet (G (kgX S κ G x0 n)) (kgX S κ G x0 (n + 1))) (kgX S κ G x0 (n + 1))) :
    S.psi Y κ ≤ ⨆ n : ℕ, kgX S κ G x0 n := by
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  refine psi_le_of_good (hκC _ _) fun y hy hyκ => ?_
  obtain ⟨n, hn⟩ := ktKeyY hκ hG h0 hx0 hg y hy
  rw [kgX_succ] at hn
  have h := lt_psi_of_mem hκ hn hyκ
  rw [← kgX_succ] at h
  exact h.trans_le (le_ciSup hbdd (n + 1))

end Plat

/-- **THE OWNERSHIP TOWARD `Y`**: every `u < ψ_κ(Y)` has `u < ψ_κ(G(u))`. -/
theorem ktOwnY {κ Y : Ordinal.{0}} (hκ : S.InR κ) (hκC : ∀ a b : Ordinal.{0}, κ ∈ S.CSet a b)
    {G : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G)
    (hgap : ∀ a, KtGapY Y G (S.CSet a (S.psi a κ)) (S.psi a κ)) :
    ∀ u, u < S.psi Y κ → u < S.psi (G u) κ := by
  set x0 := S.psi (G 0) κ with hx0def
  have h0 : x0 ≤ kgX S κ G x0 1 := by
    rw [kgX_succ, kgX_zero]; exact (psi_mono hκ (hG zero_le)).1
  have hx0 : x0 < κ := psi_lt hκ _
  have hplat := ktPlatY (S := S) (κ := κ) (Y := Y) (G := G) (x0 := x0) hκ hG h0 hx0 hκC (fun n => hgap _)
  have hown : ∀ n, ∀ u, u < kgX S κ G x0 n → u < S.psi (G u) κ := by
    intro n
    induction n with
    | zero =>
      intro u hu
      rw [kgX_zero] at hu
      exact hu.trans_le (psi_mono hκ (hG zero_le)).1
    | succ n ih =>
      intro u hu
      rcases lt_or_ge u (kgX S κ G x0 n) with h | h
      · exact ih u h
      · rw [kgX_succ] at hu
        exact hu.trans_le (psi_mono hκ (hG h)).1
  have hlt : ∀ n, kgX S κ G x0 n < κ := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ _
  have hbdd : BddAbove (range (kgX S κ G x0)) := ⟨κ, by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  intro u hu
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hu.trans_le hplat)
  exact hown n u hn

end Googology.Trans.PoR.InaccPsi.R2.Kt

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktPlatY
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kt.ktOwnY
