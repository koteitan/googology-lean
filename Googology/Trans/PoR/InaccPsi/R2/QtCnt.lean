import Googology.Trans.PoR.InaccPsi.R2.QtK
import Googology.Trans.PoR.InaccPsi.R2.ZbCnt

/-!
# QtCnt: THE MEMBERS OF `K⁽⁰⁾_y` ARE COUNTABLY MANY — `ZbTh (qtU S)`

As `Zb.zbSt`, `Zb.zbTl_cnt`, `Zb.zbU_th` for `K⁽⁰⁾_y = Ul.UlK S 0 y`: the closure of `y ∪ {0, I_n, I_ω}` under `+`,
`φ`, `Ω_·` and the collapses `ψ_π`, `π ≠ Ω₁`, is the union of countably many countable stages for a countable `y`.

* `qtSt` (the stages), `qtSt_cnt`, `qtSt_mono`, `qt_mem_St`, `qt_K_cnt` (**`K⁽⁰⁾_y` is countable** for `y < Ω₁`),
  `qtU_cnt`, `qtU_th` (**`ZbTh (qtU S)`**: the reading of an atom over a countable `y` is countable).

No new axiom.  New definition: `qtSt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Gc

variable (S : InaccSeq.{0})

/-- **The stages of `K⁽⁰⁾_y`.** -/
def qtSt (y : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio y ∪ ({0} ∪ (range S.I ∪ {S.Iw}))
  | n + 1 => qtSt y n ∪ (image2 (· + ·) (qtSt y n) (qtSt y n) ∪
      (image2 veblen (qtSt y n) (qtSt y n) ∪ (Om '' qtSt y n ∪ image2 S.psi (qtSt y n) (qtSt y n))))

variable {S}

theorem qtSt_cnt {y : Ordinal.{0}} (hy : y < Om 1) : ∀ n, (qtSt S y n).Countable
  | 0 => by
    haveI := gc_countable hy
    exact (Set.countable_coe_iff.1 inferInstance).union ((Set.countable_singleton _).union
      ((Set.countable_range _).union (Set.countable_singleton _)))
  | n + 1 => by
    have h := qtSt_cnt hy n
    exact h.union ((h.image2 h _).union ((h.image2 h _).union ((h.image _).union (h.image2 h _))))

theorem qtSt_succ {y : Ordinal.{0}} (n : ℕ) : qtSt S y n ⊆ qtSt S y (n + 1) := fun _ h => Or.inl h

theorem qtSt_mono {y : Ordinal.{0}} {n m : ℕ} (h : n ≤ m) : qtSt S y n ⊆ qtSt S y m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (qtSt_succ _)

/-- **Every member of `K⁽⁰⁾_y` is in a stage.** -/
theorem qt_mem_St {y x : Ordinal.{0}} (hx : UlK S 0 y x) : ∃ n, x ∈ qtSt S y n := by
  induction hx with
  | small h => exact ⟨0, Or.inl h⟩
  | zero => exact ⟨0, Or.inr (Or.inl rfl)⟩
  | inacc n => exact ⟨0, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
  | inaccW => exact ⟨0, Or.inr (Or.inr (Or.inr rfl))⟩
  | @add a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inl ⟨a, qtSt_mono (le_max_left _ _) h1, b, qtSt_mono (le_max_right _ _) h2,
      rfl⟩)⟩
  | @phi a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inl ⟨a, qtSt_mono (le_max_left _ _) h1, b,
      qtSt_mono (le_max_right _ _) h2, rfl⟩))⟩
  | @om a _ iha =>
    obtain ⟨n1, h1⟩ := iha
    exact ⟨n1 + 1, Or.inr (Or.inr (Or.inr (Or.inl ⟨a, h1, rfl⟩)))⟩
  | @coll π e _ _ _ _ ihπ ihe =>
    obtain ⟨n1, h1⟩ := ihπ
    obtain ⟨n2, h2⟩ := ihe
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inr (Or.inr ⟨e, qtSt_mono (le_max_right _ _) h2, π,
      qtSt_mono (le_max_left _ _) h1, rfl⟩)))⟩

/-- **`K⁽⁰⁾_y` is countable** for a countable `y`. -/
theorem qt_K_cnt {y : Ordinal.{0}} (hy : y < Om 1) : {x | UlK S 0 y x}.Countable :=
  (Set.countable_iUnion (qtSt_cnt hy)).mono fun _ hx => Set.mem_iUnion.2 (qt_mem_St hx)

theorem qtU_cnt {y : Ordinal.{0}} (hy : y < Om 1) : ((qtU S).At y).Countable :=
  (qt_K_cnt hy).mono fun _ hs => hs.2.2.2

/-- **`ZbTh (qtU S)`**: the reading of an atom over a countable strongly critical `y` is countable. -/
theorem qtU_th : ZbTh (qtU S) := fun y hy hy1 s hs =>
  zb_th_of_cnt hy hy1 ((qtU S).gxAt y) (qtU_cnt hy1) s hs

end Googology.Trans.PoR.InaccPsi.R2.Qt
