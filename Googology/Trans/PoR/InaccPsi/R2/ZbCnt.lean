import Googology.Trans.PoR.InaccPsi.R2.ZbLd

/-!
# ZbCnt: THE ATOMS OF `zbU` OVER A COUNTABLE BASE ARE COUNTABLY MANY — `ZbTh zbU`

* `zbSt` (the stages of `Tl.TlCl y`), `zbSt_cnt`, `zbTl_cnt` (**the codes of `TlCl y` are countably many for every
  `y < Ω₁`**), `zbK_cnt` (the `Yr` atoms with gate below `y`), `zbU_cnt` (**`zbU.At y` is countable**);
* `zb_th_of_cnt` (**countably many atoms ⇒ every atom reads below `Ω₁`**, the proof of `Gs.gsmTh_G`), `zbU_th`
  (**`ZbTh zbU`**).

No new axiom.  New definition: `zbSt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Ph

/-- **The stages of the codes of `TlCl y`.** -/
def zbSt (y : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio y ∪ {Om1}
  | n + 1 => zbSt y n ∪ (image2 (· + ·) (zbSt y n) (zbSt y n) ∪
      (image2 veblen (zbSt y n) (zbSt y n) ∪ image2 rhF (zbSt y n) (zbSt y n)))

theorem zbSt_cnt {y : Ordinal.{0}} (hy : y < Om 1) : ∀ n, (zbSt y n).Countable
  | 0 => by
    haveI := gc_countable hy
    exact (Set.countable_coe_iff.1 inferInstance).union (Set.countable_singleton _)
  | n + 1 => by
    have h := zbSt_cnt hy n
    exact h.union ((h.image2 h _).union ((h.image2 h _).union (h.image2 h _)))

theorem zbSt_succ {y : Ordinal.{0}} (n : ℕ) : zbSt y n ⊆ zbSt y (n + 1) := fun _ h => Or.inl h

theorem zbSt_mono {y : Ordinal.{0}} {n m : ℕ} (h : n ≤ m) : zbSt y n ⊆ zbSt y m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (zbSt_succ _)

theorem zbTl_mem_St {y x : Ordinal.{0}} (hx : TlCl y x) : ∃ n, x ∈ zbSt y n := by
  induction hx with
  | small h => exact ⟨0, Or.inl h⟩
  | om => exact ⟨0, Or.inr rfl⟩
  | @add a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inl ⟨a, zbSt_mono (le_max_left _ _) h1, b, zbSt_mono (le_max_right _ _) h2,
      rfl⟩)⟩
  | @phi a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inl ⟨a, zbSt_mono (le_max_left _ _) h1, b,
      zbSt_mono (le_max_right _ _) h2, rfl⟩))⟩
  | @atom β z _ _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inr ⟨β, zbSt_mono (le_max_left _ _) h1, z,
      zbSt_mono (le_max_right _ _) h2, rfl⟩))⟩

/-- **The codes of `TlCl y` are countably many** (`y < Ω₁`). -/
theorem zbTl_cnt {y : Ordinal.{0}} (hy : y < Om 1) : {x | TlCl y x}.Countable :=
  (Set.countable_iUnion (zbSt_cnt hy)).mono fun _ hx => Set.mem_iUnion.2 (zbTl_mem_St hx)

/-- **The `Yr` atoms with gate below `y` are countably many.** -/
theorem zbK_cnt {y : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) : (zbKAt y).Countable := by
  have hn : ∀ n : ℕ, (gcG '' {c | c < yrTw n ∧ yrG c < y}).Countable := fun n => by
    haveI := yr_count (yrTw_lt_BG n) le_rfl hy hy1
    have h : {c | c < yrTw n ∧ yrG c < y}.Countable := by
      have e : {c | c < yrTw n ∧ yrG c < y} =
          (fun b : {b : Iio (yrTw n) // yrG b.1 < y} => b.1.1) '' univ := by
        ext c
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨⟨c, h1⟩, h2⟩, trivial, rfl⟩
        · rintro ⟨b, -, rfl⟩; exact ⟨b.1.2, b.2⟩
      rw [e]; exact Set.countable_univ.image _
    exact h.image _
  refine (Set.countable_iUnion hn).mono ?_
  rintro s ⟨c, hc, hg, rfl⟩
  obtain ⟨n, hn'⟩ := yrTw_cof c hc
  exact Set.mem_iUnion.2 ⟨n, c, ⟨hn', hg⟩, rfl⟩

/-- **`zbU.At y` is countable** for every strongly critical `y < Ω₁`. -/
theorem zbU_cnt {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : (zbU.At y).Countable := by
  have hy1' : y < Om1 := by rw [Br.Om1_eq]; exact hy1
  refine ((zbTl_cnt hy1).union (zbK_cnt (gg_SC_eps hy) hy1')).mono ?_
  rintro s (hs | hs)
  · exact Or.inl hs.2.2.2
  · exact Or.inr hs

/-- **Countably many atoms ⇒ every atom reads below `Ω₁`.** -/
theorem zb_th_of_cnt {y : Ordinal.{0}} {At : Set Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hAt : GxAt At)
    (hc : At.Countable) : ∀ s ∈ At, gxTh y At s < Om 1 := by
  intro s
  induction s using WellFoundedLT.induction with
  | ind s IH =>
  intro _
  haveI : Countable {t : At // t.1 < s} := by
    haveI := hc.to_subtype
    exact Subtype.countable
  set z := ⨆ t : {t : At // t.1 < s}, gxTh y At t.1.1 with hz
  have hbdd : BddAbove (range fun t : {t : At // t.1 < s} => gxTh y At t.1.1) := Ordinal.bddAbove_of_small
  have hz1 : z < Om 1 := by
    have := Ordinal.iSup_lt_omega_one (f := fun t : {t : At // t.1 < s} => gxTh y At t.1.1)
      fun t => by
        have h := IH t.1.1 t.2 t.1.2
        rwa [← ph_Om1_eq] at h
    rwa [← ph_Om1_eq]
  obtain ⟨Y, hYS, hmY, hY1⟩ := Gd.gd_SC_above (max_lt hy1 hz1)
  refine (Ld.ldAtom_le hy hy1 hAt hYS ((le_max_left _ _).trans_lt hmY) fun t ht hts => ?_).trans_lt hY1
  exact (le_ciSup hbdd ⟨⟨t, ht⟩, hts⟩).trans_lt ((le_max_right _ _).trans_lt hmY)

/-- **`ZbTh zbU`**: every atom of `zbU` over a countable strongly critical base reads below `Ω₁`. -/
theorem zbU_th : ZbTh zbU := fun y hy hy1 s hs => zb_th_of_cnt hy hy1 (zbU.gxAt y) (zbU_cnt hy hy1) s hs

end Googology.Trans.PoR.InaccPsi.R2.Zb
