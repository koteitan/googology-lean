import Googology.Trans.PSS.Main.CIAux10

/-!
# CI, part 11: the induction

`ci_main`: for every region term `s`, `jN(𝒯(s)) = 𝒯(Coll_A(s))` (CI in normal form), by
induction on the size; `ci_val`: the value form with `J = t^α_τ ∘ ι_{τ,α}` (`jP`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

set_option linter.unusedSectionVars false

section Main

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

/-- **CI** in normal form. -/
theorem ci_main : ∀ n, CIIH H hne n := by
  intro n
  induction n with
  | zero => intro s hs; exact absurd hs (by have := Tm.size_pos s; omega)
  | succ n ih =>
    intro s hs hR
    obtain ⟨m, ch⟩ := s
    have hm := regT_y hN he hne hR
    simp only [Tm.y_node] at hm
    by_cases hch : ch = []
    · subst hch; exact ci_leaf hN he hne hR
    by_cases hl : (ch.getLast hch).y = m + 1
    · rcases m with _ | _ | k
      · omega
      · exact ci_eps_one hN he hne ih hs hR hch hl
      · exact ci_eps_high hN he hne ih hs hR hch hl
    · rcases m with _ | _ | k
      · omega
      · exact ci_noneps_one hN he hne ih hs hR hch hl
      · exact ci_noneps_high hN he hne ih hs hR hch hl

/-- **CI** (value form): `val J(𝒯_m(s)) = val 𝒯_{m-1}(Coll_A(s))` for a region term `s`. -/
theorem ci_val {s : Tm} (hs : IsRegT H hne s) :
    WP.valS (jP (trTm (.node 0 H)) (trTm s)) = (trTm (coll H s)).val := by
  have e := ci_main hN he hne s.size s le_rfl hs
  have hn : NFP (jN (trTm (.node 0 H)) (trTm s)) := by rw [e]; exact trTm_nfp _
  rw [valS_jP (aFacts hN he hne).1 _ hn, e]

end Main

end Googology.Trans.PSS.Main
