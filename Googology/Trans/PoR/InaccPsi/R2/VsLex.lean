import Googology.Trans.PoR.InaccPsi.R2.VsMove
import Mathlib.Data.DFinsupp.WellFounded

/-!
# A well-founded measure across the cardinal levels: visibility coordinates, lexicographically

`K⁽ⁱ⁾_q = Ul.UlK S i q`.  For a finite `i ≥ 1` the **visibility coordinate** `vᵢ(x) = Vs.vsV S i x` is the least
strongly critical `q ∈ (Ω_i, Ω_{i+1}]` with `x ∈ K⁽ⁱ⁾_q`, or `Ω_{i+1}` if there is none.  The measure
`μ_r(x) = Vs.vsMu S r x = (v₁(x), …, v_r(x), x)` is compared lexicographically (`Pi.Lex` on `Fin (r + 1)`, a
well-founded order).  A **part** `c` of `x` (`Vs.VsSub S c x`: every `K⁽ⁱ⁾_q`, `i ≥ 1`, `q ∈ (Ω_i, Ω_{i+1}]`, that
contains `x` contains `c`) has `vᵢ(c) ≤ vᵢ(x)` for every `i`:

* `vsV_le_mem`, `vsV_mono`, `vsV_gt` (**`x < vᵢ(x)` for `x < Ω_{i+1}`**), `vs_lex_of` (**weakly below on the first
  coordinates and strictly below at one gives `Pi.Lex`**), `vs_wf` (**the measure is well-founded**);
* `vs_lex_sub` (**a part `c < x` is below `x`**), `vs_lex_lev` (**the level `λ` of a strongly critical `ξ ∈ (Ω_s,
  Ω_{s+1})`, `1 ≤ s ≤ r`, with `λ ∈ K⁽ˢ⁾_ξ` and the coordinates below `s` inherited, is below `ξ`** — at the
  coordinate `s`: `v_s(λ) ≤ ξ < v_s(ξ)`).

No new axiom.  New definitions: `vsV`, `vsMu` (the measure), `VsSub` (a Prop).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-- The visibility coordinate `vᵢ(x)`: the least strongly critical `q ∈ (Ω_i, Ω_{i+1}]` with `x ∈ K⁽ⁱ⁾_q`, else
`Ω_{i+1}`. -/
noncomputable def vsV (S : InaccSeq.{0}) (i x : Ordinal.{0}) : Ordinal.{0} :=
  sInf (insert (Om (i + 1)) {q | SC q ∧ Om i < q ∧ q ≤ Om (i + 1) ∧ UlK S i q x})

/-- The measure `μ_r(x) = (v₁(x), …, v_r(x), x)`. -/
noncomputable def vsMu (S : InaccSeq.{0}) (r : ℕ) (x : Ordinal.{0}) : Fin (r + 1) → Ordinal.{0} :=
  fun j => if (j : ℕ) < r then vsV S (((j : ℕ) : Ordinal.{0}) + 1) x else x

/-- `c` is a part of `x`: every `K⁽ⁱ⁾_q` (`1 ≤ i < ω`, `q ∈ (Ω_i, Ω_{i+1}]` strongly critical) containing `x`
contains `c`. -/
def VsSub (S : InaccSeq.{0}) (c x : Ordinal.{0}) : Prop :=
  ∀ i : Ordinal.{0}, 1 ≤ i → i < ω → ∀ q, SC q → Om i < q → q ≤ Om (i + 1) → UlK S i q x → UlK S i q c

theorem vsV_le_mem {i x q : Ordinal.{0}} (hq : SC q) (hLq : Om i < q) (hqW : q ≤ Om (i + 1))
    (hx : UlK S i q x) : vsV S i x ≤ q :=
  csInf_le' (mem_insert_of_mem _ ⟨hq, hLq, hqW, hx⟩)

theorem vsV_le_W (i x : Ordinal.{0}) : vsV S i x ≤ Om (i + 1) := csInf_le' (mem_insert _ _)

theorem vsV_mem (i x : Ordinal.{0}) :
    vsV S i x ∈ insert (Om (i + 1)) {q | SC q ∧ Om i < q ∧ q ≤ Om (i + 1) ∧ UlK S i q x} :=
  csInf_mem (insert_nonempty _ _)

/-- **A part has a smaller coordinate.** -/
theorem vsV_mono {i c x : Ordinal.{0}}
    (hsub : ∀ q, SC q → Om i < q → q ≤ Om (i + 1) → UlK S i q x → UlK S i q c) : vsV S i c ≤ vsV S i x := by
  rcases vsV_mem (S := S) i x with h | ⟨hq, hLq, hqW, hx⟩
  · rw [h]; exact vsV_le_W i c
  · exact vsV_le_mem hq hLq hqW (hsub _ hq hLq hqW hx)

/-- **`x < vᵢ(x)`** for `x < Ω_{i+1}`. -/
theorem vsV_gt {i x : Ordinal.{0}} (hi : i < ω) (hxW : x < Om (i + 1)) : x < vsV S i x := by
  rcases vsV_mem (S := S) i x with h | ⟨hq, hLq, _, hx⟩
  · rw [h]; exact hxW
  · exact ulK_lt_W hi hq hLq hx hxW

/-- **Weakly below on the coordinates before `j₀` and strictly below at `j₀` gives `Pi.Lex`.** -/
theorem vs_lex_of {r : ℕ} (f g : Fin (r + 1) → Ordinal.{0}) (j0 : Fin (r + 1)) (hle : ∀ j, j < j0 → f j ≤ g j)
    (hlt : f j0 < g j0) : Pi.Lex (· < ·) (fun {_} => (· < ·)) f g := by
  have hwf : WellFounded (· < · : Fin (r + 1) → Fin (r + 1) → Prop) := wellFounded_lt
  set P : Set (Fin (r + 1)) := {j | f j ≠ g j ∧ j ≤ j0} with hPdef
  have hne : P.Nonempty := ⟨j0, hlt.ne, le_rfl⟩
  set i := hwf.min P hne with hidef
  have hiP : i ∈ P := hwf.min_mem P hne
  refine ⟨i, fun j hj => ?_, ?_⟩
  · by_contra hc
    exact hwf.not_lt_min P (show j ∈ P from ⟨hc, hj.le.trans hiP.2⟩) hj
  · rcases hiP.2.lt_or_eq with h | h
    · exact lt_of_le_of_ne (hle i h) hiP.1
    · rw [h]; exact hlt

/-- **The measure is well-founded.** -/
theorem vs_wf (r : ℕ) :
    WellFounded (InvImage (Pi.Lex (· < ·) (fun {_} => (· < ·))) (vsMu S r)) :=
  InvImage.wf _ (Pi.Lex.wellFounded (· < ·) fun _ => wellFounded_lt)

theorem vs_nat_lt_omega (j : ℕ) : ((j : Ordinal.{0}) + 1) < ω := by
  have := natCast_lt_omega0 (j + 1); rwa [Nat.cast_succ] at this

/-- **A part `c < x` is below `x`.** -/
theorem vs_lex_sub (r : ℕ) {c x : Ordinal.{0}} (hsub : VsSub S c x) (hcx : c < x) :
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (vsMu S r c) (vsMu S r x) := by
  refine vs_lex_of _ _ (Fin.last r) (fun j hj => ?_) ?_
  · have hjr : (j : ℕ) < r := hj
    simp only [vsMu, if_pos hjr]
    exact vsV_mono (hsub _ le_add_self (vs_nat_lt_omega j))
  · have : ¬ ((Fin.last r : Fin (r + 1)) : ℕ) < r := by simp
    simp only [vsMu, if_neg this]
    exact hcx

/-- **The level is below the atom**: for a strongly critical `ξ ∈ (Ω_s, Ω_{s+1})`, `s = k + 1 ≤ r`, and `λ` with
`λ ∈ K⁽ˢ⁾_ξ` and `λ ∈ K⁽ⁱ⁾_q` whenever `ξ ∈ K⁽ⁱ⁾_q` for `1 ≤ i < s`: `μ_r(λ) < μ_r(ξ)`. -/
theorem vs_lex_lev {r k : ℕ} (hkr : k < r) {l ξ : Ordinal.{0}}
    (hlow : ∀ i : Ordinal.{0}, 1 ≤ i → i < (k : Ordinal.{0}) + 1 → ∀ q, SC q → Om i < q → q ≤ Om (i + 1) →
      UlK S i q ξ → UlK S i q l)
    (hlK : UlK S ((k : Ordinal.{0}) + 1) ξ l) (hξ : SC ξ) (hξ1 : Om ((k : Ordinal.{0}) + 1) < ξ)
    (hξ2 : ξ < Om ((k : Ordinal.{0}) + 1 + 1)) :
    Pi.Lex (· < ·) (fun {_} => (· < ·)) (vsMu S r l) (vsMu S r ξ) := by
  have hk1 : k < r + 1 := hkr.trans (Nat.lt_succ_self r)
  refine vs_lex_of _ _ ⟨k, hk1⟩ (fun j hj => ?_) ?_
  · have hjk : (j : ℕ) < k := hj
    have hjr : (j : ℕ) < r := hjk.trans hkr
    simp only [vsMu, if_pos hjr]
    refine vsV_mono (hlow _ le_add_self ?_)
    exact_mod_cast Nat.succ_lt_succ hjk
  · have hkr' : ((⟨k, hk1⟩ : Fin (r + 1)) : ℕ) < r := hkr
    simp only [vsMu, if_pos hkr']
    exact (vsV_le_mem hξ hξ1 hξ2.le hlK).trans_lt (vsV_gt (vs_nat_lt_omega k) hξ2)

end Googology.Trans.PoR.InaccPsi.R2.Vs
