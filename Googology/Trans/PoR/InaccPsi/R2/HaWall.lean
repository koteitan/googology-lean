import Googology.Trans.PoR.InaccPsi.R2.HaFr

/-!
# HaWall: THE WALL `φ(3, G+1)`: THE READINGS OF THE TOWER ARE COFINAL IN `B₃(x)`

The `ζ`-indices `λ_{k+1} = Q_{λ_k}` (`Ha.haZt`) are read as `r_{k+1}(x) = φ(2, i₀(x) + r_k(x))` (`haZt_read`), so
their readings are cofinal in `B₃(x)` (`haZt_read_cof`).  Hence **no `GzVD` extending the starts `haLU λ_k` contains
the code `φ(3, G+1)` with its gate below some base** (`ha_wall_T`): its reading would be `≥ B₃(x)`, but every
`GzVD` reads below its bound field `Z(x) ≤ B₃(x)`.  To pass the wall the bound field must go above `B₃(x)`, i.e.
Lemma IMG is needed above `B₃(x)` (`Ha.ha_img_B3` gives it at `B₃(x)` itself).

* `haZt_read` (**`r_{k+1}(x) = φ(2, i₀(x) + r_k(x))`**), `haZt_iterB3`, `haZt_read_cof`, `ha_wall_T` (**THE WALL**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- The reading of the tower code `λ_k` (in its start). -/
noncomputable def haZr (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (haLU (haZt k)).R (haZt k) x

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem haZt_g (k : ℕ) : (haLU (haZt k)).g (haZt k) < x :=
  (haLU_γ_iff (haZt_lt_T k) hx hx1).1 (haZt_gate k x hx hx1)

/-- **`r_{k+1}(x) = φ(2, i₀(x) + r_k(x))`**: the code `λ_{k+1} = Q_{λ_k}` is read as the base reading of the start
`λ_k`. -/
theorem haZt_read (k : ℕ) : haZr (k + 1) x = veblen 2 (gzI0 x + haZr k x) := by
  set l := haZt k with hl
  have hlT : l < haT := haZt_lt_T k
  have hl'T : haZt (k + 1) < haT := haZt_lt_T (k + 1)
  have hst := haLU_start hlT
  have e : haLU (l + 1) = haSU (Bp := haLPB l hlT) hst := haLU_succ_eq hlT (haLU_self hlT) hst
  have hl1 : l + 1 ≤ haZt (k + 1) := Order.add_one_le_of_lt (haZt_lt_succ k)
  have hl1T : l + 1 < haT := hl1.trans_lt hl'T
  have hB : haZt (k + 1) = (haLU l).B := (haZt_B k).symm
  have hcB : haZt (k + 1) < (haLU (l + 1)).B := by
    rw [haLU_B hl1T, hB, haLU_B hlT]; exact ha_Q_lt_Q (lt_add_one l)
  have h1 : (1 : Ordinal.{0}) < evZ (haLPB l hlT).Q := one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
  have hc1 : haZt (k + 1) < (haSD (haLPB l hlT) (haLU l) 1).B := by
    rw [haS_one_eq, GzVD.step_B, hB]; exact lt_eN _
  have hg : (haLU l).g l < x := haZt_g hx hx1 k
  unfold haZr
  rw [(ha_ext hl1 hl'T).1 _ x hcB, e, haSU_R hst h1 hc1, haS_one_eq, GzVD.step_R, hB, GzVD.hR_G,
    (haLU_start hlT).b x hx hx1 hg, haLPB, haPBof_P _ _ _ _ hx hx1 hg]

theorem haZr_zero : haZr 0 x = 0 := by unfold haZr; exact (haLU (haZt 0)).R_zero x

/-- **The iterates of `φ(2, ·)` from `ζ_{Γ_{x+1}+1} + 1` lie below the tower readings.** -/
theorem haZt_iterB3 (n : ℕ) : (veblen 2)^[n] (evZ (lgG x) + 1) ≤ haZr (n + 2) x := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, haZt_read hx hx1 1, haZt_read hx hx1 0, haZr_zero hx hx1, add_zero,
      gzI0_spec]
    refine Order.add_one_le_of_lt ((le_add_self : evZ (lgG x) ≤ gzI0 x + evZ (lgG x)).trans_lt ?_)
    exact gz_nofix_B3 hx hx1 (gzI0_spec x) le_self_add (ha_veb_lt hx hx1 (gzZ1_lt_B3 x))
  | succ n ih =>
    rw [Function.iterate_succ_apply', haZt_read hx hx1 (n + 2)]
    exact (isNormal_veblen 2).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `B₃(x)`.** -/
theorem haZt_read_cof {v : Ordinal.{0}} (hv : v < gzB3 x) : ∃ k : ℕ, v < haZr k x := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hv
  exact ⟨n + 2, hn.trans_le (haZt_iterB3 hx hx1 n)⟩

end Base

/-- **THE WALL `φ(3, G+1)`**: no system `D : GzVD` that extends the starts `haLU λ_k` (readings and gates) contains
the code `φ(3, G+1)` with its gate below some base `x`: the reading of `φ(3, G+1)` would lie above every
`r_k(x)`, hence `≥ B₃(x)`, but `D` reads below `Z(x) ≤ B₃(x)`. -/
theorem ha_wall_T (D : GzVD) (hB : haT < D.B)
    (hR : ∀ (k : ℕ) c x, c < (haLU (haZt k)).B → D.R c x = (haLU (haZt k)).R c x)
    (hg : ∀ (k : ℕ) c, c < (haLU (haZt k)).B → D.g c = (haLU (haZt k)).g c)
    {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : D.g haT < x) : False := by
  have hk : ∀ k : ℕ, haZr k x < D.R haT x := fun k => by
    have hkB : haZt k < (haLU (haZt k)).B := haLU_self (haZt_lt_T k)
    have hgk : D.g (haZt k) < x := by rw [hg k _ hkB]; exact haZt_g hx hx1 k
    have := D.mono x hx hx1 haT hB (haZt k) (haZt_lt_T k) hgx hgk
    rwa [hR k _ x hkB] at this
  have hge : gzB3 x ≤ D.R haT x := not_lt.1 fun h => by
    obtain ⟨k, hk'⟩ := haZt_read_cof hx hx1 h
    exact absurd (hk'.trans (hk k)) (lt_irrefl _)
  exact absurd ((D.R_lt_Z x hx hx1 haT hB hgx).trans_le (D.Z_B3 x hx hx1)) (not_lt.2 hge)

end Googology.Trans.PoR.InaccPsi.R2.Ha
