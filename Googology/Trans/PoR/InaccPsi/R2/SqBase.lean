import Googology.Trans.PoR.InaccPsi.R2.SqLim

/-!
# The levels `ε + n`, the reading at the base `ε`, and the own atoms over the base `ε`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `ε = ε_{Ω₂+1}`, `ε̂ = ε_{Ω₁+1}`.

* `sqLev_epsN` (**`Sc.ScLev ⊤ (ε + n) (ε̂ + n)` and its own data for every `n`**: `Sc.scLev_succ` from
  `Sq.sqLev_eps`);
* `sqRd_eps` (**the base `ε` has a reading**: `Θ(ψ_{Ω₂}(ε)) = ψ_{Ω₁}(A + 1 + ε̂)` with `A + 1 + ε̂` own);
* `sqBase_eps` (the base `ε` of the shift `W^E`, `E < ε`), `sqClsBase_eps` (**every atom below
  `ψ_{Ω₂}(ε + W^{W^E})` is `≤ ψ_{Ω₂}(ε)` or own over the base `ε`** (family `Sn.snShG`), for `1 ≤ E < ε` in the hull
  with the closure condition at the base `ε`: `Sn.snClsLev_all` at a base `β ≥ ε`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The levels `ε + n`** (own predicate `⊤`, image `ε̂ + n`). -/
theorem sqLev_epsN : ∀ n : ℕ,
    ScLev S l (fun _ _ => True) (veblen 1 (Om (1 + 1) + 1) + n) (veblen 1 (Om 1 + 1) + n) ∧
      ScOwP S l (fun _ _ => True) (veblen 1 (Om (1 + 1) + 1) + n) (veblen 1 (Om 1 + 1) + n)
  | 0 => by
    simp only [Nat.cast_zero, add_zero]
    exact ⟨sqLev_eps hl hX, sqOwP_eps⟩
  | n + 1 => by
    obtain ⟨hL, hP⟩ := sqLev_epsN n
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc]
    exact ⟨scLev_succ hl hX hP hL (fun _ _ h => h), scOwP_succ hP⟩

/-- **The base `ε` has a reading.** -/
theorem sqRd_eps {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    RwRd S l (veblen 1 (Om (1 + 1) + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  refine ⟨A + 1 + veblen 1 (Om 1 + 1), ?_, sqRead_Feps hl hX hA hρ⟩
  exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA1) sqEpsH_mem

omit hl hX in
/-- The base `ε` of the shift `W^E`, `E < ε`. -/
theorem sqBase_eps {l E : Ordinal.{0}} (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    RoBaseE S l (0 + leWe E) 0 (veblen 1 (Om (1 + 1) + 1)) := by
  have hWE : leWe E < veblen 1 (Om (1 + 1) + 1) := by
    have h := leWe_lt hE; rwa [sqEps_We] at h
  have hEW : E < Om ω := hE.trans Sj.sjEps_lt_OmW
  refine ⟨?_, sqEps_mem, ?_, fun d _ => sqEps_mem, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]
    have h := leWe_dvd hWE.le
    rwa [sqEps_We] at h
  · rw [zero_add, add_zero]
    exact ((SC_Om omega0_ne_zero).isPrincipal Sj.sjEps_lt_OmW (roWe_lt_OmW (roWe_lt_OmW hEW))).trans_le
      le_self_add
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **Every atom below `ψ_{Ω₂}(ε + W^{W^E})` is `≤ ψ_{Ω₂}(ε)` or own over the base `ε`** (family `snShG`). -/
theorem sqClsBase_eps {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (he1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hcl : SnCL S E (veblen 1 (Om (1 + 1) + 1)) 0) :
    RwClsAt S l (snShG S l) (leWe E) 0 (veblen 1 (Om (1 + 1) + 1)) := by
  have h := snClsLev_all hl hX E hEH he1 hE _ 0 0 (Or.inl ⟨rfl, rfl⟩) hcl _ le_rfl (sqBase_eps hE)
    (sqRd_eps hl hX hA hρ)
  rwa [zero_add] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sq
