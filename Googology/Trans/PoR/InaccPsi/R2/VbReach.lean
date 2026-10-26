import Googology.Trans.PoR.InaccPsi.R2.VbMove

/-!
# The image reaches `θ`: every atom below `θ` has its normal argument in the domain

`θ = ψ_{Ω₂}(Ω_ω)`, `H_λ = cdHull S λ`, `ldAtR λ` the atoms `ψ_{Ω₂}(a)`, `a ∈ H_λ`, `a < A_{η_λ}`,
`VbD S λ` the domain of
the image `T = vbT S λ` (`VbDef`).

* `vbReach` (**every atom `s < θ` of `λ` is `ψ_{Ω₂}(d)` with a normal argument `d ∈ VbD S λ`**; so `T` and all its laws
  (`VbLaw`, `VbMove`) apply to the argument of every atom below `θ` and to its parts, at every level);
* `vbD_Om` (`Ω_{k+1} ∈ VbD S λ`), `vbT_OmW_cof` (**the images `T Ω_{k+2} = Ω_{k+1}` are cofinal in `Ω_ω`**: the
  exponents `Ω_{k+1}` are cofinal in the argument `Ω_ω` of `θ` and their images are cofinal in `Ω_ω`);
* `vbT_Y` (**PAST THE WALL**: `T(Y₃) = Y₂`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, where `Ug.ugTh S λ Y₃ = 0`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every atom `s < θ` of `λ` is `ψ_{Ω₂}(d)` with a normal argument `d ∈ VbD S λ`.** -/
theorem vbReach {s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hsθ : s < ConjT.th S) :
    ∃ d, VbD S l d ∧ S.psi d (Om (1 + 1)) = s ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
  obtain ⟨a, haH, haA, rfl⟩ := hs
  have hmem : S.psi a (Om (1 + 1)) ∈ cdHull S l :=
    CSet.psi_mem haA (InR_Om_succ 1) (Mx.mxOm2_mem _ _) haH
  have hρs : upsilon l ≤ S.psi a (Om (1 + 1)) :=
    ((vbZ hl hX).2.trans (psiS_bounds (S := S) a 1).1).le
  obtain ⟨d, hdW, -, hda, hdH, hdn, hdC⟩ := Ry.ryTh_nf_mem hsθ hmem hρs
  refine ⟨d, ⟨hdH, ?_, hdW⟩, hda, hdn⟩
  exact CSet_mono le_rfl (by rw [hda]; exact hsθ.le) hdC

omit hl hX in
theorem vbD_Om (k : ℕ) : VbD S l (Om ((k : Ordinal.{0}) + 1)) :=
  ⟨rxC_Om_succ _ _ k, rxC_Om_succ _ _ k, (Om_lt_Om.2 (by
    exact_mod_cast (show ((k + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)))⟩

/-- **The images `T Ω_{k+2} = Ω_{k+1}` are cofinal in `Ω_ω`.** -/
theorem vbT_OmW_cof {z : Ordinal.{0}} (hz : z < Om ω) :
    ∃ k : ℕ, z < vbT S l (Om ((k : Ordinal.{0}) + 1 + 1)) ∧
      vbT S l (Om ((k : Ordinal.{0}) + 1 + 1)) = Om ((k : Ordinal.{0}) + 1) := by
  obtain ⟨n, hn⟩ := rxOmW_nat hz
  have e : vbT S l (Om (((n : ℕ) : Ordinal.{0}) + 1 + 1)) = Om ((n : Ordinal.{0}) + 1) := by
    have h := vbT_Om (S := S) hl hX (k := n + 1) (by omega)
    rw [Nat.cast_succ] at h
    exact h
  refine ⟨n, ?_, e⟩
  rw [e]
  exact hn.trans (Om_lt_Om.2 (lt_add_one _))

/-- **PAST THE WALL**: `T(Y₃) = Y₂`. -/
theorem vbT_Y : vbT S l (Ug.ugY S) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have e3 : ((2 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 + 1 := by norm_num
  have e2 : ((1 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 := by norm_num
  have hd : VbD S l (Om (1 + 1 + 1)) := by have h := vbD_Om (S := S) (l := l) 2; rwa [e3] at h
  have hn : Om (1 + 1 + 1 : Ordinal.{0}) ∈
      S.CSet (Om (1 + 1 + 1)) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) := by
    have h := rxC_Om_succ (S := S) (Om (1 + 1 + 1)) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) 2
    rwa [e3] at h
  have hn' : Om (1 + 1 + 1 : Ordinal.{0}) ∈
      S.CSet (Om (1 + 1 + 1)) (S.psi (Om (1 + 1 + 1)) (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1))) := by
    rwa [e2]
  obtain ⟨h1, -⟩ := vbT_atom hl hX (k := 1) le_rfl hd hn'
  have hO := vbT_Om (S := S) hl hX (k := 2) (by omega)
  rw [e3, show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num] at hO
  rw [e2, hO] at h1
  exact h1

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vb
