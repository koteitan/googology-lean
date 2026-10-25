import Googology.Trans.PoR.InaccPsi.R2.GwZb

/-!
# LEMMA EXACT ABOVE `ζ_{Γ_{x+1}+1}`: `ϑˣ(Ω₁ + ζ + ν) = ε_{ζ+1+ν}` at the pseudo-base `ζ = ζ_{Γ_{x+1}+1}`

`Te.teGlA_eq` reads the `ε`-numbers above `Γ_{x+1}` through `ϑˣ(Ω₁ + Γ_{x+1} + ν)`, up to the next `ε`-fixed point
`ζ_{Γ_{x+1}+1}`.  The same induction works over any `ε`-number pseudo-base `P` with `ϑˣ(Ω₁ + P) = ε_{P+1}` and
`ϑˣ(Ω₁ + σ) < P` for `σ < P` (`gw_glA_eqP`).  For `P = ζ_{Γ_{x+1}+1}` both hold (`Gw.gw_eNZ`, `gw_glA_lt_Z`), so the
`ε`-numbers in `(ζ_{Γ_{x+1}+1}, ζ_{Γ_{x+1}+2})` are read and Lemma EXACT holds for them: these are the base readings
`φ(1, Γ_{x+1} + c(x))` of the unions at the indices `c ∈ (ζ_{G+1}, ζ_{G+2})`, the next case of the recursion.

* `gw_glA_eqP` (**the generic reading over an `ε`-number pseudo-base**), `gw_glA_lt_Z`, `gw_evIx_Z`, `gw_glAZ_eq`
  (**`ϑˣ(Ω₁ + ζ + ν) = ε_{ζ+1+ν}` for `ν < ζ_{ζ+1}`**), `gw_veb_Z`, `gw_evAZ_pi`, `gw_b_pi_Z` (**Lemma EXACT for
  `φ(1, ζ_{Γ_{ρ+1}+1} + ν(ρ))`, `ω ≤ ν(ρ) < ζ_{Γ_{ρ+1}+2}`**), `gw_b_eN_Z` (**`ε_{b(x)+1} = ϑˣ(Ω₁ + ζ + ν + 1)` for
  `b(x) = φ(1, ζ + ν)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- `ζ_{τ+1}` is its own `ε`-index. -/
theorem gw_evIx_Z (τ : Ordinal.{0}) : evIx (evZ τ) = evZ τ := by
  have h1 : Ordinal.epsilon (evIx (evZ τ)) = evZ τ := epsilon_evIx (evZ_E τ)
  have h2 : Ordinal.epsilon (evZ τ) = evZ τ := epsilon_evZ τ
  exact (veblen_inj).1 (h1.trans h2.symm)

/-- `φ(1, ζ + ν) = ε_{ζ+ν}` in the notation `evA`. -/
theorem gw_veb_Z (τ ν : Ordinal.{0}) : veblen 1 (evZ τ + ν) = evA (evZ τ) ν := by
  show veblen 1 _ = Ordinal.epsilon (evIx (evZ τ) + ν)
  rw [gw_evIx_Z]

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁ + P + ν) = ε_{P+1+ν}` over an `ε`-number pseudo-base `P`** (`x < P < Γ_{x+2}`, `ϑˣ(Ω₁ + P) = ε_{P+1}`,
`ϑˣ(Ω₁ + σ) < P` for `σ < P`), for every `ν` with `P + ν < Γ_{x+2}` and no limit `ν' ≤ ν` with `ε_{P+1+ν'} ≤ P + ν'`. -/
theorem gw_glA_eqP {P : Ordinal.{0}} (hPE : InE P) (hxP : x < P) (hbase : glA 1 P x = eN P)
    (hlow : ∀ σ, σ < P → glA 1 σ x < P) : ∀ ν, P + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → P + ν' < evA P (1 + ν')) → glA 1 (P + ν) x = evA P (1 + ν) := by
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have h1P : (1 : Ordinal.{0}) < P := Lu.lu_one_lt_E hPE
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0
    rw [add_zero, add_zero, hbase]
    have h := evA_add_one P 0
    rw [evA_zero hPE, zero_add] at h
    exact h.symm
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : P + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    obtain ⟨hdT, hd1⟩ := gm1_T hx hx1 hdq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc, ← glA_eN_one hx hx1 hdT hd1, IHd, ← add_assoc, evA_add_one]
  · have hων : ω ≤ ν := omega0_le_of_isSuccLimit hlim
    have h1ν : 1 + ν = ν := one_add_of_omega0_le hων
    set u := evA P (1 + ν) with hu_def
    have huE : InE u := evA_E _ _
    have hPu : P < u := by
      calc P = evA P 0 := (evA_zero hPE).symm
        _ < u := evA_lt_iff.2 (lt_of_lt_of_le zero_lt_one le_self_add)
    have htu : P + ν < u := hfix ν le_rfl hlim
    have hP : LuP 1 u := by
      have h := vzP_one.2 huE; unfold VzP at h; rwa [Nat.cast_one] at h
    have hval : ∀ ν'', ν'' < ν → glA 1 (P + ν'') x = evA P (1 + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq)
        (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 le_rfl h1T h11 htT ht1 hP (hxP.trans hPu) htu (h1P.trans hPu)
        (fun σ hσ => ?_)
      rcases lt_or_ge σ P with hσP | hσP
      · exact (hlow σ hσP).trans hPu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσP
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact evA_lt_iff.2 ((add_lt_add_iff_left 1).2 hν'')
    · rw [hu_def, h1ν]
      refine ((evA_isNormal P).le_iff_forall_le hlim).2 fun c hc => ?_
      obtain ⟨-, -, -, -, -, htA⟩ := glA_facts hx hx1 le_rfl h1T h11 htT ht1
      rcases eq_or_ne c 0 with rfl | hc0
      · rw [evA_zero hPE]; exact (le_self_add.trans htA.le)
      · have h1c : 1 ≤ c := one_le_iff_ne_zero.2 hc0
        have hc' : c - 1 < ν := lt_of_le_of_lt (sub_le_self c 1) hc
        rw [← ev_one_add_sub_one h1c, ← hval _ hc']
        have hq' : P + (c - 1) < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        exact (glA_lt_of hx hx1 le_rfl h1T h11 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

/-- `ϑˣ(Ω₁ + σ) < ζ_{Γ_{x+1}+1}` for every `σ < ζ_{Γ_{x+1}+1}`. -/
theorem gw_glA_lt_Z {σ : Ordinal.{0}} (hσ : σ < evZ (lgG x)) : glA 1 σ x < evZ (lgG x) := by
  obtain ⟨-, -, -, hGE, -⟩ := lgG_facts hx hx1
  have h1G : (1 : Ordinal.{0}) < lgG x := one_lt_omega0.trans (omega0_lt_inE hGE)
  rcases lt_or_ge σ (lgG x) with hσG | hσG
  · exact (glA_lt_G hx hx1 h1G hσG).trans (lt_evZ _)
  · obtain ⟨ν, rfl⟩ := exists_add_of_le hσG
    have hν : ν < evZ (lgG x) := lt_of_le_of_lt le_add_self hσ
    rw [gw_glA_eq hx hx1 hν]
    exact evA_lt_evZ hGE (add_lt_evZ (one_lt_omega0.trans (omega0_lt_inE (evZ_E _))) hν)

/-- **`ϑˣ(Ω₁ + ζ + ν) = ε_{ζ+1+ν}`** for `ζ = ζ_{Γ_{x+1}+1}` and every `ν < ζ_{ζ+1}`. -/
theorem gw_glAZ_eq {ν : Ordinal.{0}} (hν : ν < evZ (evZ (lgG x))) :
    glA 1 (evZ (lgG x) + ν) x = evA (evZ (lgG x)) (1 + ν) := by
  have hZE := evZ_E (lgG x)
  have hq : evZ (evZ (lgG x)) < gq 1 x := gw_evZ_lt1 hx hx1 (gn_evZG_lt1 hx hx1)
  refine gw_glA_eqP hx hx1 hZE ((lgG_facts hx hx1).2.1.trans (lt_evZ _)) (gw_eNZ hx hx1).symm
    (fun σ hσ => gw_glA_lt_Z hx hx1 hσ) ν ((add_lt_evZ (lt_evZ _) hν).trans hq)
    (fun ν' h _ => gw_lt_evA hZE (lt_of_le_of_lt h hν))

/-- **`ε_{b(x)+1} = ϑˣ(Ω₁ + ζ + ν + 1)` for `b(x) = φ(1, ζ + ν)`** (`ω ≤ ν < ζ_{ζ+1}`, `ζ = ζ_{Γ_{x+1}+1}`). -/
theorem gw_b_eN_Z {ν : Ordinal.{0}} (hω : ω ≤ ν) (hν : ν < evZ (evZ (lgG x))) :
    eN (veblen 1 (evZ (lgG x) + ν)) = glA 1 (evZ (lgG x) + (ν + 1)) x := by
  have hν1 : ν + 1 < evZ (evZ (lgG x)) := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt hν
  rw [gw_glAZ_eq hx hx1 hν1, one_add_of_omega0_le (hω.trans le_self_add), go_eN_veb, add_assoc]
  show veblen 1 _ = Ordinal.epsilon (evIx (evZ (lgG x)) + (ν + 1))
  rw [gw_evIx_Z]

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for `ε_{ζ+1+ν}`** at the pseudo-base `ζ = ζ_{Γ_{ρ+1}+1}`. -/
theorem gw_evAZ_pi {ν : Ordinal.{0}} (hνT : ν ∈ TB ρ σ) (hν : ν < evZ (evZ (lgG ρ)))
    (hν' : pi σ ρ ν < evZ (evZ (lgG σ))) :
    evA (evZ (lgG ρ)) (1 + ν) ∈ TB ρ σ ∧
      pi σ ρ (evA (evZ (lgG ρ)) (1 + ν)) = evA (evZ (lgG σ)) (1 + pi σ ρ ν) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨z1, z2⟩ := gw_Z_pi hB
  obtain ⟨s1, s2⟩ := pi_add hB z1 hνT
  rw [z2] at s2
  have hq : evZ (lgG ρ) + ν < gq 1 ρ :=
    (add_lt_evZ (lt_evZ _) hν).trans (gw_evZ_lt1 hB.2.1 hρ1 (gn_evZG_lt1 hB.2.1 hρ1))
  have hs1 : evZ (lgG ρ) + ν < Om1 := (gm1_T hB.2.1 hρ1 hq).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 hs1
  rw [o2, s2, gw_glAZ_eq hB.2.1 hρ1 hν, gw_glAZ_eq hB.1 hσ1 hν'] at h
  exact h

/-- **Lemma EXACT for `φ(1, ζ_{Γ_{ρ+1}+1} + ν(ρ))`** (`ω ≤ ν(ρ) < ζ_{Γ_{ρ+1}+2}`, `π(ν(ρ)) = ν(σ) < ζ_{Γ_{σ+1}+2}`). -/
theorem gw_b_pi_Z {ν ν' : Ordinal.{0}} (hνT : ν ∈ TB ρ σ) (hν : ν < evZ (evZ (lgG ρ)))
    (hν' : ν' < evZ (evZ (lgG σ))) (hω : ω ≤ ν) (hπ : pi σ ρ ν = ν') :
    veblen 1 (evZ (lgG ρ) + ν) ∈ TB ρ σ ∧
      pi σ ρ (veblen 1 (evZ (lgG ρ) + ν)) = veblen 1 (evZ (lgG σ) + ν') := by
  obtain ⟨e1, e2⟩ := gw_evAZ_pi hB hνT hν (by rw [hπ]; exact hν')
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωT : ω ∈ TB ρ σ := mem_TB_of_lt hB hωσ
  have hω' : ω ≤ ν' := by
    rw [← hπ, ← pi_lt hB hωσ]
    exact ((pi_bijOn hB).2.le_iff_le hωT hνT).2 hω
  rw [hπ, one_add_of_omega0_le hω'] at e2
  rw [one_add_of_omega0_le hω] at e1 e2
  rw [gw_veb_Z, gw_veb_Z]
  exact ⟨e1, e2⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Gw
