import Googology.Trans.PoR.InaccPsi.R2.TeLong

/-!
# The `ε`-atoms above `Γ_{x+1}`: `ϑˣ(Ω₁ + Γ_{x+1} + ν) = ε_{Γ_{x+1}+1+ν}` for transfinite `ν`, and Lemma EXACT

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Γ = Γ_{x+1}` (`lgG x`), `ε_{Γ+c}` (`evA Γ c`, the `c`-th `ε`-number from `Γ` on), `ϑˣ(Ω₁ + t)` (`Gl.glA 1 t x`).
`EvV.vt_Om1_add_eq_gen` gives `ϑˣ(Ω₁ + η) = ε_{x+1+η}` only while no `η' ≤ η` is a fixed point `η' = ε_{x+1+η'}`, so
it stops at `ζ_{x+1} < Γ`.  With the pseudo-base `Γ` (`Gn.gn_eNG`: `ϑˣ(Ω₁ + Γ) = ε_{Γ+1}`):

* `teGlA_eq` (**`ϑˣ(Ω₁ + Γ + ν) = ε_{Γ+1+ν}`** for every `ν` with `Γ + ν < Γ_{x+2}` and no limit `ν' ≤ ν` with
  `ε_{Γ+1+ν'} ≤ Γ + ν'`; successors by `Gl.glA_eN_one`, limits by the minimality `Gl.glA_min` and the normality of
  `ν ↦ ε_{Γ+ν}`), `teGlA_eq_lt` (**the case `ν < Γ`, no hypothesis**);
* `teEvA_pi` (**Lemma EXACT for `ε_{Γ_{ρ+1}+1+ν}`**: `π_{σ,ρ}(ε_{Γ_{ρ+1}+1+ν}) = ε_{Γ_{σ+1}+1+π(ν)}` for every
  `ν ∈ Tᵖ[σ]` below `Γ_{ρ+1}`, from `Gl.glA_pi`, [W07a] Def 5.1).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁ + Γ_{x+1} + ν) = ε_{Γ_{x+1}+1+ν}`** below `Γ_{x+2}`, up to the first fixed point. -/
theorem teGlA_eq : ∀ ν, lgG x + ν < Gb.gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → lgG x + ν' < evA (lgG x) (1 + ν')) →
    Gl.glA 1 (lgG x + ν) x = evA (lgG x) (1 + ν) := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  obtain ⟨h1T, h11⟩ := Gl.gl_one_T hx hx1
  have h1G : (1 : Ordinal.{0}) < lgG x := Lu.lu_one_lt_E hGE
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := Gm.gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0
    rw [add_zero, add_zero, ← Gn.gn_eNG hx hx1]
    have h := evA_add_one (lgG x) 0
    rw [evA_zero hGE, zero_add] at h
    exact h.symm
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : lgG x + d < Gb.gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    obtain ⟨hdT, hd1⟩ := Gm.gm1_T hx hx1 hdq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc, ← Gl.glA_eN_one hx hx1 hdT hd1, IHd, ← add_assoc, evA_add_one]
  · -- a limit `ν`
    have hων : ω ≤ ν := omega0_le_of_isSuccLimit hlim
    have h1ν : 1 + ν = ν := one_add_of_omega0_le hων
    set u := evA (lgG x) (1 + ν) with hu_def
    have huE : InE u := evA_E _ _
    have hGu : lgG x < u := by
      calc lgG x = evA (lgG x) 0 := (evA_zero hGE).symm
        _ < u := evA_lt_iff.2 (lt_of_lt_of_le zero_lt_one le_self_add)
    have htu : lgG x + ν < u := hfix ν le_rfl hlim
    have hP : Lu.LuP 1 u := by
      have h := vzP_one.2 huE; unfold VzP at h; rwa [Nat.cast_one] at h
    have hval : ∀ ν'', ν'' < ν → Gl.glA 1 (lgG x + ν'') x = evA (lgG x) (1 + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq)
        (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    refine le_antisymm ?_ ?_
    · refine Gl.glA_min hx hx1 le_rfl h1T h11 htT ht1 hP (hxG.trans hGu) htu (h1G.trans hGu)
        (fun σ hσ => ?_)
      rcases lt_or_ge σ (lgG x) with hσG | hσG
      · exact (Gl.glA_lt_G hx hx1 h1G hσG).trans hGu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσG
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact evA_lt_iff.2 ((add_lt_add_iff_left 1).2 hν'')
    · rw [hu_def, h1ν]
      refine ((evA_isNormal (lgG x)).le_iff_forall_le hlim).2 fun c hc => ?_
      obtain ⟨-, -, -, -, -, htA⟩ := Gl.glA_facts hx hx1 le_rfl h1T h11 htT ht1
      rcases eq_or_ne c 0 with rfl | hc0
      · rw [evA_zero hGE]; exact (le_self_add.trans htA.le)
      · have h1c : 1 ≤ c := one_le_iff_ne_zero.2 hc0
        have hc' : c - 1 < ν := lt_of_le_of_lt (sub_le_self c 1) hc
        rw [← ev_one_add_sub_one h1c, ← hval _ hc']
        have hq' : lgG x + (c - 1) < Gb.gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := Gm.gm1_T hx hx1 hq'
        exact (Gl.glA_lt_of hx hx1 le_rfl h1T h11 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

/-- `Γ_{x+1} + ν < Γ_{x+2}` for `ν < Γ_{x+1}`. -/
theorem te_G_add_lt {ν : Ordinal.{0}} (hν : ν < lgG x) : lgG x + ν < Gb.gq 1 x := by
  have hq := (Gm.gm1_facts hx hx1).2.2.2
  have hG := Gm.mg_lgG_lt_G1 hx hx1
  exact hq.add_lt hG (hν.trans hG)

/-- **`ϑˣ(Ω₁ + Γ_{x+1} + ν) = ε_{Γ_{x+1}+1+ν}` for every `ν < Γ_{x+1}`.** -/
theorem teGlA_eq_lt {ν : Ordinal.{0}} (hν : ν < lgG x) :
    Gl.glA 1 (lgG x + ν) x = evA (lgG x) (1 + ν) := by
  obtain ⟨-, -, -, hGE, -⟩ := lgG_facts hx hx1
  refine teGlA_eq hx hx1 ν (te_G_add_lt hx hx1 hν) fun ν' hν' _ => ?_
  have hlt : lgG x + ν' < lgG x + lgG x := (add_lt_add_iff_left _).2 (lt_of_le_of_lt hν' hν)
  have h2 : lgG x + lgG x < eN (lgG x) := (eN_E _).add_lt (lt_eN _) (lt_eN _)
  have h3 : eN (lgG x) ≤ evA (lgG x) (1 + ν') := by
    have h := evA_add_one (lgG x) 0
    rw [evA_zero hGE, zero_add] at h
    rw [← h]; exact evA_le_iff.2 le_self_add
  exact (hlt.trans h2).trans_le h3

end Base

/-- **Lemma EXACT for `ε_{Γ_{ρ+1}+1+ν}`**: `π_{σ,ρ}(ε_{Γ_{ρ+1}+1+ν}) = ε_{Γ_{σ+1}+1+π(ν)}` for every
`ν ∈ Tᵖ[σ]` below `Γ_{ρ+1}`. -/
theorem teEvA_pi {σ ρ ν : Ordinal.{0}} (hB : Bases σ ρ) (hνT : ν ∈ TB ρ σ) (hν : ν < lgG ρ) :
    evA (lgG ρ) (1 + ν) ∈ TB ρ σ ∧ pi σ ρ (evA (lgG ρ) (1 + ν)) = evA (lgG σ) (1 + pi σ ρ ν) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := Gm.mg_lgG_pi hB
  obtain ⟨s1, s2⟩ := pi_add hB g1 hνT
  rw [g2] at s2
  have hπν : pi σ ρ ν < lgG σ := by rw [← g2]; exact (pi_bijOn hB).2 hνT g1 hν
  have hs1 : lgG ρ + ν < Om1 := (Gm.gm1_T hB.2.1 hρ1 (te_G_add_lt hB.2.1 hρ1 hν)).2
  have h := Gl.glA_pi hB o1 (Gl.gl_one_T hB.2.1 hρ1).2 s1 hs1
  rw [o2, s2, teGlA_eq_lt hB.2.1 hρ1 hν, teGlA_eq_lt hB.1 hσ1 hπν] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Te
