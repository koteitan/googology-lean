import Googology.Trans.PoR.InaccPsi.R2.VpRun

/-!
# Normal forms `z = Hˡ⁽ˢ⁾_λ(y)` at every finite threshold `W = Ω_{s+1}`

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ = S.psi · W`, `Hˡ⁽ˢ⁾_γ = Ul.ulH S s γ`.  The **level** `λ = vpLev S s z`
of a strongly critical `z > Ω_s` is the least level `γ < V` visible at `z` (`ulD S s γ < z`) with `Hˡ⁽ˢ⁾_γ(z) ≠ z`;
the **index** is `y = vpI S s λ z`.  The generalization of `R2.VdNF` (which is the case `s = 1`, `vpLev_one`) to every
`s`:

* `vpI_spec`, `vpI_H`, `vpLev_spec` (**the level is below `V`, visible at `z`, does not fix `z`, every lower visible
  level fixes `z`, and `z` is a value of `Hˡ⁽ˢ⁾_λ`**), `vp_nf` (**`z = Hˡ⁽ˢ⁾_λ(y)` with `y < z`**), `vpLev_H`
  (**`Hˡ⁽ˢ⁾_γ(y)` with `γ < V`, `y < Hˡ⁽ˢ⁾_γ(y)` has level `γ` and index `y`**);
* `vp_nf_ex` (**every strongly critical `z ∈ (Ω_s, ψ_W(A))` has a normal form**: `z = ψ(e)`, `e` own; the level is the
  last exponent `k` of `e` in base `W` when `k < V`, else `ψ_V(e)`);
* `vpLev_one`, `vpI_one` (**at `s = 1` these are `Vd.vdLev`, `Vd.vdI`**).

No new axiom.  New definitions: `vpLevSet`, `vpLev`, `vpI` (the generic-`s` level and index).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- The levels below `V = Ω_{s+2}`, visible at `z`, that do not fix `z`. -/
def vpLevSet (S : InaccSeq.{0}) (s z : Ordinal.{0}) : Set Ordinal.{0} :=
  {γ | γ < Om (s + 1 + 1) ∧ ulD S s γ < z ∧ ulH S s γ z ≠ z}

/-- **The level** of `z` at the threshold `Ω_{s+1}`. -/
noncomputable def vpLev (S : InaccSeq.{0}) (s z : Ordinal.{0}) : Ordinal.{0} := sInf (vpLevSet S s z)

/-- **The index** of `z` in `Hˡ⁽ˢ⁾_γ`. -/
noncomputable def vpI (S : InaccSeq.{0}) (s γ z : Ordinal.{0}) : Ordinal.{0} := sInf {y | ulH S s γ y = z}

theorem vpI_spec {γ z : Ordinal.{0}} (h : ∃ y, ulH S s γ y = z) : ulH S s γ (vpI S s γ z) = z := csInf_mem h

theorem vpI_H (γ y : Ordinal.{0}) : vpI S s γ (ulH S s γ y) = y :=
  (ulH_normal (S := S) (s := s) γ).strictMono.injective (vpI_spec ⟨y, rfl⟩)

/-- **The level of a strongly critical `z > Ω_s` whose level set is not empty.** -/
theorem vpLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : Om s < z) (hne : (vpLevSet S s z).Nonempty) :
    vpLev S s z < Om (s + 1 + 1) ∧ ulD S s (vpLev S s z) < z ∧ ulH S s (vpLev S s z) z ≠ z ∧
      (∀ γ < vpLev S s z, ulD S s γ < z → ulH S s γ z = z) ∧ z ∈ range (ulH S s (vpLev S s z)) := by
  have hm : vpLev S s z ∈ vpLevSet S s z := csInf_mem hne
  have hlow : ∀ γ < vpLev S s z, ulD S s γ < z → ulH S s γ z = z := fun γ hγ hc => by
    by_contra h
    have hγm : γ ∈ vpLevSet S s z := ⟨hγ.trans hm.1, hc, h⟩
    exact absurd (csInf_le' hγm : vpLev S s z ≤ γ) (not_le.2 hγ)
  exact ⟨hm.1, hm.2.1, hm.2.2, hlow, ucG_range (d := ulD S s) (L := Om s) hSC h1 hm.2.1 hlow⟩

/-- **The normal form**: `z = Hˡ⁽ˢ⁾_λ(y)` with `λ = vpLev S s z`, `y = vpI S s λ z < z`. -/
theorem vp_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : Om s < z) (hne : (vpLevSet S s z).Nonempty) :
    ulH S s (vpLev S s z) (vpI S s (vpLev S s z) z) = z ∧ vpI S s (vpLev S s z) z < z := by
  obtain ⟨-, -, hne', -, hr⟩ := vpLev_spec hSC h1 hne
  have hI := vpI_spec hr
  refine ⟨hI, lt_of_le_of_ne ?_ fun e => ?_⟩
  · calc vpI S s (vpLev S s z) z ≤ ulH S s (vpLev S s z) (vpI S s (vpLev S s z) z) := ulH_le_self _ _
      _ = z := hI
  · rw [e] at hI; exact hne' hI

/-- **`Hˡ⁽ˢ⁾_γ(y)` with `γ < V` and `y < Hˡ⁽ˢ⁾_γ(y)` has level `γ` and index `y`.** -/
theorem vpLev_H {γ y : Ordinal.{0}} (hγ : γ < Om (s + 1 + 1)) (hy : y < ulH S s γ y) :
    vpLev S s (ulH S s γ y) = γ ∧ vpI S s γ (ulH S s γ y) = y := by
  have hne : ulH S s γ (ulH S s γ y) ≠ ulH S s γ y := fun e =>
    absurd ((ulH_normal (S := S) (s := s) γ).strictMono.injective e) (ne_of_gt hy)
  have hmem : γ ∈ vpLevSet S s (ulH S s γ y) := ⟨hγ, ulH_D_lt γ y, hne⟩
  refine ⟨le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_), vpI_H γ y⟩
  have hm : vpLev S s (ulH S s γ y) ∈ vpLevSet S s (ulH S s γ y) := csInf_mem ⟨γ, hmem⟩
  exact hm.2.2 (ucG_fix_lower hlt ⟨y, rfl⟩ hm.2.1)

/-- **Every strongly critical `z ∈ (Ω_s, ψ_W(A))` has a normal form** (`s` finite). -/
theorem vp_nf_ex (hs : s < ω) {z A : Ordinal.{0}} (hSC : SC z) (h1 : Om s < z) (hz : z < S.psi A (Om (s + 1))) :
    (vpLevSet S s z).Nonempty := by
  obtain ⟨e, hown, he⟩ := Ui.ui_own_of_SC (S := S) (s := s) hs hSC h1 hz
  rcases eq_or_ne e 0 with he0 | he0
  · subst he0
    have h0 : ulH S s 0 0 = z := by rw [Us.us_psi0 hs]; exact he
    refine ⟨0, (Ui.ui_SC_W (s + 1)).1, ?_, ?_⟩
    · rw [← h0]; exact ulH_D_lt 0 0
    · rw [← h0]; exact Us.us_val0_ne
  obtain ⟨k, hk, hk1, hkK, hkV⟩ := Us.us_last_K hs hown he0
  by_cases hkV' : k < Om (s + 1 + 1)
  · refine ⟨k, hkV', ?_, fun hfix => ?_⟩
    · rw [← he]; exact (ul_vis (Ui.ui_psi_SC e)).2 hkK
    · rw [← he] at hfix
      exact hk1 ((Us.us_fix_iff hs hown he0 hkV').1 hfix).1
  · have hgV : S.psi e (Om (s + 1 + 1)) < Om (s + 1 + 1) := Ui.ui_psi_lt (s := s + 1) e
    have hgK : UlK S s z (S.psi e (Om (s + 1 + 1))) := by
      rw [← he]
      exact UlK.coll (InR_Om_succ (s + 1)) (Us.us_W_ne_Om (s := s + 1) (lt_add_one s).ne)
        (Us.us_K_Om (Ui.ui_s1_lt_omega hs)) (ul_K_of_mem hown)
    refine ⟨_, hgV, (ul_vis hSC).2 hgK, fun hfix => ?_⟩
    rw [← he] at hfix
    exact lt_irrefl _ ((Us.us_fix_iff hs hown he0 hgV).1 hfix).2.1

/-- **At `s = 1` the level is `Vd.vdLev`.** -/
theorem vpLev_one (z : Ordinal.{0}) : vpLev S 1 z = Vd.vdLev S z := by
  unfold vpLev Vd.vdLev
  rw [Vd.vdLevSet_eq]; rfl

/-- **At `s = 1` the index is `Vd.vdI`.** -/
theorem vpI_one (γ z : Ordinal.{0}) : vpI S 1 γ z = Vd.vdI S γ z := by
  unfold vpI Vd.vdI
  rw [Vd.vdH_eq]

end Googology.Trans.PoR.InaccPsi.R2.Vp
