import Googology.Trans.PoR.InaccPsi.R2.SwGen

/-!
# Normal-form terms with leaves below `ε_{Ω₂+ω}`, and the image `Θ̂`

`W^E = Ω₂^E`, `log_W E = log_ω E / Ω₂` (`Sg.sgLW`), `L_k = ε_{Ω₂+1+k}`, `ε_{Ω₂+ω} = Sw.swTop`.

* `swLW_lt_self` (**`log_W E < E` for `1 ≤ E < ε_{Ω₂+ω}` unless `E` is a leaf**: a fixed point of `W^·` above
  `Ω₂` is `φ(1, a)` with `Ω₂ < a < Ω₂ + ω`);
* `swTm E` (**the normal-form term**: `eps k` at `E = L_k`, else `W^e·q ⊕ swTm r` with `e = log_W E`,
  `q = E / W^e`, `r = E mod W^e`), `swTm_spec` (**every `E ∈ H_λ` below `ε_{Ω₂+ω}` is the value of its
  well-formed normal-form term**);
* `swTh S λ E = swI (swTm E)` (**the image `Θ̂`**), `swTh_leaf` (`Θ̂ L_k = L̂_k`), `swTh_cnf`
  (**`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`** off the leaves);
* `SwEL`, `SwEU`, `SwNF` (normal form), `swTm_nf` (**the normal-form term is normal, exponents `≤ log_W E`**).

No new axiom.  New definitions: `swTm`, `swTh`, `SwEL`, `SwEU`, `SwNF`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-- **`log_W E < E` below `ε_{Ω₂+ω}` off the leaves.** -/
theorem swLW_lt_self {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < swTop S) (hL : ∀ k, E ≠ swL k) : sgLW E < E := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE1
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  by_contra h
  push Not at h
  have hle : sgLW E ≤ E :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E)
  have heq : sgLW E = E := le_antisymm hle h
  have hWE : leWe E ≤ E := by have h0 := sgLW_le hE0; rwa [heq] at h0
  have h2 : E ≤ Om (1 + 1) * E := Ordinal.le_mul_right E ldOm2_SC.1
  have h3 : Om (1 + 1) * E ≤ leWe E := right_le_opow _ one_lt_omega0
  have hm : Om (1 + 1) * E = E := le_antisymm (h3.trans hWE) h2
  have hfix : ω ^ E = E := by
    refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
    calc ω ^ E = leWe E := by unfold leWe; rw [hm]
      _ ≤ E := hWE
  have hΩE : Om (1 + 1) < E := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · calc Om (1 + 1) = Om (1 + 1) * 1 := (mul_one _).symm
        _ ≤ Om (1 + 1) * E := mul_le_mul_right hE1 _
        _ = E := hm
    · have : Om (1 + 1) * 1 < Om (1 + 1) * Om (1 + 1) := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hW1
      rw [mul_one, e] at this
      rw [e] at hm
      rw [hm] at this
      exact lt_irrefl _ this
  obtain ⟨a, rfl⟩ := (mem_range_veblen one_ne_zero).2 (fun b hb => by
    rw [Order.lt_one_iff] at hb; subst hb; rw [veblen_zero_apply]; exact hfix)
  have ha : a < Om (1 + 1) + ω := (veblen_right_strictMono 1).lt_iff_lt.1 hE
  have hΩa : Om (1 + 1) < a := by
    have h4 : veblen 1 (Om (1 + 1)) < veblen 1 a := by rw [ldOm2_SC.veblen_right hW1]; exact hΩE
    exact (veblen_right_strictMono 1).lt_iff_lt.1 h4
  obtain ⟨m, hm'⟩ : ∃ m : ℕ, a - Om (1 + 1) = m := by
    refine lt_omega0.1 ?_
    refine (add_lt_add_iff_left (Om (1 + 1))).1 ?_
    rwa [Ordinal.add_sub_cancel_of_le hΩa.le]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hm'
    have := Ordinal.add_sub_cancel_of_le hΩa.le
    rw [hm', add_zero] at this
    exact absurd this hΩa.ne
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine hL n ?_
  unfold swL
  congr 1
  rw [← Nat.cast_succ, ← hm', Ordinal.add_sub_cancel_of_le hΩa.le]

open Classical in
/-- **The normal-form term of `E`** (leaves at `L_k`, else `W^e·q ⊕ swTm r`). -/
noncomputable def swTm (E : Ordinal.{0}) : SwT :=
  if h : ∃ k : ℕ, E = swL k then SwT.eps (Classical.choose h)
  else if h' : 0 < E ∧ sgLW E < E then
    swCat (SwT.term SwT.zero (swTm (sgLW E)) (E / leWe (sgLW E))) (swTm (E % leWe (sgLW E)))
  else SwT.zero
termination_by E
decreasing_by
  · exact h'.2
  · exact (Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h'.1)

theorem swTm_leaf (k : ℕ) : swTm (swL k) = SwT.eps k := by
  have h : ∃ k' : ℕ, swL k = swL k' := ⟨k, rfl⟩
  rw [swTm, dif_pos h]
  congr 1
  exact (swL_strictMono.injective (Classical.choose_spec h)).symm

theorem swTm_zero : swTm 0 = SwT.zero := by
  have h : ¬ ∃ k : ℕ, (0 : Ordinal.{0}) = swL k := fun ⟨k, hk⟩ =>
    absurd hk (ne_of_lt (zero_lt_one.trans_le (swL_one_le k)))
  rw [swTm, dif_neg h, dif_neg (fun h => lt_irrefl _ h.1)]

theorem swTm_eq {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < swTop S) (hL : ∀ k, E ≠ swL k) :
    swTm E = swCat (SwT.term SwT.zero (swTm (sgLW E)) (E / leWe (sgLW E))) (swTm (E % leWe (sgLW E))) := by
  have h : ¬ ∃ k : ℕ, E = swL k := fun ⟨k, hk⟩ => hL k hk
  rw [swTm, dif_neg h, dif_pos ⟨zero_lt_one.trans_le hE1, swLW_lt_self hE1 hE hL⟩]

/-- **The image `Θ̂ E`** of the normal-form term. -/
noncomputable def swTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} := swI S l (swTm E)

theorem swTh_zero (l : Ordinal.{0}) : swTh S l 0 = 0 := by unfold swTh; rw [swTm_zero]; rfl

theorem swTh_leaf (l : Ordinal.{0}) (k : ℕ) : swTh S l (swL k) = swLh k := by unfold swTh; rw [swTm_leaf]; rfl

/-- **`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`** off the leaves. -/
theorem swTh_cnf {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) {E : Ordinal.{0}} (hE1 : 1 ≤ E)
    (hE : E < swTop S) (hL : ∀ k, E ≠ swL k) :
    swTh S l E = leOe (swTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      swTh S l (E % leWe (sgLW E)) := by
  unfold swTh
  rw [swTm_eq hE1 hE hL, swI_cat h1]
  show 0 + _ + _ = _
  rw [zero_add]

section Spec

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `E ∈ H_λ` below `ε_{Ω₂+ω}` is the value of its well-formed normal-form term.** -/
theorem swTm_spec : ∀ E, E ∈ cdHull S l → E < swTop S → SwWF S l (swTm E) ∧ swV (swTm E) = E := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [swTm_zero]; exact ⟨trivial, rfl⟩
  by_cases hL : ∃ k, E = swL k
  · obtain ⟨k, rfl⟩ := hL
    rw [swTm_leaf]; exact ⟨trivial, rfl⟩
  push Not at hL
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := swLW_lt_self hE1 hE hL
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
  have hqW : E / leWe e < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : E / leWe e ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH ?_
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hq1 : 1 ≤ E / leWe e := Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe)
  obtain ⟨hew, hev⟩ := IH e hel heH (hel.trans hE)
  obtain ⟨hrw, hrv⟩ := IH _ hr hrH (hr.trans hE)
  rw [swTm_eq hE1 hE hL]
  refine ⟨swWF_cat h1ρ (A := SwT.term SwT.zero (swTm e) (E / leWe e))
    ⟨trivial, hew, (ldHull_iff hl hX hqW).1 hqH, hq1, hqW⟩ _ hrw, ?_⟩
  rw [swV_cat, hrv]
  show 0 + leWe (swV (swTm (sgLW E))) * (E / leWe (sgLW E)) + E % leWe e = E
  rw [zero_add, ← he, hev]
  exact Ordinal.div_add_mod E (leWe e)

end Spec

/-! ## Normal form -/

/-- Every exponent of the term exceeds `r` (the leaf `L_k` counts as the exponent `L_k`). -/
def SwEL (r : Ordinal.{0}) : SwT → Prop
  | .zero => True
  | .eps k => r < swL k
  | .term P R _ => r < swV R ∧ SwEL r P

/-- Every exponent of the term is below `r`. -/
def SwEU (r : Ordinal.{0}) : SwT → Prop
  | .zero => True
  | .eps k => swL k < r
  | .term P R _ => swV R < r ∧ SwEU r P

/-- **Normal form**: the exponents of the prefix exceed the last exponent, recursively. -/
def SwNF : SwT → Prop
  | .zero => True
  | .eps _ => True
  | .term P R _ => SwNF P ∧ SwNF R ∧ SwEL (swV R) P

theorem swEL_cat {r : Ordinal.{0}} {A : SwT} (hA : SwEL r A) : ∀ B, SwEL r B → SwEL r (swCat A B)
  | .zero, _ => hA
  | .eps _, h => ⟨h, hA⟩
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, swEL_cat hA P h2⟩

theorem swEU_cat {r : Ordinal.{0}} {A : SwT} (hA : SwEU r A) : ∀ B, SwEU r B → SwEU r (swCat A B)
  | .zero, _ => hA
  | .eps _, h => ⟨h, hA⟩
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, swEU_cat hA P h2⟩

theorem swEU_mono {r r' : Ordinal.{0}} (h : r ≤ r') : ∀ t, SwEU r t → SwEU r' t
  | .zero, _ => trivial
  | .eps _, h1 => h1.trans_le h
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1.trans_le h, swEU_mono h P h2⟩

theorem swNF_cat {m : Ordinal.{0}} {A : SwT} (hA : SwNF A) (hAm : ∀ x, x < m → SwEL x A) :
    ∀ B, SwNF B → SwEU m B → SwNF (swCat A B)
  | .zero, _, _ => hA
  | .eps _, _, h => ⟨hA, trivial, hAm _ h⟩
  | .term P _ _, ⟨hP, hR, hPR⟩, ⟨hRm, hPm⟩ => ⟨swNF_cat hA hAm P hP hPm, hR, swEL_cat (hAm _ hRm) P hPR⟩

/-- **The normal-form term of every `E < ε_{Ω₂+ω}` has the value `E`, is normal, with exponents `≤ log_W E`.** -/
theorem swTm_nf : ∀ E, E < swTop S → swV (swTm E) = E ∧ SwNF (swTm E) ∧ SwEU (sgLW E + 1) (swTm E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [swTm_zero]; exact ⟨rfl, trivial, trivial⟩
  by_cases hL : ∃ k, E = swL k
  · obtain ⟨k, rfl⟩ := hL
    rw [swTm_leaf]
    refine ⟨rfl, trivial, ?_⟩
    show swL k < sgLW (swL k) + 1
    have : sgLW (swL k) = swL k := by
      unfold sgLW
      conv_lhs => rw [← swL_We k]
      unfold leWe
      rw [log_opow one_lt_omega0, Ordinal.mul_div_cancel _ ldOm2_SC.1.ne']
    rw [this]; exact lt_add_one _
  push Not at hL
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  have hel : sgLW E < E := swLW_lt_self hE1 hE hL
  have hWe : leWe (sgLW E) ≤ E := sgLW_le hpos
  have hW0 : leWe (sgLW E) ≠ 0 := (leWe_pos _).ne'
  have hrW : E % leWe (sgLW E) < leWe (sgLW E) := Ordinal.mod_lt _ hW0
  have hr : E % leWe (sgLW E) < E := hrW.trans_le hWe
  obtain ⟨hev, hen, -⟩ := IH _ hel (hel.trans hE)
  obtain ⟨hrv, hrn, hru⟩ := IH _ hr (hr.trans hE)
  have hrU : SwEU (sgLW E) (swTm (E % leWe (sgLW E))) := by
    rcases eq_or_ne (E % leWe (sgLW E)) 0 with h0 | h0
    · rw [h0, swTm_zero]; trivial
    have h1 : leWe 0 ≤ E % leWe (sgLW E) := by
      rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 h0
    exact swEU_mono (Order.add_one_le_of_lt (sjLogW h1 hrW).2) _ hru
  rw [swTm_eq hE1 hE hL]
  refine ⟨?_, ?_, ?_⟩
  · rw [swV_cat, hrv]
    show 0 + leWe (swV (swTm (sgLW E))) * (E / leWe (sgLW E)) + E % leWe (sgLW E) = E
    rw [zero_add, hev]
    exact Ordinal.div_add_mod E (leWe (sgLW E))
  · have hA : SwNF (SwT.term SwT.zero (swTm (sgLW E)) (E / leWe (sgLW E))) := ⟨trivial, hen, trivial⟩
    have hAm : ∀ x, x < sgLW E → SwEL x (SwT.term SwT.zero (swTm (sgLW E)) (E / leWe (sgLW E))) :=
      fun x hx => ⟨by rw [hev]; exact hx, trivial⟩
    exact swNF_cat hA hAm _ hrn hrU
  · have hA : SwEU (sgLW E + 1) (SwT.term SwT.zero (swTm (sgLW E)) (E / leWe (sgLW E))) :=
      ⟨by rw [hev]; exact Order.lt_add_one_iff.2 le_rfl, trivial⟩
    exact swEU_cat hA _ (swEU_mono le_self_add _ hrU)

end Googology.Trans.PoR.InaccPsi.R2.Sw
