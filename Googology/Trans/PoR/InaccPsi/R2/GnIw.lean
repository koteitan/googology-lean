import Googology.Trans.PoR.InaccPsi.R2.GnE2

/-!
# LEMMA IMG BELOW `ε_{Γ_{ρ+1}+ω}`: the finite `ε`-iterates above `Γ_{ρ+1}`

`eNG n x = ε_{Γ_{x+1}+1+n}` (`eNG 0 x = ε_{Γ_{x+1}+1}`, `eNG (n+1) x = ε_{eNG n x + 1}`) is the atom
`ϑˣ(Ω₁ + Γ_{x+1} + n)` (`gn_eNG`, `Gl.glA_eN_one`), so Lemma EXACT holds (`Gl.glA_pi`), and Lemma IMG in `π`-form
passes from `eNG n` to `eNG (n+1)` (the copy of an `ε`-number above the copy of `eNG n` is an `ε`-number,
`R2.GnE1` `gnI_eNG`).  With the generic step `gnImg_of_eps` of `R2.GnImg`:

* `eNG`, `eNG_glA`, `eNG_pi` (**Lemma EXACT for `ε_{Γ_{ρ+1}+1+n}`**), `eNG_lt1`, `gnI_eNGn`;
* `gnImg_Gw` (**Lemma IMG for every value below `ε_{Γ_{ρ+1}+ω} = sup_n eNG n ρ`**), `gnPkg_of_exW` (**Lemma IMG
  (gated) for a specified function with Lemma EXACT and value below `ε_{Γ_{ρ+1}+ω}`**).

No new axiom.  New definition: `eNG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The finite `ε`-iterates above `Γ_{x+1}`**: `eNG n x = ε_{Γ_{x+1}+1+n}`. -/
noncomputable def eNG : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, x => eN (lgG x)
  | n + 1, x => eN (eNG n x)

theorem eNG_E (n : ℕ) (x : Ordinal.{0}) : InE (eNG n x) := by
  cases n with
  | zero => exact eN_E _
  | succ n => exact eN_E _

theorem eNG_lt_succ (n : ℕ) (x : Ordinal.{0}) : eNG n x < eNG (n + 1) x := lt_eN _

theorem eNG_mono {m n : ℕ} (h : m < n) (x : Ordinal.{0}) : eNG m x < eNG n x := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact (ih h').trans (eNG_lt_succ n x)
    · exact eNG_lt_succ m x

theorem G_lt_eNG (n : ℕ) (x : Ordinal.{0}) : lgG x < eNG n x := by
  rcases n with _ | n
  · exact lt_eN _
  · exact (lt_eN _).trans (eNG_mono (Nat.succ_pos n) x)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gn_Gn_lt1 (n : ℕ) : lgG x + n < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (mg_lgG_lt_G1 hx hx1) ((natCast_lt_omega0 n).trans (omega0_lt_inE hq))

/-- **`ε_{Γ_{x+1}+1+n} = ϑˣ(Ω₁ + Γ_{x+1} + n)`.** -/
theorem eNG_glA : ∀ n : ℕ, eNG n x = glA 1 (lgG x + n) x
  | 0 => by rw [Nat.cast_zero, add_zero]; exact gn_eNG hx hx1
  | n + 1 => by
    have hnT := gm1_T hx hx1 (gn_Gn_lt1 hx hx1 n)
    show eN (eNG n x) = glA 1 (lgG x + ((n + 1 : ℕ) : Ordinal.{0})) x
    rw [eNG_glA n, glA_eN_one hx hx1 hnT.1 hnT.2, Nat.cast_succ, add_assoc]

theorem eNG_lt1 (n : ℕ) : eNG n x < gq 1 x := by
  rcases n with _ | n
  · exact gn_eNG_lt1 hx hx1
  · rw [eNG_glA hx hx1 (n + 1)]
    have hSC := (gm1_facts hx hx1).2.2.2
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have hn := gn_Gn_lt1 hx hx1 (n + 1)
    have hnT := gm1_T hx hx1 hn
    exact lgVt_lt_low hx hx1 h1T h11 hnT.1 hnT.2 h1T h11 (one_lt_omega0.trans (omega0_lt_inE hSC)) hn

end Base

/-- **Lemma EXACT for `ε_{Γ_{ρ+1}+1+n}`** at every pair of bases. -/
theorem eNG_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) :
    eNG n ρ ∈ TB ρ σ ∧ pi σ ρ (eNG n ρ) = eNG n σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨g1, g2⟩ := mg_lgG_pi hB
  have hn : (n : Ordinal.{0}) < σ := (natCast_lt_omega0 n).trans (omega0_lt_inE hB.1)
  obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hn)
  rw [g2, pi_lt hB hn] at s2
  have hs1 : lgG ρ + n < Om1 := (gm1_T hB.2.1 hρ1 (gn_Gn_lt1 hB.2.1 hρ1 n)).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 hs1
  rw [o2, s2, ← eNG_glA hB.2.1 hρ1 n, ← eNG_glA hB.1 hσ1 n] at h
  exact h

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG in `π`-form for `ε_{Γ_{ρ+1}+1+n}`.** -/
theorem gnI_eNGn : ∀ n : ℕ, GnI ρ δ (eNG n ρ)
  | 0 => gnI_eNG h
  | n + 1 => by
    classical
    have hρE := h.ρE
    set E := eNG (n + 1) ρ with hEdef
    set E' := eNG n ρ with hE'def
    have hE : InE E := eNG_E _ _
    have hET : E ∈ Tset ρ ∧ E < Om1 := gm1_T hρE h.ρ1 (eNG_lt1 hρE h.ρ1 (n + 1))
    have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
    have hEEδ : E + E < δ := (inE_indec h.δE).add_lt hEδ hEδ
    have hρE' : ρ < E := ((lgG_facts hρE h.ρ1).2.1.trans (G_lt_eNG (n + 1) ρ))
    have hE'E : E' < E := eNG_lt_succ n ρ
    obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (gnI_eNGn n)
    have w2 := w1.insW hρE'.le hEδ (Or.inl (inE_indec hE))
    have w3 := w2.insW (hρE'.le.trans le_self_add) hEEδ
      (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
    refine gnI_mk h w3 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    obtain ⟨hE'A, -, pE'⟩ := b1 A f hW1 hZ1 C
    have hEA : E ∈ A := hW (by simp)
    have hEEA : E + E ∈ A := hW (by simp)
    have hB := h.img_bases C
    have hfE'E : f E' < f E := C.mono hE'A hEA hE'E
    have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE' hEEδ.le) (lt_of_le_of_lt zero_le hfE'E)
    rw [(eNG_pi hB (n + 1)).2]
    rw [(eNG_pi hB n).2] at pE'
    exact eN_le (lt_of_le_of_lt pE' hfE'E) hfE

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ε_{Γ_{ρ+1}+ω}`** (`= sup_n ε_{Γ_{ρ+1}+1+n}`). -/
theorem gnImg_Gw : ∀ v, (∃ n : ℕ, v < eNG n ρ) → GnI ρ δ v := by
  have hρE := h.ρE
  intro v ⟨N, hvN⟩
  refine gnImg_of_eps h (B := eNG N ρ) (fun u hu => gm1_T hρE h.ρ1 (hu.trans (eNG_lt1 hρE h.ρ1 N)))
    (fun e he _ heB _ => ?_) v hvN
  rcases lt_trichotomy e (lgG ρ) with hlt | rfl | hgt
  · exact gnI_lowG h hlt
  · exact gnI_G h
  -- an `ε`-number in `(Γ_{ρ+1}, eNG N ρ)` is some `eNG n ρ`
  have key : ∀ n : ℕ, e < eNG n ρ → ∃ m, m ≤ n ∧ e = eNG m ρ := by
    intro n
    induction n with
    | zero => intro h0; exact absurd (eN_le hgt he) (not_le.2 h0)
    | succ n ih =>
      intro h1
      rcases lt_trichotomy e (eNG n ρ) with h2 | h2 | h2
      · obtain ⟨m, hm, rfl⟩ := ih h2; exact ⟨m, hm.trans (Nat.le_succ n), rfl⟩
      · exact ⟨n, Nat.le_succ n, h2⟩
      · exact absurd (eN_le h2 he) (not_le.2 h1)
  obtain ⟨m, -, rfl⟩ := key N heB
  exact gnI_eNGn h m

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ε_{Γ_{ρ+1}+ω}`.** -/
theorem gnPkg_of_exW {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : ∃ n : ℕ, T ρ < eNG n ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (gnImg_Gw h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Gn
