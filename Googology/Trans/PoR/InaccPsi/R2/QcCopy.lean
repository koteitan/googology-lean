import Googology.Trans.PoR.InaccPsi.R2.QcSub
import Googology.Trans.PoR.InaccPsi.R2.HeCopy
import Googology.Trans.PoR.InaccPsi.R2.GkImg
import Googology.Trans.PoR.InaccPsi.R2.GwImg
import Googology.Trans.PoR.InaccPsi.R2.LvETh
import Googology.Trans.PoR.InaccPsi.R2.GgFront

/-!
# QcCopy: THE COPY LEMMA FOR THE READINGS `Θ_E(z)` OF THE CODES `z < ε_{Ω₁+1}`

`Θ_y = Gg.ggTh y` (for a strongly critical `y`: the substitution `Ω₁ ↦ y` on the Cantor normal form, `Qc.qcSub_eq_th`),
`π = π_{f(ρ),ρ}`.  `He.he_wz_mul` gives `f(E)·π(c) ≤ f(E·c)` for `c < E`.  The reach of a point `E = ϑᵖ(Ω₁·M + σ)` of
a level `Ω₁ ≤ M < ε_{Ω₁+1}` is `Θ_E(rjL(Ω₁·M)) + ζ` (`Rj.rj_lh`), a value `Θ_E(z)` of a code `z ≥ Ω₁·Ω₁`.  Here, for
every code `z < ε_{Ω₁+1}` over a strongly critical `E` (Lemma IMG below `E`): the witness sets can be enlarged to
contain `Θ_E(z)`, and then in every copy `f` and for every strongly critical `u ∈ Tᵖ[f(ρ)]` with `π(u) = f(E)` over
which `z` is a code, **`π(Θ_u(z)) ≤ f(Θ_E(z))`**.

* `qc_split` (**`g = g₁ + ω^{g₂}` with codes `g₁ < g`, `g₂ = logend(g)`, `ω^{g₂} ∣ g₁`**), `qc_split_unique`,
  `qc_pi_eN` (`π(x) < ε_{π(u)+1}` for `x < ε_{u+1}`);
* `qc_copy` (**THE COPY LEMMA**): below `Ω₁` Lemma IMG; at `Ω₁` the hypothesis `π(u) = f(E)`; a sum
  `ω^{log z} + (z − ω^{log z})` by `f(a + b) = f(a) + f(b)`; a power `ω^g`, `g = g₁ + ω^{g₂}`, as in `He.he_wz_mul`:
  `f(ω^{Θ_E(g)}) = ω^{a'}`, `a' > π(Θ_u(g₁))` from the power `ω^{g₁}`, and the source `ω^G ≤₁ ω^G + Θ_E(g₂)`
  (`Lu.lu_lh_opow`) gives `logend(a') ≥ f(Θ_E(g₂)) ≥ π(Θ_u(g₂))` ([W07b] Theorem 2.2, `le1R_thm22`), unless
  `f(ω^G)` is a `υ`-point, which is above `ε_{f(E)+1} > π(Θ_u(z))`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.He Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Hc

/-- **The last-term split of a nonzero code** into codes: `g = g₁ + ω^{g₂}`, `g₁ < g`, `g₂ = logend(g)`,
`ω^{g₂} ∣ g₁`. -/
theorem qc_split {y : Ordinal.{0}} (hy : SC y) : ∀ g, GgCl y g → g ≠ 0 →
    ∃ g₁ g₂, g = g₁ + ω ^ g₂ ∧ g₁ < g ∧ GgCl y g₁ ∧ GgCl y g₂ ∧ g₂ = lg g ∧ ω ^ g₂ ∣ g₁ := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg hg0
  obtain ⟨hsub, hlog⟩ := ggDec hy g hg
  obtain ⟨hdec, hk0, hkω, hr⟩ := Si.si_dec hg0
  set L := log ω g with hL
  obtain ⟨k, hk⟩ := lt_omega0.1 hkω
  rw [hk] at hdec hk0
  have hwk : GgCl y (ω ^ L * k) := GgCl.mul_nat hy.1 (GgCl.opow hy.1 hlog) k
  have hle : ω ^ L * k ≤ g := by
    conv_rhs => rw [← hdec]
    exact le_self_add
  have hrC : GgCl y (g % ω ^ L) := by
    have e : g - ω ^ L * k = g % ω ^ L := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    rw [← e]; exact hsub _ hwk hle
  have hw0 : (0 : Ordinal.{0}) < ω ^ L := opow_pos _ omega0_pos
  rcases eq_or_ne (g % ω ^ L) 0 with hr0 | hr0
  · have hkn : k ≠ 0 := fun h0 => hk0 (by rw [h0, Nat.cast_zero])
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkn
    have hg' : g = ω ^ L * k' + ω ^ L := by
      conv_lhs => rw [← hdec]
      rw [hr0, add_zero, Nat.cast_succ, mul_add_one]
    refine ⟨ω ^ L * k', L, hg', ?_, GgCl.mul_nat hy.1 (GgCl.opow hy.1 hlog) k', hlog, ?_, dvd_mul_right _ _⟩
    · conv_rhs => rw [hg']
      exact lt_add_of_pos_right _ hw0
    · rw [hg', lu_lg_add_right hw0.ne', LvE.lve_lg_opow]
  · have hrg : g % ω ^ L < g := rj_mod_lt hg0
    obtain ⟨r₁, r₂, hrs, hr₁, hr₁C, hr₂C, hr₂l, hr₂d⟩ := IH _ hrg hrC hr0
    have hg' : g = (ω ^ L * k + r₁) + ω ^ r₂ := by
      rw [add_assoc, ← hrs, hdec]
    refine ⟨ω ^ L * k + r₁, r₂, hg', ?_, GgCl.add hwk hr₁C, hr₂C, ?_, ?_⟩
    · conv_rhs => rw [hg']
      exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
    · rw [hr₂l]
      conv_rhs => rw [← hdec]
      rw [lu_lg_add_right hr0]
    · refine dvd_add (dvd_mul_of_dvd_left (opow_dvd_opow ω ?_) _) hr₂d
      have h1 : ω ^ r₂ ≤ g % ω ^ L := by
        rw [hrs]; exact le_add_self
      have h2 : ω ^ r₂ < ω ^ L := h1.trans_lt hr
      exact ((opow_lt_opow_iff_right one_lt_omega0).1 h2).le

/-- **The split is unique**: two prefixes of `g` divisible by `ω^{logend g}` agree. -/
theorem qc_split_unique {g a b c : Ordinal.{0}} (ha : g = a + ω ^ c) (hb : g = b + ω ^ c) (hda : ω ^ c ∣ a)
    (hdb : ω ^ c ∣ b) : a = b := by
  obtain ⟨m, rfl⟩ := hda
  obtain ⟨m', rfl⟩ := hdb
  have hw0 : ω ^ c ≠ 0 := (opow_pos _ omega0_pos).ne'
  have e : ω ^ c * (m + 1) = ω ^ c * (m' + 1) := by rw [mul_add_one, mul_add_one, ← ha, ← hb]
  have e2 : m + 1 = m' + 1 := mul_left_cancel₀ hw0 e
  rw [show m = m' from by simpa [← Order.succ_eq_add_one] using e2]

/-- **`π(x) < ε_{π(u)+1}`** for `x ∈ Tᵖ[σ]` below `ε_{u+1}` (`u ∈ Tᵖ[σ] ∩ Ω₁`, `υ`-points `σ < ρ`). -/
theorem qc_pi_eN {σ ρ u x : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (hx : x ∈ TB ρ σ) (hxu : x < eN u) : pi σ ρ x < eN (pi σ ρ u) := by
  have hS := qc_Om1_SC
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hxu
  have key : ∀ m : ℕ, (fun a => ω ^ a)^[m] (u + 1) ∈ TB ρ σ ∧ (fun a => ω ^ a)^[m] (u + 1) < Om1 ∧
      pi σ ρ ((fun a => ω ^ a)^[m] (u + 1)) = (fun a => ω ^ a)^[m] (pi σ ρ u + 1) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨h1, hp1⟩ := one_TB hB
      obtain ⟨hT, hπ⟩ := pi_add hB hu h1
      refine ⟨hT, hS.isSuccLimit.add_one_lt hu1, ?_⟩
      simp only [Function.iterate_zero, id]
      rw [hπ, hp1]
    | succ m ih =>
      obtain ⟨hT, h1, hπ⟩ := ih
      obtain ⟨hT', hπ'⟩ := pi_opowZ hσ hρ hB hT h1
      refine ⟨by rw [Function.iterate_succ_apply']; exact hT', ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        have := hS.2 0 hS.1 _ h1; rwa [veblen_zero_apply] at this
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hπ', hπ]
  obtain ⟨hT, -, hπ⟩ := key n
  have hlt : pi σ ρ x < pi σ ρ ((fun a => ω ^ a)^[n] (u + 1)) := (pi_bijOn hB).2 hx hT hn
  rw [hπ] at hlt
  exact hlt.trans_le (iterate_le_nfp _ _ n)

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE COPY LEMMA FOR THE READINGS OF THE CODES BELOW `ε_{Ω₁+1}`**: for a strongly critical `E ∈ (ρ, δ)` in `W`
with Lemma IMG below `E` and a code `z < ε_{Ω₁+1}` over `E`, the witness sets can be enlarged to contain `Θ_E(z)`,
and then `π(Θ_u(z)) ≤ f(Θ_E(z))` in every copy `f` for every strongly critical `u ∈ Tᵖ[f(ρ)] ∩ Ω₁` with `π(u) = f(E)`
over which `z` is a code. -/
theorem qc_copy {E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ < E)
    (hES : SC E) (hE1 : E < Om 1) (hEδ : E < δ) (IH : ∀ v, v < E → GnI ρ δ v) :
    ∀ z, GgCl E z → z < ggE → ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧
      ggTh E z ∈ W' ∪ Z' ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A →
        ImgCtx ρ A f → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u z → pi (f ρ) ρ u = f E →
          ggTh u z ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ (ggTh u z) ≤ f (ggTh E z) := by
  classical
  have hE : InE E := Low.opow_eq_self_of_SC hES
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hEN : eN E ≤ δ := eN_le hEδ hδE
  have hthδ : ∀ z, GgCl E z → z < ggE → ggTh E z < δ := fun z hz hzE =>
    ((ggTh_lt hz hzE).trans_le (ggTh_le_eN hES hE1)).trans_le hEN
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IHz =>
  intro hz hzE
  rcases lt_trichotomy z (Om 1) with hzΩ | rfl | hzΩ
  · -- a countable code: Lemma IMG at `z < E`
    have hzE' : z < E := hz.lt_of_lt_Om1 hES hzΩ
    obtain ⟨W0, Z0, w0, m0, -, -, b0⟩ := gnI_use h (IH z hzE')
    refine ⟨W ∪ W0, Z ∪ Z0, w.union w0, Finset.subset_union_left, Finset.subset_union_left, ?_,
      fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
    · rw [ggTh_small hzE'.le]
      rcases Finset.mem_union.1 m0 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    · have hzu : z < u := huz.lt_of_lt_Om1 hu hzΩ
      obtain ⟨-, hzT, hπz⟩ := b0 A f (he_sub Finset.subset_union_right hW) (he_sub Finset.subset_union_right hZ) C
      rw [ggTh_small hzu.le, ggTh_small hzE'.le]
      exact ⟨hzT, hπz⟩
  · -- `Ω₁`: `Θ_E(Ω₁) = E`, `Θ_u(Ω₁) = u`
    refine ⟨W, Z, w, subset_refl _, subset_refl _, ?_, fun A f _ _ C u hu huT hu1 _ hπu => ?_⟩
    · rw [ggTh_Om1 hES hE1]; exact Finset.mem_union_left _ hEW
    · rw [ggTh_Om1 hu hu1, ggTh_Om1 hES hE1]
      exact ⟨huT, hπu.le⟩
  -- `Ω₁ < z < ε_{Ω₁+1}`
  have hz0 : z ≠ 0 := (lt_of_le_of_lt zero_le hzΩ).ne'
  have hz1 : Om1 < z := by rw [rj_Om1]; exact hzΩ
  obtain ⟨hsub, hlog⟩ := ggDec hES z hz
  set g := log ω z with hgdef
  have hgz : g < z := rj_log_lt hz1 hzE
  have hwg : ω ^ g ≤ z := opow_log_le_self ω hz0
  have hgE : g < ggE := hgz.trans hzE
  have hEz : E < ggTh E z :=
    calc E = ggTh E (Om 1) := (ggTh_Om1 hES hE1).symm
      _ < ggTh E z := ggTh_lt GgCl.om hzΩ
  have hρz : ρ ≤ ggTh E z := (hρE.trans hEz).le
  rcases hwg.lt_or_eq with hwlt | hweq
  · -- a sum `z = ω^g + (z − ω^g)`
    have hwC : GgCl E (ω ^ g) := GgCl.opow hES.1 hlog
    have hrC : GgCl E (z - ω ^ g) := hsub _ hwC hwg
    have hzs : z = ω ^ g + (z - ω ^ g) := (Ordinal.add_sub_cancel_of_le hwg).symm
    have hr0 : z - ω ^ g ≠ 0 := fun h0 => by rw [h0, add_zero] at hzs; exact absurd hzs hwlt.ne'
    have hrz : z - ω ^ g < z := by
      refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
      have habs : ω ^ g + z = z := by
        conv_rhs => rw [hzs]
        rw [e]
      have h1 : ω ^ g * ω ≤ z := Ordinal.add_eq_right_iff_mul_omega0_le.1 habs
      rw [← opow_succ] at h1
      exact absurd (lt_opow_succ_log_self one_lt_omega0 z) (not_lt.2 h1)
    obtain ⟨W1, Z1, w1, hW1, hZ1, m1, b1⟩ := IHz _ hwlt hwC (hwlt.trans hzE)
    obtain ⟨W2, Z2, w2, hW2, hZ2, m2, b2⟩ := IHz _ hrz hrC (hrz.trans hzE)
    have hthz : ggTh E z = ggTh E (ω ^ g) + ggTh E (z - ω ^ g) := by
      conv_lhs => rw [hzs]
      exact ggTh_add hES hwC _
    have hlt1 : ggTh E (ω ^ g) < ggTh E z := ggTh_lt hwC hwlt
    have hlt2 : ggTh E (z - ω ^ g) < ggTh E z := ggTh_lt hrC hrz
    have wU := w1.union w2
    have hzmem : ggTh E z ∈ insert (ggTh E z) (W1 ∪ W2) ∪ (Z1 ∪ Z2) :=
      Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have m1' : ggTh E (ω ^ g) ∈ (W1 ∪ W2) ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m1 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
    have m2' : ggTh E (z - ω ^ g) ∈ (W1 ∪ W2) ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m2 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    refine ⟨insert (ggTh E z) (W1 ∪ W2), Z1 ∪ Z2,
      wU.insW hρz (hthδ z hz hzE) (Or.inr ⟨_, m1', _, m2', hlt1, hlt2, hthz.symm⟩),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      fun a ha => Finset.mem_union_left _ (hZ1 ha), hzmem, fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
    have hWU : ↑(W1 ∪ W2) ⊆ A := he_sub (Finset.subset_insert _ _) hW
    obtain ⟨hlogu, -⟩ := (ggDec hu z huz)
    obtain ⟨hsubu, hlogu'⟩ := ggDec hu z huz
    have hwCu : GgCl u (ω ^ g) := GgCl.opow hu.1 hlogu'
    have hrCu : GgCl u (z - ω ^ g) := hsubu _ hwCu hwg
    obtain ⟨hT1, hp1⟩ := b1 A f (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ) C u hu
      huT hu1 hwCu hπu
    obtain ⟨hT2, hp2⟩ := b2 A f (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ) C u hu
      huT hu1 hrCu hπu
    have hB := h.img_bases C
    obtain ⟨hTs, hπs⟩ := pi_add hB hT1 hT2
    have hthu : ggTh u z = ggTh u (ω ^ g) + ggTh u (z - ω ^ g) := by
      conv_lhs => rw [hzs]
      exact ggTh_add hu hwCu _
    have hA1 : ggTh E (ω ^ g) ∈ A := mem_A m1 (he_sub Finset.subset_union_left hWU)
      (he_sub Finset.subset_union_left hZ)
    have hA2 : ggTh E (z - ω ^ g) ∈ A := mem_A m2 (he_sub Finset.subset_union_right hWU)
      (he_sub Finset.subset_union_right hZ)
    have hAz : ggTh E z ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hfz : f (ggTh E z) = f (ggTh E (ω ^ g)) + f (ggTh E (z - ω ^ g)) :=
      (C.add _ hA1 _ hA2 _ hAz hthz.symm).symm
    rw [hthu, hfz, hπs]
    exact ⟨hTs, add_le_add hp1 hp2⟩
  · -- a power `z = ω^g`, `Ω₁ < g`
    have hgΩ : Om 1 < g := by
      by_contra hle
      push Not at hle
      have : z ≤ Om 1 := by
        rw [← hweq, ← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos hle
      exact absurd hzΩ (not_lt.2 this)
    have hg0 : g ≠ 0 := (lt_of_le_of_lt zero_le hgΩ).ne'
    obtain ⟨g₁, g₂, hgs, hg₁g, hg₁C, hg₂C, hg₂l, hg₂d⟩ := qc_split hES g hlog hg0
    have hz₁ : ω ^ g₁ < z := by
      rw [← hweq]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hg₁g
    have hg₂z : g₂ < z := by
      have h1 : ω ^ g₂ ≤ g := by rw [hgs]; exact le_add_self
      exact ((right_le_opow g₂ one_lt_omega0).trans h1).trans_lt hgz
    have hz₁C : GgCl E (ω ^ g₁) := GgCl.opow hES.1 hg₁C
    obtain ⟨W1, Z1, w1, hW1, hZ1, m1, b1⟩ := IHz _ hz₁ hz₁C (hz₁.trans hzE)
    obtain ⟨W2, Z2, w2, hW2, hZ2, m2, b2⟩ := IHz _ hg₂z hg₂C (hg₂z.trans hzE)
    set G := ggTh E g with hGdef
    set G₁ := ggTh E g₁ with hG₁def
    set G₂ := ggTh E g₂ with hG₂def
    have hGs : G = G₁ + ω ^ G₂ := by
      rw [hGdef, hgs, ggTh_add hES hg₁C, ggTh_opow hES hg₂C]
    have hthz : ggTh E z = ω ^ G := by rw [← hweq, ggTh_opow hES hlog]
    have hth₁ : ggTh E (ω ^ g₁) = ω ^ G₁ := ggTh_opow hES hg₁C
    have hG₁G : G₁ < G := by rw [hGs]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
    have hwδ : ω ^ G < δ := by rw [← hthz]; exact hthδ z hz hzE
    have hρw : ρ ≤ ω ^ G := by rw [← hthz]; exact hρz
    have wU := w1.union w2
    set W3 := insert (ω ^ G) (W1 ∪ W2) with hW3
    have w3 : WZ ρ δ W3 (Z1 ∪ Z2) := wU.insW hρw hwδ (Or.inl (indec_opow _))
    have hwW3 : ω ^ G ∈ W3 := Finset.mem_insert_self _ _
    have m2' : G₂ ∈ W3 ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m2 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    have hEG : E < G :=
      calc E = ggTh E (Om 1) := (ggTh_Om1 hES hE1).symm
        _ < G := ggTh_lt GgCl.om hgΩ
    have hGN : G < eN E := (ggTh_lt hlog hgE).trans_le (ggTh_le_eN hES hE1)
    have hGw : G < ω ^ G := lt_of_le_of_ne (right_le_opow G one_lt_omega0) fun e =>
      absurd (eN_le hEG e.symm) (not_le.2 hGN)
    have hG₂w : G₂ < ω ^ G :=
      ((right_le_opow G₂ one_lt_omega0).trans (by rw [hGs]; exact le_add_self)).trans_lt hGw
    have hEw : E < ω ^ G := hEG.trans hGw
    have hw₁w : ω ^ G₁ < ω ^ G := (opow_lt_opow_iff_right one_lt_omega0).2 hG₁G
    have hlgG : lg G = G₂ := by rw [hGs, lu_lg_add_right (opow_pos _ omega0_pos).ne', LvE.lve_lg_opow]
    -- the common part of a copy
    have core : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W3 ⊆ A → ↑(Z1 ∪ Z2) ⊆ A →
        ImgCtx ρ A f → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u z → pi (f ρ) ρ u = f E →
        ∃ a', f (ω ^ G) = ω ^ a' ∧ ω ^ G ∈ A ∧ G₂ ∈ A ∧ E ∈ A ∧
          ggTh u z = ω ^ (ggTh u g₁ + ω ^ ggTh u g₂) ∧ ggTh u z ∈ TB ρ (f ρ) ∧
          pi (f ρ) ρ (ggTh u z) = ω ^ (pi (f ρ) ρ (ggTh u g₁) + ω ^ pi (f ρ) ρ (ggTh u g₂)) ∧
          pi (f ρ) ρ (ggTh u g₁) < a' ∧ pi (f ρ) ρ (ggTh u g₂) ≤ f G₂ ∧
          (g₂ ≠ 0 → 0 < pi (f ρ) ρ (ggTh u g₂)) := by
      intro A f hW hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      have hWU : ↑(W1 ∪ W2) ⊆ A := he_sub (Finset.subset_insert _ _) hW
      have hlogu : GgCl u g := (ggDec hu z huz).2
      obtain ⟨g₁', g₂', hgs', -, hg₁u', hg₂u', hg₂l', hg₂d'⟩ := qc_split hu g hlogu hg0
      have e2 : g₂' = g₂ := by rw [hg₂l', hg₂l]
      rw [e2] at hgs' hg₂d' hg₂u'
      have e1 : g₁' = g₁ := qc_split_unique hgs' hgs hg₂d' hg₂d
      rw [e1] at hg₁u'
      set G₁u := ggTh u g₁ with hG₁u
      set G₂u := ggTh u g₂ with hG₂u
      have hthu : ggTh u z = ω ^ (G₁u + ω ^ G₂u) := by
        rw [← hweq, ggTh_opow hu hlogu, hgs, ggTh_add hu hg₁u', ggTh_opow hu hg₂u']
      have hz₁u : GgCl u (ω ^ g₁) := GgCl.opow hu.1 hg₁u'
      obtain ⟨hT1, hp1⟩ := b1 A f (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ) C u hu
        huT hu1 hz₁u hπu
      obtain ⟨hT2, hp2⟩ := b2 A f (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ) C u
        hu huT hu1 hg₂u' hπu
      rw [ggTh_opow hu hg₁u', hth₁] at hp1
      rw [ggTh_opow hu hg₁u'] at hT1
      have hOmE : InE (Om (1 : Ordinal.{0})) := Low.opow_eq_self_of_SC (SC_Om one_ne_zero)
      have hcnt : ∀ c, GgCl u c → c < ggE → ggTh u c < Om1 := fun c hc hcE => by
        rw [rj_Om1]
        exact (ggTh_lt hc hcE).trans_le ((ggTh_le_eN hu hu1).trans (eN_le hu1 hOmE))
      have hthg : ggTh u g = G₁u + ω ^ G₂u := by rw [hgs, ggTh_add hu hg₁u', ggTh_opow hu hg₂u']
      have hG₁1 : G₁u < Om1 := hcnt _ hg₁u' (hg₁g.trans hgE)
      have hG₂1 : G₂u < Om1 := hcnt _ hg₂u' (hg₂z.trans hzE)
      have hs1 : G₁u + ω ^ G₂u < Om1 := by rw [← hthg]; exact hcnt _ hlogu hgE
      have hG₁T : G₁u ∈ TB ρ (f ρ) := by
        have hw1 : ω ^ G₁u < Om1 := by
          have := hcnt _ hz₁u (hz₁.trans hzE); rwa [ggTh_opow hu hg₁u'] at this
        have := (he_TB_cnf C.ups h.ρU hB hT1 hw1 (opow_pos _ omega0_pos).ne').2.1
        rwa [log_opow one_lt_omega0] at this
      obtain ⟨hw₂T, hw₂π⟩ := pi_opowZ C.ups h.ρU hB hT2 hG₂1
      obtain ⟨hsT, hsπ⟩ := pi_add hB hG₁T hw₂T
      obtain ⟨hzT, hzπ⟩ := pi_opowZ C.ups h.ρU hB hsT hs1
      obtain ⟨-, hw₁π⟩ := pi_opowZ C.ups h.ρU hB hG₁T hG₁1
      have hA3 : ω ^ G ∈ A := hW (Finset.mem_coe.2 hwW3)
      have hA2 : G₂ ∈ A := mem_A m2 (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ)
      have hA1 : ω ^ G₁ ∈ A := by
        have := mem_A m1 (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ)
        rwa [hth₁] at this
      have hEA : E ∈ A := hWU (Finset.mem_coe.2 (Finset.mem_union_left _ (hW1 hEW)))
      obtain ⟨a', ha'⟩ := hc_indec_opow h (C.indec _ hA3 (indec_opow _))
      have hlt1 : f (ω ^ G₁) < f (ω ^ G) := C.mono hA1 hA3 hw₁w
      have hG₁a : pi (f ρ) ρ G₁u < a' := by
        have : ω ^ pi (f ρ) ρ G₁u < ω ^ a' := by rw [← hw₁π, ← ha']; exact hp1.trans_lt hlt1
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      have hpos : g₂ ≠ 0 → 0 < pi (f ρ) ρ G₂u := fun hg₂0 => by
        have h0 : ggTh u 0 < G₂u := ggTh_lt (GgCl.zero hu.1) (pos_iff_ne_zero.2 hg₂0)
        rw [ggTh_small zero_le] at h0
        have h0T : (0 : Ordinal.{0}) ∈ TB ρ (f ρ) := mem_TB_of_lt hB hB.1.pos
        have := (pi_bijOn hB).2 h0T hT2 h0
        rwa [pi_lt hB hB.1.pos] at this
      refine ⟨a', ha', hA3, hA2, hEA, hthu, by rw [hthu]; exact hzT, by rw [hthu, hzπ, hsπ, hw₂π], hG₁a, hp2,
        hpos⟩
    have hW13 : W ⊆ W3 := fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha))
    have hZ13 : Z ⊆ Z1 ∪ Z2 := fun a ha => Finset.mem_union_left _ (hZ1 ha)
    rcases eq_or_ne g₂ 0 with hg₂0 | hg₂0
    · -- `g = g₁ + 1`
      refine ⟨W3, Z1 ∪ Z2, w3, hW13, hZ13, by rw [hthz]; exact Finset.mem_union_left _ hwW3,
        fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
      obtain ⟨a', ha', -, -, -, -, hzT, hzπ, hG₁a, -, -⟩ := core A f hW hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      refine ⟨hzT, ?_⟩
      have e0 : ggTh u g₂ = 0 := by rw [hg₂0]; exact ggTh_small zero_le
      rw [hzπ, hthz, ha', e0, pi_lt hB hB.1.pos, opow_zero]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hG₁a)
    · -- the source `ω^G ≤₁ ω^G + Θ_E(g₂)`
      have hG₂0 : 0 < G₂ := by
        have := ggTh_lt (GgCl.zero hES.1) (pos_iff_ne_zero.2 hg₂0); rwa [ggTh_small zero_le] at this
      have hTop : ω ^ G + G₂ < δ := hδI.add_lt hwδ (hG₂w.trans hwδ)
      set W4 := insert (ω ^ G + G₂) W3 with hW4
      have w4 : WZ ρ δ W4 (Z1 ∪ Z2) := w3.insW (hρw.trans le_self_add) hTop
        (Or.inr ⟨ω ^ G, Finset.mem_union_left _ hwW3, G₂, m2', lt_add_of_pos_right _ hG₂0,
          hG₂w.trans_le le_self_add, rfl⟩)
      have hL := lu_lh_opow (pos_iff_ne_zero.1 (hE.pos.trans hEG)) hGw
      rw [hlgG] at hL
      have hsrc : le1 (ω ^ G) (ω ^ G + G₂) := (h.lowδ _ _ (hρE.trans hEw) hTop.le).2 hL.1
      refine ⟨W4, Z1 ∪ Z2, w4, fun a ha => Finset.mem_insert_of_mem (hW13 ha), hZ13,
        by rw [hthz]; exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hwW3),
        fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
      have hW3A : ↑W3 ⊆ A := he_sub (Finset.subset_insert _ _) hW
      obtain ⟨a', ha', hA3, hA2, hEA, -, hzT, hzπ, hG₁a, hp2, hpos⟩ := core A f hW3A hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      refine ⟨hzT, ?_⟩
      rw [hthz]
      have hTA : ω ^ G + G₂ ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have himg : le1 (f (ω ^ G)) (f (ω ^ G) + f G₂) := by
        have := C.cov1 _ hA3 _ hTA hsrc
        rwa [← C.add _ hA3 _ hA2 _ hTA rfl] at this
      by_cases hU : UpsPt (f (ω ^ G))
      · have hfE : InE (f (ω ^ G)) := upsPt_inE hU
        have hlt : f E < f (ω ^ G) := C.mono hEA hA3 hEw
        have hN : eN (pi (f ρ) ρ u) ≤ f (ω ^ G) := by rw [hπu]; exact eN_le hlt hfE
        have hzN : ggTh u z < eN u := (ggTh_lt huz hzE).trans_le (ggTh_le_eN hu hu1)
        have hu1' : u < Om1 := by rw [rj_Om1]; exact hu1
        exact ((qc_pi_eN C.ups h.ρU hB huT hu1' hzT hzN).trans_le hN).le
      · have hR := (C.sk _ (C.low _ hA3) hU _).1 himg
        have hf0 : 0 < f G₂ := (hpos hg₂0).trans_le hp2
        have hfle : f G₂ ≤ f (ω ^ G) := (C.mono hA2 hA3 hG₂w).le
        obtain ⟨a'', -, ha'', hlg⟩ := (le1R_thm22 hf0 hfle).1 hR
        have e : a'' = a' := by
          have h2 : ω ^ a'' = ω ^ a' := ha''.symm.trans ha'
          exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 h2.le)
            ((opow_le_opow_iff_right one_lt_omega0).1 h2.ge)
        rw [e] at hlg
        set p₁ := pi (f ρ) ρ (ggTh u g₁) with hp₁
        have hsplit : a' = p₁ + (a' - p₁) := (Ordinal.add_sub_cancel_of_le hG₁a.le).symm
        have hr0 : a' - p₁ ≠ 0 := fun h0 => by
          rw [h0, add_zero] at hsplit; exact absurd hsplit hG₁a.ne'
        have hlgr : lg a' = lg (a' - p₁) := by
          conv_lhs => rw [hsplit]
          exact lu_lg_add_right hr0
        have hdvd : ω ^ pi (f ρ) ρ (ggTh u g₂) ∣ a' - p₁ := (le_lg_iff hr0 _).1 (by rw [← hlgr]; exact hp2.trans hlg)
        have hge : p₁ + ω ^ pi (f ρ) ρ (ggTh u g₂) ≤ a' := by
          conv_rhs => rw [hsplit]
          exact add_le_add le_rfl (Ordinal.le_of_dvd hr0 hdvd)
        rw [hzπ, ha']
        exact opow_le_opow_right omega0_pos hge

end Copy

end Googology.Trans.PoR.InaccPsi.R2.Qc
