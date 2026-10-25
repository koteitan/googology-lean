import Googology.Trans.PoR.InaccPsi.R2.HcGLev

/-!
# HcGImg: LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY LEVEL `1 ≤ q < ω^ω`

At a level `1 ≤ q < ω^ω` the reach of `E = ϑᵖ(Ω₁·q + t)` is `E·(1+q) + z` (`Hc.hc_lhG`).  The product `E·c`,
`0 < c < ω^ω`, is built in the witness set from `E` by sums and the indecomposables `E·ω^j = ω^{E+j}`, and every copy
keeps the lower bound `f(E)·c ≤ f(E·c)` (`hc_wz_mulE`: an indecomposable above `f(E)·ω^j` is `≥ f(E)·ω^{j+1}`); on
the other side `π(u·c) = π(u)·c` (`hc_pi_mulc`, from `Ev.pi_opowZ` and `π` additive).  So the argument of
`Ha.ha_img_down` (finite levels) and `Hc.hc_img_downW` (level `ω`) runs at every level `q < ω^ω`
(`hc_img_downG`): Lemma IMG at `E` once it holds below `E` and every `ε`-number `u ∈ (E', E)` has a reach
`u·(1+q') + ζ` with `ζ < u` and `q' < q`, or `q' = q` and `ζ < z`.

* `hc_pi_mulc` (**`π(u·c) = π(u)·c` for `c < ω^ω`**), `hc_wz_mulE` (**the products `E·c` in the witness set, with
  `f(E)·c ≤ f(E·c)` in every copy**), `hc_img_downG` (**LEMMA IMG BY THE REACH TEST GOING DOWN, EVERY LEVEL
  `1 ≤ q < ω^ω`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gf
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Products `u·c`, `c < ω^ω` -/

/-- `logend(c) < ω` and `ω^{logend(c)} ≤ c` for `0 < c < ω^ω`. -/
theorem hc_lg_fin {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < ω ^ ω) : lg c < ω ∧ ω ^ lg c ≤ c := by
  obtain ⟨c', hcs, -, -⟩ := lg_split hc0
  have hle : ω ^ lg c ≤ c := by
    conv_rhs => rw [hcs]
    exact Ordinal.le_add_left _ _
  exact ⟨(opow_lt_opow_iff_right one_lt_omega0).1 (hle.trans_lt hc), hle⟩

theorem hc_om_lt_ww : ω < (ω ^ ω : Ordinal.{0}) := by
  simpa using (opow_lt_opow_iff_right one_lt_omega0).2 (one_lt_omega0 : (1 : Ordinal.{0}) < ω)

theorem hc_one_lt_ww : 1 < (ω ^ ω : Ordinal.{0}) := one_lt_omega0.trans hc_om_lt_ww

/-- `ω^ω` is indecomposable. -/
theorem hc_ww_indec : Indec (ω ^ ω : Ordinal.{0}) := indec_opow _

/-- **`π(u·c) = π(u)·c`** for an `ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁` and every `c < ω^ω` (`υ`-points `σ < ρ`). -/
theorem hc_pi_mulc {σ ρ u : Ordinal.{0}} (hσU : UpsPt σ) (hρU : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (huE : InE u) : ∀ c, c < ω ^ ω → u * c ∈ TB ρ σ ∧ pi σ ρ (u * c) = pi σ ρ u * c := by
  have hσ0 : (0 : Ordinal.{0}) < σ := hB.1.pos
  have hωσ : ω < σ := omega0_lt_inE hB.1
  -- `π(u)` is an `ε`-number
  have hπuE : InE (pi σ ρ u) := by
    obtain ⟨-, hp⟩ := pi_opowZ hσU hρU hB hu hu1
    rw [show ω ^ u = u from huE] at hp
    exact hp.symm
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [mul_zero, mul_zero]; exact ⟨mem_TB_of_lt hB hσ0, pi_lt hB hσ0⟩
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
  obtain ⟨hj, -⟩ := hc_lg_fin hc0 hc
  set j := lg c with hjdef
  -- the power `u·ω^j = ω^{u+j}`
  have hjσ : j < σ := hj.trans hωσ
  have hjTB : j ∈ TB ρ σ := mem_TB_of_lt hB hjσ
  obtain ⟨hujTB, hpuj⟩ := pi_add hB hu hjTB
  rw [pi_lt hB hjσ] at hpuj
  have huj1 : u + j < Om1 := (inE_indec gl_Om1_E).add_lt hu1 (hj.trans omega_lt_Om1)
  obtain ⟨hwTB, hwpi⟩ := pi_opowZ hσU hρU hB hujTB huj1
  have ew : ω ^ (u + j) = u * ω ^ j := by rw [opow_add, show ω ^ u = u from huE]
  have ew' : ω ^ (pi σ ρ u + j) = pi σ ρ u * ω ^ j := by rw [opow_add, show ω ^ pi σ ρ u = pi σ ρ u from hπuE]
  rw [hpuj, ew', ew] at hwpi
  rw [ew] at hwTB
  rcases eq_or_ne c' 0 with h0 | h0
  · rw [hcs, h0, zero_add]; exact ⟨hwTB, hwpi⟩
  obtain ⟨h1, h2⟩ := IH c' hc'c (hc'c.trans hc)
  obtain ⟨s1, s2⟩ := pi_add hB h1 hwTB
  rw [hcs, mul_add, mul_add]
  exact ⟨s1, by rw [s2, h2, hwpi]⟩

/-- **The products `E·c` (`0 < c < ω^ω`) in the witness set**, with the lower bound `f(E)·c ≤ f(E·c)` in every copy
of a set containing them. -/
theorem hc_wz_mulE {ρ δ E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ ≤ E)
    (hE : InE E) (hEδ : ∀ c, c < ω ^ ω → E * c < δ) :
    ∀ c, c < ω ^ ω → 0 < c → ∃ W' : Finset Ordinal.{0}, WZ ρ δ W' Z ∧ W ⊆ W' ∧ E * c ∈ W' ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ImgCtx ρ A f → f E * c ≤ f (E * c) := by
  classical
  have hE0 : 0 < E := hE.pos
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc0
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0.ne'
  obtain ⟨hj, -⟩ := hc_lg_fin hc0.ne' hc
  set j := lg c with hjdef
  obtain ⟨n, hn⟩ := lt_omega0.1 hj
  rcases eq_or_ne c' 0 with h0 | h0
  · -- `c = ω^n`
    rw [h0, zero_add, hn] at hcs
    subst hcs
    rcases n with _ | m
    · refine ⟨W, w, subset_refl _, by rw [Nat.cast_zero, opow_zero, mul_one]; exact hEW, fun A f _ _ => ?_⟩
      rw [Nat.cast_zero, opow_zero, mul_one, mul_one]
    · have hm : ω ^ (m : Ordinal.{0}) < ω ^ ((m + 1 : ℕ) : Ordinal.{0}) :=
        (opow_lt_opow_iff_right one_lt_omega0).2 (by exact_mod_cast Nat.lt_succ_self m)
      obtain ⟨W1, w1, hW1, hm1, b1⟩ := IH _ hm (hm.trans hc) (opow_pos _ omega0_pos)
      have e1 : E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}) = ω ^ (E + ((m + 1 : ℕ) : Ordinal.{0})) := by
        rw [opow_add, show ω ^ E = E from hE]
      have hlt : E * ω ^ (m : Ordinal.{0}) < E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}) :=
        (mul_lt_mul_iff_right₀ hE0).2 hm
      have hρle : ρ ≤ E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}) :=
        hρE.trans (le_mul_of_one_le_right' (one_le_iff_pos.2 (opow_pos _ omega0_pos)))
      refine ⟨insert (E * ω ^ ((m + 1 : ℕ) : Ordinal.{0})) W1,
        w1.insW hρle (hEδ _ hc) (Or.inl (by rw [e1]; exact indec_opow _)),
        hW1.trans (Finset.subset_insert _ _), Finset.mem_insert_self _ _, fun A f hA C => ?_⟩
      have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha)))
      have hEA : E ∈ A := hA1 (Finset.mem_coe.2 (hW1 hEW))
      have hmA : E * ω ^ (m : Ordinal.{0}) ∈ A := hA1 (Finset.mem_coe.2 hm1)
      have hcA : E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}) ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hb := b1 A f hA1 C
      have hfEI : Indec (f E) := C.indec _ hEA (inE_indec hE)
      have hfcI : Indec (f (E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}))) := C.indec _ hcA (by rw [e1]; exact indec_opow _)
      have hlt' : f E * ω ^ (m : Ordinal.{0}) < f (E * ω ^ ((m + 1 : ℕ) : Ordinal.{0})) :=
        hb.trans_lt (C.mono hmA hcA hlt)
      have hmI : Indec (f E * ω ^ (m : Ordinal.{0})) := by
        obtain ⟨hne, hpa⟩ := indec_iff.1 hfEI
        rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hpa with h0 | ⟨a, ha⟩
        · exact absurd h0 hne
        · rw [show f E = ω ^ a from ha.symm, ← opow_add]; exact indec_opow _
      have e2 : f E * ω ^ (m : Ordinal.{0}) * ω = f E * ω ^ ((m + 1 : ℕ) : Ordinal.{0}) := by
        rw [mul_assoc, Nat.cast_succ, opow_add, opow_one]
      rw [← e2]; exact hc_indec_mul_om hmI hfcI hlt'
  · -- `c = c' + ω^j`, `c' ≠ 0`
    have hc'0 : 0 < c' := pos_iff_ne_zero.2 h0
    have hjc' : ω ^ j ≤ c' := Ordinal.le_of_dvd h0 hdvd
    have hjc : ω ^ j < c := by
      rw [hcs]; exact (lt_add_of_pos_right (ω ^ j) (opow_pos j omega0_pos)).trans_le (add_le_add hjc' le_rfl)
    obtain ⟨W1, w1, hW1, hm1, b1⟩ := IH c' hc'c (hc'c.trans hc) hc'0
    obtain ⟨W2, w2, hW2, hm2, b2⟩ := IH _ hjc (hjc.trans hc) (opow_pos _ omega0_pos)
    have w12 : WZ ρ δ (W1 ∪ W2) Z := by have := w1.union w2; rwa [Finset.union_self] at this
    have eC : E * c = E * c' + E * ω ^ j := by rw [hcs, mul_add]
    have h1lt : E * c' < E * c := (mul_lt_mul_iff_right₀ hE0).2 hc'c
    have h2lt : E * ω ^ j < E * c := (mul_lt_mul_iff_right₀ hE0).2 hjc
    have hρle : ρ ≤ E * c := hρE.trans (le_mul_of_one_le_right' (one_le_iff_pos.2 hc0))
    refine ⟨insert (E * c) (W1 ∪ W2), w12.insW hρle (hEδ c hc) (Or.inr ⟨E * c', Finset.mem_union_left _
      (Finset.mem_union_left _ hm1), E * ω ^ j, Finset.mem_union_left _ (Finset.mem_union_right _ hm2), h1lt, h2lt,
      eC.symm⟩), fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      Finset.mem_insert_self _ _, fun A f hA C => ?_⟩
    have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
    have hA2 : ↑W2 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
    have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hadd := C.add _ (hA1 (Finset.mem_coe.2 hm1)) _ (hA2 (Finset.mem_coe.2 hm2)) _ hcA eC.symm
    rw [← hadd]
    calc f E * c = f E * c' + f E * ω ^ j := by rw [hcs, mul_add]
      _ ≤ f (E * c') + f (E * ω ^ j) := add_le_add (b1 A f hA1 C) (b2 A f hA2 C)

/-! ## Lemma IMG by the reach test going down at every level `q < ω^ω` -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY LEVEL `1 ≤ q < ω^ω`**: let `E = ϑᵖ(Ω₁·q + t)` (reach
`E·(1+q) + z`, `z = luZeta ρ q t`), `ρ < E' < E`.  If Lemma IMG holds below `E` and every `ε`-number `u ∈ (E', E)`
has a reach `u·(1+q') + ζ` with `ζ < u`, `q' ≤ q`, and `ζ < z` when `q' = q`, then Lemma IMG holds at `E`. -/
theorem hc_img_downG {q t E' : Ordinal.{0}} (hq1 : 1 ≤ q) (hq : q < ω ^ ω) (htT : t ∈ Tset ρ) (ht1 : t < Om1)
    (hρE' : ρ < E') (hE'E : E' < glA q t ρ)
    (hdown : ∀ u, InE u → E' < u → u < glA q t ρ → ∃ q' ζ, q' ≤ q ∧
      IsLh1 u (u * (1 + q') + ζ) ∧ ζ < u ∧ (q' = q → ζ < luZeta ρ q t))
    (IH : ∀ u, u < glA q t ρ → GnI ρ δ u) : GnI ρ δ (glA q t ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hL, hzE⟩ := hc_lhG hρE hρ1 hq1 hq htT ht1
  set E := glA q t ρ with hEdef
  set z := luZeta ρ q t with hzdef
  have hqq : q < gq 1 ρ := hq.trans (hc_ww_lt_E (gm1_facts hρE hρ1).2.2.2)
  obtain ⟨hqT, hqΩ⟩ := gm1_T hρE hρ1 hqq
  obtain ⟨hET0, hρEE, hE1, hE, -, -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hcw : ∀ c, c < ω ^ ω → E * c < δ := fun c hc => InE.mul_lt h.δE hEδ (hc.trans (hc_ww_lt_E h.δE))
  set c := 1 + q with hcdef
  have hc : c < ω ^ ω := hc_ww_indec.add_lt hc_one_lt_ww hq
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one le_self_add
  have hEc : E * c < δ := hcw c hc
  have hTopδ : E * c + z < δ := hδI.add_lt hEc (hzE.trans hEδ)
  have hsrc : le1 E (E * c + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEpos : 0 < E := hE.pos
  have hEEc : E ≤ E * c := le_mul_of_one_le_right' (one_le_iff_pos.2 hc0)
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  set W3 := insert E (W1 ∪ W2) with hW3
  have w3 : WZ ρ δ W3 (Z1 ∪ Z2) := (w1.union w2).insW hρEE.le hEδ (Or.inl (inE_indec hE))
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 (Z1 ∪ Z2) := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hEpos,
      lt_add_of_pos_right _ hEpos, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  obtain ⟨W5, w5, h45, hc5, bmul⟩ := hc_wz_mulE w4 (h34 hE3) hρEE.le hE hcw c hc hc0
  have hzZ : z ∈ W5 ∪ (Z1 ∪ Z2) := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h45 (h34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
  obtain ⟨W6, w6, h56, hTop⟩ : ∃ W6 : Finset Ordinal.{0}, WZ ρ δ W6 (Z1 ∪ Z2) ∧ W5 ⊆ W6 ∧ E * c + z ∈ W6 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W5, w5, subset_refl _, by rw [hz0, add_zero]; exact hc5⟩
    · refine ⟨insert (E * c + z) W5, w5.insW ((hρEE.le.trans hEEc).trans le_self_add) hTopδ
        (Or.inr ⟨_, Finset.mem_union_left _ hc5, z, hzZ, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le (hEEc.trans le_self_add), rfl⟩), Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  have hsub : W4 ⊆ W6 := fun a ha => h56 (h45 ha)
  refine gnI_mk h w6 (Finset.mem_union_left _ (hsub (h34 hE3))) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ (by simp [Finset.mem_coe.1 ha])
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ (by simp [Finset.mem_coe.1 ha])
  have hW5 : ↑W5 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h56 (Finset.mem_coe.1 ha)))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hW (Finset.mem_coe.2 (hsub (h34 hE3)))
  have hEEA : E + E ∈ A := hW (Finset.mem_coe.2 (hsub (Finset.mem_insert_self _ _)))
  have hEcA : E * c ∈ A := hW5 (Finset.mem_coe.2 hc5)
  have hTopA : E * c + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  have hmulc : f E * c ≤ f (E * c) := bmul A f hW5 C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f (E * c) + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [← C.add _ hEcA _ hzA _ hTopA rfl] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨q', ζ, hq'q, hlhu, hζu, hζz⟩ := hdown u huI hE'u huE
  have hl' : l = u * (1 + q') + ζ := lkcIsLh1_unique hl hlhu
  have hc' : 1 + q' < ω ^ ω :=
    hc_ww_indec.add_lt hc_one_lt_ww (hq'q.trans_lt hq)
  obtain ⟨hmTB, hmpi⟩ := hc_pi_mulc C.ups h.ρU hB huTB hu1 huI (1 + q') hc'
  have hum1 : u * (1 + q') < Om1 := InE.mul_lt gl_Om1_E hu1 (hc'.trans (hc_ww_lt_E gl_Om1_E))
  rw [hl'] at hlTB hle0
  have hlg1 : u * (1 + q') + ζ < Om1 := (inE_indec gl_Om1_E).add_lt hum1 (hζu.trans hu1)
  obtain ⟨hζTB, -⟩ := TB_sub hB hmTB hlTB le_self_add hlg1
  rw [Ordinal.add_sub_cancel] at hζTB
  obtain ⟨-, hps⟩ := pi_add hB hmTB hζTB
  rw [hps, hmpi, hpu] at hle0
  rcases hq'q.lt_or_eq with hlt' | heq
  · -- a lower level: the reach of `u` is too short
    have hπζ : pi (f ρ) ρ ζ < f E := by rw [← hpu]; exact (pi_bijOn hB).2 hζTB huTB hζu
    have h1 : f E * (1 + q') + pi (f ρ) ρ ζ < f E * (1 + q' + 1) := by
      rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hπζ
    have h2 : f E * (1 + q' + 1) ≤ f E * c :=
      mul_le_mul_right (Order.add_one_le_of_lt ((add_lt_add_iff_left 1).2 hlt')) _
    exact absurd (hle0.trans_lt (h1.trans_le h2)) (not_lt.2 (hmulc.trans le_self_add))
  · -- the same level: `ζ < z`, but `π(z) ≤ f(z) ≤ π(ζ)`
    subst heq
    have hfz : f z ≤ pi (f ρ) ρ ζ := (add_le_add_iff_left (f E * c)).1 ((add_le_add hmulc le_rfl).trans hle0)
    have hzζ : z ≤ ζ := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    exact absurd (hζz rfl) (not_lt.2 hzζ)

end Img

end Googology.Trans.PoR.InaccPsi.R2.Hc
