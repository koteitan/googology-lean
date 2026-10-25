import Googology.Trans.PoR.InaccPsi.R2.HcLev
import Googology.Trans.PoR.InaccPsi.R2.GqVb

/-!
# HcImg: LEMMA IMG AT VEBLEN LEVEL `ω`, AND BELOW `B_{ω+1}(ρ) = N_ω(Γ_{ρ+1})`

The `R₁⁺`-reach of a point of Veblen level `ω` is known at every argument (`Gq.gq_lh_th` with the ϑ-index `ω`):
`lh(ϑᵖ(Ω₁·ω + t)) = luL(E, ω) + ζ = E·ω + ζ` with `ζ = luZeta ρ ω t < E` (`hc_lhW`).  So the source of Lemma IMG at
`E = ϑᵖ(Ω₁·ω + t)` is `E ≤₁ E·ω + ζ`, and `E·ω` enters the witness set as an indecomposable; a copy `f` keeps
indecomposables and order, so `f(E·ω) ≥ f(E)·ω` (`hc_indec_mul_om`), and the copy of the source gives
`f(E) ≤₁ f(E)·ω + f(ζ)`.  The reach test going down at level `ω` (`hc_img_downW`): every `ε`-number `u` between the
last checked point `E'` and `E` has a reach `u·(m+1) + ζ'` (finite level) or `u·ω + ζ'` with `ζ' < ζ` (level `ω`);
`π(u·ω) = π(u)·ω` (`Ev.pi_opowZ`).  Over a fixed point `P` of `φ(ω, ·)`: the interval `(P, hcS P)` and the intervals
`(φ(ω, j), φ(ω, j+1))` have only finite levels (`Hb.hb_down`, `Hb.hb_img_next` over every pseudo-base of every
finite level), the points `φ(ω, P+1+d) = ϑᵖ(Ω₁·ω + P + d)` are checked by the reach test going down (successor `d`:
`E'` the previous point; limit `d = c' + ω^z`: `E' = φ(ω, P+1+c')`, the points between have `ζ' ≤ logend < z`).

* `hc_luL_om` (`luL(a, ω) = a·ω`), `hc_lhW` (**THE REACH AT LEVEL `ω`**), `hc_indec_mul_om`, `hc_img_downW`
  (**LEMMA IMG BY THE REACH TEST GOING DOWN AT LEVEL `ω`**);
* `hc_downFin`, `hc_imgFin` (the finite levels below `hcS Q`), `hc_floorW`, `hc_step_cfW`, `hc_step_lhW`,
  `HcDownW`, `HcNextW` (the statements over every fixed point of `φ(ω, ·)`), `hc_downAt`, `hc_nextAt`, `hc_downW`,
  `hc_nextW` (**both hold, every `P`**);
* `hcB1` (`B_{ω+1}(x) = N_ω(Γ_{x+1})`), `hcB1_lt1`, `hc_Bw_lt_B1`, `hc_img_B1` (**LEMMA IMG BELOW `B_{ω+1}(ρ)`**),
  `hc_pkg_B1` (**LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B_{ω+1}(ρ)`**).

No new axiom.  New definitions: `HcDownW`, `HcNextW`, `hcB1`.
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

/-! ## The reach at level `ω` -/

theorem hc_log_om : Ordinal.log ω (ω : Ordinal.{0}) = 1 := by
  have := Ordinal.log_opow one_lt_omega0 (1 : Ordinal.{0}); rwa [opow_one] at this

/-- **`luL(a, ω) = a·ω`.** -/
theorem hc_luL_om (a : Ordinal.{0}) : luL a ω = a * ω := by
  have hlg1 : lg (1 : Ordinal.{0}) = 0 := by exact_mod_cast lg_nat (n := 1) one_ne_zero
  rw [lu_luL_inf le_rfl, hc_log_om, opow_one, hlg1, add_zero, Ordinal.sub_self, mul_zero, add_zero]

/-- **THE `R₁⁺`-REACH AT VEBLEN LEVEL `ω`**: `lh(ϑˣ(Ω₁·ω + t)) = ϑˣ(Ω₁·ω + t)·ω + ζ`, `ζ = luZeta x ω t <
ϑˣ(Ω₁·ω + t)`, for every `t ∈ Tˣ ∩ Ω₁`. -/
theorem hc_lhW {x t : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (ht : t ∈ Tset x) (ht1 : t < Om1) :
    IsLh1 (glA ω t x) (glA ω t x * ω + luZeta x ω t) ∧ luZeta x ω t < glA ω t x := by
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  obtain ⟨hL, hζ, -, -⟩ := gq_lh_th hx hx1 hc_one_le_om hωT hω1 ht ht1
  rw [hc_luL_om] at hL
  exact ⟨hL, hζ⟩

/-- **`a·ω ≤ b`** for indecomposables `a < b`. -/
theorem hc_indec_mul_om {a b : Ordinal.{0}} (ha : Indec a) (hb : Indec b) (hab : a < b) : a * ω ≤ b := by
  obtain ⟨ha0, hpa⟩ := indec_iff.1 ha
  obtain ⟨hb0, hpb⟩ := indec_iff.1 hb
  rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hpa with h0 | ⟨c, rfl⟩
  · exact absurd h0 ha0
  rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hpb with h0 | ⟨d, rfl⟩
  · exact absurd h0 hb0
  have hcd : c < d := (opow_lt_opow_iff_right one_lt_omega0).1 hab
  rw [← opow_succ]
  exact opow_le_opow_right omega0_pos (Order.succ_le_of_lt hcd)

theorem hc_E_mul_om {E : Ordinal.{0}} (hE : InE E) : ω ^ (E + 1) = E * ω := by
  rw [opow_add, opow_one, show ω ^ E = E from hE]

/-! ## Lemma IMG by the reach test going down at level `ω` -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BY THE REACH TEST GOING DOWN AT VEBLEN LEVEL `ω`**: let `E = ϑᵖ(Ω₁·ω + t)` (reach `E·ω + z`,
`z = luZeta ρ ω t`), `ρ < E' < E`.  If Lemma IMG holds below `E` and every `ε`-number `u ∈ (E', E)` has a reach
`u·(m+1) + ζ` with `ζ < u` (some finite `m`), or `u·ω + ζ` with `ζ < z`, then Lemma IMG holds at `E`. -/
theorem hc_img_downW {t E' : Ordinal.{0}} (htT : t ∈ Tset ρ) (ht1 : t < Om1)
    (hρE' : ρ < E') (hE'E : E' < glA ω t ρ)
    (hdown : ∀ u, InE u → E' < u → u < glA ω t ρ →
      (∃ m : ℕ, ∃ ζ, IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u) ∨
      (∃ ζ, IsLh1 u (u * ω + ζ) ∧ ζ < luZeta ρ ω t))
    (IH : ∀ u, u < glA ω t ρ → GnI ρ δ u) : GnI ρ δ (glA ω t ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hL, hzE⟩ := hc_lhW hρE hρ1 htT ht1
  set E := glA ω t ρ with hEdef
  set z := luZeta ρ ω t with hzdef
  obtain ⟨hωT, hω1⟩ := hc_om_T hρE hρ1
  obtain ⟨hET0, hρEE, hE1, hE, -, -⟩ := glA_facts hρE hρ1 hc_one_le_om hωT hω1 htT ht1
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEω : E * ω < δ := InE.mul_lt h.δE hEδ (omega0_lt_inE h.δE)
  have hTopδ : E * ω + z < δ := hδI.add_lt hEω (hzE.trans hEδ)
  have hsrc : le1 E (E * ω + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEpos : 0 < E := hE.pos
  have hEEw : E < E * ω := by
    calc E = E * 1 := (mul_one E).symm
      _ < E * ω := (mul_lt_mul_iff_right₀ hEpos).2 one_lt_omega0
  have hwI : Indec (E * ω) := by rw [← hc_E_mul_om hE]; exact indec_opow _
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
  set W5 := insert (E * ω) W4 with hW5
  have w5 : WZ ρ δ W5 (Z1 ∪ Z2) := w4.insW (hρEE.le.trans hEEw.le) hEω (Or.inl hwI)
  have h45 : W4 ⊆ W5 := Finset.subset_insert _ _
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  have hw5 : E * ω ∈ W5 := Finset.mem_insert_self _ _
  have hzZ : z ∈ W5 ∪ (Z1 ∪ Z2) := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h45 (h34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
  obtain ⟨W6, w6, h56, hTop⟩ : ∃ W6 : Finset Ordinal.{0}, WZ ρ δ W6 (Z1 ∪ Z2) ∧ W5 ⊆ W6 ∧ E * ω + z ∈ W6 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W5, w5, subset_refl _, by rw [hz0, add_zero]; exact hw5⟩
    · refine ⟨insert (E * ω + z) W5, w5.insW ((hρEE.le.trans hEEw.le).trans le_self_add) hTopδ
        (Or.inr ⟨_, Finset.mem_union_left _ hw5, z, hzZ, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans (hEEw.trans_le le_self_add), rfl⟩), Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  have hsub : W3 ⊆ W6 := fun a ha => h56 (h45 (h34 ha))
  refine gnI_mk h w6 (Finset.mem_union_left _ (hsub hE3)) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha)))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ (by simp [Finset.mem_coe.1 ha])
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ (by simp [Finset.mem_coe.1 ha])
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hW (Finset.mem_coe.2 (hsub hE3))
  have hEEA : E + E ∈ A := hW (Finset.mem_coe.2 (h56 (h45 (Finset.mem_insert_self _ _))))
  have hEωA : E * ω ∈ A := hW (Finset.mem_coe.2 (h56 hw5))
  have hTopA : E * ω + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f (E * ω) + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [← C.add _ hEωA _ hzA _ hTopA rfl] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  have hfEI : Indec (f E) := C.indec _ hEA (inE_indec hE)
  have hfwI : Indec (f (E * ω)) := C.indec _ hEωA hwI
  have hfEw : f E < f (E * ω) := C.mono hEA hEωA hEEw
  have hmulw : f E * ω ≤ f (E * ω) := hc_indec_mul_om hfEI hfwI hfEw
  have hfE0 : 0 < f E := hfEI.pos
  rcases hdown u huI hE'u huE with ⟨m, ζ, hlhu, hζu⟩ | ⟨ζ, hlhu, hζz⟩
  · -- a finite level: the reach of `u` is too short
    have hl' : l = u * ((m : Ordinal.{0}) + 1) + ζ := lkcIsLh1_unique hl hlhu
    have hum1 : u * ((m : Ordinal.{0}) + 1) < Om1 := ha_mul_lt (inE_indec gl_Om1_E) hu1 m
    obtain ⟨hmTB, hmpi⟩ := ha_pi_muls hB huTB hu1 m
    rw [hl'] at hlTB hle0
    have hlg1 : u * ((m : Ordinal.{0}) + 1) + ζ < Om1 := (inE_indec gl_Om1_E).add_lt hum1 (hζu.trans hu1)
    obtain ⟨hζTB, -⟩ := TB_sub hB hmTB hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hζTB
    obtain ⟨-, hps⟩ := pi_add hB hmTB hζTB
    rw [hps, hmpi, hpu] at hle0
    have hπζ : pi (f ρ) ρ ζ < f E := by rw [← hpu]; exact (pi_bijOn hB).2 hζTB huTB hζu
    have h1 : f E * ((m : Ordinal.{0}) + 1) + pi (f ρ) ρ ζ < f E * (((m + 1 : ℕ) : Ordinal.{0}) + 1) := by
      rw [ha_mul_succ]; exact (add_lt_add_iff_left _).2 hπζ
    have h2 : f E * (((m + 1 : ℕ) : Ordinal.{0}) + 1) < f E * ω := by
      refine (mul_lt_mul_iff_right₀ hfE0).2 ?_
      rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
    exact absurd (hle0.trans_lt (h1.trans h2)) (not_lt.2 (hmulw.trans le_self_add))
  · -- level `ω`: `ζ < z`, but `π(z) ≤ f(z) ≤ π(ζ)`
    have hl' : l = u * ω + ζ := lkcIsLh1_unique hl hlhu
    obtain ⟨h1TB, hp1⟩ := one_TB hB
    obtain ⟨hu1TB, hpu1⟩ := pi_add hB huTB h1TB
    have hu11 : u + 1 < Om1 := (ev_isSuccLimit_of_inE gl_Om1_E).add_one_lt hu1
    obtain ⟨hwTB, hwpi⟩ := pi_opowZ C.ups h.ρU hB hu1TB hu11
    have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρEE hEEδ.le)
      (lt_of_le_of_lt zero_le (C.mono C.rho hEA hρEE))
    rw [hpu1, hp1, hpu, hc_E_mul_om hfE] at hwpi
    rw [hc_E_mul_om huI] at hwTB hwpi
    rw [hl'] at hlTB hle0
    have hζ1 : ζ < Om1 := hζz.trans (hzE.trans hET.2)
    have hlg1 : u * ω + ζ < Om1 := (inE_indec gl_Om1_E).add_lt (InE.mul_lt gl_Om1_E hu1 omega_lt_Om1) hζ1
    obtain ⟨hζTB, -⟩ := TB_sub hB hwTB hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hζTB
    obtain ⟨-, hps⟩ := pi_add hB hwTB hζTB
    rw [hps, hwpi] at hle0
    have hfz : f z ≤ pi (f ρ) ρ ζ := (add_le_add_iff_left (f E * ω)).1 ((add_le_add hmulw le_rfl).trans hle0)
    have hzζ : z ≤ ζ := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    exact absurd hζz (not_lt.2 hzζ)

end Img

/-! ## Over a fixed point of `φ(ω, ·)` -/

/-- **The reach test over every fixed point of `φ(ω, ·)`**: every `ε`-number in `(P, N_ω(P))` has a reach of a finite
level or of level `ω`. -/
def HcDownW (ρ : Ordinal.{0}) : Prop :=
  ∀ P u : Ordinal.{0}, veblen ω P = P → ρ < P → hcNw P < gq 1 ρ → InE u → P < u → u < hcNw P →
    (∃ m : ℕ, ∃ ζ, IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u) ∨ (∃ ζ, IsLh1 u (u * ω + ζ) ∧ ζ < u)

/-- **Lemma IMG from `P` to `N_ω(P)` over every fixed point `P` of `φ(ω, ·)`.** -/
def HcNextW (ρ δ : Ordinal.{0}) : Prop :=
  ∀ P : Ordinal.{0}, veblen ω P = P → ρ < P → hcNw P < gq 1 ρ → (∀ v, v ≤ P → GnI ρ δ v) →
    ∀ v, v < hcNw P → GnI ρ δ v

/-- Every ordinal in `[hcS P, N_ω(P))` lies in some `[φ(ω, j), φ(ω, j+1))` with `P + 1 ≤ j`. -/
theorem hc_floorW {P u : Ordinal.{0}} (hP : veblen ω P = P) (hSu : hcS P ≤ u) (huN : u < hcNw P) :
    ∃ j, P + 1 ≤ j ∧ veblen ω j ≤ u ∧ u < veblen ω (j + 1) ∧ veblen ω (j + 1) < hcNw P := by
  have hi0 : veblen ω (P + 1) ≤ u := by rw [← hcS_fix hP]; exact hSu
  obtain ⟨j, hj1, hj2⟩ := hb_floor ω (u := u) (j0 := P + 1) hi0
  have hi0j : P + 1 ≤ j := by
    have : veblen ω (P + 1) < veblen ω (j + 1) := hi0.trans_lt hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
  have hH := hcNw_fix P
  have hjH : j < hcNw P := by
    have : veblen ω j < veblen ω (hcNw P) := by rw [hH]; exact hj1.trans_lt huN
    exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
  have hj1H : j + 1 < hcNw P := (hcNw_lim P).add_one_lt hjH
  refine ⟨j, hi0j, hj1, hj2, ?_⟩
  have := (isNormal_veblen ω).strictMono hj1H
  rwa [hH] at this

theorem hc_veb_fix_k (j : Ordinal.{0}) (k : ℕ) : veblen (k : Ordinal.{0}) (veblen ω j) = veblen ω j :=
  veblen_veblen_of_lt (natCast_lt_omega0 k) j

section Steps

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The finite levels below `hcS Q`**: every `ε`-number in `(Q, hcS Q)` has a reach `u·(m+1) + ζ`. -/
theorem hc_downFin {Q u : Ordinal.{0}} (hQ : ∀ k : ℕ, veblen (k : Ordinal.{0}) Q = Q) (hρQ : ρ < Q)
    (hSq : hcS Q < gq 1 ρ) (hu : InE u) (hQu : Q < u) (huS : u < hcS Q) :
    ∃ m : ℕ, ∃ ζ, IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u := by
  obtain ⟨k, hk⟩ := hc_lt_S huS
  have hk2 : u < hbN (k + 2) Q := hk.trans_le (hbN_mono (by omega) Q)
  obtain ⟨m, ζ, -, hl, hζ⟩ := hb_down h (k := k + 2) (by omega) Q u (hQ (k + 2)) hρQ
    ((hbN_lt_S _ Q).trans hSq) hu hQu hk2
  exact ⟨m, ζ, hl, hζ⟩

/-- **Lemma IMG below `hcS Q`** from Lemma IMG up to `Q` (`Q` a fixed point of every `φ(k, ·)`). -/
theorem hc_imgFin {Q : Ordinal.{0}} (hQ : ∀ k : ℕ, veblen (k : Ordinal.{0}) Q = Q) (hρQ : ρ < Q)
    (hSq : hcS Q < gq 1 ρ) (hle : ∀ v, v ≤ Q → GnI ρ δ v) : ∀ v, v < hcS Q → GnI ρ δ v := by
  intro v hv
  obtain ⟨k, hk⟩ := hc_lt_S hv
  have hk2 : v < hbN (k + 2) Q := hk.trans_le (hbN_mono (by omega) Q)
  exact hb_img_next h (k := k + 2) (by omega) Q (hQ (k + 2)) hρQ ((hbN_lt_S _ Q).trans hSq) hle v hk2

/-- **The closed form over `P`**: `ϑᵖ(Ω₁·ω + P + d) = φ(ω, P+1+d)` below `N_ω(P)`. -/
theorem hc_step_cfW {P d : Ordinal.{0}} (hP : veblen ω P = P) (hρP : ρ < P) (hNq : hcNw P < gq 1 ρ)
    (hd : veblen ω (P + 1 + d) < hcNw P) :
    glA ω (P + d) ρ = veblen ω (P + 1 + d) ∧ P + d < gq 1 ρ := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPq : P < gq 1 ρ := (hcNw_gt P).trans hNq
  have hi : P < veblen ω (P + 1) := by rw [← hcS_fix hP]; exact hcS_gt P
  have hnf : ∀ ν', ν' ≤ d → P + 1 + ν' < veblen ω (P + 1 + ν') := fun ν' h' =>
    hc_nofixW hi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hd)
  have hdq : P + d < gq 1 ρ :=
    (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq
      ((((le_add_self : d ≤ P + 1 + d).trans_lt (hnf d le_rfl))).trans (hd.trans hNq))
  have hG0 : glA ω P ρ = veblen ω (P + 1) := (hc_glA_fixW hρE hρ1 hP hρP hPq).trans (hcS_fix hP)
  exact ⟨hc_glAV hρE hρ1 hc_one_le_om (hc_om_q hρE hρ1) hPq hG0 d hdq (fun ν' h' _ => hnf ν' h'), hdq⟩

/-- **The reach of a point of level `ω` over `P`**: `φ(ω, P+1+d)` (below `N_ω(P)`) has reach `u·ω + ζ`,
`ζ = luZeta ρ ω (P + d) < u`. -/
theorem hc_step_lhW {P d : Ordinal.{0}} (hP : veblen ω P = P) (hρP : ρ < P) (hNq : hcNw P < gq 1 ρ)
    (hd : veblen ω (P + 1 + d) < hcNw P) :
    IsLh1 (veblen ω (P + 1 + d)) (veblen ω (P + 1 + d) * ω + luZeta ρ ω (P + d)) ∧
      luZeta ρ ω (P + d) < veblen ω (P + 1 + d) := by
  obtain ⟨hval, hdq⟩ := hc_step_cfW h hP hρP hNq hd
  obtain ⟨hdT, hd1⟩ := gm1_T h.ρE h.ρ1 hdq
  have H := hc_lhW h.ρE h.ρ1 hdT hd1
  rw [hval] at H
  exact H

/-- **THE REACH TEST OVER `P`.** -/
theorem hc_downAt {P u : Ordinal.{0}} (hP : veblen ω P = P) (hρP : ρ < P) (hNq : hcNw P < gq 1 ρ) (hu : InE u)
    (hPu : P < u) (huN : u < hcNw P) :
    (∃ m : ℕ, ∃ ζ, IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u) ∨ (∃ ζ, IsLh1 u (u * ω + ζ) ∧ ζ < u) := by
  have hSq : hcS P < gq 1 ρ := (hcS_lt_Nw hP).trans hNq
  rcases lt_or_ge u (hcS P) with huS | hSu
  · exact Or.inl (hc_downFin h (hc_fixW_k hP) hρP hSq hu hPu huS)
  obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorW hP hSu huN
  rcases hj1.lt_or_eq with hju | hju
  · have hρQ : ρ < veblen ω j := hρP.trans ((hcS_gt P).trans_le (by
      rw [hcS_fix hP]; exact (isNormal_veblen _).monotone hPj))
    refine Or.inl (hc_downFin h (hc_veb_fix_k j) hρQ ?_ hu hju (by rw [hcS_veb_eq]; exact hj2))
    rw [hcS_veb_eq]; exact hj1N.trans hNq
  · obtain ⟨d, rfl⟩ := exists_add_of_le hPj
    obtain ⟨hL, hζ⟩ := hc_step_lhW h hP hρP hNq (hju ▸ huN)
    rw [hju] at hL hζ
    exact Or.inr ⟨_, hL, hζ⟩

/-- **LEMMA IMG FROM `P` TO `N_ω(P)`** over a fixed point `P` of `φ(ω, ·)`. -/
theorem hc_nextAt {P : Ordinal.{0}} (hP : veblen ω P = P) (hρP : ρ < P) (hNq : hcNw P < gq 1 ρ)
    (hle : ∀ v, v ≤ P → GnI ρ δ v) : ∀ v, v < hcNw P → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hSq : hcS P < gq 1 ρ := (hcS_lt_Nw hP).trans hNq
  have hPq : P < gq 1 ρ := (hcNw_gt P).trans hNq
  have hbelowS := hc_imgFin h (hc_fixW_k hP) hρP hSq hle
  have hG0 : glA ω P ρ = veblen ω (P + 1) := (hc_glA_fixW hρE hρ1 hP hρP hPq).trans (hcS_fix hP)
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hNq)) (fun e he _ heB IHe => ?_)
  rcases lt_or_ge e (hcS P) with heS | hSe
  · exact hbelowS e heS
  obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorW hP hSe heB
  have hρj : ρ < veblen ω j := hρP.trans ((hcS_gt P).trans_le (by
    rw [hcS_fix hP]; exact (isNormal_veblen _).monotone hPj))
  rcases hj1.lt_or_eq with hje | hje
  · -- `e` strictly between two points of level `ω`: the finite levels over `φ(ω, j)`
    refine hc_imgFin h (hc_veb_fix_k j) hρj (by rw [hcS_veb_eq]; exact hj1N.trans hNq)
      (fun v hv => IHe v (hv.trans_lt hje)) e (by rw [hcS_veb_eq]; exact hj2)
  obtain ⟨d, rfl⟩ := exists_add_of_le hPj
  have hdN : veblen ω (P + 1 + d) < hcNw P := hje ▸ heB
  obtain ⟨hval, hdq⟩ := hc_step_cfW h hP hρP hNq hdN
  obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
  have he' : glA ω (P + d) ρ = e := hval.trans hje
  have hnf : ∀ ν', ν' ≤ d → IsSuccLimit ν' → P + 1 + ν' < veblen ω (P + 1 + ν') := fun ν' h' _ =>
    hc_nofixW (by rw [← hcS_fix hP]; exact hcS_gt P) le_self_add
      (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hdN)
  have IH' : ∀ u, u < glA ω (P + d) ρ → GnI ρ δ u := fun u hu => IHe u (by rw [he'] at hu; exact hu)
  rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
  · -- the first point `hcS P`: the reach test with `E' = P`
    subst h0
    have he0 : glA ω (P + 0) ρ = hcS P := by rw [add_zero, hG0, hcS_fix hP]
    have H := hc_img_downW h hdT hd1 hρP (by rw [he0]; exact hcS_gt P)
      (fun u hu hPu huE => by
        rw [he0] at huE
        exact Or.inl (hc_downFin h (hc_fixW_k hP) hρP hSq hu hPu huE)) IH'
    rwa [he'] at H
  · -- successor: `e = hcS(φ(ω, P+1+d'))`, the reach test with `E'` the previous point
    have hd'' : d = d' + 1 := by rw [← hd', succ_eq_add_one]
    subst hd''
    set Q' := veblen ω (P + 1 + d') with hQ'
    have heS : e = hcS Q' := by rw [← hje, ← add_assoc, hQ', hcS_veb_eq]
    have hQ'e : Q' < e := by rw [heS]; exact hcS_gt Q'
    have hρQ' : ρ < Q' := hρP.trans ((hcS_gt P).trans_le (by
      rw [hcS_fix hP, hQ']; exact (isNormal_veblen _).monotone le_self_add))
    have H := hc_img_downW h hdT hd1 hρQ' (by rw [he']; exact hQ'e)
      (fun u hu hQ'u huE => by
        rw [he', heS] at huE
        exact Or.inl (hc_downFin h (hc_veb_fix_k _) hρQ' (by rw [← heS]; exact heB.trans hNq) hu hQ'u huE)) IH'
    rwa [he'] at H
  · -- limit: the reach test with `E' = φ(ω, P+1+c')`, `d = c' + ω^z`
    have hd0 : d ≠ 0 := hlim.bot_lt.ne'
    obtain ⟨c', hcs, -, hc'd⟩ := lg_split hd0
    set z := lg d with hzdef
    set E' := veblen ω (P + 1 + c') with hE'def
    have hE'e : E' < e := by
      rw [← hje]; exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hc'd)
    have hSE' : hcS P ≤ E' := by rw [hcS_fix hP, hE'def]; exact (isNormal_veblen _).monotone le_self_add
    have hρE' : ρ < E' := hρP.trans ((hcS_gt P).trans_le hSE')
    have hz' : luZeta ρ ω (P + d) = z := hc_zetaW hρE hρ1 hPq hG0 hdq hnf hlim
    have H := hc_img_downW h hdT hd1 hρE' (by rw [he']; exact hE'e) (fun u hu hE'u huE => ?_) IH'
    · rwa [he'] at H
    rw [he'] at huE
    have huN : u < hcNw P := huE.trans heB
    obtain ⟨j', hPj', hj1', hj2', hj1N'⟩ := hc_floorW hP (hSE'.trans hE'u.le) huN
    have hcj : P + 1 + c' ≤ j' := by
      have : veblen ω (P + 1 + c') < veblen ω (j' + 1) := hE'u.trans hj2'
      exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
    have hjE : j' < P + 1 + d := by
      have : veblen ω j' < veblen ω (P + 1 + d) := by rw [hje]; exact hj1'.trans_lt huE
      exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
    rcases hj1'.lt_or_eq with hju | hju
    · have hρj : ρ < veblen ω j' := hρE'.trans_le ((isNormal_veblen _).monotone hcj)
      exact Or.inl (hc_downFin h (hc_veb_fix_k j') hρj (by rw [hcS_veb_eq]; exact hj1N'.trans hNq) hu hju
        (by rw [hcS_veb_eq]; exact hj2'))
    · obtain ⟨d'', rfl⟩ := exists_add_of_le hPj'
      have hc'd'' : c' < d'' := by
        rcases ((add_le_add_iff_left _).1 hcj).lt_or_eq with h' | h'
        · exact h'
        · exfalso; rw [← h'] at hju; exact absurd hju hE'u.ne
      have hd''d : d'' < d := (add_lt_add_iff_left _).1 hjE
      have hd''0 : d'' ≠ 0 := (lt_of_le_of_lt zero_le hc'd'').ne'
      obtain ⟨hL, -⟩ := hc_step_lhW h hP hρP hNq (hju ▸ huN)
      rw [hju] at hL
      have hζlg : luZeta ρ ω (P + d'') ≤ lg d'' := hc_zeta_leW hd''0
      obtain ⟨δ', hδ'⟩ : ∃ δ', d'' = c' + δ' := ⟨d'' - c', (Ordinal.add_sub_cancel_of_le hc'd''.le).symm⟩
      have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd''.ne'
      have hδlt : δ' < ω ^ z := by
        have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hd''d
        exact (add_lt_add_iff_left _).1 this
      have hlgd : lg d'' < z := by
        rw [hδ', gz_lg_add _ hδ0]
        by_contra hge; push Not at hge
        obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
        have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
        have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
        exact absurd hδlt (not_lt.2 (h1.trans h2))
      exact Or.inr ⟨_, hL, by rw [hz']; exact hζlg.trans_lt hlgd⟩

/-- **`HcDownW` HOLDS** (every fixed point `P` of `φ(ω, ·)`). -/
theorem hc_downW : HcDownW ρ := fun _ _ hP hρP hNq hu hPu huN => hc_downAt h hP hρP hNq hu hPu huN

/-- **`HcNextW` HOLDS** (every fixed point `P` of `φ(ω, ·)`). -/
theorem hc_nextW : HcNextW ρ δ := fun _ hP hρP hNq hle => hc_nextAt h hP hρP hNq hle

end Steps

/-! ## Lemma IMG below `B_{ω+1}(ρ)` -/

/-- **`B_{ω+1}(x) = N_ω(Γ_{x+1})`**, the least fixed point of `φ(ω, ·)` above `Γ_{x+1}` (`= φ(ω+1, Γ_{x+1}+1)`). -/
noncomputable def hcB1 (x : Ordinal.{0}) : Ordinal.{0} := hcNw (lgG x)

section B1

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`B_{ω+1}(x) ≤ ϑˣ(Ω₁·(ω+1) + Γ_{x+1}) < Γ_{x+2}`.** -/
theorem hcB1_lt1 : hcB1 x < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hω1q : ω + 1 < gq 1 x := (ev_isSuccLimit_of_inE hq).add_one_lt (omega0_lt_inE hq)
  obtain ⟨hkT, hk1⟩ := gm1_T hx hx1 hω1q
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have h1 : (1 : Ordinal.{0}) ≤ ω + 1 := le_add_self
  obtain ⟨b, hb⟩ := glA_P hx hx1 h1 hkT hk1 hGT hG1
  have hfix : veblen ω (glA (ω + 1) (lgG x) x) = glA (ω + 1) (lgG x) x := by
    rw [← hb]; exact veblen_veblen_of_lt (lt_add_one ω) b
  obtain ⟨-, -, -, -, -, hGa⟩ := glA_facts hx hx1 h1 hkT hk1 hGT hG1
  exact (hcNw_le hfix hGa).trans_lt (lgVt_lt_low hx hx1 hkT hk1 hGT hG1 (gm1_one_T hx hx1).1
    (gm1_one_T hx hx1).2 hω1q (mg_lgG_lt_G1 hx hx1))

/-- **`B_ω(x) < B_{ω+1}(x)`.** -/
theorem hc_Bw_lt_B1 : hbBw x < hcB1 x := by
  rw [← hcS_Bw]; exact hcS_lt_Nw (hc_G_fixW hx hx1)

end B1

section ImgB1

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BELOW `B_{ω+1}(ρ) = N_ω(Γ_{ρ+1})`.** -/
theorem hc_img_B1 : ∀ v, v < hcB1 ρ → GnI ρ δ v := by
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts h.ρE h.ρ1
  refine hc_nextAt h (hc_G_fixW h.ρE h.ρ1) hρG (hcB1_lt1 h.ρE h.ρ1) (fun v hv => ?_)
  rcases hv.lt_or_eq with hlt | rfl
  · exact gnI_lowG h hlt
  · exact gnI_G h

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B_{ω+1}(ρ)`.** -/
theorem hc_pkg_B1 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < hcB1 ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (hc_img_B1 h _ hT) hex

end ImgB1

end Googology.Trans.PoR.InaccPsi.R2.Hc
