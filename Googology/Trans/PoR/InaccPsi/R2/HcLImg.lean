import Googology.Trans.PoR.InaccPsi.R2.HcGInd

/-!
# HcLImg: LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY CONSTANT LEVEL `1 ≤ q < ρ`

At a constant level `q` the reach of `E = ϑᵖ(Ω₁·q + t)` is `luL(E, q) + z = E·(1+q) + e_q + z` (`hc_luL_dec`;
`e_q = logend(log_ω q)` when `q = ω^{log_ω q} ≥ ω`, else `0`).  `Hc.hc_wz_mulE` gives `f(E)·c ≤ f(E·c)` only for
`c < ω^ω`: a finite witness set cannot follow `E·ω^j` for infinite `j` by indecomposables alone.  Here the source
`ω^{E+j} ≤₁ ω^{E+j} + logend(j)` ([W07b] Theorem 2.2, `Lu.lu_lh_opow`) enters the witness set: its copy
`f(E·ω^j) ≤₁ f(E·ω^j) + logend(j)` forces `f(E·ω^j) = ω^{a'}` with `logend(j) ≤ logend(a')` (`le1R_thm22`), and with
`a' > α + j₁` (`f(E) = ω^α`, `j = j₁ + ω^{logend(j)}`, the induction hypothesis at `ω^{j₁}`) this gives
`a' ≥ α + j`: **`f(E)·c ≤ f(E·c)` for every constant `c < ρ`** (`hc_wz_mulL`).  On the other side `π(u·c) = π(u)·c`
for every `c < σ` (`hc_pi_mulL`), and the constants of the witness set lie below `σ = f(ρ)`.  So Lemma IMG by the reach
test going down holds at every constant level `1 ≤ q < ρ` (`hc_img_downL`).

* `hcE`, `hc_luL_dec` (**`luL(a, q) = a·(1+q) + e_q`**), `hc_lhL` (**THE REACH AT EVERY CONSTANT LEVEL**),
  `hc_pi_mulL` (**`π(u·c) = π(u)·c`, every `c < σ`**), `hc_wz_mulL` (**THE PRODUCTS `E·c`, EVERY `c < ρ`, WITH
  `f(E)·c ≤ f(E·c)`**), `hc_img_downL` (**LEMMA IMG BY THE REACH TEST GOING DOWN, EVERY CONSTANT LEVEL**).

No new axiom.  New definition: `hcE`.
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

/-! ## The reach at a constant level -/

open Classical in
/-- **The constant part of the reach**: `logend(log_ω q)` when `q = ω^{log_ω q} ≥ ω`, else `0`. -/
noncomputable def hcE (q : Ordinal.{0}) : Ordinal.{0} :=
  if ω ≤ q ∧ q = ω ^ log ω q then lg (log ω q) else 0

theorem hcE_le (q : Ordinal.{0}) : hcE q ≤ q := by
  unfold hcE
  split_ifs with h
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le omega0_pos h.1).ne'
    have hb0 : log ω q ≠ 0 := (log_pos one_lt_omega0 hq0 h.1).ne'
    exact (lg_le hb0).trans (log_le_self ω q)
  · exact zero_le

/-- **`luL(a, q) = a·(1+q) + e_q`** for an `ε`-number `a` and `1 ≤ q < a`. -/
theorem hc_luL_dec {a q : Ordinal.{0}} (ha : InE a) (hq1 : 1 ≤ q) (hqa : q < a) :
    luL a q = a * (1 + q) + hcE q := by
  classical
  rcases lt_or_ge q ω with hqω | hqω
  · rw [lu_luL_fin hqω]
    unfold hcE; rw [if_neg (fun h => absurd h.1 (not_le.2 hqω)), add_zero]
  rw [lu_luL_inf hqω, one_add_of_omega0_le hqω]
  have hq0 : q ≠ 0 := (lt_of_lt_of_le omega0_pos hqω).ne'
  set b := log ω q with hb
  have hle : ω ^ b ≤ q := opow_log_le_self ω hq0
  by_cases heq : q = ω ^ b
  · unfold hcE; rw [if_pos ⟨hqω, heq⟩, ← hb]
    rw [← heq, Ordinal.sub_self, mul_zero, add_zero]
  · unfold hcE; rw [if_neg (fun h => heq h.2)]
    have hd0 : q - ω ^ b ≠ 0 := by
      intro h0; exact heq (le_antisymm (Ordinal.sub_eq_zero_iff_le.1 h0) hle)
    have hlgb : lg b < a := by
      have hb0 : b ≠ 0 := (log_pos one_lt_omega0 hq0 hqω).ne'
      exact ((lg_le hb0).trans (log_le_self ω q)).trans_lt hqa
    have habs : lg b + a * (q - ω ^ b) = a * (q - ω ^ b) := by
      refine add_of_omega0_opow_le (b := a) (by rw [show ω ^ a = a from ha]; exact hlgb) ?_
      rw [show ω ^ a = a from ha]
      exact le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
    rw [add_assoc, habs, ← mul_add, Ordinal.add_sub_cancel_of_le hle, add_zero]

/-- **THE `R₁⁺`-REACH AT EVERY CONSTANT LEVEL `1 ≤ q < x`**: `lh(ϑˣ(Ω₁·q + t)) = ϑˣ(Ω₁·q + t)·(1+q) + e_q + ζ`,
`ζ = luZeta x q t < ϑˣ(Ω₁·q + t)`. -/
theorem hc_lhL {x q t : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hq1 : 1 ≤ q) (hqx : q < x) (ht : t ∈ Tset x)
    (ht1 : t < Om1) :
    IsLh1 (glA q t x) (glA q t x * (1 + q) + hcE q + luZeta x q t) ∧ luZeta x q t < glA q t x := by
  obtain ⟨hqT, hqΩ⟩ : q ∈ Tset x ∧ q < Om1 := ⟨mem_T_of_le hx hx1 hqx.le, hqx.trans hx1⟩
  obtain ⟨hL, hζ, hqv, hvE⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ ht ht1
  have e := hc_luL_dec hvE hq1 hqv
  have e' : vt x (Om1 * q + t) = glA q t x := rfl
  rw [e, e'] at hL
  exact ⟨hL, hζ⟩

/-! ## Products `u·c`, `c` a constant -/

/-- **`π(u·c) = π(u)·c`** for an `ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁` and every `c < σ` (`υ`-points `σ < ρ`). -/
theorem hc_pi_mulL {σ ρ u : Ordinal.{0}} (hσU : UpsPt σ) (hρU : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (huE : InE u) : ∀ c, c < σ → u * c ∈ TB ρ σ ∧ pi σ ρ (u * c) = pi σ ρ u * c := by
  have hσ0 : (0 : Ordinal.{0}) < σ := hB.1.pos
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
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
  set j := lg c with hjdef
  have hjσ : j < σ := (lg_le hc0).trans_lt hc
  have hjTB : j ∈ TB ρ σ := mem_TB_of_lt hB hjσ
  obtain ⟨hujTB, hpuj⟩ := pi_add hB hu hjTB
  rw [pi_lt hB hjσ] at hpuj
  have huj1 : u + j < Om1 := (inE_indec gl_Om1_E).add_lt hu1 (hjσ.trans hσ1)
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

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- `f(E)` is a power `ω^α`. -/
theorem hc_indec_opow {a : Ordinal.{0}} (ha : Indec a) : ∃ α : Ordinal.{0}, a = ω ^ α := by
  obtain ⟨hne, hpa⟩ := indec_iff.1 ha
  rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hpa with h0 | ⟨α, hα⟩
  · exact absurd h0 hne
  · exact ⟨α, hα.symm⟩

/-- **THE PRODUCTS `E·c` FOR EVERY CONSTANT `0 < c < ρ`** in the witness sets, with `f(E)·c ≤ f(E·c)` in every copy of
a set containing them. -/
theorem hc_wz_mulL {E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ < E)
    (hE : InE E) (hEδ : E < δ) :
    ∀ c, c < ρ → 0 < c → ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧ E * c ∈ W' ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A → ImgCtx ρ A f →
        f E * c ≤ f (E * c) := by
  classical
  have hE0 : 0 < E := hE.pos
  have hδI := inE_indec h.δE
  have hcδ : ∀ c, c < ρ → E * c < δ := fun c hc => InE.mul_lt h.δE hEδ (hc.trans (h.ρτ.trans h.τδ))
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc0
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0.ne'
  set j := lg c with hjdef
  have hjc : j ≤ c := lg_le hc0.ne'
  have hjρ : j < ρ := hjc.trans_lt hc
  have hρle : ∀ d, 0 < d → ρ ≤ E * d := fun d hd => hρE.le.trans (le_mul_of_one_le_right' (one_le_iff_pos.2 hd))
  rcases eq_or_ne c' 0 with h0 | h0
  · -- `c = ω^j`
    rw [h0, zero_add] at hcs
    rcases eq_or_ne j 0 with hj0 | hj0
    · refine ⟨W, Z, w, subset_refl _, subset_refl _, by rw [hcs, hj0, opow_zero, mul_one]; exact hEW,
        fun A f _ _ _ => ?_⟩
      rw [hcs, hj0, opow_zero, mul_one, mul_one]
    obtain ⟨j1, hjs, hjdvd, hj1j⟩ := lg_split hj0
    have hm : ω ^ j1 < c := by rw [hcs]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hj1j
    obtain ⟨W1, Z1, w1, hW1, hZ1, hm1, b1⟩ := IH _ hm (hm.trans hc) (opow_pos _ omega0_pos)
    have hjE : j < E := hjρ.trans hρE
    have e1 : E * c = ω ^ (E + j) := by rw [hcs, opow_add, show ω ^ E = E from hE]
    have hcI : Indec (E * c) := by rw [e1]; exact indec_opow _
    have hlt : E * ω ^ j1 < E * c := (mul_lt_mul_iff_right₀ hE0).2 hm
    -- the bound shared by both cases
    have key : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W1 ⊆ A → ↑Z1 ⊆ A → ImgCtx ρ A f →
        E * c ∈ A → ∀ a', f (E * c) = ω ^ a' → (∀ α, f E = ω ^ α → α + j1 < a' → α + j ≤ a') →
          f E * c ≤ f (E * c) := by
      intro A f hA1 hZA C hcA a' ha' hstep
      have hEA : E ∈ A := hA1 (Finset.mem_coe.2 (hW1 hEW))
      have hmA : E * ω ^ j1 ∈ A := hA1 (Finset.mem_coe.2 hm1)
      obtain ⟨α, hα⟩ := hc_indec_opow h (C.indec _ hEA (inE_indec hE))
      have hlt' : f E * ω ^ j1 < f (E * c) := (b1 A f hA1 hZA C).trans_lt (C.mono hmA hcA hlt)
      rw [hα, ← opow_add, ha'] at hlt'
      have := hstep α hα ((opow_lt_opow_iff_right one_lt_omega0).1 hlt')
      have e2 : f E * c = ω ^ (α + j) := by rw [hα, opow_add, ← hcs]
      rw [e2, ha']
      exact opow_le_opow_right omega0_pos this
    rcases eq_or_ne (lg j) 0 with hl0 | hl0
    · -- `logend(j) = 0`: `j = j₁ + 1`
      refine ⟨insert (E * c) W1, Z1, w1.insW (hρle c hc0) (hcδ c hc) (Or.inl hcI),
        hW1.trans (Finset.subset_insert _ _), hZ1, Finset.mem_insert_self _ _, fun A f hA hZA C => ?_⟩
      have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha)))
      have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      obtain ⟨a', ha'⟩ := hc_indec_opow h (C.indec _ hcA hcI)
      refine key A f hA1 hZA C hcA a' ha' (fun α _ hlt2 => ?_)
      rw [hjs, hl0, opow_zero, ← add_assoc]
      exact Order.add_one_le_of_lt hlt2
    · -- the source `ω^{E+j} ≤₁ ω^{E+j} + logend(j)`
      have hlj : lg j < ρ := (lg_le hj0).trans_lt hjρ
      have hX0 : E + j ≠ 0 := (lt_of_lt_of_le hE0 le_self_add).ne'
      have h1c' : (1 : Ordinal.{0}) < c := by
        rw [hcs]
        have := (opow_lt_opow_iff_right one_lt_omega0).2 (pos_iff_ne_zero.2 hj0)
        rwa [opow_zero] at this
      have hEc' : E < E * c := by
        calc E = E * 1 := (mul_one E).symm
          _ < E * c := (mul_lt_mul_iff_right₀ hE0).2 h1c'
      have hXlt : E + j < ω ^ (E + j) := by
        rw [← e1]; exact hcI.add_lt hEc' (hjE.trans hEc')
      have hL := lu_lh_opow hX0 hXlt
      rw [lu_lg_add hE hj0 hjE, ← e1] at hL
      have hTop : E * c + lg j < δ := hδI.add_lt (hcδ c hc) (hlj.trans (h.ρτ.trans h.τδ))
      have hsrc : le1 (E * c) (E * c + lg j) :=
        (h.lowδ _ _ (hρE.trans_le (le_mul_of_one_le_right' (one_le_iff_pos.2 hc0))) hTop.le).2 hL.1
      have hl0' : 0 < lg j := pos_iff_ne_zero.2 hl0
      set W2 := insert (E * c) W1 with hW2
      set Z2 := insert j (insert (lg j) Z1) with hZ2
      have w2 : WZ ρ δ W2 (insert (lg j) Z1) := (w1.insZ hlj).insW (hρle c hc0) (hcδ c hc) (Or.inl hcI)
      have w3 : WZ ρ δ (insert (E * c + lg j) W2) Z2 :=
        (w2.insZ hjρ).insW ((hρle c hc0).trans le_self_add) hTop (Or.inr ⟨E * c,
          Finset.mem_union_left _ (Finset.mem_insert_self _ _), lg j,
          Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
          lt_add_of_pos_right _ hl0',
          (hlj.trans (hρE.trans_le (le_mul_of_one_le_right' (one_le_iff_pos.2 hc0)))).trans_le le_self_add, rfl⟩)
      refine ⟨insert (E * c + lg j) W2, Z2, w3,
        fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hW1 ha)),
        fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hZ1 ha)),
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun A f hA hZA C => ?_⟩
      have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha))))
      have hZA1 : ↑Z1 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha))))
      have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have hTA : E * c + lg j ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hlA : lg j ∈ A := hZA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have hjA : j ∈ A := hZA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hEA : E ∈ A := hA1 (Finset.mem_coe.2 (hW1 hEW))
      have hfl : f (lg j) = lg j := C.fix _ hlA hlj
      have hjf : j < f E := by
        have := C.mono hjA hEA hjE; rwa [C.fix _ hjA hjρ] at this
      have himg : le1 (f (E * c)) (f (E * c) + lg j) := by
        have := C.cov1 _ hcA _ hTA hsrc
        rwa [← C.add _ hcA _ hlA _ hTA rfl, hfl] at this
      have hyI : Indec (f (E * c)) := C.indec _ hcA hcI
      have h1c : (1 : Ordinal.{0}) < c := by
        rw [hcs]
        have := (opow_lt_opow_iff_right one_lt_omega0).2 (pos_iff_ne_zero.2 hj0)
        rwa [opow_zero] at this
      have hEc : E < E * c := by
        calc E = E * 1 := (mul_one E).symm
          _ < E * c := (mul_lt_mul_iff_right₀ hE0).2 h1c
      have hEy : f E < f (E * c) := C.mono hEA hcA hEc
      by_cases hU : UpsPt (f (E * c))
      · -- a `υ`-point: an `ε`-number above `f(E)` and `j`
        have hyE : InE (f (E * c)) := upsPt_inE hU
        obtain ⟨α, hα⟩ := hc_indec_opow h (C.indec _ hEA (inE_indec hE))
        have hαy : α < f (E * c) := lt_of_le_of_lt (right_le_opow α one_lt_omega0) (by rw [← hα]; exact hEy)
        have hjy : j < f (E * c) := hjf.trans hEy
        have hlt3 : ω ^ (α + j) < f (E * c) := by
          conv_rhs => rw [← show ω ^ f (E * c) = f (E * c) from hyE]
          exact (opow_lt_opow_iff_right one_lt_omega0).2 ((inE_indec hyE).add_lt hαy hjy)
        have e2 : f E * c = ω ^ (α + j) := by rw [hα, opow_add, ← hcs]
        rw [e2]; exact hlt3.le
      · have hR := (C.sk _ (C.low _ hcA) hU _).1 himg
        have hly : lg j ≤ f (E * c) := ((lg_le hj0).trans hjf.le).trans hEy.le
        obtain ⟨a', -, ha', hla'⟩ := (le1R_thm22 hl0' hly).1 hR
        refine key A f hA1 hZA1 C hcA a' ha' (fun α _ hlt2 => ?_)
        obtain ⟨Y, hY⟩ := exists_add_of_le hlt2.le
        have hY0 : Y ≠ 0 := by rintro rfl; rw [add_zero] at hY; exact absurd hY hlt2.ne'
        have hlY : lg a' = lg Y := by rw [hY]; exact lu_lg_add_right hY0
        have hdY : ω ^ lg j ∣ Y := (opow_dvd_opow ω (hla'.trans_eq hlY)).trans (lg_dvd hY0)
        have hYge : ω ^ lg j ≤ Y := Ordinal.le_of_dvd hY0 hdY
        rw [hY, hjs, ← add_assoc]
        exact add_le_add le_rfl hYge
  · -- `c = c' + ω^j`, `c' ≠ 0`
    have hc'0 : 0 < c' := pos_iff_ne_zero.2 h0
    have hjc' : ω ^ j ≤ c' := Ordinal.le_of_dvd h0 hdvd
    have hjc2 : ω ^ j < c := by
      rw [hcs]; exact (lt_add_of_pos_right (ω ^ j) (opow_pos j omega0_pos)).trans_le (add_le_add hjc' le_rfl)
    obtain ⟨W1, Z1, w1, hW1, hZ1, hm1, b1⟩ := IH c' hc'c (hc'c.trans hc) hc'0
    obtain ⟨W2, Z2, w2, hW2, hZ2, hm2, b2⟩ := IH _ hjc2 (hjc2.trans hc) (opow_pos _ omega0_pos)
    have eC : E * c = E * c' + E * ω ^ j := by rw [hcs, mul_add]
    have h1lt : E * c' < E * c := (mul_lt_mul_iff_right₀ hE0).2 hc'c
    have h2lt : E * ω ^ j < E * c := (mul_lt_mul_iff_right₀ hE0).2 hjc2
    refine ⟨insert (E * c) (W1 ∪ W2), Z1 ∪ Z2, (w1.union w2).insW (hρle c hc0) (hcδ c hc)
      (Or.inr ⟨E * c', Finset.mem_union_left _ (Finset.mem_union_left _ hm1), E * ω ^ j,
        Finset.mem_union_left _ (Finset.mem_union_right _ hm2), h1lt, h2lt, eC.symm⟩),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      fun a ha => Finset.mem_union_left _ (hZ1 ha), Finset.mem_insert_self _ _, fun A f hA hZA C => ?_⟩
    have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
    have hA2 : ↑W2 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
    have hZ1A : ↑Z1 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
    have hZ2A : ↑Z2 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 ha)))
    have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hadd := C.add _ (hA1 (Finset.mem_coe.2 hm1)) _ (hA2 (Finset.mem_coe.2 hm2)) _ hcA eC.symm
    rw [← hadd]
    calc f E * c = f E * c' + f E * ω ^ j := by rw [hcs, mul_add]
      _ ≤ f (E * c') + f (E * ω ^ j) := add_le_add (b1 A f hA1 hZ1A C) (b2 A f hA2 hZ2A C)

end Copy

/-! ## Lemma IMG by the reach test going down at every constant level -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY CONSTANT LEVEL `1 ≤ q < ρ`**: let `E = ϑᵖ(Ω₁·q + t)` (reach
`E·(1+q) + e_q + z`, `z = luZeta ρ q t`), `ρ < E' < E`.  If Lemma IMG holds below `E` and every `ε`-number
`u ∈ (E', E)` has a reach `u·(1+q') + e_{q'} + ζ` with `ζ < u`, `q' ≤ q`, and `ζ < z` when `q' = q`, then Lemma IMG
holds at `E`. -/
theorem hc_img_downL {q t E' : Ordinal.{0}} (hq1 : 1 ≤ q) (hqρ : q < ρ) (htT : t ∈ Tset ρ) (ht1 : t < Om1)
    (hρE' : ρ < E') (hE'E : E' < glA q t ρ)
    (hdown : ∀ u, InE u → E' < u → u < glA q t ρ → ∃ q' ζ, q' ≤ q ∧
      IsLh1 u (u * (1 + q') + hcE q' + ζ) ∧ ζ < u ∧ (q' = q → ζ < luZeta ρ q t))
    (IH : ∀ u, u < glA q t ρ → GnI ρ δ u) : GnI ρ δ (glA q t ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hL, hzE⟩ := hc_lhL hρE hρ1 hq1 hqρ htT ht1
  set E := glA q t ρ with hEdef
  set z := luZeta ρ q t with hzdef
  set e := hcE q with hedef
  have hqT : q ∈ Tset ρ := mem_T_of_le hρE hρ1 hqρ.le
  have hqΩ : q < Om1 := hqρ.trans hρ1
  obtain ⟨hET0, hρEE, hE1, hE, -, -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hρδ : ρ < δ := h.ρτ.trans h.τδ
  set c := 1 + q with hcdef
  have hc : c < ρ := (inE_indec hρE).add_lt (one_lt_omega0.trans (omega0_lt_inE hρE)) hqρ
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one le_self_add
  have heρ : e < ρ := (hcE_le q).trans_lt hqρ
  have hEc : E * c < δ := InE.mul_lt h.δE hEδ (hc.trans hρδ)
  have hT1δ : E * c + e < δ := hδI.add_lt hEc (heρ.trans hρδ)
  have hTopδ : E * c + e + z < δ := hδI.add_lt hT1δ (hzE.trans hEδ)
  have hsrc : le1 E (E * c + e + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEpos : 0 < E := hE.pos
  have hEEc : E ≤ E * c := le_mul_of_one_le_right' (one_le_iff_pos.2 hc0)
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  set W3 := insert E (W1 ∪ W2) with hW3
  set Z3 := insert q (insert e (Z1 ∪ Z2)) with hZ3
  have w3 : WZ ρ δ W3 Z3 := (((w1.union w2).insZ heρ).insZ hqρ).insW hρEE.le hEδ (Or.inl (inE_indec hE))
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 Z3 := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hEpos,
      lt_add_of_pos_right _ hEpos, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  obtain ⟨W5, Z5, w5, h45, hZ35, hc5, bmul⟩ := hc_wz_mulL h w4 (h34 hE3) hρEE hE hEδ c hc hc0
  have heZ : e ∈ Z5 := hZ35 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hqZ : q ∈ Z5 := hZ35 (Finset.mem_insert_self _ _)
  obtain ⟨W6, w6, h56, hT1⟩ : ∃ W6 : Finset Ordinal.{0}, WZ ρ δ W6 Z5 ∧ W5 ⊆ W6 ∧ E * c + e ∈ W6 := by
    rcases eq_or_ne e 0 with he0 | he0
    · exact ⟨W5, w5, subset_refl _, by rw [he0, add_zero]; exact hc5⟩
    · refine ⟨insert (E * c + e) W5, w5.insW ((hρEE.le.trans hEEc).trans le_self_add) hT1δ
        (Or.inr ⟨_, Finset.mem_union_left _ hc5, e, Finset.mem_union_right _ heZ,
          lt_add_of_pos_right _ (pos_iff_ne_zero.2 he0), (heρ.trans hρEE).trans_le (hEEc.trans le_self_add), rfl⟩),
        Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  have hzZ : z ∈ W6 ∪ Z5 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h56 (h45 (h34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)))))
    · exact Finset.mem_union_right _ (hZ35 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ hm))))
  obtain ⟨W7, w7, h67, hTop⟩ : ∃ W7 : Finset Ordinal.{0}, WZ ρ δ W7 Z5 ∧ W6 ⊆ W7 ∧ E * c + e + z ∈ W7 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W6, w6, subset_refl _, by rw [hz0, add_zero]; exact hT1⟩
    · refine ⟨insert (E * c + e + z) W6, w6.insW (((hρEE.le.trans hEEc).trans le_self_add).trans le_self_add) hTopδ
        (Or.inr ⟨_, Finset.mem_union_left _ hT1, z, hzZ, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le ((hEEc.trans le_self_add).trans le_self_add), rfl⟩), Finset.subset_insert _ _,
          Finset.mem_insert_self _ _⟩
  have hsub : W4 ⊆ W7 := fun a ha => h67 (h56 (h45 ha))
  refine gnI_mk h w7 (Finset.mem_union_left _ (hsub (h34 hE3))) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ5 : ↑Z5 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hW1 : ↑W1 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (hsub (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ5 (Finset.mem_coe.2 (hZ35 (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ5 (Finset.mem_coe.2 (hZ35 (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hW5 : ↑W5 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h67 (h56 (Finset.mem_coe.1 ha))))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hW (Finset.mem_coe.2 (hsub (h34 hE3)))
  have hEEA : E + E ∈ A := hW (Finset.mem_coe.2 (hsub (Finset.mem_insert_self _ _)))
  have hEcA : E * c ∈ A := hW5 (Finset.mem_coe.2 hc5)
  have hT1A : E * c + e ∈ A := hW (Finset.mem_coe.2 (h67 hT1))
  have hTopA : E * c + e + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have heA : e ∈ A := hZ5 (Finset.mem_coe.2 heZ)
  have hqA : q ∈ A := hZ5 (Finset.mem_coe.2 hqZ)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  have hmulc : f E * c ≤ f (E * c) := bmul A f hW5 hZ5 C
  have hqσ : q < f ρ := C.above q hqA hqρ
  have hσE : f ρ < f E := C.mono C.rho hEA hρEE
  have hfT : f (E * c + e + z) = f (E * c) + e + f z := by
    rw [← C.add _ hT1A _ hzA _ hTopA rfl, ← C.add _ hEcA _ heA _ hT1A rfl, C.fix _ heA heρ]
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f (E * c) + e + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [hfT] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨q', ζ, hq'q, hlhu, hζu, hζz⟩ := hdown u huI hE'u huE
  have hl' : l = u * (1 + q') + hcE q' + ζ := lkcIsLh1_unique hl hlhu
  have hσE' : InE (f ρ) := upsPt_inE C.ups
  have hσ1 : f ρ < Om1 := hB.2.2.1.trans hB.2.2.2
  have hq'σ : q' < f ρ := hq'q.trans_lt hqσ
  have hc'σ : 1 + q' < f ρ := (inE_indec hσE').add_lt (one_lt_omega0.trans (omega0_lt_inE hσE')) hq'σ
  have he'σ : hcE q' < f ρ := (hcE_le q').trans_lt hq'σ
  obtain ⟨hmTB, hmpi⟩ := hc_pi_mulL C.ups h.ρU hB huTB hu1 huI (1 + q') hc'σ
  have he'TB : hcE q' ∈ TB ρ (f ρ) := mem_TB_of_lt hB he'σ
  obtain ⟨hs1TB, hs1pi⟩ := pi_add hB hmTB he'TB
  rw [hmpi, pi_lt hB he'σ, hpu] at hs1pi
  have hum1 : u * (1 + q') < Om1 := InE.mul_lt gl_Om1_E hu1 (hc'σ.trans hσ1)
  have hs11 : u * (1 + q') + hcE q' < Om1 := (inE_indec gl_Om1_E).add_lt hum1 (he'σ.trans hσ1)
  rw [hl'] at hlTB hle0
  have hlg1 : u * (1 + q') + hcE q' + ζ < Om1 := (inE_indec gl_Om1_E).add_lt hs11 (hζu.trans hu1)
  obtain ⟨hζTB, -⟩ := TB_sub hB hs1TB hlTB le_self_add hlg1
  rw [Ordinal.add_sub_cancel] at hζTB
  obtain ⟨-, hps⟩ := pi_add hB hs1TB hζTB
  rw [hps, hs1pi] at hle0
  have hπζ : pi (f ρ) ρ ζ < f E := by rw [← hpu]; exact (pi_bijOn hB).2 hζTB huTB hζu
  rcases hq'q.lt_or_eq with hlt' | heq
  · -- a lower level: the reach of `u` is too short
    have hfEI : Indec (f E) := C.indec _ hEA (inE_indec hE)
    have h1 : f E * (1 + q') + hcE q' + pi (f ρ) ρ ζ < f E * (1 + q' + 1) := by
      rw [mul_add_one, add_assoc]
      exact (add_lt_add_iff_left _).2 (hfEI.add_lt (he'σ.trans hσE) hπζ)
    have h2 : f E * (1 + q' + 1) ≤ f E * c :=
      mul_le_mul_right (Order.add_one_le_of_lt ((add_lt_add_iff_left 1).2 hlt')) _
    exact absurd (hle0.trans_lt (h1.trans_le h2)) (not_lt.2 ((hmulc.trans le_self_add).trans le_self_add))
  · -- the same level: `ζ < z`, but `π(z) ≤ f(z) ≤ π(ζ)`
    subst heq
    have hfz : f z ≤ pi (f ρ) ρ ζ :=
      (add_le_add_iff_left (f E * c + e)).1 ((add_le_add (add_le_add hmulc le_rfl) le_rfl).trans hle0)
    have hzζ : z ≤ ζ := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    exact absurd (hζz rfl) (not_lt.2 hzζ)

end Img

end Googology.Trans.PoR.InaccPsi.R2.Hc
