import Googology.Trans.PoR.InaccPsi.R2.QcCopy
import Googology.Trans.PoR.InaccPsi.R2.QfLh

/-!
# QfMul: THE PRODUCT COPY LEMMA `f(X)·π(Θ_u m) ≤ f(X·Θ_E m)` FOR THE CODES BELOW A BOUND

`He.he_wz_mul` gives `f(E)·π(c) ≤ f(E·c)` for `c < E` from Lemma IMG below `E`.  Here the multiplier is the reading
`Θ_E(m)` of a code `m` and the target is `π(Θ_u m)` (`π(u) = f(E)`), for any `ε`-number `X` of the witness sets with
`Θ_E(m) < X`: the facts used at the parts of `m` (its exponents and their last exponents) are the **copy data**
`QfCD` of those parts (the conclusion form of `Qc.qc_copy`), assumed for every code below a bound `c₀`.  The proof is
the one of `He.he_wz_mul`:

* `QfCD` (**the copy data of a code `z`**: the witness sets can be enlarged to contain `Θ_E z`, and `Θ_u z ∈ Tᵖ[f(ρ)]`,
  `π(Θ_u z) ≤ f(Θ_E z)` in every copy for every strongly critical `u` with `π(u) = f(E)` over which `z` is a code);
* `qf_mul` (**THE PRODUCT COPY LEMMA**): `m = m₁ + ω^j` by the sum; `m = ω^j`, `j = j₁ + ω^{j₂}`: `f(X·ω^{Θ j₁}) ≥
  f(X)·ω^{π(Θ_u j₁)}` (induction) and the source `ω^{X + Θ j} ≤₁ ω^{X + Θ j} + Θ(j₂)` ([W07b] Theorem 2.2 through
  `Lu.lu_lh_opow`), unless the value is a `υ`-point.

No new axiom.  New definition: `QfCD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.He Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Hc

/-- **The copy data of a code `z`** over `E`, relative to the witness sets `W, Z`. -/
def QfCD (ρ δ E : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (z : Ordinal.{0}) : Prop :=
  ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧ ggTh E z ∈ W' ∪ Z' ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A → ImgCtx ρ A f →
      ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u z → pi (f ρ) ρ u = f E →
        ggTh u z ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ (ggTh u z) ≤ f (ggTh E z)

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE PRODUCT COPY LEMMA**: for an `ε`-number `X ∈ W` in `(ρ, δ)`, codes below `c₀` with copy data, and `Θ_E` below
`X` there: the witness sets can be enlarged to contain `X·Θ_E(m)`, and then `f(X)·π(Θ_u m) ≤ f(X·Θ_E m)`. -/
theorem qf_mul {E X c₀ : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hXW : X ∈ W) (hρX : ρ < X)
    (hX : InE X) (hXδ : X < δ) (hES : SC E) (hE1 : E < Om 1)
    (hCD : ∀ z, GgCl E z → z < c₀ → QfCD ρ δ E W Z z) (hbd : ∀ m, GgCl E m → m < c₀ → ggTh E m < X) :
    ∀ m, GgCl E m → m < c₀ → 0 < m → ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧
      X * ggTh E m ∈ W' ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A →
        ImgCtx ρ A f → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u m → pi (f ρ) ρ u = f E →
          ggTh u m ∈ TB ρ (f ρ) ∧ f X * pi (f ρ) ρ (ggTh u m) ≤ f (X * ggTh E m) := by
  classical
  have hX0 : 0 < X := hX.pos
  have hδI := inE_indec h.δE
  have hcδ : ∀ c, c < X → X * c < δ := fun c hc => InE.mul_lt h.δE hXδ (hc.trans hXδ)
  have hρle : ∀ d, 0 < d → ρ ≤ X * d := fun d hd => hρX.le.trans (le_mul_of_one_le_right' (one_le_iff_pos.2 hd))
  have hXle : ∀ d, 0 < d → X ≤ X * d := fun d hd => le_mul_of_one_le_right' (one_le_iff_pos.2 hd)
  have hcnt : ∀ u, SC u → u < Om 1 → ∀ c, GgCl u c → ggTh u c < Om1 := fun u hu hu1 c hc => by
    rw [rj_Om1]; exact Ph.phTh_lt_Om1 hu hu1 hc
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH' =>
  intro hm hmc hm0
  obtain ⟨m', j, hms, hm'm, hm'C, hjC, hjl, hdvd⟩ := Qc.qc_split hES m hm hm0.ne'
  have hjm : j ≤ m := by
    have h1 : ω ^ j ≤ m := by rw [hms]; exact le_add_self
    exact (right_le_opow j one_lt_omega0).trans h1
  rcases eq_or_ne m' 0 with h0 | h0
  · -- `m = ω^j`
    rw [h0, zero_add] at hms
    rcases eq_or_ne j 0 with hj0 | hj0
    · -- `m = 1`
      have hm1 : m = 1 := by rw [hms, hj0, opow_zero]
      subst hm1
      refine ⟨W, Z, w, subset_refl _, subset_refl _, ?_, fun A f _ _ C u hu huT hu1 _ _ => ?_⟩
      · rw [ggTh_small (gg_one_lt_of_SC hES).le, mul_one]; exact hXW
      · obtain ⟨h1, hp1⟩ := one_TB (h.img_bases C)
        rw [ggTh_small (gg_one_lt_of_SC hu).le, ggTh_small (gg_one_lt_of_SC hES).le, hp1, mul_one, mul_one]
        exact ⟨h1, le_rfl⟩
    have hjc₀ : j < c₀ := hjm.trans_lt hmc
    obtain ⟨j1, j2, hjs, hj1j, hj1C, hj2C, hj2l, hj2d⟩ := Qc.qc_split hES j hjC hj0
    have hj2j : j2 ≤ j := by
      have h1 : ω ^ j2 ≤ j := by rw [hjs]; exact le_add_self
      exact (right_le_opow j2 one_lt_omega0).trans h1
    have hm1 : ω ^ j1 < m := by rw [hms]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hj1j
    have hm1C : GgCl E (ω ^ j1) := GgCl.opow hES.1 hj1C
    obtain ⟨W1, Z1, w1, hW1, hZ1, hmW1, b1⟩ := IH' _ hm1 hm1C (hm1.trans hmc) (opow_pos _ omega0_pos)
    obtain ⟨Wa, Za, wa, hWa, hZa, ma, ba⟩ := hCD j hjC hjc₀
    obtain ⟨Wb, Zb, wb, hWb, hZb, mb, bb⟩ := hCD j1 hj1C (hj1j.trans hjc₀)
    obtain ⟨Wl, Zl, wl, hWl, hZl, ml, bl⟩ := hCD j2 hj2C (hj2j.trans_lt hjc₀)
    set WU := W1 ∪ Wa ∪ Wb ∪ Wl with hWU
    set ZU := Z1 ∪ Za ∪ Zb ∪ Zl with hZU
    have wU : WZ ρ δ WU ZU := ((w1.union wa).union wb).union wl
    have s1 : W1 ⊆ WU := fun a ha => by simp [hWU, ha]
    have sa : Wa ⊆ WU := fun a ha => by simp [hWU, ha]
    have sb : Wb ⊆ WU := fun a ha => by simp [hWU, ha]
    have sl : Wl ⊆ WU := fun a ha => by simp [hWU, ha]
    have t1 : Z1 ⊆ ZU := fun a ha => by simp [hZU, ha]
    have ta : Za ⊆ ZU := fun a ha => by simp [hZU, ha]
    have tb : Zb ⊆ ZU := fun a ha => by simp [hZU, ha]
    have tl : Zl ⊆ ZU := fun a ha => by simp [hZU, ha]
    set J := ggTh E j with hJ
    set J1 := ggTh E j1 with hJ1
    set J2 := ggTh E j2 with hJ2
    have hThm : ggTh E m = ω ^ J := by rw [hms, ggTh_opow hES hjC]
    have hJs : J = J1 + ω ^ J2 := by rw [hJ, hjs, ggTh_add hES hj1C, ggTh_opow hES hj2C]
    have hJX : J < X := by
      have := hbd m hm hmc
      rw [hThm] at this
      exact (right_le_opow J one_lt_omega0).trans_lt this
    have hJ0 : J ≠ 0 := Ph.phTh_ne_zero hES hj0
    have hJ2X : J2 < X := (ggTh_mono (y := E) hj2j).trans_lt hJX
    have e1 : X * ggTh E m = ω ^ (X + J) := by rw [hThm, opow_add, show ω ^ X = X from hX]
    have hcI : Indec (X * ggTh E m) := by rw [e1]; exact indec_opow _
    have hmX : ggTh E m < X := hbd m hm hmc
    have hm0' : 0 < ggTh E m := by rw [hThm]; exact opow_pos _ omega0_pos
    have hlt : X * ggTh E (ω ^ j1) < X * ggTh E m :=
      (mul_lt_mul_iff_right₀ hX0).2 (ggTh_lt hm1C hm1)
    -- the data in a copy
    have hdat : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑WU ⊆ A → ↑ZU ⊆ A → ImgCtx ρ A f →
        X * ggTh E m ∈ A → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u m → pi (f ρ) ρ u = f E →
        ∃ α, f X = ω ^ α ∧ ggTh u m ∈ TB ρ (f ρ) ∧
          pi (f ρ) ρ (ggTh u m) = ω ^ (pi (f ρ) ρ (ggTh u j1) + ω ^ pi (f ρ) ρ (ggTh u j2)) ∧
          ω ^ (α + pi (f ρ) ρ (ggTh u j1)) < f (X * ggTh E m) ∧ J ∈ A ∧ pi (f ρ) ρ (ggTh u j) ≤ f J ∧
          J2 ∈ A ∧ pi (f ρ) ρ (ggTh u j2) ≤ f J2 ∧
          pi (f ρ) ρ (ggTh u j) = pi (f ρ) ρ (ggTh u j1) + ω ^ pi (f ρ) ρ (ggTh u j2) ∧
          ggTh u j2 ∈ TB ρ (f ρ) := by
      intro A f hA hZA C hcA u hu huT hu1 hmu hπu
      have hB := h.img_bases C
      have hXA : X ∈ A := hA (Finset.mem_coe.2 (s1 (hW1 hXW)))
      have hmA : X * ggTh E (ω ^ j1) ∈ A := hA (Finset.mem_coe.2 (s1 hmW1))
      -- the codes over `u`
      have hju : GgCl u j := by
        have := (ggDec hu m hmu).2; rwa [hms, log_opow one_lt_omega0] at this
      obtain ⟨j1', j2', hjs', -, hj1u', hj2u', hj2l', hj2d'⟩ := Qc.qc_split hu j hju hj0
      have e2 : j2' = j2 := by rw [hj2l', hj2l]
      rw [e2] at hjs' hj2d' hj2u'
      have e1' : j1' = j1 := Qc.qc_split_unique hjs' hjs hj2d' hj2d
      rw [e1'] at hj1u'
      have hm1u : GgCl u (ω ^ j1) := GgCl.opow hu.1 hj1u'
      obtain ⟨hmTB, hb1⟩ := b1 A f (he_sub s1 hA) (he_sub t1 hZA) C u hu huT hu1 hm1u hπu
      have hjA : J ∈ A := mem_A ma (he_sub sa hA) (he_sub ta hZA)
      obtain ⟨hjTB, pj⟩ := ba A f (he_sub sa hA) (he_sub ta hZA) C u hu huT hu1 hju hπu
      obtain ⟨hj1TB, -⟩ := bb A f (he_sub sb hA) (he_sub tb hZA) C u hu huT hu1 hj1u' hπu
      have hlA : J2 ∈ A := mem_A ml (he_sub sl hA) (he_sub tl hZA)
      obtain ⟨hlTB, pl⟩ := bl A f (he_sub sl hA) (he_sub tl hZA) C u hu huT hu1 hj2u' hπu
      obtain ⟨α, hα⟩ := hc_indec_opow h (C.indec _ hXA (inE_indec hX))
      have hl1 : ggTh u j2 < Om1 := hcnt u hu hu1 j2 hj2u'
      obtain ⟨hwTB, hwπ⟩ := pi_opowZ C.ups h.ρU hB hlTB hl1
      obtain ⟨-, hjπ⟩ := pi_add hB hj1TB hwTB
      have hThuj : ggTh u j = ggTh u j1 + ω ^ ggTh u j2 := by
        rw [hjs, ggTh_add hu hj1u', ggTh_opow hu hj2u']
      rw [hwπ] at hjπ
      rw [← ggTh_opow hu hj2u', ← ggTh_add hu hj1u', ← hjs] at hjπ
      have hThum : ggTh u m = ω ^ ggTh u j := by rw [hms, ggTh_opow hu hju]
      have hj1 : ggTh u j < Om1 := hcnt u hu hu1 j hju
      obtain ⟨hcTB, hcπ⟩ := pi_opowZ C.ups h.ρU hB hjTB hj1
      rw [← hThum, hjπ] at hcπ
      rw [← hThum] at hcTB
      have hj11 : ggTh u j1 < Om1 := hcnt u hu hu1 j1 hj1u'
      obtain ⟨-, hmπ⟩ := pi_opowZ C.ups h.ρU hB hj1TB hj11
      rw [ggTh_opow hu hj1u', hmπ] at hb1
      have hlt' : f X * ω ^ pi (f ρ) ρ (ggTh u j1) < f (X * ggTh E m) := hb1.trans_lt (C.mono hmA hcA hlt)
      rw [hα, ← opow_add] at hlt'
      exact ⟨α, hα, hcTB, hcπ, hlt', hjA, pj, hlA, pl, hjπ, hlTB⟩
    rcases eq_or_ne j2 0 with hl0 | hl0
    · -- `logend(j) = 0`: `j = j₁ + 1`
      refine ⟨insert (X * ggTh E m) WU, ZU, wU.insW (hρle _ hm0') (hcδ _ hmX) (Or.inl hcI),
        fun a ha => Finset.mem_insert_of_mem (s1 (hW1 ha)), hZ1.trans t1, Finset.mem_insert_self _ _,
        fun A f hA hZA C u hu huT hu1 hmu hπu => ?_⟩
      have hA' : ↑WU ⊆ A := he_sub (Finset.subset_insert _ _) hA
      have hcA : X * ggTh E m ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      obtain ⟨α, hα, hcTB, hcπ, hlt', -, -, -, -, -, -⟩ := hdat A f hA' hZA C hcA u hu huT hu1 hmu hπu
      have hB := h.img_bases C
      have hσ0 : (0 : Ordinal.{0}) < f ρ := hB.1.pos
      have e0 : ggTh u j2 = 0 := by rw [hl0]; exact ggTh_small zero_le
      rw [e0, pi_lt hB hσ0, opow_zero] at hcπ
      obtain ⟨a', ha'⟩ := hc_indec_opow h (C.indec _ hcA hcI)
      rw [ha'] at hlt'
      have hstep : α + pi (f ρ) ρ (ggTh u j1) < a' := (opow_lt_opow_iff_right one_lt_omega0).1 hlt'
      refine ⟨hcTB, ?_⟩
      rw [hcπ, hα, ← opow_add, ha', ← add_assoc]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hstep)
    · -- the source `ω^{X+J} ≤₁ ω^{X+J} + J₂`
      have hX0' : X + J ≠ 0 := (lt_of_lt_of_le hX0 le_self_add).ne'
      have hXc : X < X * ggTh E m := by
        rw [e1]
        calc X = ω ^ X := hX.symm
          _ < ω ^ (X + J) := (opow_lt_opow_iff_right one_lt_omega0).2
              (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hJ0))
      have hXlt : X + J < ω ^ (X + J) := by
        rw [← e1]; exact hcI.add_lt hXc (hJX.trans hXc)
      have hL := lu_lh_opow hX0' hXlt
      have hlgJ : lg (X + J) = J2 := by
        rw [lu_lg_add hX hJ0 hJX, hJ, ← Qc.qc_th_lg hES hjC hj0, hJ2, hj2l]
      rw [hlgJ, ← e1] at hL
      have hTop : X * ggTh E m + J2 < δ := hδI.add_lt (hcδ _ hmX) (hJ2X.trans hXδ)
      have hsrc : le1 (X * ggTh E m) (X * ggTh E m + J2) :=
        (h.lowδ _ _ (hρX.trans_le (hXle _ hm0')) hTop.le).2 hL.1
      have hJ20 : 0 < J2 := pos_iff_ne_zero.2 (Ph.phTh_ne_zero hES hl0)
      set W2 := insert (X * ggTh E m) WU with hW2
      have w2 : WZ ρ δ W2 ZU := wU.insW (hρle _ hm0') (hcδ _ hmX) (Or.inl hcI)
      have hlW : J2 ∈ W2 ∪ ZU := by
        rcases Finset.mem_union.1 ml with hm' | hm'
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (sl hm'))
        · exact Finset.mem_union_right _ (tl hm')
      have w3 : WZ ρ δ (insert (X * ggTh E m + J2) W2) ZU :=
        w2.insW ((hρle _ hm0').trans le_self_add) hTop (Or.inr ⟨X * ggTh E m,
          Finset.mem_union_left _ (Finset.mem_insert_self _ _), J2, hlW,
          lt_add_of_pos_right _ hJ20, (hJ2X.trans_le (hXle _ hm0')).trans_le le_self_add, rfl⟩)
      refine ⟨insert (X * ggTh E m + J2) W2, ZU, w3,
        fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (s1 (hW1 ha))),
        hZ1.trans t1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        fun A f hA hZA C u hu huT hu1 hmu hπu => ?_⟩
      have hA' : ↑WU ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha))))
      have hcA : X * ggTh E m ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have hTA : X * ggTh E m + J2 ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      obtain ⟨α, hα, hcTB, hcπ, hlt', hjA, pj, hlA, pl, hjπ, hlTB⟩ :=
        hdat A f hA' hZA C hcA u hu huT hu1 hmu hπu
      have hB := h.img_bases C
      refine ⟨hcTB, ?_⟩
      rw [hcπ, hα, ← opow_add]
      have hfl0 : 0 < f J2 := by
        have h0TB : (0 : Ordinal.{0}) ∈ TB ρ (f ρ) := mem_TB_of_lt hB hB.1.pos
        have hJ2u0 : 0 < ggTh u j2 := pos_iff_ne_zero.2 (Ph.phTh_ne_zero hu hl0)
        have := (pi_bijOn hB).2 h0TB hlTB hJ2u0
        rw [pi_lt hB hB.1.pos] at this
        exact this.trans_le pl
      have himg : le1 (f (X * ggTh E m)) (f (X * ggTh E m) + f J2) := by
        have := C.cov1 _ hcA _ hTA hsrc
        rwa [← C.add _ hcA _ hlA _ hTA rfl] at this
      have hXA : X ∈ A := hA' (Finset.mem_coe.2 (s1 (hW1 hXW)))
      have hXy : f X < f (X * ggTh E m) := C.mono hXA hcA hXc
      by_cases hU : UpsPt (f (X * ggTh E m))
      · have hyE : InE (f (X * ggTh E m)) := upsPt_inE hU
        have hαy : α < f (X * ggTh E m) :=
          lt_of_le_of_lt (right_le_opow α one_lt_omega0) (by rw [← hα]; exact hXy)
        have hjy : pi (f ρ) ρ (ggTh u j) < f (X * ggTh E m) :=
          pj.trans_lt (C.mono hjA hcA (hJX.trans hXc))
        rw [← hjπ]
        conv_rhs => rw [← show ω ^ f (X * ggTh E m) = f (X * ggTh E m) from hyE]
        exact opow_le_opow_right omega0_pos ((inE_indec hyE).add_lt hαy hjy).le
      · have hR := (C.sk _ (C.low _ hcA) hU _).1 himg
        have hly : f J2 ≤ f (X * ggTh E m) := (C.mono hlA hcA (hJ2X.trans hXc)).le
        obtain ⟨a', -, ha', hla'⟩ := (le1R_thm22 hfl0 hly).1 hR
        rw [ha'] at hlt'
        have hstep : α + pi (f ρ) ρ (ggTh u j1) < a' := (opow_lt_opow_iff_right one_lt_omega0).1 hlt'
        obtain ⟨Y, hY⟩ := exists_add_of_le hstep.le
        have hY0 : Y ≠ 0 := by rintro rfl; rw [add_zero] at hY; exact absurd hY hstep.ne'
        have hlY : lg a' = lg Y := by rw [hY]; exact lu_lg_add_right hY0
        have hdY : ω ^ pi (f ρ) ρ (ggTh u j2) ∣ Y :=
          (opow_dvd_opow ω ((pl.trans hla').trans_eq hlY)).trans (lg_dvd hY0)
        have hYge : ω ^ pi (f ρ) ρ (ggTh u j2) ≤ Y := Ordinal.le_of_dvd hY0 hdY
        rw [ha', hY, ← add_assoc]
        exact opow_le_opow_right omega0_pos (add_le_add le_rfl hYge)
  · -- `m = m' + ω^j`, `m' ≠ 0`
    have hm'0 : 0 < m' := pos_iff_ne_zero.2 h0
    have hwC : GgCl E (ω ^ j) := GgCl.opow hES.1 hjC
    have hjm' : ω ^ j ≤ m' := Ordinal.le_of_dvd h0 hdvd
    have hjm2 : ω ^ j < m := by
      rw [hms]
      exact (lt_add_of_pos_right (ω ^ j) (opow_pos _ omega0_pos)).trans_le (add_le_add hjm' le_rfl)
    obtain ⟨W1, Z1, w1, hW1, hZ1, hm1, b1⟩ := IH' m' hm'm hm'C (hm'm.trans hmc) hm'0
    obtain ⟨W2, Z2, w2, hW2, hZ2, hm2, b2⟩ := IH' _ hjm2 hwC (hjm2.trans hmc) (opow_pos _ omega0_pos)
    have hThm : ggTh E m = ggTh E m' + ggTh E (ω ^ j) := by rw [hms, ggTh_add hES hm'C]
    have eC : X * ggTh E m = X * ggTh E m' + X * ggTh E (ω ^ j) := by rw [hThm, mul_add]
    have h1lt : X * ggTh E m' < X * ggTh E m := (mul_lt_mul_iff_right₀ hX0).2 (ggTh_lt hm'C hm'm)
    have h2lt : X * ggTh E (ω ^ j) < X * ggTh E m := (mul_lt_mul_iff_right₀ hX0).2 (ggTh_lt hwC hjm2)
    have hmX : ggTh E m < X := hbd m hm hmc
    have hm0' : 0 < ggTh E m := pos_iff_ne_zero.2 (Ph.phTh_ne_zero hES hm0.ne')
    refine ⟨insert (X * ggTh E m) (W1 ∪ W2), Z1 ∪ Z2, (w1.union w2).insW (hρle _ hm0') (hcδ _ hmX)
      (Or.inr ⟨X * ggTh E m', Finset.mem_union_left _ (Finset.mem_union_left _ hm1), X * ggTh E (ω ^ j),
        Finset.mem_union_left _ (Finset.mem_union_right _ hm2), h1lt, h2lt, eC.symm⟩),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      fun a ha => Finset.mem_union_left _ (hZ1 ha), Finset.mem_insert_self _ _,
      fun A f hA hZA C u hu huT hu1 hmu hπu => ?_⟩
    have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
    have hA2 : ↑W2 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
    have hZ1A : ↑Z1 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
    have hZ2A : ↑Z2 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 ha)))
    have hcA : X * ggTh E m ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hadd := C.add _ (hA1 (Finset.mem_coe.2 hm1)) _ (hA2 (Finset.mem_coe.2 hm2)) _ hcA eC.symm
    obtain ⟨m'', j', hms', -, hm''u, hj'u, hj'l, hj'd⟩ := Qc.qc_split hu m hmu hm0.ne'
    have e2 : j' = j := by rw [hj'l, hjl]
    rw [e2] at hms' hj'd hj'u
    have e1 : m'' = m' := Qc.qc_split_unique hms' hms hj'd hdvd
    rw [e1] at hm''u
    have hwu : GgCl u (ω ^ j) := GgCl.opow hu.1 hj'u
    obtain ⟨t1, b1'⟩ := b1 A f hA1 hZ1A C u hu huT hu1 hm''u hπu
    obtain ⟨t2, b2'⟩ := b2 A f hA2 hZ2A C u hu huT hu1 hwu hπu
    obtain ⟨tc, pc⟩ := pi_add (h.img_bases C) t1 t2
    have hThu : ggTh u m = ggTh u m' + ggTh u (ω ^ j) := by rw [hms, ggTh_add hu hm''u]
    rw [hThu]
    refine ⟨tc, ?_⟩
    rw [← hadd, pc, mul_add]
    exact add_le_add b1' b2'

end Copy

end Googology.Trans.PoR.InaccPsi.R2.Qf
