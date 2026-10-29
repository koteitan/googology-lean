import Googology.Trans.PoR.InaccPsi.R2.VpDat
import Googology.Trans.PoR.InaccPsi.R2.UsRun

/-!
# The `ψ`-side of the atom move at every threshold `W = Ω_{s+1}`: validity, the run of an atom, values, first values

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ_π = S.psi · π`, `Hˡ_γ = Ul.ulH S s γ`, *own*: `B ∈ Cl(B, ψ_W B)`,
`m(γ) = ulDat S W γ` (the largest leaf of `γ` below `W`).  Generic in `s`:

* `vp_valid` (**validity from `D < ψ(B + W^γ·D)`**: `W^γ ∣ B`, `Hˡ_γ(c) = ψ(B)` give `d < Hˡ_γ(c + d)` for every
  `d ≤ D`; the port of `Vj.vj_validP` / `Uf.uf_valid`);
* `vp_dec` (**the run of an atom**: `y < Hˡ_γ(y) < ψ_W(A)` gives `y = c + D` with an own `B`, `ψ(B) = Hˡ_γ(c)`, `D`
  valid, and either `c = 0` or `c` is the largest fixed point of `Hˡ_γ` that is `≤ y`; the port of `Uf.ufRun`);
* `vp_run` (**`ψ(B + W^γ·D) = Hˡ_γ(c + D)` with `B + W^γ·D` own**, from every value base);
* `vp_val_of` (**a value test**: an own `B ≠ 0` with `W^γ ∣ B`, `γ ≤ ψ_V(B)` and `γ ∈ K_{ψ B}` (`0 < γ < V`) has
  `ψ(B)` in the range of `Hˡ_γ`);
* `VpCertCore` (**a certificate of a first value**: `γ = ψ_V(B₀)`, or `B₀ = K + W^γ`, `K` own, with `K = 0`,
  `ψ_W(K) ≤ m(γ)`, `ψ_V(K) < γ`, or `ψ_V(K) ≤ γ` and `W^γ ∤ K`), `vp_first_of_cert` (**a value `ψ(B₀)` with a certificate is the first value `Hˡ_γ(0)`**).

No new axiom.  New definition: `VpCertCore` (a Prop).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uo
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

theorem vp_Wg_indec (s j : Ordinal.{0}) : Indec (Om (s + 1) ^ j) := by rw [Ui.ui_W_eq s j]; exact indec_opow _

/-- An own `x` for `ψ_W` is own for `ψ_V`. -/
theorem vp_ownV {x : Ordinal.{0}} (h : x ∈ S.CSet x (S.psi x (Om (s + 1)))) :
    x ∈ S.CSet x (S.psi x (Om (s + 1 + 1))) :=
  CSet_mono le_rfl (ul_psiW_le_psiV x x) h

/-- **Validity from `D < ψ(B + W^γ·D)`** (`W^γ ∣ B`, `Hˡ_γ(c) = ψ(B)`). -/
theorem vp_valid (hs : s < ω) {γ B c D : Ordinal.{0}} (hB : Om (s + 1) ^ γ ∣ B)
    (hc : ulH S s γ c = S.psi B (Om (s + 1)))
    (hv : D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1))) : ∀ d, d ≤ D → d < ulH S s γ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (ulH_SC _ _).1)
  have hDΩ : D ≤ Om (s + 1) := hv.le.trans (Ui.ui_psi_lt _).le
  have hprev : ∀ d'', d'' < D → d'' < ulH S s γ (c + d) →
      S.psi (B + Om (s + 1) ^ γ * d'') (Om (s + 1)) < ulH S s γ (c + d) := fun d'' hd'' hq => by
    have hUB := ulUB (S := S) (s := s) hs γ B c d'' hB (by rw [hc]) (hd''.le.trans hDΩ)
    exact hUB.trans_lt ((ulH_lt_iff γ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have hcl : ∀ j < γ, ulD S s j < ulH S s γ (c + d) → ∀ z < ulH S s γ (c + d),
      ulH S s j z < ulH S s γ (c + d) := fun j hj hdj z hz => by
    have hf : ulH S s j (ulH S s γ (c + d)) = ulH S s γ (c + d) := ucG_fix_lower hj ⟨c + d, rfl⟩ hdj
    have := (ulH_lt_iff (S := S) (s := s) j).2 hz
    rwa [hf] at this
  have hBq : S.psi B (Om (s + 1)) < ulH S s γ (c + d) := by
    rw [← hc]; exact (ulH_lt_iff γ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))
  have h := ulInv (S := S) (s := s) hs hB (ulH_SC γ (c + d)) hcl hBq hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- **The run of an atom `Hˡ_γ(y)`** (`y < Hˡ_γ(y) < ψ_W(A)`): `y = c + D` with an own `B`, `ψ(B) = Hˡ_γ(c)`, every
`d ≤ D` valid; either `c = 0`, or `c` is a fixed point of `Hˡ_γ` and every fixed point `≤ y` is `≤ c`. -/
theorem vp_dec (hs : s < ω) {γ y A : Ordinal.{0}} (hyz : y < ulH S s γ y)
    (hzA : ulH S s γ y < S.psi A (Om (s + 1))) :
    ∃ B c D, B ∈ S.CSet B (S.psi B (Om (s + 1))) ∧ ulH S s γ c = S.psi B (Om (s + 1)) ∧ c + D = y ∧
      (∀ d, d ≤ D → d < ulH S s γ (c + d)) ∧
      (c = 0 ∨ (ulH S s γ c = c ∧ ∀ q, ulH S s γ q = q → q ≤ y → q ≤ c)) := by
  by_cases hA : ∃ q, ulH S s γ q = q ∧ q ≤ y
  · obtain ⟨q, hqf, hqy⟩ := hA
    have hne : ulH S s γ (y + 1) ≠ y + 1 := SC.ne_add_one (ulH_SC γ (y + 1)) y
    have hq1 : Om s < q := by rw [← hqf]; exact ulH_gt γ q
    obtain ⟨p, hpb, hpy, hmax⟩ := Rh.rh_base_below (ulH_normal γ)
      (hq1.trans_le (hqy.trans (le_self_add : y ≤ y + 1))) hne
    have hqp : q ≤ p := hmax q hqf hq1 (Order.lt_add_one_iff.2 hqy)
    have hp1 : Om s < p := hq1.trans_le hqp
    have hpf : ulH S s γ p = p := by
      rcases hpb with e | ⟨-, hf⟩
      · exact absurd e hp1.ne'
      · exact hf
    have hpy' : p ≤ y := Order.lt_add_one_iff.1 hpy
    have hpz : p < S.psi A (Om (s + 1)) := hpy'.trans_lt (hyz.trans hzA)
    have hpSC : SC p := by rw [← hpf]; exact ulH_SC γ p
    obtain ⟨Bp, hown, hBp⟩ := Ui.ui_own_of_SC hs hpSC hp1 hpz
    refine ⟨Bp, p, y - p, hown, by rw [hBp, hpf], Ordinal.add_sub_cancel_of_le hpy', fun d hd => ?_,
      Or.inr ⟨hpf, fun q' hq'f hq'y => hmax q' hq'f (by rw [← hq'f]; exact ulH_gt γ q')
        (Order.lt_add_one_iff.2 hq'y)⟩⟩
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero, hpf]; exact lt_of_le_of_lt zero_le hp1
    have hpd : p < p + d := lt_add_of_pos_right p (pos_iff_ne_zero.2 hd0)
    have hdy : p + d ≤ y := by
      calc p + d ≤ p + (y - p) := add_le_add_right hd p
        _ = y := Ordinal.add_sub_cancel_of_le hpy'
    have hnf : ulH S s γ (p + d) ≠ p + d := fun hf =>
      absurd (hmax (p + d) hf (hp1.trans hpd) (Order.lt_add_one_iff.2 hdy)) (not_le.2 hpd)
    exact le_add_self.trans_lt (lt_of_le_of_ne (ulH_le_self γ _) hnf.symm)
  push Not at hA
  have h0z : ulH S s γ 0 < S.psi A (Om (s + 1)) := ((ulH_le_iff γ).2 zero_le).trans_lt hzA
  obtain ⟨e0, hown, he0⟩ := Ui.ui_own_of_SC hs (ulH_SC γ 0) (ulH_gt γ 0) h0z
  refine ⟨e0, 0, y, hown, he0.symm, zero_add y, fun d hd => ?_, Or.inl rfl⟩
  rw [zero_add]
  have hnf : ulH S s γ d ≠ d := fun hf => absurd hd (not_le.2 (hA d hf))
  exact lt_of_le_of_ne (ulH_le_self γ _) hnf.symm

/-- **The run from a value base, with the ownness of its argument**: for own `B` with `ψ(B) = Hˡ_γ(c)`, `γ < V`,
`D < W` valid: `ψ(B + W^γ·D) = Hˡ_γ(c + D)` and `B + W^γ·D` is own. -/
theorem vp_run (hs : s < ω) {γ B c D : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hc : ulH S s γ c = S.psi B (Om (s + 1)))
    (hD : D < Om (s + 1)) (hcond : ∀ d, d ≤ D → d < ulH S s γ (c + d)) :
    S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (c + D) ∧
      B + Om (s + 1) ^ γ * D ∈ S.CSet (B + Om (s + 1) ^ γ * D) (S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1))) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have heq := Us.us_run hs hγV hown hc hD hcond
  refine ⟨heq, ?_⟩
  rcases eq_or_ne D 0 with hD0 | hD0
  · rw [hD0, mul_zero, add_zero]; exact hown
  set e := B + Om (s + 1) ^ γ * D with hedef
  have hγe : γ ∈ S.CSet e (S.psi e (Om (s + 1))) := by
    rcases (Us.us_val_le hs hown hc).lt_or_eq with hlt | hγeq
    · have hK : UlK S s (S.psi B (Om (s + 1))) γ :=
        (ul_vis (Ui.ui_psi_SC B)).1 (by rw [← hc]; exact ulH_D_lt γ c)
      exact (psi_mono hκ (le_self_add : B ≤ e)).2 (uoDV hs B γ hown hK hlt)
    · obtain ⟨-, hγC, -⟩ := Us.us_second hs hown hc hγeq
      have hle : B + Om (s + 1) ^ γ ≤ e := by
        rw [hedef]
        have : Om (s + 1) ^ γ ≤ Om (s + 1) ^ γ * D := by
          conv_lhs => rw [← mul_one (Om (s + 1) ^ γ)]
          exact mul_le_mul_right (one_le_iff_ne_zero.2 hD0) _
        exact add_le_add_right this B
      exact (psi_mono hκ hle).2 hγC
  have hDe : D ∈ S.CSet e (S.psi e (Om (s + 1))) := by
    refine CSet.of_lt ?_
    rw [hedef, heq]; exact hcond D le_rfl
  exact CSet.add_mem ((psi_mono hκ (le_self_add : B ≤ e)).2 hown) (ul_Wpow_mem hs hγe hDe)

/-- **A value test**: for own `B ≠ 0`, `0 < γ < V`, `W^γ ∣ B`, `γ ≤ ψ_V(B)`, `γ ∈ K_{ψ B}`: `ψ(B)` is a value of
`Hˡ_γ`. -/
theorem vp_val_of (hs : s < ω) {B γ : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB0 : B ≠ 0)
    (hγ0 : γ ≠ 0) (hγV : γ < Om (s + 1 + 1)) (hdvd : Om (s + 1) ^ γ ∣ B)
    (hle : γ ≤ S.psi B (Om (s + 1 + 1))) (hK : UlK S s (S.psi B (Om (s + 1))) γ) :
    S.psi B (Om (s + 1)) ∈ range (ulH S s γ) := by
  have hSC : SC (S.psi B (Om (s + 1))) := Ui.ui_psi_SC B
  rcases hle.lt_or_eq with hlt | heq
  · refine ucG_range (d := ulD S s) (L := Om s) (μ := γ) hSC (Ui.ui_L_lt_psi B) ((ul_vis hSC).2 hK)
      fun j hj hdj => ?_
    have hjC := uoDV hs B j hown ((ul_vis hSC).1 hdj) (hj.trans hlt)
    exact uo_fwd hs j (hj.trans hγV) B hown ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans hdvd) hB0 hjC
  · exact ⟨0, Us.us_bv hs B hown hB0 γ hγ0 hγV hdvd hle hK (Or.inl heq)⟩

/-- `ψ_W(B) = Hˡ_γ(0)` with `γ ≠ 0` forces `B ≠ 0`. -/
theorem vp_B0_ne (hs : s < ω) {B γ : Ordinal.{0}} (hγ0 : γ ≠ 0) (hB : ulH S s γ 0 = S.psi B (Om (s + 1))) :
    B ≠ 0 := by
  rintro rfl
  have hv : ulH S s γ 0 = ulH S s 0 0 := by rw [hB, Us.us_psi0 hs]
  have hf : ulH S s 0 (ulH S s γ 0) = ulH S s γ 0 :=
    ucG_fix_lower (pos_iff_ne_zero.2 hγ0) ⟨0, rfl⟩ ((ulD_le_self 0).trans_lt (ulH_SC γ 0).1)
  rw [hv] at hf
  exact Us.us_val0_ne hf

/-- **A certificate of a first value** `ψ_W(B₀)` of `Hˡ_γ`: `γ = ψ_V(B₀)`, or `B₀ = K + W^γ` with an own `K` and
`K = 0`, `ψ_W(K) ≤ m(γ)`, `ψ_V(K) < γ`, or `ψ_V(K) ≤ γ` with `W^γ ∤ K`. -/
def VpCertCore (S : InaccSeq.{0}) (s γ B0 : Ordinal.{0}) : Prop :=
  γ = S.psi B0 (Om (s + 1 + 1)) ∨ ∃ K, B0 = K + Om (s + 1) ^ γ ∧ K ∈ S.CSet K (S.psi K (Om (s + 1))) ∧
    (K = 0 ∨ S.psi K (Om (s + 1)) ≤ ulDat S (Om (s + 1)) γ ∨ S.psi K (Om (s + 1 + 1)) < γ ∨
      (S.psi K (Om (s + 1 + 1)) ≤ γ ∧ ¬ Om (s + 1) ^ γ ∣ K))

/-- **A value `ψ_W(B₀)` of `Hˡ_γ` with a certificate is the first value**: `Hˡ_γ(0) = ψ_W(B₀)` (`B₀` own,
`0 < γ < V`, `γ` of the notation). -/
theorem vp_first_of_cert (hs : s < ω) {γ B0 : Ordinal.{0}} (hγ0 : γ ≠ 0)
    (hγN : γ ∈ ⋃ a, S.CSet a 0) (hown : B0 ∈ S.CSet B0 (S.psi B0 (Om (s + 1))))
    (hval : S.psi B0 (Om (s + 1)) ∈ range (ulH S s γ)) (hcert : VpCertCore S s γ B0) :
    ulH S s γ 0 = S.psi B0 (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  obtain ⟨o, ho⟩ := hval
  have hle : ulH S s γ 0 ≤ S.psi B0 (Om (s + 1)) := by rw [← ho]; exact (ulH_le_iff γ).2 zero_le
  have hlt1 : ulH S s γ 0 < S.psi (B0 + 1) (Om (s + 1)) := hle.trans_lt (Ui.ui_psi_lt_of_own hown (lt_add_one B0))
  obtain ⟨B, hownB, hB⟩ := Ui.ui_own_of_SC hs (ulH_SC γ 0) (ulH_gt γ 0) hlt1
  have hvB : ulH S s γ 0 = S.psi B (Om (s + 1)) := hB.symm
  suffices hB0B : B0 ≤ B by
    exact le_antisymm hle (by rw [hvB]; exact (psi_mono hκ hB0B).1)
  have hdvd : Om (s + 1) ^ γ ∣ B := Us.us_dvd_val hs hownB hvB
  have hγψ : γ ≤ S.psi B (Om (s + 1 + 1)) := Us.us_val_le hs hownB hvB
  rcases hcert with heq | ⟨K, hB0K, hownK, hK⟩
  · by_contra hc
    push Not at hc
    have h1 := (Ui.ui_own_lt_iff (s := s + 1) (vp_ownV hownB) (vp_ownV hown)).2 hc
    rw [← heq] at h1
    exact absurd h1 (not_lt.2 hγψ)
  rw [hB0K]
  have hKB : K < B := by
    rcases hK with hK0 | hKm | hKV | ⟨hKV, hKd⟩
    · rw [hK0]; exact pos_iff_ne_zero.2 (vp_B0_ne hs hγ0 hvB)
    · by_contra hc
      push Not at hc
      have hm : ulDat S (Om (s + 1)) γ < S.psi B (Om (s + 1)) := by
        rw [← hvB]
        exact (uo_vis_dat hs (ulH_SC γ 0) (ulH_gt γ 0) (by rw [hvB]; exact (Ui.ui_psi_lt B).le) hγN).1
          (ulH_D_lt γ 0)
      exact absurd (((psi_mono hκ hc).1.trans hKm).trans_lt hm) (lt_irrefl _)
    · by_contra hc
      push Not at hc
      exact absurd (((psi_mono hκV hc).1.trans_lt hKV).trans_le hγψ) (lt_irrefl _)
    · by_contra hc
      push Not at hc
      have he : S.psi B (Om (s + 1 + 1)) = S.psi K (Om (s + 1 + 1)) :=
        le_antisymm ((psi_mono hκV hc).1) (hKV.trans hγψ)
      have hBK := Ui.ui_own_unique (s := s + 1) (vp_ownV hownB) (vp_ownV hownK) he
      exact hKd (hBK ▸ hdvd)
  exact Vp.vp_add_le_of_dvd (vp_Wg_indec s γ) hdvd hKB

end Googology.Trans.PoR.InaccPsi.R2.Vp
