import Googology.Trans.PoR.InaccPsi.R2.SeRoad

/-!
# `B_n` commutes with `ϑ^β` at every countable argument, at every `ε`-base `β < L(n+2)`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `ω̄ = wbar` ([W07a] Def 3.4), `L(ω) = Nc.ncL S ω`.

* `siExp`, `si_wbar_eq` (**`ω̄_γ = ω^{siExp γ}`**, `siExp γ = γ + 1` if the limit part `ω·(γ/ω)` of `γ` is an
  `ε`-number, `γ` otherwise; the unique strictly increasing function onto the additive principal numbers that are not
  `ε`-numbers);
* `siB_omul` (`B_n(ω·q) = ω·B_n q`), `siB_E_iff` (`B_n` keeps and reflects `ε`-numbers below `L(ω)`),
  `siB_wbar` (**`B_n(ω̄_γ) = ω̄_{B_n γ}`** for `γ < L(ω)`);
* `siVt_zero` (**`ϑ^τ(0) = τ`**, from [W07b] Cor 5.10 (`T_inter_Om1`), [W07a] Thm 3.23 (`vt_rep`), Lemma 4.2
  (`vt_wbar`), Lemma 4.3 (`vt_E_iff`));
* `siVtHomC` (**`B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` for every `ε`-number `β < c_{n+1}` and every `η < c_{n+1}`**,
  unconditionally: part (a) and part (b) of `Se.SePiHom2` at the countable arguments).

No new axiom.  New definition: `siExp` (an ordinal function used to compute `ω̄`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Si

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## `ω̄` in closed form -/

/-- The exponent of `ω̄_γ`: `γ + 1` if the limit part `ω·(γ/ω)` of `γ` is an `ε`-number, else `γ`. -/
noncomputable def siExp (γ : Ordinal.{0}) : Ordinal.{0} :=
  open Classical in if InE (ω * (γ / ω)) then γ + 1 else γ

theorem si_nat_lt_omega {j : Ordinal.{0}} (hj : j < ω) : j + 1 < ω := by
  obtain ⟨m, rfl⟩ := lt_omega0.1 hj
  exact_mod_cast natCast_lt_omega0 (m + 1)

/-- `(γ + 1)/ω = γ/ω`. -/
theorem si_div_succ (γ : Ordinal.{0}) : (γ + 1) / ω = γ / ω := by
  have h := Ordinal.div_add_mod γ ω
  have hj : γ % ω < ω := Ordinal.mod_lt γ omega0_ne_zero
  have e : γ + 1 = ω * (γ / ω) + (γ % ω + 1) := by
    conv_lhs => rw [← h]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt (si_nat_lt_omega hj), add_zero]

/-- `(ω·q + j)/ω = q` for `j < ω`. -/
theorem si_div_eq {q j : Ordinal.{0}} (hj : j < ω) : (ω * q + j) / ω = q := by
  rw [Ordinal.mul_add_div _ omega0_ne_zero, Ordinal.div_eq_zero_of_lt hj, add_zero]

theorem si_inE_pos {e : Ordinal.{0}} (h : InE e) : 0 < e := by
  have h1 : (0 : Ordinal.{0}) < ω ^ e := opow_pos e omega0_pos
  have h2 : ω ^ e = e := h
  rwa [h2] at h1

/-- An `ε`-number is its own limit part. -/
theorem si_inE_limpart {e : Ordinal.{0}} (h : InE e) : ω * (e / ω) = e := by
  have h1 : (1 : Ordinal.{0}) ≤ e := one_le_iff_ne_zero.2 (si_inE_pos h).ne'
  have hd : ω ∣ e := by
    have := Ordinal.opow_dvd_opow ω h1
    rw [opow_one] at this
    have h2 : ω ^ e = e := h
    rwa [h2] at this
  have hm : e % ω = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hd
  have := Ordinal.div_add_mod e ω
  rwa [hm, add_zero] at this

theorem siExp_le (γ : Ordinal.{0}) : siExp γ ≤ γ + 1 := by
  unfold siExp; split_ifs
  · exact le_rfl
  · exact (lt_add_one γ).le

theorem le_siExp (γ : Ordinal.{0}) : γ ≤ siExp γ := by
  unfold siExp; split_ifs
  · exact (lt_add_one γ).le
  · exact le_rfl

theorem siExp_strictMono : StrictMono siExp := by
  intro γ δ h
  have h1 : siExp γ ≤ δ := (siExp_le γ).trans (add_one_le_of_lt h)
  rcases h1.lt_or_eq with h2 | h2
  · exact h2.trans_le (le_siExp δ)
  · have hγ : siExp γ = γ + 1 := by
      unfold siExp at h2 ⊢
      split_ifs with hc
      · rfl
      · rw [if_neg hc] at h2; exact absurd h2 h.ne
    have hP : InE (ω * (γ / ω)) := by
      by_contra hc; unfold siExp at hγ; rw [if_neg hc] at hγ
      exact absurd hγ (lt_add_one γ).ne
    have hδ : δ = γ + 1 := by rw [← h2, hγ]
    have hPδ : InE (ω * (δ / ω)) := by rw [hδ, si_div_succ]; exact hP
    have hsδ : siExp δ = δ + 1 := by unfold siExp; rw [if_pos hPδ]
    rw [h2, hsδ]; exact lt_add_one δ

/-- **`ω̄_γ = ω^{siExp γ}`.** -/
theorem si_wbar_eq : wbar = fun γ => ω ^ siExp γ := by
  unfold wbar
  refine (eq_enumOrd _ nonEAP_unbounded).2 ⟨fun a b h => ?_, ?_⟩
  · exact (opow_lt_opow_iff_right one_lt_omega0).2 (siExp_strictMono h)
  · ext w
    constructor
    · rintro ⟨γ, rfl⟩
      show ω ^ siExp γ ∈ NonEAP
      unfold siExp
      split_ifs with hc
      · exact opow_succ_mem γ
      · refine ⟨indec_opow _, fun hE => hc ?_⟩
        rw [inE_opow_iff] at hE
        rw [si_inE_limpart hE]; exact hE
    · intro hw
      obtain ⟨c, rfl⟩ := indec_eq_opow hw.1
      have hcE : ¬ InE c := fun h => hw.2 ((inE_opow_iff c).2 h)
      by_cases hsucc : ∃ γ, c = γ + 1 ∧ InE (ω * (γ / ω))
      · obtain ⟨γ, rfl, hP⟩ := hsucc
        exact ⟨γ, by show ω ^ siExp γ = _; unfold siExp; rw [if_pos hP]⟩
      · refine ⟨c, ?_⟩
        show ω ^ siExp c = _
        unfold siExp
        rw [if_neg]
        intro hP
        have hdec := Ordinal.div_add_mod c ω
        have hj : c % ω < ω := Ordinal.mod_lt c omega0_ne_zero
        obtain ⟨m, hm⟩ := lt_omega0.1 hj
        rcases m with _ | m
        · rw [hm, Nat.cast_zero, add_zero] at hdec
          exact hcE (by rw [← hdec]; exact hP)
        · refine hsucc ⟨ω * (c / ω) + m, ?_, ?_⟩
          · conv_lhs => rw [← hdec]
            rw [hm]; push_cast; rw [add_assoc]
          · rw [si_div_eq (natCast_lt_omega0 m)]; exact hP

/-! ## `B_n` and `ω̄` -/

theorem si_L_E : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC (Lw.lw_L_SC S ω)

theorem si_opow_lt_L {a : Ordinal.{0}} (ha : a < Nc.ncL S ω) : ω ^ a < Nc.ncL S ω := by
  have h : ω ^ a < ω ^ Nc.ncL S ω := (opow_lt_opow_iff_right one_lt_omega0).2 ha
  have hE : ω ^ Nc.ncL S ω = Nc.ncL S ω := si_L_E
  rwa [hE] at h

theorem si_add_lt_L {a b : Ordinal.{0}} (ha : a < Nc.ncL S ω) (hb : b < Nc.ncL S ω) : a + b < Nc.ncL S ω :=
  (Lq.lq_SC_indec (Lw.lw_L_SC S ω)).add_lt ha hb

theorem si_one_lt_L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S

/-- **`B_n(ω·q) = ω·B_n q`** for `ω·q < L(ω)`. -/
theorem siB_omul {n : ℕ} : ∀ q, ω * q < Nc.ncL S ω → Bc.bcB S n (ω * q) = ω * Bc.bcB S n q := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero, Bc.bcB_zero, mul_zero]
  set g := log ω q with hg
  have hwg : ω ^ g ≤ q := opow_log_le_self ω hq0
  set r := q - ω ^ g with hr
  have hqr : ω ^ g + r = q := Ordinal.add_sub_cancel_of_le hwg
  have hrq : r < q := Ph.ph_sub_log_lt hq0
  have hqL : q < Nc.ncL S ω := (Ordinal.le_mul_right q omega0_pos).trans_lt hq
  have hwgL : ω ^ g < Nc.ncL S ω := hwg.trans_lt hqL
  have hgL : g < Nc.ncL S ω := (right_le_opow g one_lt_omega0).trans_lt hwgL
  have hrL : r < Nc.ncL S ω := hrq.trans hqL
  have hsplit : ω * q = ω ^ (1 + g) + ω * r := by
    rw [← hqr, mul_add, opow_add, opow_one]
  have h1 : ω ^ (1 + g) ≤ ω * q := by rw [hsplit]; exact le_self_add
  have h2 : ω * r ≤ ω * q := by rw [hsplit]; exact le_add_self
  have h1L : ω ^ (1 + g) < Nc.ncL S ω := h1.trans_lt hq
  have h2L : ω * r < Nc.ncL S ω := h2.trans_lt hq
  have h1gL : 1 + g < Nc.ncL S ω := si_add_lt_L si_one_lt_L hgL
  rw [hsplit, Bc.bcB_add h1L h2L, IH r hrq h2L, Tp.tpOpowB h1L, Bc.bcB_add si_one_lt_L hgL, Mw.mwB_one,
    ← hqr, Bc.bcB_add hwgL hrL, Tp.tpOpowB hwgL, mul_add, opow_add, opow_one]

/-- **`B_n` keeps and reflects `ε`-numbers below `L(ω)`.** -/
theorem siB_E_iff {n : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ω) : InE (Bc.bcB S n x) ↔ InE x := by
  refine ⟨fun h => ?_, fun h => Se.seB_E h hx⟩
  have hwL := si_opow_lt_L hx
  have e : Bc.bcB S n (ω ^ x) = Bc.bcB S n x := by rw [Tp.tpOpowB hwL]; exact h
  rcases lt_trichotomy (ω ^ x) x with hlt | heq | hgt
  · exact absurd e ((Bc.bcB_lt_iff hwL hx).2 hlt).ne
  · exact heq
  · exact absurd e ((Bc.bcB_lt_iff hx hwL).2 hgt).ne'

/-- `B_n γ = ω·B_n(γ/ω) + γ % ω` and the limit part moves: `ω·(B_n γ/ω) = B_n(ω·(γ/ω))`. -/
theorem siB_limpart {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < Nc.ncL S ω) :
    ω * (Bc.bcB S n γ / ω) = Bc.bcB S n (ω * (γ / ω)) ∧ ω * (γ / ω) < Nc.ncL S ω := by
  have hdec := Ordinal.div_add_mod γ ω
  have hj : γ % ω < ω := Ordinal.mod_lt γ omega0_ne_zero
  have hqL : ω * (γ / ω) < Nc.ncL S ω := (le_self_add.trans hdec.le).trans_lt hγ
  have hjL : γ % ω < Nc.ncL S ω := hj.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  obtain ⟨m, hm⟩ := lt_omega0.1 hj
  have hBj : Bc.bcB S n (γ % ω) = γ % ω := by rw [hm]; exact Mw.mwB_nat n m
  have hBγ : Bc.bcB S n γ = ω * Bc.bcB S n (γ / ω) + γ % ω := by
    conv_lhs => rw [← hdec]
    rw [Bc.bcB_add hqL hjL, siB_omul _ hqL, hBj]
  refine ⟨?_, hqL⟩
  rw [hBγ, si_div_eq hj, siB_omul _ hqL]

/-- **`B_n(siExp γ) = siExp(B_n γ)`** for `γ < L(ω)`. -/
theorem siB_exp {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < Nc.ncL S ω) :
    Bc.bcB S n (siExp γ) = siExp (Bc.bcB S n γ) := by
  obtain ⟨hlp, hqL⟩ := siB_limpart (n := n) hγ
  have hP : InE (ω * (Bc.bcB S n γ / ω)) ↔ InE (ω * (γ / ω)) := by rw [hlp]; exact siB_E_iff hqL
  unfold siExp
  by_cases h : InE (ω * (γ / ω))
  · rw [if_pos h, if_pos (hP.2 h), Bc.bcB_add hγ si_one_lt_L, Mw.mwB_one]
  · rw [if_neg h, if_neg (fun h' => h (hP.1 h'))]

/-- **`B_n(ω̄_γ) = ω̄_{B_n γ}`** for `γ < L(ω)`. -/
theorem siB_wbar {n : ℕ} {γ : Ordinal.{0}} (hγ : γ < Nc.ncL S ω) :
    Bc.bcB S n (wbar γ) = wbar (Bc.bcB S n γ) := by
  have hsL : siExp γ < Nc.ncL S ω := (siExp_le γ).trans_lt
    ((Lq.lq_SC_indec (Lw.lw_L_SC S ω)).add_lt hγ si_one_lt_L)
  rw [si_wbar_eq]
  show Bc.bcB S n (ω ^ siExp γ) = ω ^ siExp (Bc.bcB S n γ)
  rw [Tp.tpOpowB (si_opow_lt_L hsL), siB_exp hγ]

/-! ## `ϑ^β` at the countable arguments -/

/-- **`ϑ^τ(0) = τ`** ([W07b] Cor 5.10 gives `τ ∈ Tᵗ`; [W07a] Thm 3.23: `τ = ϑ^τ(ξ)`; Lemmas 4.2, 4.3: only `ξ = 0`
gives a value `≤ τ`). -/
theorem siVt_zero {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : vt τ 0 = τ := by
  obtain ⟨m, hτm, -, -, hT⟩ := T_inter_Om1 hτ hτ1
  have hτT : τ ∈ Tset τ := (hT τ hτ1).2 hτm
  obtain ⟨ξ, hξT, hξ2, hv⟩ := vt_rep hτ hτ1 hτT le_rfl hτ1 (inE_indec hτ)
  rcases lt_or_ge ξ Om1 with hξ1 | hξ1
  · rcases eq_or_ne ξ 0 with rfl | h0
    · exact hv
    · exfalso
      have h1 : 1 ≤ ξ := one_le_iff_ne_zero.2 h0
      have he : 1 + (ξ - 1) = ξ := Ordinal.add_sub_cancel_of_le h1
      have hα : ξ - 1 < Om1 := (Ordinal.sub_le_self ξ 1).trans_lt hξ1
      have := vt_wbar hτ hτ1 hα
      rw [he, hv] at this
      have h2 : τ + (ξ - 1) < wbar (τ + (ξ - 1)) := Se.se_wbar_gt _
      rw [← this] at h2
      exact absurd (le_self_add.trans_lt h2) (lt_irrefl τ)
  · exact absurd hv ((vt_E_iff hτ hτ1 hξT hξ2).2 hξ1).1.ne'

/-- **`B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` for every `ε`-number `β < c_{n+1}` and every `η < c_{n+1}`.** -/
theorem siVtHomC {n : ℕ} {β η : Ordinal.{0}} (hβ : InE β) (hβc : β < Bc.bcC S (n + 1))
    (hηc : η < Bc.bcC S (n + 1)) : Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η) := by
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hβL : β < Nc.ncL S ω := hβc.trans hLc
  have hηL : η < Nc.ncL S ω := hηc.trans hLc
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hβ'E : InE (Bc.bcB S n β) := Se.seB_E hβ hβL
  have hβ'1 : Bc.bcB S n β < Om1 := (Rt.rt_lt_Om1 hβc).2
  rcases eq_or_ne η 0 with rfl | h0
  · rw [siVt_zero hβ hβ1, Bc.bcB_zero, siVt_zero hβ'E hβ'1]
  · have h1 : 1 ≤ η := one_le_iff_ne_zero.2 h0
    have he : 1 + (η - 1) = η := Ordinal.add_sub_cancel_of_le h1
    have hαη : η - 1 ≤ η := Ordinal.sub_le_self η 1
    have hαc : η - 1 < Bc.bcC S (n + 1) := hαη.trans_lt hηc
    have hαL : η - 1 < Nc.ncL S ω := hαη.trans_lt hηL
    have hα1 : η - 1 < Om1 := (Rt.rt_lt_Om1 hαc).1
    have hBα1 : Bc.bcB S n (η - 1) < Om1 := (Rt.rt_lt_Om1 hαc).2
    rw [← he, vt_wbar hβ hβ1 hα1, siB_wbar (si_add_lt_L hβL hαL), Bc.bcB_add hβL hαL,
      Bc.bcB_add si_one_lt_L hαL, Mw.mwB_one, vt_wbar hβ'E hβ'1 hBα1]

end Googology.Trans.PoR.InaccPsi.R2.Si
