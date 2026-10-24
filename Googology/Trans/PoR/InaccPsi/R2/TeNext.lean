import Googology.Trans.PoR.InaccPsi.R2.TeOrd

/-!
# The `ε`-step as an offset code system: `TeHyp K → Tb.TbCS` with top `ε_{V(x)+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

* `te_pi` (**Lemma EXACT for every code below `ε_{K.B+1}`**: `K.R_pi` below `K.B`, `TeHyp.Vpi` at `K.B`,
  `V·n + r` by `pi_mul_nat`, `pi_add`, `ω^{e(ρ)}·n + r` by `Te.te_opow_pi` with the pseudo-base `V`);
* `te_ld` (**Lemma EXACT for the last exponent of every limit code**), `te_mem` (**every code with gate below `b` lies
  in every hull `Cl(a, b)` with `0 < a`, also as `ω^e·c`**), `te_V_le` (**`ε_{V(x)+1}` is at most every `υ`-point
  above `x`**: `ε_{V(x)+1} ∈ Tˣ` and `Tˣ ∩ Ω₁` is the least `<₁ ∞` point above `x`, [W07b] Cor 5.10 via `T_next`);
* `teRr` (the reading, the code itself at `x ≥ Ω₁`), `teNext K h : Tb.TbCS` (**the step**: codes below `ε_{K.B+1}`,
  top `V'(x) = ε_{V(x)+1}`).

No new axiom.  New definitions: `teRr`, `teNext`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable (K : Tb.TbCS) (h : TeHyp K)

/-- `cdExp E = E` for an `ε`-number `E`. -/
theorem te_cdExp_E {E : Ordinal.{0}} (hE : InE E) : cdExp E = E := by
  have h1 := Tb.tbExp_opow_mul (E := E) one_pos one_lt_omega0
  have hE' : ω ^ E = E := hE
  rwa [mul_one, hE'] at h1

/-- `cdExp(V·n) = V` for an `ε`-number `V`, `0 < n < ω`. -/
theorem te_cdExp_mul {E n : Ordinal.{0}} (hE : InE E) (hn0 : 0 < n) (hn : n < ω) : cdExp (E * n) = E := by
  have h1 := Tb.tbExp_opow_mul (E := E) hn0 hn
  have hE' : ω ^ E = E := hE
  rwa [hE'] at h1

/-- A nonzero rest of a limit code is a limit. -/
theorem te_rest_lim {c q r : Ordinal.{0}} (hl : IsSuccLimit c) (hdec : q + r = c) (h0 : r ≠ 0) :
    IsSuccLimit r := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit r with h | ⟨d, hd⟩ | hlim
  · exact absurd h h0
  · exfalso
    have hd' : r = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    have e2 : q + d + 1 = c := by rw [add_assoc, ← hd', hdec]
    have hlt : q + d < c := by
      calc _ < q + d + 1 := lt_add_one _
        _ = c := e2
    have := hl.succ_lt hlt
    rw [succ_eq_add_one, e2] at this
    exact lt_irrefl _ this
  · exact hlim

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include h hB

/-- **Lemma EXACT for every code below `ε_{K.B+1}`** at every pair of bases above its gate. -/
theorem te_pi : ∀ c, c < eN K.B → teG K c < σ → teR K c ρ ∈ TB ρ σ ∧ pi σ ρ (teR K c ρ) = teR K c σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hBE := h.BE
  have hBe : ω ^ K.B = K.B := hBE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_trichotomy c K.B with hcB | rfl | hcB
  · rw [teR_low K hcB, teR_low K hcB]
    rw [teG_low K hcB] at hg
    exact K.R_pi σ ρ c hB hcB hg
  · rw [teR_B K, teR_B K]; exact h.Vpi σ ρ hB
  obtain ⟨heB', hec, hn, -, hr, hrc, -⟩ := te_parts K hBE hcB hc
  obtain ⟨k, hk⟩ := lt_omega0.1 hn
  by_cases heq : log ω c = K.B
  · rw [teR_hiB K hcB hc heq ρ, teR_hiB K hcB hc heq σ, hk]
    rw [teG_hiB K hcB hc heq] at hg
    have hrB : c % ω ^ log ω c < K.B := by rw [heq, hBe] at hr ⊢; exact hr
    obtain ⟨hmT, hmpi⟩ := pi_mul_nat hB (h.Vpi σ ρ hB).1 (h.Vpi σ ρ hB).2 k
    obtain ⟨hrT, hrpi⟩ := K.R_pi σ ρ _ hB hrB hg
    obtain ⟨hsT, hspi⟩ := pi_add hB hmT hrT
    exact ⟨hsT, by rw [hspi, hmpi, hrpi]⟩
  · have heB : K.B < log ω c := lt_of_le_of_ne heB' (Ne.symm heq)
    rw [teG_hi K hcB hc heq] at hg
    have hge : teG K (log ω c) < σ := lt_of_le_of_lt (le_max_left _ _) hg
    have hgr : teG K (c % ω ^ log ω c) < σ := lt_of_le_of_lt (le_max_right _ _) hg
    have heE : log ω c < eN K.B := hec.trans hc
    obtain ⟨hET, hEpi⟩ := IH _ hec heE hge
    obtain ⟨hrT, hrpi⟩ := IH _ hrc (hrc.trans hc) hgr
    rw [teR_hi K hcB hc heq ρ, teR_hi K hcB hc heq σ, hk]
    have hgeρ := hge.trans hB.2.2.1
    obtain ⟨hpT, hppi⟩ := te_opow_pi hB K.V_E K.V_gt (fun x hx hx1 => (h.VT x hx hx1).2) (h.Vpi σ ρ hB)
      (h.VNpi σ ρ hB) hET (te_V_lt K hBE hB.2.1 hρ1 heB heE hgeρ).le (teR_lt K hBE hB.2.1 hρ1 _ heE hgeρ)
    rw [hEpi] at hppi
    obtain ⟨hmT, hmpi⟩ := pi_mul_nat hB hpT hppi k
    obtain ⟨hsT, hspi⟩ := pi_add hB hmT hrT
    exact ⟨hsT, by rw [hspi, hmpi, hrpi]⟩

/-- **Lemma EXACT for the last exponent of every limit code below `ε_{K.B+1}`.** -/
theorem te_ld : ∀ c, IsSuccLimit c → c < eN K.B → teG K c < σ →
    cdExp (teR K c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (teR K c ρ)) = cdExp (teR K c σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hBE := h.BE
  have hBe : ω ^ K.B = K.B := hBE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc hg
  rcases lt_trichotomy c K.B with hcB | rfl | hcB
  · rw [teR_low K hcB, teR_low K hcB]
    rw [teG_low K hcB] at hg
    exact K.R_ld σ ρ c hB hl hcB hg
  · rw [teR_B K, teR_B K, te_cdExp_E (K.V_E ρ hB.2.1 hρ1), te_cdExp_E (K.V_E σ hB.1 hσ1)]
    exact h.Vpi σ ρ hB
  obtain ⟨heB', hec, hn, hn0, hr, hrc, hdec⟩ := te_parts K hBE hcB hc
  by_cases heq : log ω c = K.B
  · rw [teR_hiB K hcB hc heq ρ, teR_hiB K hcB hc heq σ]
    rw [teG_hiB K hcB hc heq] at hg
    have hrB : c % ω ^ log ω c < K.B := by rw [heq, hBe] at hr ⊢; exact hr
    rcases eq_or_ne (c % ω ^ log ω c) 0 with h0 | h0
    · rw [h0, K.zero_R, K.zero_R, add_zero, add_zero, te_cdExp_mul (K.V_E ρ hB.2.1 hρ1) hn0 hn,
        te_cdExp_mul (K.V_E σ hB.1 hσ1) hn0 hn]
      exact h.Vpi σ ρ hB
    · have hlr : IsSuccLimit (c % ω ^ log ω c) := te_rest_lim hl hdec h0
      have hexp : ∀ y, InE y → y < Om1 → K.G (c % ω ^ log ω c) < y →
          cdExp (K.V y * (c / ω ^ log ω c) + K.R (c % ω ^ log ω c) y) = cdExp (K.R (c % ω ^ log ω c) y) := by
        intro y hy hy1 hgy
        have hVE := K.V_E y hy hy1
        have hVe : ω ^ K.V y = K.V y := hVE
        have hz0 : K.R (c % ω ^ log ω c) y ≠ 0 := by
          have := K.R_mono y 0 _ hy hrB (pos_iff_ne_zero.2 h0) (by rw [K.zero_G]; exact hy.pos) hgy
          rw [K.zero_R] at this; exact this.ne'
        have hzE : K.R (c % ω ^ log ω c) y < ω ^ K.V y := by rw [hVe]; exact K.R_lt y _ hy hy1 hrB hgy
        refine Tb.tbExp_add hz0 ((opow_dvd_opow ω (Order.add_one_le_of_lt (Tb.tbExp_lt hz0 hzE))).trans ?_)
        rw [hVe]; exact dvd_mul_right _ _
      rw [hexp ρ hB.2.1 hρ1 (hg.trans hB.2.2.1), hexp σ hB.1 hσ1 hg]
      exact K.R_ld σ ρ _ hB hlr hrB hg
  · have heB : K.B < log ω c := lt_of_le_of_ne heB' (Ne.symm heq)
    have hg' := hg
    rw [teG_hi K hcB hc heq] at hg'
    have hge : teG K (log ω c) < σ := lt_of_le_of_lt (le_max_left _ _) hg'
    have hgr : teG K (c % ω ^ log ω c) < σ := lt_of_le_of_lt (le_max_right _ _) hg'
    have heE : log ω c < eN K.B := hec.trans hc
    rw [teR_hi K hcB hc heq ρ, teR_hi K hcB hc heq σ]
    rcases eq_or_ne (c % ω ^ log ω c) 0 with h0 | h0
    · rw [h0, teR_zero, teR_zero, add_zero, add_zero, Tb.tbExp_opow_mul hn0 hn, Tb.tbExp_opow_mul hn0 hn]
      exact te_pi K h hB _ heE hge
    · have hlr : IsSuccLimit (c % ω ^ log ω c) := te_rest_lim hl hdec h0
      have hexp : ∀ y, InE y → y < Om1 → teG K c < y →
          cdExp (ω ^ teR K (log ω c) y * (c / ω ^ log ω c) + teR K (c % ω ^ log ω c) y) =
            cdExp (teR K (c % ω ^ log ω c) y) := by
        intro y hy hy1 hgy
        have hgy' := hgy
        rw [teG_hi K hcB hc heq] at hgy'
        have hz0 : teR K (c % ω ^ log ω c) y ≠ 0 := by
          have := teR_mono K hBE hy hy1 (hrc.trans hc) (pos_iff_ne_zero.2 h0) (by rw [teG_zero]; exact hy.pos)
            (lt_of_le_of_lt (le_max_right _ _) hgy')
          rw [teR_zero] at this; exact this.ne'
        have hzE := teR_rest K hBE hy hy1 hcB hc heq hgy
        refine Tb.tbExp_add hz0 ((opow_dvd_opow ω ?_).trans (dvd_mul_right _ _))
        exact Order.add_one_le_of_lt (Tb.tbExp_lt hz0 hzE)
      rw [hexp ρ hB.2.1 hρ1 (hg.trans hB.2.2.1), hexp σ hB.1 hσ1 hg]
      exact IH _ hrc hlr (hrc.trans hc) hgr

end Pi

/-! ## Hull membership -/

include h in
/-- **Every code with gate below `b` lies in every hull `Cl(a, b)` with `0 < a`, also as `ω^e·c`.** -/
theorem te_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) :
    ∀ c, c < eN K.B → teG K c < b → ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  have hBE := h.BE
  have hBe : ω ^ K.B = K.B := hBE
  have hBM := h.Bmem S a b ha
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg e' he'
  rcases lt_trichotomy c K.B with hcB | rfl | hcB
  · rw [teG_low K hcB] at hg
    exact K.R_mem S a b c ha hcB hg e' he'
  · have e1 : ω ^ e' * K.B = ω ^ (e' + K.B) * ((1 : ℕ) : Ordinal.{0}) := by
      rw [Nat.cast_one, mul_one, opow_add, hBe]
    rw [e1]
    exact Tb.tb_opow_nat_mem (CSet.add_mem he' hBM) 1
  obtain ⟨-, hec, hn, -, -, hrc, hdec⟩ := te_parts K hBE hcB hc
  obtain ⟨k, hk⟩ := lt_omega0.1 hn
  by_cases heq : log ω c = K.B
  · rw [teG_hiB K hcB hc heq] at hg
    have hrB : c % ω ^ log ω c < K.B := by
      have := (te_parts K hBE hcB hc).2.2.2.2.1; rw [heq, hBe] at this ⊢; exact this
    have hrM := K.R_mem S a b _ ha hrB hg e' he'
    have e1 : ω ^ e' * c = ω ^ (e' + K.B) * (k : Ordinal.{0}) + ω ^ e' * (c % ω ^ log ω c) := by
      conv_lhs => rw [← hdec]
      rw [hk, mul_add, ← mul_assoc, ← opow_add, heq]
    rw [e1]
    exact CSet.add_mem (Tb.tb_opow_nat_mem (CSet.add_mem he' hBM) k) hrM
  · rw [teG_hi K hcB hc heq] at hg
    have hge : teG K (log ω c) < b := lt_of_le_of_lt (le_max_left _ _) hg
    have hgr : teG K (c % ω ^ log ω c) < b := lt_of_le_of_lt (le_max_right _ _) hg
    have heM : log ω c ∈ S.CSet a b := by
      have := IH _ hec (hec.trans hc) hge 0 (CSet.zero_mem a b)
      rwa [opow_zero, one_mul] at this
    have hrM := IH _ hrc (hrc.trans hc) hgr e' he'
    have e1 : ω ^ e' * c = ω ^ (e' + log ω c) * (k : Ordinal.{0}) + ω ^ e' * (c % ω ^ log ω c) := by
      conv_lhs => rw [← hdec]
      rw [hk, mul_add, ← mul_assoc, ← opow_add]
    rw [e1]
    exact CSet.add_mem (Tb.tb_opow_nat_mem (CSet.add_mem he' heM) k) hrM

include h in
/-- **`ε_{V(x)+1}` is at most every `υ`-point above `x`.** -/
theorem te_V_le {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    eN (K.V x) ≤ u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, h1⟩ := h.VT x hx hx1
  exact (((hTm _ h1).1 hT).trans_le (hmin u hxu hu.2)).le

/-! ## The step -/

/-- The reading of the step, with a stand-in `c` at the bases `x ≥ Ω₁`. -/
noncomputable def teRr (c x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if x < Om1 then teR K c x else c

theorem teRr_eq {c x : Ordinal.{0}} (hx1 : x < Om1) : teRr K c x = teR K c x := by
  unfold teRr; rw [if_pos hx1]

theorem teRr_hi {c x : Ordinal.{0}} (hx1 : Om1 ≤ x) : teRr K c x = c := by
  unfold teRr; rw [if_neg (not_lt.2 hx1)]

/-- **The `ε`-step**: from an offset code system `K` with `TeHyp K`, the codes below `ε_{K.B+1}` with the readings
`teR K` form an offset code system with top `V'(x) = ε_{V(x)+1}`. -/
noncomputable def teNext : Tb.TbCS where
  R := teRr K
  G := teG K
  B := eN K.B
  V := fun x => eN (K.V x)
  B_lim := ev_isSuccLimit_of_inE (eN_E _)
  B_le := h.Bth
  zero_R := fun x => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [teRr_eq K hx1, teR_zero]
    · rw [teRr_hi K hx1]
  zero_G := teG_zero K
  succ_R := fun b x hb => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [teRr_eq K hx1, teRr_eq K hx1, teR_succ K h.BE b x hb]
    · rw [teRr_hi K hx1, teRr_hi K hx1]
  succ_G := fun b Z hb hZ hg => teG_succ K h.BE b Z hb hZ hg
  R_mono := fun x b c hx hc hbc hgb hgc => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [teRr_eq K hx1, teRr_eq K hx1]; exact teR_mono K h.BE hx hx1 hc hbc hgb hgc
    · rw [teRr_hi K hx1, teRr_hi K hx1]; exact hbc
  R_lt := fun x c hx hx1 hc hg => by rw [teRr_eq K hx1]; exact teR_lt K h.BE hx hx1 c hc hg
  R_ex := fun x ν hx hx1 hν => by
    obtain ⟨c, h1, h2, h3⟩ := teR_ex K h.BE hx hx1 ν hν
    exact ⟨c, h1, h2, by rw [teRr_eq K hx1]; exact h3⟩
  R_pi := fun σ ρ c hB hc hg => by
    rw [teRr_eq K hB.2.2.2, teRr_eq K (hB.2.2.1.trans hB.2.2.2)]; exact te_pi K h hB c hc hg
  R_ld := fun σ ρ c hB hl hc hg => by
    rw [teRr_eq K hB.2.2.2, teRr_eq K (hB.2.2.1.trans hB.2.2.2)]; exact te_ld K h hB c hl hc hg
  R_mem := fun _ _ _ c ha hc hg e he => te_mem K h ha c hc hg e he
  V_E := fun _ _ _ => eN_E _
  V_gt := fun x hx hx1 => (K.V_gt x hx hx1).trans (lt_eN _)
  V_le := fun _ _ hx hx1 hxu hu => te_V_le K h hx hx1 hxu hu

theorem teNext_V : (teNext K h).V = fun x => eN (K.V x) := rfl

theorem teNext_B : (teNext K h).B = eN K.B := rfl

end Googology.Trans.PoR.InaccPsi.R2.Te
