import Googology.Trans.PoR.InaccPsi.R2.TbCode

/-!
# The codes below `ε_{Γ_{Ω₁+1}+1}` as an offset code system: realizers up to `υ_{a+ε_{Γ_{a+1}+1}}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The codes of `R2.TbCode` (`Γ_{Ω₁+1}·γ + c'` of `R2.GmQ0` below `Γ_{Ω₁+1}²`, `ω^e·n + r` above) satisfy every field of
`Tb.TbCS` with the bound `V(x) = ε_{Γ_{x+1}+1}`:

* `tbR_opow` (the code `ω^e` reads `ω^{e(x)}`), `tbR_pi` (**Lemma EXACT for every code**: `ω^{e(ρ)}` by
  `Tb.tbOpow_pi`, `·n` by `pi_mul_nat`, `+` by `pi_add`), `tbR_ld` (**Lemma EXACT for the last exponent of every
  limit code**), `tbR_mem` (**every code with gate below `b` lies in every hull `Cl(a, b)` with `0 < a`**, also as
  `ω^e·c`), `tbB_le` (`ε_{Γ_{Ω₁+1}+1} ≤ θ_{k+1}`), `tbV_le` (**`ε_{Γ_{x+1}+1}` is at most every `υ`-point above
  `x`**: `Γ_{x+1} ∈ Tˣ` and `Tˣ ∩ Ω₁` is the least `<₁ ∞` point above `x`, [W07b] Cor 5.10);
* `tbRr` (the reading, with a stand-in `c` at the bases `x ≥ Ω₁`), `tbEc : TbCS` (**the offset code system with
  `V(x) = ε_{Γ_{x+1}+1}`**);
* `tbEcReal_M`, `tbEcReal_L` (**`LrReal S a υ_{a+ε_{Γ_{a+1}+1}}` at `m*` and every `L(n+1)`**), `tbEcShort_L`,
  `tbEcShort_M`, `tbEcRoad`, `tbEcCL_iff_noUncov`, `tbEcM_iff_noUncov`;
* `tbEc_gt_G` (`υ_{a+Γ_{a+1}} < υ_{a+ε_{Γ_{a+1}+1}}`), `tbGap_of_gapG` (the gaps above `υ_{a+Γ_{a+1}}` give those
  above `υ_{a+ε_{Γ_{a+1}+1}}`).

No new axiom.  New definitions: `tbRr`, `tbEc`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

/-- The code `ω^e` (`e ≥ Γ_{Ω₁+1}·2`) reads `ω^{e(x)}`, with the gate of `e`. -/
theorem tbR_opow {e : Ordinal.{0}} (he : gcG 0 + gcG 0 ≤ e) (heB : e < tbB) (x : Ordinal.{0}) :
    ω ^ e < tbB ∧ tbR (ω ^ e) x = ω ^ tbR e x ∧ tbG (ω ^ e) = tbG e := by
  have hp := opow_pos e omega0_pos
  have e1 : ω ^ e = ω ^ e * 1 + 0 := by rw [mul_one, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (tb_mk he heB one_pos one_lt_omega0 hp).2.1
  · rw [e1, tbR_mk he heB one_pos one_lt_omega0 hp, tbR_zero, mul_one, add_zero]
  · rw [e1, tbG_mk he heB one_pos one_lt_omega0 hp, tbG_zero, max_eq_left zero_le]

theorem tb_two_le_omega {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : lgG x + ω ≤ lgG x * 2 := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]
  exact add_le_add_right (omega0_lt_inE (lgG_facts hx hx1).2.2.2.1).le _

/-- `c(x) < ω^{e(x)}` for the rest `c mod ω^e` of a code `c ≥ Γ_{Ω₁+1}²`. -/
theorem tbR_rest {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : mqB ≤ c) (h2 : c < tbB)
    (hg : tbG c < x) : tbR (c % ω ^ log ω c) x < ω ^ tbR (log ω c) x := by
  obtain ⟨he2, hec, -, -, hr, -, -⟩ := tb_parts h1 h2
  rw [tbG_hi h1 h2] at hg
  obtain ⟨o1, o2, o3⟩ := tbR_opow he2 (hec.trans h2) x
  rw [← o2]
  exact tbR_mono hx hx1 o1 hr (lt_of_le_of_lt (le_max_right _ _) hg)
    (by rw [o3]; exact lt_of_le_of_lt (le_max_left _ _) hg)

/-! ## Lemma EXACT -/

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for every code below `ε_{Γ_{Ω₁+1}+1}`** at every pair of bases above its gate. -/
theorem tbR_pi : ∀ c, c < tbB → tbG c < σ → tbR c ρ ∈ TB ρ σ ∧ pi σ ρ (tbR c ρ) = tbR c σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c mqB with hQ | hQ
  · rw [tbR_low hQ, tbR_low hQ]
    rw [tbG_low hQ] at hg
    exact mqR_pi hB hQ hg
  obtain ⟨he2, hec, hn, -, -, hrc, -⟩ := tb_parts hQ hc
  have hg' := hg
  rw [tbG_hi hQ hc] at hg'
  have hge : tbG (log ω c) < σ := lt_of_le_of_lt (le_max_left _ _) hg'
  have hgr : tbG (c % ω ^ log ω c) < σ := lt_of_le_of_lt (le_max_right _ _) hg'
  have heB : log ω c < tbB := hec.trans hc
  obtain ⟨hET, hEpi⟩ := IH _ hec heB hge
  obtain ⟨hrT, hrpi⟩ := IH _ hrc (hrc.trans hc) hgr
  rw [tbR_hi hQ hc ρ, tbR_hi hQ hc σ]
  have hgeρ := hge.trans hB.2.2.1
  obtain ⟨hpT, hppi⟩ := tbOpow_pi hB hET
    ((tb_two_le_omega hB.2.1 hρ1).trans (tbR_two hB.2.1 hρ1 he2 heB hgeρ))
    (tbR_lt hB.2.1 hρ1 _ heB hgeρ)
    (by rw [hEpi]; exact (tb_two_le_omega hB.1 hσ1).trans (tbR_two hB.1 hσ1 he2 heB hge))
    (by rw [hEpi]; exact tbR_lt hB.1 hσ1 _ heB hge)
  rw [hEpi] at hppi
  obtain ⟨k, hk⟩ := lt_omega0.1 hn
  rw [hk]
  obtain ⟨hmT, hmpi⟩ := pi_mul_nat hB hpT hppi k
  obtain ⟨hsT, hspi⟩ := pi_add hB hmT hrT
  exact ⟨hsT, by rw [hspi, hmpi, hrpi]⟩

/-- **Lemma EXACT for the last exponent of every limit code below `ε_{Γ_{Ω₁+1}+1}`.** -/
theorem tbR_ld : ∀ c, IsSuccLimit c → c < tbB → tbG c < σ →
    cdExp (tbR c ρ) ∈ TB ρ σ ∧ pi σ ρ (cdExp (tbR c ρ)) = cdExp (tbR c σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc hg
  rcases lt_or_ge c mqB with hQ | hQ
  · rw [tbR_low hQ, tbR_low hQ]
    rw [tbG_low hQ] at hg
    exact tbMq_ld hB hl hQ hg
  obtain ⟨he2, hec, hn, hn0, hr, hrc, hdec⟩ := tb_parts hQ hc
  have hg' := hg
  rw [tbG_hi hQ hc] at hg'
  have hge : tbG (log ω c) < σ := lt_of_le_of_lt (le_max_left _ _) hg'
  have hgr : tbG (c % ω ^ log ω c) < σ := lt_of_le_of_lt (le_max_right _ _) hg'
  have heB : log ω c < tbB := hec.trans hc
  rw [tbR_hi hQ hc ρ, tbR_hi hQ hc σ]
  rcases eq_or_ne (c % ω ^ log ω c) 0 with h0 | h0
  · rw [h0, tbR_zero, tbR_zero, add_zero, add_zero, tbExp_opow_mul hn0 hn, tbExp_opow_mul hn0 hn]
    exact tbR_pi hB _ heB hge
  · -- the rest is a limit code; the last exponent is that of the rest
    have hlr : IsSuccLimit (c % ω ^ log ω c) := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit (c % ω ^ log ω c) with h | ⟨d, hd⟩ | hlim
      · exact absurd h h0
      · exfalso
        have hd' : c % ω ^ log ω c = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
        have e2 : ω ^ log ω c * (c / ω ^ log ω c) + d + 1 = c := by rw [add_assoc, ← hd', hdec]
        have hlt : ω ^ log ω c * (c / ω ^ log ω c) + d < c := by
          calc _ < ω ^ log ω c * (c / ω ^ log ω c) + d + 1 := lt_add_one _
            _ = c := e2
        have := hl.succ_lt hlt
        rw [succ_eq_add_one, e2] at this
        exact lt_irrefl _ this
      · exact hlim
    have hexp : ∀ y, InE y → y < Om1 → tbG c < y →
        cdExp (ω ^ tbR (log ω c) y * (c / ω ^ log ω c) + tbR (c % ω ^ log ω c) y) =
          cdExp (tbR (c % ω ^ log ω c) y) := by
      intro y hy hy1 hgy
      have hgy' := hgy
      rw [tbG_hi hQ hc] at hgy'
      have hz0 : tbR (c % ω ^ log ω c) y ≠ 0 := by
        have := tbR_mono hy hy1 (hrc.trans hc) (pos_iff_ne_zero.2 h0) (by rw [tbG_zero]; exact hy.pos)
          (lt_of_le_of_lt (le_max_right _ _) hgy')
        rw [tbR_zero] at this; exact this.ne'
      have hzE := tbR_rest hy hy1 hQ hc hgy
      refine tbExp_add hz0 ((opow_dvd_opow ω ?_).trans (dvd_mul_right _ _))
      exact Order.add_one_le_of_lt (tbExp_lt hz0 hzE)
    rw [hexp ρ hB.2.1 hρ1 (hg.trans hB.2.2.1), hexp σ hB.1 hσ1 hg]
    exact IH _ hrc hlr (hrc.trans hc) hgr

end Pi

/-! ## Hull membership -/

theorem tb_opow_nat_mem {S : InaccSeq.{0}} {a b E : Ordinal.{0}} (hE : E ∈ S.CSet a b) :
    ∀ k : ℕ, ω ^ E * (k : Ordinal.{0}) ∈ S.CSet a b := by
  have hω : ω ^ E ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem a b) hE
    rwa [veblen_zero_apply] at this
  intro k
  induction k with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem _ _
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hω

/-- **Every code with gate below `b` lies in every hull `Cl(a, b)` with `0 < a`, also as `ω^e·c`.** -/
theorem tbR_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) :
    ∀ c, c < tbB → tbG c < b → ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg e' he'
  rcases lt_or_ge c mqB with hQ | hQ
  · rw [tbG_low hQ] at hg
    obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hQ
    rw [mqG_split γ hc'] at hg
    have hgc' : glG c' < b := lt_of_le_of_lt (le_max_right _ _) hg
    have h2 := (gl_mem (S := S) (a := a) (b := b) c' hc' hgc').2 e' he'
    have hG : e' + gcG 0 ∈ S.CSet a b := CSet.add_mem he' (gmS_G0_mem S ha)
    have e1 : ω ^ e' * (gcG 0 * γ + c') = ω ^ (e' + gcG 0) * γ + ω ^ e' * c' := by
      rw [mul_add, ← mul_assoc, opow_add, gl_G0_E]
    rw [e1]
    refine CSet.add_mem ?_ h2
    rcases lt_or_ge γ ω with hω | hω
    · obtain ⟨k, rfl⟩ := lt_omega0.1 hω
      exact tb_opow_nat_mem hG k
    · have hgγ : glG γ < b := by
        have := lt_of_le_of_lt (le_max_left _ _) hg; rwa [mq_glQ_inf hω] at this
      exact (gl_mem (S := S) (a := a) (b := b) γ hγ hgγ).2 _ hG
  · obtain ⟨-, hec, hn, -, -, hrc, hdec⟩ := tb_parts hQ hc
    rw [tbG_hi hQ hc] at hg
    have hge : tbG (log ω c) < b := lt_of_le_of_lt (le_max_left _ _) hg
    have hgr : tbG (c % ω ^ log ω c) < b := lt_of_le_of_lt (le_max_right _ _) hg
    have heM : log ω c ∈ S.CSet a b := by
      have := IH _ hec (hec.trans hc) hge 0 (CSet.zero_mem a b)
      rwa [opow_zero, one_mul] at this
    have hrM := IH _ hrc (hrc.trans hc) hgr e' he'
    obtain ⟨k, hk⟩ := lt_omega0.1 hn
    have e1 : ω ^ e' * c = ω ^ (e' + log ω c) * (k : Ordinal.{0}) + ω ^ e' * (c % ω ^ log ω c) := by
      conv_lhs => rw [← hdec]
      rw [hk, mul_add, ← mul_assoc, ← opow_add]
    rw [e1]
    exact CSet.add_mem (tb_opow_nat_mem (CSet.add_mem he' heM) k) hrM

/-! ## The bounds -/

theorem tb_G0_lt_th (S : InaccSeq.{0}) (k : ℕ) : gcG 0 < Lc.lcTh S (k + 1) := by
  have hG := gmS_psi S 0 zero_le
  rcases k with _ | k
  · have h1 : Lc.lcTh S (0 + 1) = S.psi (Om ω) (Om (1 + 1)) := by
      rw [zero_add, Lc.lcTh_one]; rfl
    rw [h1, ← hG]
    exact psi_lt_psi (InR_Om_succ 1) (Om_pos omega0_ne_zero) (CSet.zero_mem _ _)
  · have h1 : gcG 0 < Om (1 + 1 : Ordinal.{0}) := by rw [← hG]; exact psi_lt (InR_Om_succ 1) 0
    have h2 : Om (1 + 1 : Ordinal.{0}) ≤ Om (((k + 1 + 1 : ℕ) : Ordinal.{0})) := by
      refine Om_le_Om.2 ?_
      rw [one_add_one_eq_two]
      exact_mod_cast (by omega : 2 ≤ k + 1 + 1)
    exact h1.trans_le (h2.trans (psiS_bounds (S := S) (Om ω) (((k + 1 + 1 : ℕ) : Ordinal.{0}))).1.le)

/-- `ε_{Γ_{Ω₁+1}+1} ≤ θ_{k+1}`. -/
theorem tbB_le (S : InaccSeq.{0}) (k : ℕ) : tbB ≤ Lc.lcTh S (k + 1) :=
  eN_le (tb_G0_lt_th S k) (Ls.lsTh_opow (S := S) (k + 1))

/-- **`ε_{Γ_{x+1}+1}` is at most every `υ`-point above `x`** ([W07b] Cor 5.10 through `T_next`). -/
theorem tbV_le {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    eN (lgG x) ≤ u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  exact eN_le (((hTm _ hG1).1 hGT).trans_le (hmin u hxu hu.2)) (upsPt_inE hu)

/-! ## The offset code system -/

/-- **The reading**: `tbR` at the bases `x < Ω₁`, the code itself at `x ≥ Ω₁` (where nothing is read). -/
noncomputable def tbRr (c x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if x < Om1 then tbR c x else c

theorem tbRr_eq {c x : Ordinal.{0}} (hx1 : x < Om1) : tbRr c x = tbR c x := by unfold tbRr; rw [if_pos hx1]

theorem tbRr_hi {c x : Ordinal.{0}} (hx1 : Om1 ≤ x) : tbRr c x = c := by
  unfold tbRr; rw [if_neg (not_lt.2 hx1)]

/-- **The offset code system of the codes below `ε_{Γ_{Ω₁+1}+1}`**, readings below `V(x) = ε_{Γ_{x+1}+1}`. -/
noncomputable def tbEc : TbCS where
  R := tbRr
  G := tbG
  B := tbB
  V := fun x => eN (lgG x)
  B_lim := tbB_lim
  B_le := tbB_le
  zero_R := fun x => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [tbRr_eq hx1, tbR_zero]
    · rw [tbRr_hi hx1]
  zero_G := tbG_zero
  succ_R := fun b x hb => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [tbRr_eq hx1, tbRr_eq hx1, tbR_succ b x hb]
    · rw [tbRr_hi hx1, tbRr_hi hx1]
  succ_G := fun b Z hb hZ hg => tbG_succ b Z hb hZ hg
  R_mono := fun x b c hx hc hbc hgb hgc => by
    rcases lt_or_ge x Om1 with hx1 | hx1
    · rw [tbRr_eq hx1, tbRr_eq hx1]; exact tbR_mono hx hx1 hc hbc hgb hgc
    · rw [tbRr_hi hx1, tbRr_hi hx1]; exact hbc
  R_lt := fun x c hx hx1 hc hg => by rw [tbRr_eq hx1]; exact tbR_lt hx hx1 c hc hg
  R_ex := fun x ν hx hx1 hν => by
    obtain ⟨c, h1, h2, h3⟩ := tbR_ex hx hx1 ν hν
    exact ⟨c, h1, h2, by rw [tbRr_eq hx1]; exact h3⟩
  R_pi := fun σ ρ c hB hc hg => by
    rw [tbRr_eq hB.2.2.2, tbRr_eq (hB.2.2.1.trans hB.2.2.2)]; exact tbR_pi hB c hc hg
  R_ld := fun σ ρ c hB hl hc hg => by
    rw [tbRr_eq hB.2.2.2, tbRr_eq (hB.2.2.1.trans hB.2.2.2)]; exact tbR_ld hB c hl hc hg
  R_mem := fun _ _ _ c ha hc hg e he => tbR_mem ha c hc hg e he
  V_E := fun x _ _ => eN_E _
  V_gt := fun x hx hx1 => (lgG_facts hx hx1).2.1.trans (lt_eN _)
  V_le := fun _ _ hx hx1 hxu hu => tbV_le hx hx1 hxu hu

theorem tbEc_V : tbEc.V = fun x => eN (lgG x) := rfl

/-! ## The realizers and the road up to `υ_{a+ε_{Γ_{a+1}+1}}` -/

variable {S : InaccSeq.{0}}

/-- **The new bound is strictly larger**: `υ_{a+Γ_{a+1}} < υ_{a+ε_{Γ_{a+1}+1}}`. -/
theorem tbEc_gt_G {a : Ordinal.{0}} : upsilon (a + lgG a) < upsilon (a + eN (lgG a)) :=
  upsilon_normal.strictMono ((add_lt_add_iff_left a).2 (lt_eN _))

/-- **The gaps above `υ_{a+Γ_{a+1}}` give the gaps above `υ_{a+ε_{Γ_{a+1}+1}}`.** -/
theorem tbGap_of_gapG {a b : Ordinal.{0}} (h : LrGap S a b (upsilon (a + lgG a))) :
    LrGap S a b (upsilon (a + eN (lgG a))) :=
  Ls.lsGap_mono (upsilon_normal.strictMono.monotone (add_le_add le_rfl (lt_eN _).le)) h

/-- **The realizers at `m*` up to `υ_{m*+ε_{Γ_{m*+1}+1}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem tbEcReal_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) ∧
      upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0))) < Nc.ncL S 1 :=
  tbReal_M tbEc hlow hU hL hstd

/-- **The realizers at `L(n+1)` up to `υ_{a+ε_{Γ_{a+1}+1}} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem tbEcReal_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) :=
  tbReal_L tbEc hlow hU hL hstd n

/-- **`L(n+1) ≤₁ υ_{a+ε_{Γ_{a+1}+1}}`** from UPPER, CapV, LOWER. -/
theorem tbEcShort_L (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :=
  tbShort_L tbEc hU hV hVt hL n

/-- **`m* ≤₁ υ_{m*+ε_{Γ_{m*+1}+1}}`** from UPPER, CapV, LOWER. -/
theorem tbEcShort_M (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))) :=
  tbShort_M tbEc hU hV hVt hL

/-- **The road with the gaps asked only above `υ_{a+ε_{Γ_{a+1}+1}}`** (at `m*` and every `L(n+1)`). -/
theorem tbEcRoad (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S) (hmove : Cx.CxStdMoveTop S)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0)))))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))))) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tbRoad tbEc hU hO hL hV hVt hEQ htop hmove h0 hn

/-- **(CL) at `n` iff no uncovered reach of `L(n+1)` in `[υ_{a+ε_{Γ_{a+1}+1}}, L(n+2))`** (UPPER, CapV, LOWER). -/
theorem tbEcCL_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (n : ℕ) :
    le1 (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) r ∧
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (lgG (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) ≤ r ∧
        r < Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
        ∀ l, CdRange S l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ upsilon l → upsilon l ≤ r →
          cdR S l ≤ r :=
  tbCL_iff_noUncov tbEc hU hV hVt hL n

/-- **`m* ≤₁ L(1)` iff no uncovered reach of `m*` in `[υ_{m*+ε_{Γ_{m*+1}+1}}, L(1))`** (UPPER, CapV, LOWER). -/
theorem tbEcM_iff_noUncov (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    le1 (Nc.ncL S 0) (Nc.ncL S 1) ↔
      ¬ ∃ r, IsReach R2C (Nc.ncL S 0) r ∧ upsilon (Nc.ncL S 0 + eN (lgG (Nc.ncL S 0))) ≤ r ∧
        r < Nc.ncL S 1 ∧
        ∀ l, CdRange S l → Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ r → cdR S l ≤ r :=
  tbM_iff_noUncov tbEc hU hV hVt hL

end Googology.Trans.PoR.InaccPsi.R2.Tb
