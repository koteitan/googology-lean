import Googology.Trans.PoR.InaccPsi.R2.MvExp
import Googology.Trans.PoR.InaccPsi.R2.GgUni

/-!
# `SfEQlong` at the long codes below `ε_{Ω₁+1}`: the hull transport under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `η_λ` the name, `e = cdExp(η_λ)`, `m_λ` the code,
`Θ_λ(m)` the order type of the codes of `Cl(A_{η_λ}, ρ_λ)` below `m`, `r(λ) = k_λ(Θ_λ(m_λ))`.  `GgCl Z` are the
codes over `Z` (from `[0, Z)` and `Ω₁` by `+`, `φ`), `ggTh Z c` their order type below `c`, `ggE = ε_{Ω₁+1}`,
`ggGam` the least strongly critical ordinal above `Ω₁` (`R2.GgCl`).

* `mvHull_iff`, `mvTheta_eq`, `mvCode_mem` (**at every named restart**, not only at the fixed points of
  `R2.GgUni`): the hull below `ggGam` is `GgCl ρ_λ`, so `Θ_λ(m) = ggTh ρ_λ m` for `m ≤ ggGam`, and `e ∈ GgCl ρ_λ`
  when `e < ggGam`;
* `mvGg_move` (**the hull transport**, by induction on the code): for strongly critical countable `ρ, ρ'` with
  `B_n ρ = ρ'`, an `ε`-number `X` with `ρ < X < L(ω)`, and a code `x` over `ρ` below `ε_{Ω₁+1}`: `x ∈ MvD`,
  `B_n x` is a code over `ρ'` below `ε_{Ω₁+1}`, `ggTh ρ x < X`, and **`ggTh ρ' (B_n x) = B_n(ggTh ρ x)`**
  (cases `x < Ω₁`, `x = Ω₁`, `x = ω^a`, `x = ω^a + r`; `R2.GgOtp.ggTh_add`, `ggTh_opow`, `Mv.mvB_add`, `mvB_opow`);
* `mvEQlong_low` (**`B_n r(λ) = r(λ')` at every long code with `e < ε_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`):
  `m_λ = e`, `m_{λ'} = B_n e` (`Mv.mvExp_move`), `Θ_λ(m_λ) = ggTh ρ_λ e < δ_λ`,
  `Θ_{λ'}(m_{λ'}) = B_n(Θ_λ(m_λ))`, and `k_{λ'}(B_n p) = B_n(k_λ(p))` for `p < δ_λ` (`Mv.mvk_move`);
* `MvEQtop S` (a hypothesis name): `SfEQlong` at the long codes with `ε_{Ω₁+1} ≤ e`;
  `mvEQlong_top`: `L(ω+1) ≤ ν_C` and `MvEQtop` give `SfEQlong`;
* `mvRoad_top`: the road with `SfKMove` gone and `SfEQlong` replaced by `L(ω+1) ≤ ν_C → MvEQtop`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-! ## The hull below `ggGam` at a named restart -/

theorem mvUps_pos {l : Ordinal.{0}} (hl : IsRestartIdx l) : 0 < upsilon l :=
  (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)).1

/-- **At a named restart the hull below `ggGam` is the set of codes over `ρ_λ`.** -/
theorem mvHull_iff {l ηx x : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hx : x < ggGam) : x ∈ cdHull S l ↔ GgCl (upsilon l) x := by
  constructor
  · intro h
    exact ggCl_of_CSet (mvUps_pos hl) (ggKey hl hX) x h hx
  · intro h
    exact h.mem_CSet le_rfl

/-- **`Θ_λ(m) = ggTh ρ_λ m`** for `m ≤ ggGam` at a named restart. -/
theorem mvTheta_eq {l ηx m : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hm : m ≤ ggGam) : cdTheta S l m = ggTh (upsilon l) m :=
  ggOtp_congr m fun _ hx => mvHull_iff hl hX (hx.trans_le hm)

/-- **The last exponent of the name is a code over `ρ_λ`** (when below `ggGam`). -/
theorem mvCode_mem {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (he : cdExp (cdEta S l) < ggGam) : GgCl (upsilon l) (cdExp (cdEta S l)) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmem : cdExp (cdEta S l) ∈ cdHull S l := by
    unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  exact (mvHull_iff hl hX he).1 hmem

theorem mvNamed_SC {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx) :
    SC (upsilon l) ∧ upsilon l < Om 1 := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  rw [← hpv]
  exact ⟨Nm.Pv_SC S _, Nm.Pv_lt_Om1 S _⟩

/-! ## The hull transport -/

/-- **The hull transport under `B_n`** for the codes below `ε_{Ω₁+1}`. -/
theorem mvGg_move {k : ℕ} {ρ ρ' X : Ordinal.{0}} (hρ : SC ρ) (hρ1 : ρ < Om 1) (hρ' : SC ρ')
    (hρ'1 : ρ' < Om 1) (hB : Bc.bcB S k ρ = ρ') (hX : ω ^ X = X) (hρX : ρ < X)
    (hXL : X < Nc.ncL S ω) :
    ∀ x, GgCl ρ x → x < ggE → MvD S x ∧ GgCl ρ' (Bc.bcB S k x) ∧ Bc.bcB S k x < ggE ∧
      ggTh ρ x < X ∧ ggTh ρ' (Bc.bcB S k x) = Bc.bcB S k (ggTh ρ x) := by
  have hρL : ρ < Nc.ncL S ω := hρX.trans hXL
  have hXp := isPrincipal_add_omega0_opow X
  rw [hX] at hXp
  have hEp := isPrincipal_add_omega0_opow ggE
  rw [ggE_spec.1] at hEp
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 ha
    rwa [hX] at this
  have hEo : ∀ a < ggE, ω ^ a < ggE := fun a ha => by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 ha
    rwa [ggE_spec.1] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxE
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · -- a countable code: below `ρ`
    have hxρ : x < ρ := hx.lt_of_lt_Om1 hρ hx1
    have hxL : x < Nc.ncL S ω := hxρ.trans hρL
    have hBx : Bc.bcB S k x < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hxL hρL).2 hxρ
    refine ⟨mvD_of_lt hxL, GgCl.small hBx, hBx.trans (hρ'1.trans ggE_spec.2), ?_, ?_⟩
    · rw [ggTh_small hxρ.le]; exact hxρ.trans hρX
    · rw [ggTh_small hxρ.le, ggTh_small hBx.le]
  · -- `Ω₁`
    subst hx1
    obtain ⟨hD, hBO⟩ := mvB_Om1 (S := S) (k := k)
    refine ⟨hD, by rw [hBO]; exact GgCl.om, by rw [hBO]; exact ggE_spec.2, ?_, ?_⟩
    · rw [ggTh_Om1 hρ hρ1]; exact hρX
    · rw [hBO, ggTh_Om1 hρ hρ1, ggTh_Om1 hρ' hρ'1, hB]
  · -- `Ω₁ < x < ε_{Ω₁+1}`: not an ε-number
    have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    have hnE : ω ^ x ≠ x := fun h => absurd (ggE_le h hx1) (not_le.2 hxE)
    obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
    have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
    have hxlt : x < ω ^ a * ω := by
      rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
    have hga : GgCl ρ a := by rw [ha]; exact (ggDec hρ x hx).2
    have hgl : GgCl ρ (ω ^ a) := GgCl.opow hρ.1 hga
    have hgr : GgCl ρ (x - ω ^ a) := (ggDec hρ x hx).1 _ hgl hlead
    have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
    by_cases hr : x - ω ^ a = 0
    · -- `x = ω^a`
      have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
      have hax : a < x := by
        rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
        · rwa [hxa] at h
        · exfalso; apply hnE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
      obtain ⟨hDa, hga', haE, hta, hea⟩ := IH a hax hga (hax.trans hxE)
      have hne : ω ^ a ≠ a := fun h => hax.ne (h.symm.trans hxa)
      obtain ⟨hDx, hBx⟩ := mvB_opow (k := k) hDa hne
      subst hxa
      have hta' : ω ^ ggTh ρ a < X := hXo _ hta
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GgCl.opow hρ'.1 hga'
      · rw [hBx]; exact hEo _ haE
      · rw [ggTh_opow hρ hga]; exact hta'
      · rw [hBx, ggTh_opow hρ' hga', hea, ggTh_opow hρ hga, Tp.tpOpowB (hta'.trans hXL)]
    · -- `x = ω^a + r` with `0 < r < x`
      obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
      rw [← hr'] at hgr hdec hr
      have hlx : ω ^ a < x := by
        rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
      have hrx : r < x := by
        refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
        have h' : ω ^ a + x = x := by
          calc ω ^ a + x = ω ^ a + r := by rw [e]
            _ = x := hdec
        have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
        exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
      obtain ⟨hDl, hgl', hlE, htl, hel⟩ := IH _ hlx hgl (hlx.trans hxE)
      obtain ⟨hDr, hgr', hrE, htr, her⟩ := IH r hrx hgr (hrx.trans hxE)
      obtain ⟨hDx, hBx⟩ := mvB_add (k := k) hDl hDr
      have hts : ggTh ρ (ω ^ a + r) = ggTh ρ (ω ^ a) + ggTh ρ r := ggTh_add hρ hgl r
      rw [← hdec]
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GgCl.add hgl' hgr'
      · rw [hBx]; exact hEp hlE hrE
      · rw [hts]; exact hXp htl htr
      · rw [hBx, ggTh_add hρ' hgl', hel, her, hts, Bc.bcB_add (htl.trans hXL) (htr.trans hXL)]

/-! ## The reach equation at the long codes below `ε_{Ω₁+1}` -/

/-- **`B_n r(λ) = r(λ')` at every long code `m_λ` with `e(η_λ) < ε_{Ω₁+1}`**, given `L(ω+1) ≤ ν_C`. -/
theorem mvEQlong_low (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hm : upsilon l < cdCode S l)
    (he : cdExp (cdEta S l) < ggE) : Bc.bcB S n (cdR S l) = cdR S l' := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hρSC, hρ1⟩ := mvNamed_SC hl hX
  obtain ⟨hρSC', hρ1'⟩ := mvNamed_SC hl' hX'
  obtain ⟨e, he_def⟩ : ∃ e, e = cdExp (cdEta S l) := ⟨_, rfl⟩
  rw [← he_def] at he
  have heG : e < ggGam := he.trans_le ggE_le_ggGam
  have hge : GgCl (upsilon l) e := by rw [he_def]; exact mvCode_mem hl hX (he_def ▸ heG)
  have hXε : ω ^ cdDelta l = cdDelta l :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.1) (le_self_add.trans le_self_add)))
  obtain ⟨hDe, -, heE', hte, hθe⟩ := mvGg_move (k := n) hρSC hρ1 hρSC' hρ1' hB hXε
    (cdRho_lt_delta l) (hδr.trans hLw) e hge he
  -- the last exponent moves
  have hθ : ggGam ≤ ConjT.th S := ggGam_le (ConjT.SC_th S) (psiS_bounds (S := S) (Om ω) 1).1
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (he_def ▸ heG.trans_le hθ) (he_def ▸ hDe.1)
  rw [← he_def] at hexp'
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  -- the codes
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have hωe : (ω : Ordinal.{0}) < e := by
    have hce : cdCode S l ≤ e := by rw [he_def]; exact cdCodeOf_le_exp S _
    exact (hωC.trans h1).trans (hm.trans_le hce)
  have hO2 : e < Om (1 + 1) := heG.trans (ggGam_lt_Om2 S)
  have hcode : cdCode S l = e := by
    show cdCodeOf S (cdEta S l) = e
    rw [cdCodeOf_of_lt (he_def ▸ hO2), ← he_def]
    unfold cdOff; rw [if_neg (not_lt.2 hωe.le)]
  have hBω : (ω : Ordinal.{0}) < Bc.bcB S n e := by
    have hωL : (ω : Ordinal.{0}) < Nc.ncL S ω := hωC.trans (Bc.bcC_lt S n)
    have := (mvB_lt_iff (k := n) (mvD_of_lt hωL) hDe).2 hωe
    rwa [Bc.bcB_fix hωC] at this
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ heE'.trans_le ggE_le_ggGam |>.trans (ggGam_lt_Om2 S)), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hBω.le)]
  -- the readings
  have hΘ : cdTheta S l (cdCode S l) = ggTh (upsilon l) e := by
    rw [hcode]; exact mvTheta_eq hl hX heG.le
  have hΘ' : cdTheta S l' (cdCode S l') = ggTh (upsilon l') (Bc.bcB S n e) := by
    rw [hcode']; exact mvTheta_eq hl' hX' (heE'.le.trans ggE_le_ggGam)
  show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
  rw [hΘ, hΘ', hθe]
  exact (mvk_move hν hl hl' h1 hδr hB hte).symm

/-- `SfEQlong` at the long codes with `ε_{Ω₁+1} ≤ e(η_λ)`. -/
def MvEQtop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggE ≤ cdExp (cdEta S l) → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`L(ω+1) ≤ ν_C` and `MvEQtop` give `SfEQlong`.** -/
theorem mvEQlong_top (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : MvEQtop S) : Sf.SfEQlong S := by
  intro n l l' hR h1 hr hl' hB hm
  by_cases he : cdExp (cdEta S l) < ggE
  · exact mvEQlong_low hν hR h1 hr hl' hB hm he
  · exact htop n l l' hR h1 hr hl' hB hm (not_lt.1 he)

/-- **The road with `SfKMove` gone and `SfEQlong` needed only at the codes `≥ ε_{Ω₁+1}`.** -/
theorem mvRoad_top (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : Sf.SfLhTMove S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MvEQtop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mvRoad hU hO hL hV hN hlh fun hν => mvEQlong_top hν (htop hν)

end Googology.Trans.PoR.InaccPsi.R2.Mv
