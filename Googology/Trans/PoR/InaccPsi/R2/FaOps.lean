import Googology.Trans.PoR.InaccPsi.R2.FaLev
import Googology.Trans.PoR.InaccPsi.R2.AwOps

/-!
# Fa: THE `ϑ`-TERMS OF THE READINGS OVER A GENERAL BASE

`Θ = gxTh y At` for strongly critical `y`, atoms `At`; `wb` a strongly critical code above `Ω₁`, `x = Θ wb` strongly critical
(`FaBase`; the proofs of `Aw.aw_Rd_opow`, `Aw.aw_Rd_ind`, `Aw.aw_Rd_phi` with `θ`, `awNx y` replaced by `wb`, `x`):

* `fa_Rd_inj`, `fa_Rd_E_iff`, `faS0`, `fa_Rd_opow` (**`Θ(ω^a) = ϑˣ(1 + Θ(s₀(a)))`** for a code `a ≥ wb`, `ω^a ≠ a`);
* `fa_maxfix_code`, `fa_Rd_fix`, `fa_Rd_X0`, `fa_Rd_ind`;
* `fa_Rd_phi` (**`Θ(φ(a, b)) = ϑˣ(Ω₁·Θ(a) + Θ(ind(a, wb, b)))`** for codes `1 ≤ a`, `b` with `a, b, wb < φ(a, b)`, below the next
  `υ`-point).

No new axiom.  New definitions: `FaBase`, `faS0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Aw

variable {S : InaccSeq.{0}}

/-- **The base `wb` of a reading**: a strongly critical code above `Ω₁` whose reading `x` is strongly critical. -/
structure FaBase (y : Ordinal.{0}) (At : Set Ordinal.{0}) (wb x : Ordinal.{0}) : Prop where
  yS : SC y
  y1 : y < Om1
  at' : GxAt At
  wc : GxCl y At wb
  wS : SC wb
  w1 : Om1 < wb
  wR : gxTh y At wb = x
  xS : SC x
  x1 : x < Om1
  lt1 : ∀ c, GxCl y At c → gxTh y At c < Om1

variable {y : Ordinal.{0}} {At : Set Ordinal.{0}} {wb x : Ordinal.{0}}

section Base


/-- `Θ_y` is injective on the codes. -/
theorem fa_Rd_inj (hB : FaBase y At wb x) {c d : Ordinal.{0}} (hc : GxCl y At c) (hd : GxCl y At d)
    (e : gxTh y At c = gxTh y At d) : c = d := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  rcases lt_trichotomy c d with h | h | h
  · exact absurd e (gxTh_lt hc h).ne
  · exact h
  · exact absurd e (gxTh_lt hd h).ne'

/-- A code is an `ε`-number iff its reading is. -/
theorem fa_Rd_E_iff (hB : FaBase y At wb x) {c : Ordinal.{0}} (hc : GxCl y At c) :
    ω ^ c = c ↔ ω ^ gxTh y At c = gxTh y At c := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have hp := gxTh_opow hy hAt hc
  constructor
  · intro h
    rw [h] at hp
    exact hp.symm
  · intro h
    rw [h] at hp
    exact fa_Rd_inj hB0 (hc.opow hy.1) hc hp

/-- `Θ_y(ν) = ν` for a natural number `ν`. -/
theorem fa_Rd_nat (hB : FaBase y At wb x) {n : Ordinal.{0}} (hn : n < ω) : gxTh y At n = n :=
  by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  exact
  gxTh_small (hn.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hy))).le

/-- A natural number is a code. -/
theorem fa_nat_code (hB : FaBase y At wb x) {n : Ordinal.{0}} (hn : n < ω) : GxCl y At n :=
  by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  exact
  GxCl.small (hn.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hy)))

end Base

/-! ## `ω`-powers -/

open Classical in
/-- **The argument of the node of `ω^a`.** -/
noncomputable def faS0 (wb a : Ordinal.{0}) : Ordinal.{0} :=
  if InE (ω * (a / ω)) then (ω * (a / ω) + (a % ω - 1)) - wb else a - wb

section Opow


/-- **`Θ_y(ω^a) = ϑˣ(1 + Θ_y(s₀(a)))`** for a code `a ≥ θ` with `ω^a ≠ a`; `s₀(a)` is a code. -/
theorem fa_Rd_opow (hB : FaBase y At wb x) {a : Ordinal.{0}} (ha : GxCl y At a) (hwa : wb ≤ a) (hE : ω ^ a ≠ a) :
    GxCl y At (faS0 wb a) ∧ faS0 wb a ≤ a ∧
      gxTh y At (ω ^ a) = vt x (1 + gxTh y At (faS0 wb a)) := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have hxE : InE x := Low.opow_eq_self_of_SC hxS
  have hsub : ∀ w, GxCl y At w → wb ≤ w →
      GxCl y At (w - wb) ∧ w - wb ≤ w ∧
        gxTh y At w = x + gxTh y At (w - wb) := by
    intro w hw hθw
    have hs := (gxDec hy hAt w hw).1 _ hwc hθw
    refine ⟨hs, Ordinal.sub_le_self _ _, ?_⟩
    have e := gxTh_add hy hAt hwc (w - wb)
    rw [Ordinal.add_sub_cancel_of_le hθw, hwR] at e
    exact e
  have hop := gxTh_opow hy hAt ha
  have hlt1 := hΘ1
  have hS0 : wbar = fun γ => ω ^ siExp γ := si_wbar_eq
  by_cases hlam : InE (ω * (a / ω))
  · obtain ⟨hj0, e1, e2⟩ := aw_lim_parts hE hlam
    set l := ω * (a / ω) with hl
    set j := a % ω - 1 with hj
    have hj' : j < ω := (Ordinal.sub_le_self _ _).trans_lt (Ordinal.mod_lt a omega0_ne_zero)
    have hla : a = l + (1 + j) := by rw [e1]; exact (Ordinal.div_add_mod a ω).symm
    have hl0 : 0 < l := by
      have h1 : (0 : Ordinal.{0}) < ω ^ l := opow_pos _ omega0_pos
      have h2 : ω ^ l = l := hlam
      rwa [h2] at h1
    have hlw : ω ≤ l := omega0_lt_inE hlam |>.le
    have hsmall : 1 + j < ω ^ l := by
      have h2 : ω ^ l = l := hlam
      rw [h2]
      exact (isPrincipal_add_omega0 one_lt_omega0 hj').trans_le hlw
    have hlog : log ω a = l := by
      have h2 : ω ^ l * 1 + (1 + j) = a := by rw [mul_one, show ω ^ l = l from hlam]; exact hla.symm
      rw [← h2]
      rw [log_opow_mul_add one_lt_omega0 one_ne_zero hsmall, log_one_right, add_zero]
    have hlc : GxCl y At l := by
      have := (gxDec hy hAt a ha).2
      rwa [hlog] at this
    have ha1c : GxCl y At (l + j) := GxCl.add hlc (fa_nat_code hB0 hj')
    have hθl : wb ≤ l := by
      by_contra hlt
      push Not at hlt
      have hI := (hwS).isPrincipal
      have : a < wb := by
        rw [hla]
        exact hI hlt ((isPrincipal_add_omega0 one_lt_omega0 hj').trans (omega0_lt_inE (Low.opow_eq_self_of_SC hwS)))
      exact absurd hwa (not_le.2 this)
    obtain ⟨hs1, hs2, hs3⟩ := hsub (l + j) ha1c (hθl.trans le_self_add)
    have hval : faS0 wb a = l + j - wb := by
      unfold faS0; rw [if_pos hlam]
    rw [hval]
    refine ⟨hs1, hs2.trans ?_, ?_⟩
    · exact le_self_add.trans_eq e2
    · rw [hop, vt_wbar hxE hx1 (hlt1 _ hs1), ← hs3, hS0]
      -- `siExp (Θ(l + j)) = Θ(a)`
      have hRa : gxTh y At a = gxTh y At (l + j) + 1 := by
        conv_lhs => rw [← e2]
        rw [gxTh_add hy hAt ha1c 1, gxTh_small (Gg.gg_one_lt_of_SC hy).le]
      have hRl : gxTh y At (l + j) = gxTh y At l + j := by
        rw [gxTh_add hy hAt hlc j, fa_Rd_nat hB0 hj']
      have hRlE : InE (gxTh y At l) := (fa_Rd_E_iff hB0 hlc).1 hlam
      have hlim : ω * (gxTh y At (l + j) / ω) = gxTh y At l := by
        rw [hRl]
        have hq : gxTh y At l = ω * (gxTh y At l / ω) := (si_inE_limpart hRlE).symm
        conv_lhs => rw [hq]
        rw [si_div_eq hj']
        exact hq.symm
      have hsi : siExp (gxTh y At (l + j)) = gxTh y At (l + j) + 1 := by
        unfold siExp
        rw [if_pos (by rw [hlim]; exact hRlE)]
      show ω ^ gxTh y At a = ω ^ siExp _
      rw [hsi, hRa]
  · obtain ⟨hs1, hs2, hs3⟩ := hsub a ha hwa
    have hval : faS0 wb a = a - wb := by
      unfold faS0; rw [if_neg hlam]
    rw [hval]
    refine ⟨hs1, hs2, ?_⟩
    rw [hop, vt_wbar hxE hx1 (hlt1 _ hs1), ← hs3, hS0]
    show ω ^ gxTh y At a = ω ^ siExp _
    have hsi : siExp (gxTh y At a) = gxTh y At a := by
      unfold siExp
      rw [if_neg]
      intro hE'
      -- the limit part of the reading is a reading of a code
      set v := gxTh y At a with hv
      have hlev : ω * (v / ω) ≤ v := by
        conv_rhs => rw [← Ordinal.div_add_mod v ω]
        exact le_self_add
      rcases hlev.lt_or_eq with hlt | heq
      · obtain ⟨c, hc, hca, ec⟩ := gxTh_onto (Z := y) (At := At) (m := a) (v := ω * (v / ω)) hlt
        have hcE : ω ^ c = c := (fa_Rd_E_iff hB0 hc).2 (by rw [ec]; exact hE')
        have hjj : v % ω < ω := Ordinal.mod_lt v omega0_ne_zero
        have hsum : gxTh y At (c + v % ω) = v := by
          rw [gxTh_add hy hAt hc, fa_Rd_nat hB0 hjj, ec]
          exact Ordinal.div_add_mod v ω
        have hac : a = c + v % ω :=
          fa_Rd_inj hB0 ha (GxCl.add hc (fa_nat_code hB0 hjj)) hsum.symm
        apply hlam
        have hcq : ω * (c / ω) = c := si_inE_limpart hcE
        have : a / ω = c / ω := by
          rw [hac]
          conv_lhs => rw [← hcq]
          rw [si_div_eq hjj]
        rw [this, hcq]
        exact hcE
      · rw [heq] at hE'
        exact hE ((fa_Rd_E_iff hB0 ha).2 hE')
    rw [hsi]

end Opow

/-! ## The largest fixed point -/

section Fix


/-- **The largest fixed point of `φ_a` in `(θ, b]`, for a code `b`, is a code.** -/
theorem fa_maxfix_code (hB : FaBase y At wb x) {a : Ordinal.{0}} :
    ∀ b, GxCl y At b → ∀ p, QfMaxFix a wb b p → GxCl y At p := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb p hp
  obtain ⟨hpP, hθp, hpb, hmax⟩ := hp
  rcases hpb.lt_or_eq with hlt | rfl
  swap
  · exact hb
  have hpE : ω ^ p = p := Lu.luP_E (β := a + 1) le_add_self hpP
  have hOb : (Om1 : Ordinal.{0}) < b := (hw1.trans hθp).trans hlt
  by_cases hbE : ω ^ b = b
  · by_cases hI : invVeblen₁ b < b
    · have e : veblen (invVeblen₁ b) (invVeblen₂ b) = b := by rw [veblen_invVeblen₁_invVeblen₂, hbE]
      have h2 : invVeblen₂ b < b := Tf.tf_inv2_lt hbE
      obtain ⟨-, hb'c⟩ := gxDecV hy.1 hAt hb _ _ e h2
      rcases lt_or_ge a (invVeblen₁ b) with hlt' | hle
      · exfalso
        have hfb : veblen a b = b := by
          conv_lhs => rw [← e]
          rw [veblen_veblen_of_lt hlt', e]
        exact absurd (hmax b (luP_succ.2 hfb) (hθp.trans hlt) le_rfl) (not_le.2 hlt)
      · have hfix : veblen (invVeblen₁ b) p = p := by
          rcases hle.lt_or_eq with h | h
          · have h1 := veblen_veblen_of_lt h p
            rwa [luP_succ.1 hpP] at h1
          · rw [h]; exact luP_succ.1 hpP
        have hpb' : p < invVeblen₂ b := by
          have h3 : veblen (invVeblen₁ b) p < veblen (invVeblen₁ b) (invVeblen₂ b) := by
            rw [hfix, e]; exact hlt
          exact veblen_lt_veblen_iff_right.1 h3
        exact IH _ h2 hb'c p ⟨hpP, hθp, hpb'.le, fun q h1 h3 h4 => hmax q h1 h3 (h4.trans h2.le)⟩
    · exfalso
      have hSC : SC b := by
        rw [← Tf.tf_SC_gamma hOb hI]; exact Lq.lq_gamma_SC _
      rcases lt_or_ge a b with hab | hba
      · exact absurd (hmax b (luP_succ.2 (hSC.veblen_right hab)) (hθp.trans hlt) le_rfl) (not_le.2 hlt)
      · have hap : a ≤ p := (left_le_veblen a p).trans_eq (luP_succ.1 hpP)
        exact absurd (hba.trans hap) (not_le.2 hlt)
  · have hl : log ω b < b := Tf.tf_log_lt hOb hbE
    have hpl : p ≤ log ω b := by
      have h1 : ω ^ p < ω ^ (log ω b + 1) := by
        rw [hpE]; exact hlt.trans (lt_opow_succ_log_self one_lt_omega0 b)
      exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h1)
    exact IH _ hl (gxDec hy hAt b hb).2 p ⟨hpP, hθp, hpl, fun q h1 h3 h4 => hmax q h1 h3 (h4.trans hl.le)⟩

/-- A code is a fixed point of `φ_a` iff its reading is a fixed point of `φ_{Θ a}`. -/
theorem fa_Rd_fix (hB : FaBase y At wb x) {a q : Ordinal.{0}} (ha : GxCl y At a) (hq : GxCl y At q) :
    veblen a q = q ↔ veblen (gxTh y At a) (gxTh y At q) = gxTh y At q := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have hp := gxTh_phi hy hAt a ha q hq
  constructor
  · intro h
    rw [h] at hp
    exact hp.symm
  · intro h
    exact fa_Rd_inj hB0 (GxCl.phi ha hq) hq (hp.trans h)

end Fix

/-! ## The index -/

section Ind


/-- **`Θ_y(x₀(a, θ)) = x₀(Θ_y a, x)`.** -/
theorem fa_Rd_X0 (hB : FaBase y At wb x) {a : Ordinal.{0}} (ha : GxCl y At a) :
    GxCl y At (awX0 a wb) ∧
      gxTh y At (awX0 a wb) = awX0 (gxTh y At a) x := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  have hlt : gxTh y At a < x ↔ a < wb := by
    rw [← hwR]
    constructor
    · intro h
      by_contra hle
      exact absurd h (not_lt.2 (gxTh_mono (not_lt.1 hle)))
    · exact gxTh_lt ha
  have h0 : veblen (gxTh y At a) 0 = gxTh y At a ↔ veblen a 0 = a := by
    have hp := gxTh_phi hy hAt a ha 0 (GxCl.zero hy.1)
    rw [gxTh_zero] at hp
    constructor
    · intro h
      rw [h] at hp
      exact fa_Rd_inj hB0 (GxCl.phi ha (GxCl.zero hy.1)) ha hp
    · intro h
      rw [h] at hp
      exact hp.symm
  unfold awX0
  by_cases h1 : a < wb
  · rw [if_pos h1, if_pos (hlt.2 h1), gxTh_add hy hAt hwc 1, hwR, gxTh_small h1lt.le]
    exact ⟨GxCl.add hwc (GxCl.small h1lt), rfl⟩
  · rw [if_neg h1, if_neg (fun h => h1 (hlt.1 h))]
    by_cases h2 : veblen a 0 = a
    · rw [if_pos h2, if_pos (h0.2 h2), gxTh_small h1lt.le]
      exact ⟨GxCl.small h1lt, rfl⟩
    · rw [if_neg h2, if_neg (fun h => h2 (h0.1 h)), gxTh_zero]
      exact ⟨GxCl.zero hy.1, rfl⟩

/-- **`Θ_y(ind(a, θ, b)) = ind(Θ_y a, x, Θ_y b)`**, and the index is a code `≤ b`. -/
theorem fa_Rd_ind (hB : FaBase y At wb x) {a b : Ordinal.{0}} (ha : GxCl y At a) (hb : GxCl y At b)
    (hab : a < veblen a b) (hbb : b < veblen a b) (hθ : wb < veblen a b) :
    GxCl y At (qfInd a wb b) ∧ qfInd a wb b ≤ b ∧
      gxTh y At (qfInd a wb b) =
        qfInd (gxTh y At a) x (gxTh y At b) := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  have hφc : GxCl y At (veblen a b) := GxCl.phi ha hb
  have hφR := gxTh_phi hy hAt a ha b hb
  have hxφ : x < veblen (gxTh y At a) (gxTh y At b) := by
    rw [← hφR, ← hwR]; exact gxTh_lt hwc hθ
  have huφ : gxTh y At a < veblen (gxTh y At a) (gxTh y At b) := by
    rw [← hφR]; exact gxTh_lt ha hab
  by_cases hex : ∃ q, LuP (a + 1) q ∧ wb < q ∧ q ≤ b
  · obtain ⟨p, hp⟩ := qf_maxfix hex
    have hpc := fa_maxfix_code hB0 b hb p hp
    obtain ⟨hpP, hθp, hpb, hmax⟩ := hp
    have hbP : ¬ LuP (a + 1) b := fun h => hbb.ne (luP_succ.1 h).symm
    have hpb' : p < b := lt_of_le_of_ne hpb fun e => hbP (e ▸ hpP)
    obtain ⟨d, hd⟩ := exists_add_of_le (Order.add_one_le_of_lt hpb')
    have hp1c : GxCl y At (p + 1) := GxCl.add hpc (GxCl.small h1lt)
    have hdc : GxCl y At d := by
      have := (gxDec hy hAt b hb).1 _ hp1c (Order.add_one_le_of_lt hpb')
      rwa [hd, Ordinal.add_sub_cancel] at this
    have hind : qfInd a wb b = p + d := by
      rw [hd]
      refine qfInd_above' hpP hθp fun z hz hz' => ?_
      have h1 : p + 1 + z ≤ p := hmax _ hz' (hθp.trans ((lt_add_one p).trans_le le_self_add))
        (by rw [hd]; exact ((add_lt_add_iff_left _).2 hz).le)
      exact absurd h1 (not_le.2 ((lt_add_one p).trans_le le_self_add))
    rw [hind]
    refine ⟨GxCl.add hpc hdc, ?_, ?_⟩
    · rw [hd, add_assoc]
      exact add_le_add le_rfl le_add_self
    · have hRp1 : gxTh y At (p + 1) = gxTh y At p + 1 := by
        rw [gxTh_add hy hAt hpc 1, gxTh_small h1lt.le]
      have hRb : gxTh y At b = gxTh y At p + 1 + gxTh y At d := by
        rw [hd, gxTh_add hy hAt hp1c d, hRp1]
      rw [gxTh_add hy hAt hpc d, hRb]
      refine (qfInd_above' (luP_succ.2 ((fa_Rd_fix hB0 ha hpc).1 (luP_succ.1 hpP))) ?_ ?_).symm
      · rw [← hwR]; exact gxTh_lt hwc hθp
      · intro z hz hzP
        obtain ⟨d', hd'c, hd'd, rfl⟩ := gxTh_onto hz
        have hc' : GxCl y At (p + 1 + d') := GxCl.add hp1c hd'c
        have hRc : gxTh y At (p + 1 + d') = gxTh y At p + 1 + gxTh y At d' := by
          rw [gxTh_add hy hAt hp1c d', hRp1]
        rw [← hRc] at hzP
        have hfix := (fa_Rd_fix hB0 ha hc').2 (luP_succ.1 hzP)
        have h1 : p + 1 + d' ≤ p := hmax _ (luP_succ.2 hfix)
          (hθp.trans ((lt_add_one p).trans_le le_self_add))
          (by rw [hd]; exact ((add_lt_add_iff_left _).2 hd'd).le)
        exact absurd h1 (not_le.2 ((lt_add_one p).trans_le le_self_add))
  · push Not at hex
    have hcode := aw_noFix (hwS) hθ hab (fun q h1 h2 h3 => absurd h3 (not_le.2 (hex q h1 h2)))
    obtain ⟨hx0c, hx0R⟩ := fa_Rd_X0 hB0 ha
    have hx0le : awX0 a wb ≤ b := by
      conv_rhs => rw [hcode]
      exact le_self_add
    have hic : GxCl y At (qfInd a wb b) := by
      have := (gxDec hy hAt b hb).1 _ hx0c hx0le
      rwa [show b - awX0 a wb = qfInd a wb b by
        conv_lhs => rw [hcode]
        exact Ordinal.add_sub_cancel _ _] at this
    refine ⟨hic, by conv_rhs => rw [hcode]
                    exact le_add_self, ?_⟩
    have hval : ∀ q, LuP (gxTh y At a + 1) q → x < q → ¬ q ≤ gxTh y At b := by
      intro q hqP hxq hqb
      have hqφ : veblen (gxTh y At a) q = q := luP_succ.1 hqP
      rcases hqb.lt_or_eq with hlt | rfl
      · obtain ⟨q', hq'c, hq'b, rfl⟩ := gxTh_onto hlt
        have hfix := (fa_Rd_fix hB0 ha hq'c).2 hqφ
        have hθq' : wb < q' := by
          by_contra hle
          push Not at hle
          have := gxTh_mono (Z := y) (At := At) hle
          rw [hwR] at this
          exact absurd hxq (not_lt.2 this)
        exact absurd hq'b.le (not_le.2 (hex q' (luP_succ.2 hfix) hθq'))
      · rw [← hφR] at hqφ
        exact absurd hqφ (gxTh_lt hb hbb).ne'
    have hv := aw_noFix hxS hxφ huφ hval
    have hRb := gxTh_add hy hAt hx0c (qfInd a wb b)
    rw [← hcode, hx0R] at hRb
    exact (add_left_cancel_iff).1 (hRb.symm.trans hv)

/-- **`Θ_y(φ(a, b)) = ϑˣ(Ω₁·Θ_y(a) + Θ_y(ind(a, θ, b)))`** for codes `1 ≤ a`, `b` with `a, b, θ < φ(a, b)`. -/
theorem fa_Rd_phi (hB : FaBase y At wb x) {a b : Ordinal.{0}} (ha : GxCl y At a) (hb : GxCl y At b) (h1 : 1 ≤ a)
    (hab : a < veblen a b) (hbb : b < veblen a b) (hθ : wb < veblen a b)
    (hφm : gxTh y At (veblen a b) < awNx x) :
    gxTh y At (veblen a b) =
      vt x (Om1 * gxTh y At a + gxTh y At (qfInd a wb b)) := by
  have hB0 := hB
  obtain ⟨hy, hy1, hAt, hwc, hwS, hw1, hwR, hxS, hx1, hΘ1⟩ := hB
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  obtain ⟨-, -, -, hm1, hTm, -⟩ := awNx_facts hxS hx1
  have hφR := gxTh_phi hy hAt a ha b hb
  have hxφ : x < veblen (gxTh y At a) (gxTh y At b) := by
    rw [← hφR, ← hwR]; exact gxTh_lt hwc hθ
  have huφ : gxTh y At a < veblen (gxTh y At a) (gxTh y At b) := by
    rw [← hφR]; exact gxTh_lt ha hab
  have hvφ : gxTh y At b < veblen (gxTh y At a) (gxTh y At b) := by
    rw [← hφR]; exact gxTh_lt hb hbb
  have hum : gxTh y At a < awNx x := (gxTh_lt ha hab).trans hφm
  have hvm : gxTh y At b < awNx x := (gxTh_lt hb hbb).trans hφm
  have hu1 : 1 ≤ gxTh y At a := by
    have := gxTh_mono (Z := y) (At := At) h1
    rwa [gxTh_small h1lt.le] at this
  obtain ⟨hic, hile, hiR⟩ := fa_Rd_ind hB0 ha hb hab hbb hθ
  have him : gxTh y At (qfInd a wb b) < awNx x := (gxTh_mono hile).trans_lt hvm
  rw [hφR, hiR]
  rw [hiR] at him
  exact qf_dict' hxS hx1 hu1 ((hTm _ (hum.trans hm1)).2 hum) (hum.trans hm1) _ hxφ huφ
    (fun h => hvφ.ne (luP_succ.1 h).symm) ((hTm _ (him.trans hm1)).2 him) (him.trans hm1)

end Ind

end Googology.Trans.PoR.InaccPsi.R2.Fa
