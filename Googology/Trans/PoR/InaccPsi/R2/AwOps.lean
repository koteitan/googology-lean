import Googology.Trans.PoR.InaccPsi.R2.AwRead
import Googology.Trans.PoR.InaccPsi.R2.QfTB
import Googology.Trans.PoR.InaccPsi.R2.SiCnt

/-!
# AwOps: THE `ϑ`-TERMS OF THE READINGS OF THE CODES ABOVE `θ`, WITH THE SAME CODES AT EVERY BASE

`Θ_y = gxTh y (awAt S y)`, `x = awNx y`.  Above `θ` a code reads in `seg(x)`; its reading is a node over `x` whose argument
is the reading of **a code that does not depend on `y`**:

* `aw_Rd_inj`, `aw_Rd_E_iff` (`Θ_y` is injective on the codes, and a code is an `ε`-number iff its reading is);
* `awS0`, `aw_Rd_opow` (**`Θ_y(ω^a) = ϑˣ(1 + Θ_y(s₀(a)))`** for a code `a ≥ θ`, `ω^a ≠ a`; `s₀(a) = a − θ`, or `a' − θ` for
  `a = a' + 1` when the limit part of `a` is an `ε`-number: `ϑˣ(1 + α) = ω̄_{x+α}`, `Si.si_wbar_eq`);
* `aw_maxfix_code` (**the largest fixed point of `φ_a` in `(θ, b]` of codes `a`, `b` is a code**), `aw_Rd_fix`,
  `aw_maxfix_Rd`;
* `awX0`, `aw_noFix` (`b = x₀(a, θ) + ind(b)` when `φ_a` has no fixed point in `(θ, b]`), `aw_ind_code`, `aw_Rd_ind`
  (**`Θ_y(ind(a, θ, b)) = ind(Θ_y a, x, Θ_y b)`**);
* `aw_Rd_phi` (**`Θ_y(φ(a, b)) = ϑˣ(Ω₁·Θ_y(a) + Θ_y(ind(a, θ, b)))`** for codes `1 ≤ a`, `b` with `a, b, θ < φ(a, b)`).

No new axiom.  New definitions: `awS0`, `awX0`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

section Base

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy

/-- `Θ_y` is injective on the codes. -/
theorem aw_Rd_inj {c d : Ordinal.{0}} (hc : GxCl y (awAt S y) c) (hd : GxCl y (awAt S y) d)
    (e : gxTh y (awAt S y) c = gxTh y (awAt S y) d) : c = d := by
  rcases lt_trichotomy c d with h | h | h
  · exact absurd e (gxTh_lt hc h).ne
  · exact h
  · exact absurd e (gxTh_lt hd h).ne'

/-- A code is an `ε`-number iff its reading is. -/
theorem aw_Rd_E_iff {c : Ordinal.{0}} (hc : GxCl y (awAt S y) c) :
    ω ^ c = c ↔ ω ^ gxTh y (awAt S y) c = gxTh y (awAt S y) c := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hp := gxTh_opow hy hAt hc
  constructor
  · intro h
    rw [h] at hp
    exact hp.symm
  · intro h
    rw [h] at hp
    exact aw_Rd_inj hy (hc.opow hy.1) hc hp

/-- `Θ_y(ν) = ν` for a natural number `ν`. -/
theorem aw_Rd_nat {n : Ordinal.{0}} (hn : n < ω) : gxTh y (awAt S y) n = n :=
  gxTh_small (hn.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hy))).le

/-- A natural number is a code. -/
theorem aw_nat_code {n : Ordinal.{0}} (hn : n < ω) : GxCl y (awAt S y) n :=
  GxCl.small (hn.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hy)))

end Base

/-! ## `ω`-powers -/

open Classical in
/-- **The argument of the node of `ω^a`.** -/
noncomputable def awS0 (S : InaccSeq.{0}) (a : Ordinal.{0}) : Ordinal.{0} :=
  if InE (ω * (a / ω)) then (ω * (a / ω) + (a % ω - 1)) - ConjT.th S else a - ConjT.th S

/-- `θ` is an `ε`-number below every code above it, and additive principal. -/
theorem aw_th_E : InE (ConjT.th S) := Low.opow_eq_self_of_SC (ConjT.SC_th S)

/-- The parts of `a = ω·(a/ω) + a%ω` when the limit part is an `ε`-number and `a` is not. -/
theorem aw_lim_parts {a : Ordinal.{0}} (hE : ω ^ a ≠ a) (hlam : InE (ω * (a / ω))) :
    a % ω ≠ 0 ∧ 1 + (a % ω - 1) = a % ω ∧ ω * (a / ω) + (a % ω - 1) + 1 = a := by
  have hdm := Ordinal.div_add_mod a ω
  have hj : a % ω < ω := Ordinal.mod_lt a omega0_ne_zero
  have hj0 : a % ω ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hdm
    apply hE
    have : ω ^ (ω * (a / ω)) = ω * (a / ω) := hlam
    rwa [hdm] at this
  have h1 : (1 : Ordinal.{0}) ≤ a % ω := one_le_iff_ne_zero.2 hj0
  have e1 : 1 + (a % ω - 1) = a % ω := Ordinal.add_sub_cancel_of_le h1
  obtain ⟨n, hn⟩ := lt_omega0.1 hj
  have e2 : a % ω - 1 + 1 = a % ω := by
    rw [hn]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
      cases n with
      | zero => exact absurd (by rw [hn]; rfl) hj0
      | succ k => exact ⟨k, rfl⟩
    have : ((k + 1 : ℕ) : Ordinal.{0}) - 1 = (k : Ordinal.{0}) := by
      have h := Ordinal.add_sub_cancel (1 : Ordinal.{0}) (k : Ordinal.{0})
      rwa [show (1 : Ordinal.{0}) + (k : Ordinal.{0}) = ((k + 1 : ℕ) : Ordinal.{0}) by
        rw [Nat.add_comm]; push_cast; rfl] at h
    rw [this]; push_cast; rfl
  refine ⟨hj0, e1, ?_⟩
  rw [add_assoc, e2]; exact hdm

section Opow

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

/-- **`Θ_y(ω^a) = ϑˣ(1 + Θ_y(s₀(a)))`** for a code `a ≥ θ` with `ω^a ≠ a`; `s₀(a)` is a code. -/
theorem aw_Rd_opow {a : Ordinal.{0}} (ha : GxCl y (awAt S y) a) (hθa : ConjT.th S ≤ a) (hE : ω ^ a ≠ a) :
    GxCl y (awAt S y) (awS0 S a) ∧ awS0 S a ≤ a ∧
      gxTh y (awAt S y) (ω ^ a) = vt (awNx y) (1 + gxTh y (awAt S y) (awS0 S a)) := by
  obtain ⟨hyx, -, hxS, hx1, -, -⟩ := awNx_facts hy hy1
  have hxE : InE (awNx y) := Low.opow_eq_self_of_SC hxS
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hθc : GxCl y (awAt S y) (ConjT.th S) := GxCl.atom (aw_th_mem y)
  have hsub : ∀ w, GxCl y (awAt S y) w → ConjT.th S ≤ w →
      GxCl y (awAt S y) (w - ConjT.th S) ∧ w - ConjT.th S ≤ w ∧
        gxTh y (awAt S y) w = awNx y + gxTh y (awAt S y) (w - ConjT.th S) := by
    intro w hw hθw
    have hs := (gxDec hy hAt w hw).1 _ hθc hθw
    refine ⟨hs, Ordinal.sub_le_self _ _, ?_⟩
    have e := gxTh_add hy hAt hθc (w - ConjT.th S)
    rw [Ordinal.add_sub_cancel_of_le hθw, aw_Rd_th hy hy1] at e
    exact e
  have hop := gxTh_opow hy hAt ha
  have hlt1 : ∀ w, GxCl y (awAt S y) w → gxTh y (awAt S y) w < Om1 := fun w hw => by
    obtain ⟨hxm, -, -, hm1, -, -⟩ := awNx_facts hxS hx1
    exact (aw_Rd_lt hy hy1 hw).trans hm1
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
    have hlc : GxCl y (awAt S y) l := by
      have := (gxDec hy hAt a ha).2
      rwa [hlog] at this
    have ha1c : GxCl y (awAt S y) (l + j) := GxCl.add hlc (aw_nat_code hy hj')
    have hθl : ConjT.th S ≤ l := by
      by_contra hlt
      push Not at hlt
      have hI := (ConjT.SC_th S).isPrincipal
      have : a < ConjT.th S := by
        rw [hla]
        exact hI hlt ((isPrincipal_add_omega0 one_lt_omega0 hj').trans (omega0_lt_inE aw_th_E))
      exact absurd hθa (not_le.2 this)
    obtain ⟨hs1, hs2, hs3⟩ := hsub (l + j) ha1c (hθl.trans le_self_add)
    have hval : awS0 S a = l + j - ConjT.th S := by
      unfold awS0; rw [if_pos hlam]
    rw [hval]
    refine ⟨hs1, hs2.trans ?_, ?_⟩
    · exact le_self_add.trans_eq e2
    · rw [hop, vt_wbar hxE hx1 (hlt1 _ hs1), ← hs3, hS0]
      -- `siExp (Θ(l + j)) = Θ(a)`
      have hRa : gxTh y (awAt S y) a = gxTh y (awAt S y) (l + j) + 1 := by
        conv_lhs => rw [← e2]
        rw [gxTh_add hy hAt ha1c 1, gxTh_small (Gg.gg_one_lt_of_SC hy).le]
      have hRl : gxTh y (awAt S y) (l + j) = gxTh y (awAt S y) l + j := by
        rw [gxTh_add hy hAt hlc j, aw_Rd_nat hy hj']
      have hRlE : InE (gxTh y (awAt S y) l) := (aw_Rd_E_iff hy hlc).1 hlam
      have hlim : ω * (gxTh y (awAt S y) (l + j) / ω) = gxTh y (awAt S y) l := by
        rw [hRl]
        have hq : gxTh y (awAt S y) l = ω * (gxTh y (awAt S y) l / ω) := (si_inE_limpart hRlE).symm
        conv_lhs => rw [hq]
        rw [si_div_eq hj']
        exact hq.symm
      have hsi : siExp (gxTh y (awAt S y) (l + j)) = gxTh y (awAt S y) (l + j) + 1 := by
        unfold siExp
        rw [if_pos (by rw [hlim]; exact hRlE)]
      show ω ^ gxTh y (awAt S y) a = ω ^ siExp _
      rw [hsi, hRa]
  · obtain ⟨hs1, hs2, hs3⟩ := hsub a ha hθa
    have hval : awS0 S a = a - ConjT.th S := by
      unfold awS0; rw [if_neg hlam]
    rw [hval]
    refine ⟨hs1, hs2, ?_⟩
    rw [hop, vt_wbar hxE hx1 (hlt1 _ hs1), ← hs3, hS0]
    show ω ^ gxTh y (awAt S y) a = ω ^ siExp _
    have hsi : siExp (gxTh y (awAt S y) a) = gxTh y (awAt S y) a := by
      unfold siExp
      rw [if_neg]
      intro hE'
      -- the limit part of the reading is a reading of a code
      set v := gxTh y (awAt S y) a with hv
      have hlev : ω * (v / ω) ≤ v := by
        conv_rhs => rw [← Ordinal.div_add_mod v ω]
        exact le_self_add
      rcases hlev.lt_or_eq with hlt | heq
      · obtain ⟨c, hc, hca, ec⟩ := gxTh_onto (Z := y) (At := awAt S y) (m := a) (v := ω * (v / ω)) hlt
        have hcE : ω ^ c = c := (aw_Rd_E_iff hy hc).2 (by rw [ec]; exact hE')
        have hjj : v % ω < ω := Ordinal.mod_lt v omega0_ne_zero
        have hsum : gxTh y (awAt S y) (c + v % ω) = v := by
          rw [gxTh_add hy hAt hc, aw_Rd_nat hy hjj, ec]
          exact Ordinal.div_add_mod v ω
        have hac : a = c + v % ω :=
          aw_Rd_inj hy ha (GxCl.add hc (aw_nat_code hy hjj)) hsum.symm
        apply hlam
        have hcq : ω * (c / ω) = c := si_inE_limpart hcE
        have : a / ω = c / ω := by
          rw [hac]
          conv_lhs => rw [← hcq]
          rw [si_div_eq hjj]
        rw [this, hcq]
        exact hcE
      · rw [heq] at hE'
        exact hE ((aw_Rd_E_iff hy ha).2 hE')
    rw [hsi]

end Opow

/-! ## The largest fixed point -/

section Fix

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

/-- **The largest fixed point of `φ_a` in `(θ, b]`, for a code `b`, is a code.** -/
theorem aw_maxfix_code {a : Ordinal.{0}} :
    ∀ b, GxCl y (awAt S y) b → ∀ p, QfMaxFix a (ConjT.th S) b p → GxCl y (awAt S y) p := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb p hp
  obtain ⟨hpP, hθp, hpb, hmax⟩ := hp
  rcases hpb.lt_or_eq with hlt | rfl
  swap
  · exact hb
  have hpE : ω ^ p = p := Lu.luP_E (β := a + 1) le_add_self hpP
  have hOb : (Om1 : Ordinal.{0}) < b := by
    rw [Rj.rj_Om1]
    exact ((psiS_bounds (S := S) _ 1).1.trans hθp).trans hlt
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
theorem aw_Rd_fix {a q : Ordinal.{0}} (ha : GxCl y (awAt S y) a) (hq : GxCl y (awAt S y) q) :
    veblen a q = q ↔ veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) q) = gxTh y (awAt S y) q := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hp := gxTh_phi hy hAt a ha q hq
  constructor
  · intro h
    rw [h] at hp
    exact hp.symm
  · intro h
    exact aw_Rd_inj hy (GxCl.phi ha hq) hq (hp.trans h)

end Fix

/-! ## The index -/

open Classical in
/-- The first argument of `qfC' β y` when `φ_β` has no fixed point in `(y, b]`. -/
noncomputable def awX0 (β y : Ordinal.{0}) : Ordinal.{0} :=
  if β < y then y + 1 else if veblen β 0 = β then 1 else 0

/-- **`b = x₀(β, y) + ind(b)`** when `φ_β` has no fixed point in `(y, b]`. -/
theorem aw_noFix {β y b : Ordinal.{0}} (hy : SC y) (hyb : y < veblen β b) (hβb : β < veblen β b)
    (hex : ∀ q, LuP (β + 1) q → y < q → ¬ q ≤ b) : b = awX0 β y + qfInd β y b := by
  unfold awX0 qfInd
  have hex' : ∀ q, LuP (β + 1) q → y < q → b < q := fun q h1 h2 => not_le.1 (hex q h1 h2)
  split_ifs with hβy h0
  · have hfy : veblen β y = y := hy.veblen_right hβy
    have hyb' : y < b := by
      by_contra hle
      push Not at hle
      exact absurd ((Ordinal.veblen_le_veblen_iff_right.2 hle).trans_eq hfy) (not_le.2 hyb)
    obtain ⟨d, hd⟩ := exists_add_of_le (Order.add_one_le_of_lt hyb')
    have hlow : Cd.cdOtp (qfC' β y) (y + 1) = 0 := phOtp_low _ fun c hc => by
      refine Order.add_one_le_of_lt (lt_of_not_ge fun hcy => ?_)
      exact absurd ((Ordinal.veblen_le_veblen_iff_right.2 hcy).trans_eq hfy) (not_le.2 hc.1)
    have hmem : ∀ z < d, y + 1 + z ∈ qfC' β y := fun z hz => by
      have hyz : y < y + 1 + z := (lt_add_one y).trans_le le_self_add
      have hv : y + 1 + z ≤ veblen β (y + 1 + z) := right_le_veblen _ _
      refine ⟨hyz.trans_le hv, (hβy.trans hyz).trans_le hv, fun hP => ?_⟩
      have h1 := hex' _ hP hyz
      rw [hd] at h1
      exact absurd h1 (not_lt.2 ((add_lt_add_iff_left _).2 hz).le)
    rw [hd, phOtp_shift _ _ d hmem, hlow, zero_add]
  · have hyβ := not_lt.1 hβy
    have hb0 : b ≠ 0 := fun e => by rw [e, h0] at hβb; exact lt_irrefl _ hβb
    obtain ⟨d, hd⟩ := exists_add_of_le (one_le_iff_ne_zero.2 hb0)
    have hlow : Cd.cdOtp (qfC' β y) 1 = 0 := phOtp_low _ fun c hc => by
      refine one_le_iff_ne_zero.2 fun hc0 => ?_
      have h2 := hc.2.1
      rw [hc0, h0] at h2
      exact lt_irrefl _ h2
    have hmem : ∀ z < d, 1 + z ∈ qfC' β y := fun z hz => by
      have hlt : β < veblen β (1 + z) :=
        h0.symm.trans_lt (Ordinal.veblen_lt_veblen_iff_right.2 (lt_of_lt_of_le zero_lt_one le_self_add))
      refine ⟨hyβ.trans_lt hlt, hlt, fun hP => ?_⟩
      have h1 := hex' _ hP ((hyβ.trans_lt hlt).trans_eq (luP_succ.1 hP))
      rw [hd] at h1
      exact absurd h1 (not_lt.2 ((add_lt_add_iff_left _).2 hz).le)
    rw [hd, phOtp_shift _ _ d hmem, hlow, zero_add]
  · have hyβ := not_lt.1 hβy
    have hβ0 : β < veblen β 0 := lt_of_le_of_ne (left_le_veblen β 0) fun e => h0 e.symm
    have hmem : ∀ z < b, 0 + z ∈ qfC' β y := fun z hz => by
      rw [zero_add]
      have hlt : β < veblen β z := hβ0.trans_le (Ordinal.veblen_le_veblen_iff_right.2 zero_le)
      refine ⟨hyβ.trans_lt hlt, hlt, fun hP => ?_⟩
      have h1 := hex' _ hP ((hyβ.trans_lt hlt).trans_eq (luP_succ.1 hP))
      exact absurd h1 (not_lt.2 hz.le)
    have h2 := phOtp_shift (qfC' β y) 0 b hmem
    rw [zero_add, Gg.ggOtp_zero, zero_add] at h2
    rw [zero_add, h2]

section Ind

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

/-- **`Θ_y(x₀(a, θ)) = x₀(Θ_y a, x)`.** -/
theorem aw_Rd_X0 {a : Ordinal.{0}} (ha : GxCl y (awAt S y) a) :
    GxCl y (awAt S y) (awX0 a (ConjT.th S)) ∧
      gxTh y (awAt S y) (awX0 a (ConjT.th S)) = awX0 (gxTh y (awAt S y) a) (awNx y) := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hθc : GxCl y (awAt S y) (ConjT.th S) := GxCl.atom (aw_th_mem y)
  have hθR := aw_Rd_th (S := S) hy hy1
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  have hlt : gxTh y (awAt S y) a < awNx y ↔ a < ConjT.th S := by
    rw [← hθR]
    constructor
    · intro h
      by_contra hle
      exact absurd h (not_lt.2 (gxTh_mono (not_lt.1 hle)))
    · exact gxTh_lt ha
  have h0 : veblen (gxTh y (awAt S y) a) 0 = gxTh y (awAt S y) a ↔ veblen a 0 = a := by
    have hp := gxTh_phi hy hAt a ha 0 (GxCl.zero hy.1)
    rw [gxTh_zero] at hp
    constructor
    · intro h
      rw [h] at hp
      exact aw_Rd_inj hy (GxCl.phi ha (GxCl.zero hy.1)) ha hp
    · intro h
      rw [h] at hp
      exact hp.symm
  unfold awX0
  by_cases h1 : a < ConjT.th S
  · rw [if_pos h1, if_pos (hlt.2 h1), gxTh_add hy hAt hθc 1, hθR, gxTh_small h1lt.le]
    exact ⟨GxCl.add hθc (GxCl.small h1lt), rfl⟩
  · rw [if_neg h1, if_neg (fun h => h1 (hlt.1 h))]
    by_cases h2 : veblen a 0 = a
    · rw [if_pos h2, if_pos (h0.2 h2), gxTh_small h1lt.le]
      exact ⟨GxCl.small h1lt, rfl⟩
    · rw [if_neg h2, if_neg (fun h => h2 (h0.1 h)), gxTh_zero]
      exact ⟨GxCl.zero hy.1, rfl⟩

/-- **`Θ_y(ind(a, θ, b)) = ind(Θ_y a, x, Θ_y b)`**, and the index is a code `≤ b`. -/
theorem aw_Rd_ind {a b : Ordinal.{0}} (ha : GxCl y (awAt S y) a) (hb : GxCl y (awAt S y) b)
    (hab : a < veblen a b) (hbb : b < veblen a b) (hθ : ConjT.th S < veblen a b) :
    GxCl y (awAt S y) (qfInd a (ConjT.th S) b) ∧ qfInd a (ConjT.th S) b ≤ b ∧
      gxTh y (awAt S y) (qfInd a (ConjT.th S) b) =
        qfInd (gxTh y (awAt S y) a) (awNx y) (gxTh y (awAt S y) b) := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hθc : GxCl y (awAt S y) (ConjT.th S) := GxCl.atom (aw_th_mem y)
  have hθR := aw_Rd_th (S := S) hy hy1
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  obtain ⟨-, -, hxS, -, -, -⟩ := awNx_facts hy hy1
  have hφc : GxCl y (awAt S y) (veblen a b) := GxCl.phi ha hb
  have hφR := gxTh_phi hy hAt a ha b hb
  have hxφ : awNx y < veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) b) := by
    rw [← hφR, ← hθR]; exact gxTh_lt hθc hθ
  have huφ : gxTh y (awAt S y) a < veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) b) := by
    rw [← hφR]; exact gxTh_lt ha hab
  by_cases hex : ∃ q, LuP (a + 1) q ∧ ConjT.th S < q ∧ q ≤ b
  · obtain ⟨p, hp⟩ := qf_maxfix hex
    have hpc := aw_maxfix_code hy hy1 b hb p hp
    obtain ⟨hpP, hθp, hpb, hmax⟩ := hp
    have hbP : ¬ LuP (a + 1) b := fun h => hbb.ne (luP_succ.1 h).symm
    have hpb' : p < b := lt_of_le_of_ne hpb fun e => hbP (e ▸ hpP)
    obtain ⟨d, hd⟩ := exists_add_of_le (Order.add_one_le_of_lt hpb')
    have hp1c : GxCl y (awAt S y) (p + 1) := GxCl.add hpc (GxCl.small h1lt)
    have hdc : GxCl y (awAt S y) d := by
      have := (gxDec hy hAt b hb).1 _ hp1c (Order.add_one_le_of_lt hpb')
      rwa [hd, Ordinal.add_sub_cancel] at this
    have hind : qfInd a (ConjT.th S) b = p + d := by
      rw [hd]
      refine qfInd_above' hpP hθp fun z hz hz' => ?_
      have h1 : p + 1 + z ≤ p := hmax _ hz' (hθp.trans ((lt_add_one p).trans_le le_self_add))
        (by rw [hd]; exact ((add_lt_add_iff_left _).2 hz).le)
      exact absurd h1 (not_le.2 ((lt_add_one p).trans_le le_self_add))
    rw [hind]
    refine ⟨GxCl.add hpc hdc, ?_, ?_⟩
    · rw [hd, add_assoc]
      exact add_le_add le_rfl le_add_self
    · have hRp1 : gxTh y (awAt S y) (p + 1) = gxTh y (awAt S y) p + 1 := by
        rw [gxTh_add hy hAt hpc 1, gxTh_small h1lt.le]
      have hRb : gxTh y (awAt S y) b = gxTh y (awAt S y) p + 1 + gxTh y (awAt S y) d := by
        rw [hd, gxTh_add hy hAt hp1c d, hRp1]
      rw [gxTh_add hy hAt hpc d, hRb]
      refine (qfInd_above' (luP_succ.2 ((aw_Rd_fix hy hy1 ha hpc).1 (luP_succ.1 hpP))) ?_ ?_).symm
      · rw [← hθR]; exact gxTh_lt hθc hθp
      · intro z hz hzP
        obtain ⟨d', hd'c, hd'd, rfl⟩ := gxTh_onto hz
        have hc' : GxCl y (awAt S y) (p + 1 + d') := GxCl.add hp1c hd'c
        have hRc : gxTh y (awAt S y) (p + 1 + d') = gxTh y (awAt S y) p + 1 + gxTh y (awAt S y) d' := by
          rw [gxTh_add hy hAt hp1c d', hRp1]
        rw [← hRc] at hzP
        have hfix := (aw_Rd_fix hy hy1 ha hc').2 (luP_succ.1 hzP)
        have h1 : p + 1 + d' ≤ p := hmax _ (luP_succ.2 hfix)
          (hθp.trans ((lt_add_one p).trans_le le_self_add))
          (by rw [hd]; exact ((add_lt_add_iff_left _).2 hd'd).le)
        exact absurd h1 (not_le.2 ((lt_add_one p).trans_le le_self_add))
  · push Not at hex
    have hcode := aw_noFix (ConjT.SC_th S) hθ hab (fun q h1 h2 h3 => absurd h3 (not_le.2 (hex q h1 h2)))
    obtain ⟨hx0c, hx0R⟩ := aw_Rd_X0 (S := S) hy hy1 ha
    have hx0le : awX0 a (ConjT.th S) ≤ b := by
      conv_rhs => rw [hcode]
      exact le_self_add
    have hic : GxCl y (awAt S y) (qfInd a (ConjT.th S) b) := by
      have := (gxDec hy hAt b hb).1 _ hx0c hx0le
      rwa [show b - awX0 a (ConjT.th S) = qfInd a (ConjT.th S) b by
        conv_lhs => rw [hcode]
        exact Ordinal.add_sub_cancel _ _] at this
    refine ⟨hic, by conv_rhs => rw [hcode]
                    exact le_add_self, ?_⟩
    have hval : ∀ q, LuP (gxTh y (awAt S y) a + 1) q → awNx y < q → ¬ q ≤ gxTh y (awAt S y) b := by
      intro q hqP hxq hqb
      have hqφ : veblen (gxTh y (awAt S y) a) q = q := luP_succ.1 hqP
      rcases hqb.lt_or_eq with hlt | rfl
      · obtain ⟨q', hq'c, hq'b, rfl⟩ := gxTh_onto hlt
        have hfix := (aw_Rd_fix hy hy1 ha hq'c).2 hqφ
        have hθq' : ConjT.th S < q' := by
          by_contra hle
          push Not at hle
          have := gxTh_mono (Z := y) (At := awAt S y) hle
          rw [hθR] at this
          exact absurd hxq (not_lt.2 this)
        exact absurd hq'b.le (not_le.2 (hex q' (luP_succ.2 hfix) hθq'))
      · rw [← hφR] at hqφ
        exact absurd hqφ (gxTh_lt hb hbb).ne'
    have hv := aw_noFix hxS hxφ huφ hval
    have hRb := gxTh_add hy hAt hx0c (qfInd a (ConjT.th S) b)
    rw [← hcode, hx0R] at hRb
    exact (add_left_cancel_iff).1 (hRb.symm.trans hv)

/-- **`Θ_y(φ(a, b)) = ϑˣ(Ω₁·Θ_y(a) + Θ_y(ind(a, θ, b)))`** for codes `1 ≤ a`, `b` with `a, b, θ < φ(a, b)`. -/
theorem aw_Rd_phi {a b : Ordinal.{0}} (ha : GxCl y (awAt S y) a) (hb : GxCl y (awAt S y) b) (h1 : 1 ≤ a)
    (hab : a < veblen a b) (hbb : b < veblen a b) (hθ : ConjT.th S < veblen a b) :
    gxTh y (awAt S y) (veblen a b) =
      vt (awNx y) (Om1 * gxTh y (awAt S y) a + gxTh y (awAt S y) (qfInd a (ConjT.th S) b)) := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hθc : GxCl y (awAt S y) (ConjT.th S) := GxCl.atom (aw_th_mem y)
  have hθR := aw_Rd_th (S := S) hy hy1
  have h1lt : (1 : Ordinal.{0}) < y := Gg.gg_one_lt_of_SC hy
  obtain ⟨-, -, hxS, hx1, -, -⟩ := awNx_facts hy hy1
  obtain ⟨-, -, -, hm1, hTm, -⟩ := awNx_facts hxS hx1
  have hφR := gxTh_phi hy hAt a ha b hb
  have hxφ : awNx y < veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) b) := by
    rw [← hφR, ← hθR]; exact gxTh_lt hθc hθ
  have huφ : gxTh y (awAt S y) a < veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) b) := by
    rw [← hφR]; exact gxTh_lt ha hab
  have hvφ : gxTh y (awAt S y) b < veblen (gxTh y (awAt S y) a) (gxTh y (awAt S y) b) := by
    rw [← hφR]; exact gxTh_lt hb hbb
  have hum := aw_Rd_lt (S := S) hy hy1 ha
  have hvm := aw_Rd_lt (S := S) hy hy1 hb
  have hu1 : 1 ≤ gxTh y (awAt S y) a := by
    have := gxTh_mono (Z := y) (At := awAt S y) h1
    rwa [gxTh_small h1lt.le] at this
  obtain ⟨hic, -, hiR⟩ := aw_Rd_ind (S := S) hy hy1 ha hb hab hbb hθ
  have him := aw_Rd_lt (S := S) hy hy1 hic
  rw [hφR, hiR]
  rw [hiR] at him
  exact qf_dict' hxS hx1 hu1 ((hTm _ (hum.trans hm1)).2 hum) (hum.trans hm1) _ hxφ huφ
    (fun h => hvφ.ne (luP_succ.1 h).symm) ((hTm _ (him.trans hm1)).2 him) (him.trans hm1)

end Ind

end Googology.Trans.PoR.InaccPsi.R2.Aw
