import Googology.Trans.PoR.InaccPsi.R2.QfTB0
import Googology.Trans.PoR.InaccPsi.R2.QfImg

/-!
# QfTB: `Tᵖ[σ]` IS CLOSED UNDER THE COUNTABLE VALUES OF `φ` (`Qf.QfTBphi`)

For `υ`-points `σ < ρ`: a Veblen point `X = φ(a, b) ∈ (ρ, Ω₁)` is `ϑᵖ(Ω₁·a + ind(b))` (`Qf.qf_dict'`), and the index
`ind(b)` and `b` differ by the largest fixed point `p` of `φ_a` in `(ρ, b]` (`b = p + 1 + d`, `ind(b) = p + d`) or by a
constant (`0`, `1`, `ρ + 1`).  By one induction on `x ∈ Tᵖ[σ]`:

* (F) the largest fixed point `p` of `φ_β` in `(ρ, x]` is in `Tᵖ[σ]`: it is the largest `ε`-number `e ≤ x`
  (`R2.base_TB`), or `e = φ(a', b')` with `a' ≤ β` is no fixed point and `p` is the largest one in `(ρ, b']`;
* (★) the parts `a, b` of `x = φ(a, b)` are in `Tᵖ[σ]` (`Qf.qf_glA_TB_inv` and (F) at the index).

Then `φ(a, b) ∈ Tᵖ[σ]` for `a, b ∈ Tᵖ[σ]` with `ρ < φ(a, b) < Ω₁` (`Gl.glA_pi` with (F) at `b`).

* `QfMaxFix`, `qf_maxfix` (the largest fixed point exists), `qfInd_above'`, `qf_ind_struct` (**`b = p + 1 + d`,
  `ind(b) = p + d`, or `b = x₀ + ind(b)`, `x₀ ∈ {0, 1, ρ + 1}`**);
* `qf_rho_SC`, `qf_TB_const`, `qf_TB_ind` (**(★) and (F)**; (F) through `R2.base_TB`, the largest `ε`-number `e ≤ x`,
  and `e = φ(a', b')`), `qf_TB_veblen`, `qf_TBphi` (**`QfTBphi`**), `qf_imgH_all` (**`Qd.QdImgH`**).

No new axiom.  New definition: `QfMaxFix`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ph

/-- **`p` is the largest fixed point of `φ_β` in `(ρ, x]`.** -/
def QfMaxFix (β ρ x p : Ordinal.{0}) : Prop :=
  LuP (β + 1) p ∧ ρ < p ∧ p ≤ x ∧ ∀ q, LuP (β + 1) q → ρ < q → q ≤ x → q ≤ p

/-- The largest fixed point exists when some fixed point lies in `(ρ, x]`. -/
theorem qf_maxfix {β ρ x : Ordinal.{0}} (hne : ∃ q, LuP (β + 1) q ∧ ρ < q ∧ q ≤ x) : ∃ p, QfMaxFix β ρ x p := by
  classical
  set F := {q | LuP (β + 1) q ∧ ρ < q ∧ q ≤ x} with hF
  have hbdd : BddAbove F := ⟨x, fun q hq => hq.2.2⟩
  have hne' : F.Nonempty := hne
  refine ⟨sSup F, ?_, ?_, csSup_le hne' fun q hq => hq.2.2, fun q h1 h2 h3 => le_csSup hbdd ⟨h1, h2, h3⟩⟩
  · refine luP_succ.2 ?_
    rw [(isNormal_veblen β).map_sSup hne' hbdd]
    congr 1
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩; rw [luP_succ.1 hw.1]; exact hw
    · intro hv; exact ⟨v, hv, luP_succ.1 hv.1⟩
  · obtain ⟨q, hq⟩ := hne
    exact hq.2.1.trans_le (le_csSup hbdd hq)

/-- **`qfInd(p + 1 + δ) = p + δ`** above a fixed point `p > y` of `φ_β` with none in `(p, p + 1 + δ)`. -/
theorem qfInd_above' {β y p δ : Ordinal.{0}} (hP : LuP (β + 1) p) (hyp : y < p)
    (h : ∀ z < δ, ¬ LuP (β + 1) (p + 1 + z)) : qfInd β y (p + 1 + δ) = p + δ := by
  have hβp : β ≤ p := (left_le_veblen β p).trans_eq (luP_succ.1 hP)
  have e1 : cdOtp (qfC' β y) p = cdOtp (qfC' β y) (p + 1) :=
    cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact hc.2.2 (hcp' ▸ hP)
  have e2 : cdOtp (qfC' β y) p = p := qfInd_P p hP hyp
  have hmem : ∀ z < δ, p + 1 + z ∈ qfC' β y := fun z hz => by
    have hpz : p < p + 1 + z := (lt_add_one p).trans_le le_self_add
    have hv : p + 1 + z ≤ veblen β (p + 1 + z) := right_le_veblen _ _
    exact ⟨hyp.trans (hpz.trans_le hv), (hβp.trans_lt hpz).trans_le hv, h z hz⟩
  show cdOtp (qfC' β y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ hmem, ← e1, e2]

/-- **The index and the argument differ by the largest fixed point or by a constant**: `b = p + 1 + d` and
`ind(b) = p + d` for the largest fixed point `p` of `φ_β` in `(y, b]`, or `b = x₀ + ind(b)` with `x₀ ∈ {0, 1, y + 1}`. -/
theorem qf_ind_struct {β y b : Ordinal.{0}} (hy : SC y) (hyb : y < veblen β b) (hβb : β < veblen β b)
    (hbP : ¬ LuP (β + 1) b) :
    (∃ p d, QfMaxFix β y b p ∧ b = p + 1 + d ∧ qfInd β y b = p + d) ∨
      ∃ x₀, (x₀ = 0 ∨ x₀ = 1 ∨ x₀ = y + 1) ∧ b = x₀ + qfInd β y b := by
  by_cases hex : ∃ q, LuP (β + 1) q ∧ y < q ∧ q ≤ b
  · left
    obtain ⟨p, hp⟩ := qf_maxfix hex
    obtain ⟨hpP, hyp, hpb, hmax⟩ := hp
    have hpb' : p < b := lt_of_le_of_ne hpb fun e => hbP (e ▸ hpP)
    obtain ⟨d, hd⟩ := exists_add_of_le (Order.add_one_le_of_lt hpb')
    refine ⟨p, d, ⟨hpP, hyp, hpb, hmax⟩, hd, ?_⟩
    rw [hd]
    refine qfInd_above' hpP hyp fun z hz hz' => ?_
    have h1 : p + 1 + z ≤ p := hmax _ hz' (hyp.trans ((lt_add_one p).trans_le le_self_add))
      (by rw [hd]; exact ((add_lt_add_iff_left _).2 hz).le)
    exact absurd h1 (not_le.2 ((lt_add_one p).trans_le le_self_add))
  · right
    push Not at hex
    rcases lt_or_ge β y with hβy | hyβ
    · have hfy : veblen β y = y := hy.veblen_right hβy
      have hyb' : y < b := by
        by_contra hle
        push Not at hle
        exact absurd ((veblen_le_veblen_iff_right.2 hle).trans_eq hfy) (not_le.2 hyb)
      obtain ⟨d, hd⟩ := exists_add_of_le (Order.add_one_le_of_lt hyb')
      refine ⟨y + 1, Or.inr (Or.inr rfl), ?_⟩
      have hlow : cdOtp (qfC' β y) (y + 1) = 0 := phOtp_low _ fun c hc => by
        refine Order.add_one_le_of_lt (lt_of_not_ge fun hcy => ?_)
        exact absurd ((veblen_le_veblen_iff_right.2 hcy).trans_eq hfy) (not_le.2 hc.1)
      have hmem : ∀ z < d, y + 1 + z ∈ qfC' β y := fun z hz => by
        have hyz : y < y + 1 + z := (lt_add_one y).trans_le le_self_add
        have hv : y + 1 + z ≤ veblen β (y + 1 + z) := right_le_veblen _ _
        refine ⟨hyz.trans_le hv, (hβy.trans hyz).trans_le hv, fun hP => ?_⟩
        have h1 := hex _ hP hyz
        rw [hd] at h1
        exact absurd h1 (not_lt.2 ((add_lt_add_iff_left _).2 hz).le)
      show b = y + 1 + cdOtp (qfC' β y) b
      rw [hd, phOtp_shift _ _ d hmem, hlow, zero_add]
    · by_cases h0 : veblen β 0 = β
      · have hb0 : b ≠ 0 := fun e => by rw [e, h0] at hβb; exact lt_irrefl _ hβb
        obtain ⟨d, hd⟩ := exists_add_of_le (one_le_iff_ne_zero.2 hb0)
        refine ⟨1, Or.inr (Or.inl rfl), ?_⟩
        have hlow : cdOtp (qfC' β y) 1 = 0 := phOtp_low _ fun c hc => by
          refine one_le_iff_ne_zero.2 fun hc0 => ?_
          have h2 := hc.2.1
          rw [hc0, h0] at h2
          exact lt_irrefl _ h2
        have hmem : ∀ z < d, 1 + z ∈ qfC' β y := fun z hz => by
          have hlt : β < veblen β (1 + z) :=
            h0.symm.trans_lt (veblen_lt_veblen_iff_right.2 (lt_of_lt_of_le zero_lt_one le_self_add))
          refine ⟨hyβ.trans_lt hlt, hlt, fun hP => ?_⟩
          have h1 := hex _ hP ((hyβ.trans_lt hlt).trans_eq (luP_succ.1 hP))
          rw [hd] at h1
          exact absurd h1 (not_lt.2 ((add_lt_add_iff_left _).2 hz).le)
        show b = 1 + cdOtp (qfC' β y) b
        rw [hd, phOtp_shift _ _ d hmem, hlow, zero_add]
      · have hβ0 : β < veblen β 0 := lt_of_le_of_ne (left_le_veblen β 0) fun e => h0 e.symm
        refine ⟨0, Or.inl rfl, ?_⟩
        have hmem : ∀ z < b, 0 + z ∈ qfC' β y := fun z hz => by
          rw [zero_add]
          have hlt : β < veblen β z := hβ0.trans_le (veblen_le_veblen_iff_right.2 zero_le)
          refine ⟨hyβ.trans_lt hlt, hlt, fun hP => ?_⟩
          have h1 := hex _ hP ((hyβ.trans_lt hlt).trans_eq (luP_succ.1 hP))
          exact absurd h1 (not_lt.2 hz.le)
        have h2 := phOtp_shift (qfC' β y) 0 b hmem
        rw [zero_add, ggOtp_zero, zero_add] at h2
        show b = 0 + cdOtp (qfC' β y) b
        rw [zero_add, h2]

section Main

variable {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
include hσ hρ hB

omit hσ in
/-- The base `ρ` is strongly critical (a `υ`-point above the `ε`-number `σ`). -/
theorem qf_rho_SC : SC ρ := Qc.qc_ups_SC ρ hρ hB.2.2.2 σ hB.1 hB.2.2.1

omit hσ hρ in
/-- The constants `0`, `1`, `ρ + 1` are in `Tᵖ[σ]`. -/
theorem qf_TB_const {x₀ : Ordinal.{0}} (h : x₀ = 0 ∨ x₀ = 1 ∨ x₀ = ρ + 1) : x₀ ∈ TB ρ σ := by
  rcases h with rfl | rfl | rfl
  · exact qf_TB_zero hB
  · exact (one_TB hB).1
  · exact (pi_add hB (pi_base hB).1 (one_TB hB).1).1

/-- **(★) and (F) by one induction on `x ∈ Tᵖ[σ] ∩ Ω₁`**: the parts `a, b` of `x = φ(a, b)` (`1 ≤ a < x`,
`b < x`, `ρ < x`) are in `Tᵖ[σ]`, and so is the largest fixed point of every `φ_β` in `(ρ, x]`. -/
theorem qf_TB_ind : ∀ x, x ∈ TB ρ σ → x < Om1 →
    (∀ a b, veblen a b = x → 1 ≤ a → a < x → b < x → ρ < x → a ∈ TB ρ σ ∧ b ∈ TB ρ σ) ∧
      (∀ β p, QfMaxFix β ρ x p → p ∈ TB ρ σ) := by
  have hρS : SC ρ := qf_rho_SC hρ hB
  have hρE : InE ρ := hB.2.1
  have hρ1 : ρ < Om1 := hB.2.2.2
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hx1
  -- (★): the parts of a Veblen point
  have hS : ∀ a b, veblen a b = x → 1 ≤ a → a < x → b < x → ρ < x → a ∈ TB ρ σ ∧ b ∈ TB ρ σ := by
    intro a b hab ha1 hax hbx hρx
    have haT : a ∈ Tset ρ := vz_T_down hρE hρ1 hx.1 hx1 hax.le
    have haΩ : a < Om1 := hax.trans hx1
    have hyb : ρ < veblen a b := hab ▸ hρx
    have hab' : a < veblen a b := hab ▸ hax
    have hbP : ¬ LuP (a + 1) b := fun hP => by
      rw [luP_succ.1 hP] at hab; exact absurd hab hbx.ne
    have hib : qfInd a ρ b ≤ b := cdOtp_le_self _ b
    have hix : qfInd a ρ b < x := hib.trans_lt hbx
    have hiT : qfInd a ρ b ∈ Tset ρ := vz_T_down hρE hρ1 hx.1 hx1 hix.le
    have hi1 : qfInd a ρ b < Om1 := hix.trans hx1
    have hd := qf_dict' hρS hρ1 ha1 haT haΩ b hyb hab' hbP hiT hi1
    rw [hab] at hd
    obtain ⟨haTB, hiTB⟩ := qf_glA_TB_inv hσ hρ hB ha1 haT haΩ hiT hi1 (by rw [← hd]; exact hx)
    refine ⟨haTB, ?_⟩
    rcases qf_ind_struct hρS hyb hab' hbP with ⟨p, d, ⟨hpP, hρp, -, hmax⟩, hbd, hid⟩ | ⟨x₀, hx₀, hbx₀⟩
    · have hpi : p ≤ qfInd a ρ b := by rw [hid]; exact le_self_add
      have hpTB : p ∈ TB ρ σ := (IH _ hix hiTB hi1).2 a p ⟨hpP, hρp, hpi,
        fun q hq hρq hqi => hmax q hq hρq (hqi.trans hib)⟩
      obtain ⟨hdTB, -⟩ := TB_sub hB hpTB hiTB hpi hi1
      rw [hid, Ordinal.add_sub_cancel] at hdTB
      rw [hbd]
      exact (pi_add hB (pi_add hB hpTB (one_TB hB).1).1 hdTB).1
    · rw [hbx₀]; exact (pi_add hB (qf_TB_const hB hx₀) hiTB).1
  refine ⟨hS, fun β p hp => ?_⟩
  -- (F): the largest fixed point of `φ_β` in `(ρ, x]`
  obtain ⟨hpP, hρp, hpx, hmax⟩ := hp
  have hpE : InE p := lu_P_E hpP
  have hρx : ρ ≤ x := (hρp.trans_le hpx).le
  obtain ⟨c, -, hm1, hm2⟩ := evA_bracket hρE hρx
    (show x < evA ρ (x + 1) from lt_of_lt_of_le (lt_add_one x) (le_evA_idx ρ _))
  set e := evA ρ c with hedef
  have heE : InE e := evA_E _ _
  have heE' : ω ^ e = e := heE
  have heTB : e ∈ TB ρ σ := base_TB hB x hx hρx hx1 c hm1 hm2
  have hpe : p ≤ e := by
    by_contra hlt
    push Not at hlt
    exact absurd ((evA_succ_le hlt hpE).trans hpx) (not_le.2 hm2)
  by_cases hfix : veblen β e = e
  · rw [le_antisymm hpe (hmax e (luP_succ.2 hfix) (hρp.trans_le hpe) hm1)]; exact heTB
  have hpe' : p < e := lt_of_le_of_ne hpe fun h => hfix (by rw [← h]; exact luP_succ.1 hpP)
  have hβp : β ≤ p := (left_le_veblen β p).trans_eq (luP_succ.1 hpP)
  have hβe : β < e := hβp.trans_lt hpe'
  -- `e = φ(a', b')` in Veblen normal form
  set a' := invVeblen₁ e with ha'
  set b' := invVeblen₂ e with hb'
  have hdec : veblen a' b' = e := by rw [ha', hb', veblen_invVeblen₁_invVeblen₂, heE']
  have hb'e : b' < e := by have := invVeblen₂_lt e; rwa [heE'] at this
  have ha1 : 1 ≤ a' := by
    refine one_le_iff_ne_zero.2 fun h0 => ?_
    have h2 := hdec
    rw [h0, veblen_zero_apply] at h2
    have h3 : ω ^ b' = ω ^ e := h2.trans heE'.symm
    have h4 := (opow_right_inj one_lt_omega0).1 h3
    rw [h4] at hb'e
    exact lt_irrefl _ hb'e
  have ha'e : a' < e := by
    refine lt_of_le_of_ne ((left_le_veblen a' b').trans_eq hdec) fun h => ?_
    have hfix0 : veblen e 0 = e := by
      refine le_antisymm ?_ (left_le_veblen e 0)
      calc veblen e 0 ≤ veblen e b' := veblen_le_veblen_iff_right.2 zero_le
        _ = veblen a' b' := by rw [h]
        _ = e := hdec
    exact hfix ((qf_SC_of_fix heE.pos hfix0).veblen_right hβe)
  have hβa' : a' ≤ β := by
    by_contra hlt
    push Not at hlt
    exact hfix (by rw [← hdec]; exact veblen_veblen_of_lt hlt _)
  have hpa' : veblen a' p = p := by
    rcases hβa'.lt_or_eq with hlt | heq
    · rw [← luP_succ.1 hpP]; exact veblen_veblen_of_lt hlt p
    · rw [heq]; exact luP_succ.1 hpP
  have hpb' : p < b' := by
    have h1 : veblen a' p < veblen a' b' := by rw [hpa', hdec]; exact hpe'
    exact veblen_lt_veblen_iff_right.1 h1
  -- (★) at `e ≤ x`, then (F) at `b' < e`
  have hρe : ρ < e := hρp.trans hpe'
  have hpart : a' ∈ TB ρ σ ∧ b' ∈ TB ρ σ := by
    rcases hm1.lt_or_eq with hlt | heq
    · exact (IH e hlt heTB (hlt.trans hx1)).1 a' b' hdec ha1 ha'e hb'e hρe
    · exact hS a' b' (hdec.trans heq) ha1 (ha'e.trans_eq heq) (hb'e.trans_eq heq) (hρe.trans_eq heq)
  have hb'x : b' < x := hb'e.trans_le hm1
  exact (IH b' hb'x hpart.2 (hb'x.trans hx1)).2 β p ⟨hpP, hρp, hpb'.le,
    fun q hq hρq hqb => hmax q hq hρq (hqb.trans hb'x.le)⟩

/-- **`Tᵖ[σ]` is closed under the countable values of `φ` above `ρ`.** -/
theorem qf_TB_veblen {a b : Ordinal.{0}} (ha : a ∈ TB ρ σ) (hb : b ∈ TB ρ σ) (hρX : ρ < veblen a b)
    (hX1 : veblen a b < Om1) : veblen a b ∈ TB ρ σ := by
  have hρS : SC ρ := qf_rho_SC hρ hB
  have hρ1 : ρ < Om1 := hB.2.2.2
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply] at hX1 ⊢
    exact (pi_opowZ hσ hρ hB hb ((right_le_opow b one_lt_omega0).trans_lt hX1)).1
  have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
  by_cases hea : a = veblen a b
  · rw [← hea]; exact ha
  have hab : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) hea
  by_cases heb : b = veblen a b
  · rw [← heb]; exact hb
  have hbb : b < veblen a b := lt_of_le_of_ne (right_le_veblen a b) heb
  have haΩ : a < Om1 := hab.trans hX1
  have hb1 : b < Om1 := hbb.trans hX1
  have hbP : ¬ LuP (a + 1) b := fun hP => heb (luP_succ.1 hP).symm
  have hib : qfInd a ρ b ≤ b := cdOtp_le_self _ b
  have hi1 : qfInd a ρ b < Om1 := hib.trans_lt hb1
  have hiTB : qfInd a ρ b ∈ TB ρ σ := by
    rcases qf_ind_struct hρS hρX hab hbP with ⟨p, d, hp, hbd, hid⟩ | ⟨x₀, hx₀, hbx₀⟩
    · have hpTB : p ∈ TB ρ σ := (qf_TB_ind hσ hρ hB b hb hb1).2 a p hp
      have hp1 : p + 1 ∈ TB ρ σ := (pi_add hB hpTB (one_TB hB).1).1
      obtain ⟨hdTB, -⟩ := TB_sub hB hp1 hb (by rw [hbd]; exact le_self_add) hb1
      rw [hbd, Ordinal.add_sub_cancel] at hdTB
      rw [hid]; exact (pi_add hB hpTB hdTB).1
    · obtain ⟨hTB, -⟩ := TB_sub hB (qf_TB_const hB hx₀) hb (by rw [hbx₀]; exact le_self_add) hb1
      rwa [hbx₀, Ordinal.add_sub_cancel] at hTB
  have hd := qf_dict' hρS hρ1 ha1 ha.1 haΩ b hρX hab hbP hiTB.1 hi1
  rw [hd]
  exact (Gl.glA_pi hB ha haΩ hiTB hi1).1

end Main

/-- **`QfTBphi`.** -/
theorem qf_TBphi : QfTBphi := fun _ _ _ _ hσ hρ hB ha hb hρX hX1 => qf_TB_veblen hσ hρ hB ha hb hρX hX1

/-- **LEMMA IMG BELOW `ϑ^ρ(Ω₁·N)` AT EVERY VEBLEN LEVEL** `Ω₁ ≤ N < Γ_{Ω₁+1}`, with no hypothesis left. -/
theorem qf_imgH_all : Qd.QdImgH := qf_imgH qf_TBphi

end Googology.Trans.PoR.InaccPsi.R2.Qf
