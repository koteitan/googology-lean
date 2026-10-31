import Googology.Trans.PoR.InaccPsi.R2.VySup
import Googology.Trans.PoR.InaccPsi.R2.VyOff
import Googology.Trans.PoR.InaccPsi.R2.RxTh
import Googology.Trans.PoR.InaccPsi.R2.LdEQ
import Googology.Trans.PoR.InaccPsi.R2.SfNF
import Googology.Trans.PoR.InaccPsi.R2.SfPv
import Googology.Trans.PoR.InaccPsi.R2.BcName

/-!
# `VyPast` decided by the code level: false at `θ₁ = θ`, and from one reading at `θ_{k+2}`

`ρ = ρ_μ = υ_μ`, `A = A_{η_μ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `θ_{k+1} = Lc.lcTh S (k+1)`,
`C = Vy.vyC S ρ = {c : Ω_ω + θ₂·c ∈ Cl(a, b) for all a > Ω_ω, b ≥ ρ}`, `At_C = Ld.ldAt S (Ω_ω+1) ρ`
(the atoms `ψ_{Ω₂}(x)`, `x ∈ Cl(Ω_ω+1, ρ)`, `x ≤ Ω_ω`), `Θ_C = gxTh ρ At_C`, `g' = ω^{ω^{υ_{μ+1}+1}}`.

`VyPastAt S μ k` (the statement `VyPast` of `Vy` at one restart and one code level): some limit `X ≤ Ω₁` with
`g' + ω²·2 < X`, `η_μ + y` good for `y < X`, and `X ≤ otp(C ∩ θ_{k+1})`.

* `wcMul_mem`, `wcDiv_mem` (**for an `ε`-number `t ∈ Cl(a, b)`: `t·c ∈ Cl(a, b) ⇔ c ∈ Cl(a, b)`**);
* `wcCode_vyC` (**every code over `ρ` with the atoms `At_C` is in `C`**), `wcVyC_hull` (**`C ⊆ Cl(A, ρ)`**, the hull
  of `μ`), `wcOtp_sub` (otp is monotone in the set);
* `wcOtp_le_psi` (**`otp(C ∩ m) ≤ Θ_μ(m) ≤ ψ_{Ω₁}(A + m)` for every `m`**), `wcOtp_th` (**`otp(C ∩ θ) ≤ υ_{μ+1}`**);
* `wcNoPast0` (**NO-GO: `VyPastAt S μ 0` is false at every Range restart `μ` with code `G_{k+1}+1` below `L(ω)`**),
  `wcNoPast0_cof` (such restarts are cofinal below `L(1)`);
* `WcRead0 S μ` (**`υ_{μ+1} ≤ Θ_C(θ)`**), `wcRead0_iff` (`WcRead0 ⇔ Θ_C(θ) = υ_{μ+1}`), `wcRead0_theta`
  (`WcRead0 ⇒ Θ_μ(θ) = υ_{μ+1}`), `wcPast` (**`WcRead0 ⇒ ω^{ω^{υ_{μ+1}+1}+1} ≤ otp(C ∩ θ_{k+2})`**, by the code
  `ω^{ω^{θ+1}+1}` and the `φ`-law of `Θ_C`), `wcGood` (goodness below `υ_{μ+2}`), `wcPastAt` (**`WcRead0 ⇒ VyPastAt S μ
  (k+1)`** at code `G_{k+2}+1**), `wcSup` (**`WcRead0 ⇒ υ_{μ+X} ≤ r(μ)` with `X = ω^{ω^{υ_{μ+1}+1}+1} > g' + ω²·2`**).

New definitions: `VyPastAt`, `WcRead0` (statements), `wcX` (an ordinal term).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## Products with an `ε`-number in the closure -/

theorem wcOpow_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : ω ^ x ∈ S.CSet a b := by
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) hx; rwa [veblen_zero_apply] at this

/-- **`t·c ∈ Cl(a, b)`** for an `ε`-number `t ∈ Cl(a, b)` and `c ∈ Cl(a, b)`. -/
theorem wcMul_mem {a b t : Ordinal.{0}} (ht : ω ^ t = t) (htC : t ∈ S.CSet a b) :
    ∀ c, c ∈ S.CSet a b → t * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [mul_zero]; exact CSet.zero_mem a b
  set L := log ω c with hLdef
  have hL : L ∈ S.CSet a b := (Rx.rxCDec c hc).2
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt c one_lt_omega0)
  have hdec : c = ω ^ L * n + c % ω ^ L := by rw [← hn]; exact (Ordinal.div_add_mod c (ω ^ L)).symm
  have hlead : ω ^ L * n ∈ S.CSet a b := ConjT.mul_nat_mem S (wcOpow_mem hL) n
  have hr : c % ω ^ L ∈ S.CSet a b := by
    have h1 := (Rx.rxCDec c hc).1 _ hlead (by conv_rhs => rw [hdec]
                                              exact le_self_add)
    have h2 : c - ω ^ L * n = c % ω ^ L := by
      conv_lhs => rw [hdec]
      exact Ordinal.add_sub_cancel _ _
    rwa [h2] at h1
  have hrlt : c % ω ^ L < c := mod_opow_log_lt_self ω hc0
  have e : t * c = ω ^ (t + L) * n + t * (c % ω ^ L) := by
    conv_lhs => rw [hdec]
    rw [mul_add, ← mul_assoc, Ls.lsMul_opow ht]
  rw [e]
  exact CSet.add_mem (ConjT.mul_nat_mem S (wcOpow_mem (CSet.add_mem htC hL)) n) (IH _ hrlt hr)

/-- **`t·c ∈ Cl(a, b) ⇒ c ∈ Cl(a, b)`** for an `ε`-number `t ∈ Cl(a, b)`. -/
theorem wcDiv_mem {a b t : Ordinal.{0}} (ht : ω ^ t = t) (htC : t ∈ S.CSet a b) :
    ∀ c, t * c ∈ S.CSet a b → c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact CSet.zero_mem a b
  set L := log ω c with hLdef
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt c one_lt_omega0)
  have hdec : c = ω ^ L * n + c % ω ^ L := by rw [← hn]; exact (Ordinal.div_add_mod c (ω ^ L)).symm
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by rw [← hn]; exact (div_opow_log_pos ω hc0).ne'
  have hrlt' : c % ω ^ L < ω ^ L := Ordinal.mod_lt c (opow_pos L omega0_pos).ne'
  have htr : t * (c % ω ^ L) < ω ^ (t + L) := by
    rw [← Ls.lsMul_opow ht]
    exact (mul_lt_mul_iff_right₀ (show 0 < t by rw [← ht]; exact opow_pos t omega0_pos)).2 hrlt'
  have e : t * c = ω ^ (t + L) * n + t * (c % ω ^ L) := by
    conv_lhs => rw [hdec]
    rw [mul_add, ← mul_assoc, Ls.lsMul_opow ht]
  have hlog : log ω (t * c) = t + L := by
    rw [e, log_opow_mul_add one_lt_omega0 hn0 htr, Ordinal.log_eq_zero (natCast_lt_omega0 n), add_zero]
  have htL : t + L ∈ S.CSet a b := by rw [← hlog]; exact (Rx.rxCDec _ hc).2
  have hL : L ∈ S.CSet a b := by
    have := (Rx.rxCDec _ htL).1 t htC le_self_add
    rwa [Ordinal.add_sub_cancel] at this
  have hlead : ω ^ (t + L) * n ∈ S.CSet a b := ConjT.mul_nat_mem S (wcOpow_mem htL) n
  have htr' : t * (c % ω ^ L) ∈ S.CSet a b := by
    have h1 := (Rx.rxCDec _ hc).1 _ hlead (by rw [e]; exact le_self_add)
    rwa [e, Ordinal.add_sub_cancel] at h1
  have hr := IH _ (mod_opow_log_lt_self ω hc0) htr'
  rw [hdec]
  exact CSet.add_mem (ConjT.mul_nat_mem S (wcOpow_mem hL) n) hr

/-! ## The codes over `ρ` with the atoms of `Cl(Ω_ω + 1, ρ)` -/

/-- The atoms of `At_C` are in every `Cl(a, b)`, `a > Ω_ω`, `b ≥ ρ`. -/
theorem wcAt_mem {ρ a b s : Ordinal.{0}} (hs : s ∈ Ld.ldAt S (Om ω + 1) ρ) (ha : Om ω < a) (hb : ρ ≤ b) :
    s ∈ S.CSet a b := by
  obtain ⟨x, hx, hxlt, rfl⟩ := hs
  have ha1 : Om ω + 1 ≤ a := Order.add_one_le_of_lt ha
  exact CSet.psi_mem (hxlt.trans_le ha1) (InR_Om_succ 1) (mxOm2_mem a b) (CSet_mono ha1 hb hx)

/-- **Every code over `ρ` with the atoms `At_C` is in every `Cl(a, b)`, `a > Ω_ω`, `b ≥ ρ`.** -/
theorem wcCode_mem {ρ c : Ordinal.{0}} (hc : GxCl ρ (Ld.ldAt S (Om ω + 1) ρ) c) :
    ∀ a b, Om ω < a → ρ ≤ b → c ∈ S.CSet a b := by
  intro a b ha hb
  induction hc with
  | small h => exact CSet.of_lt (h.trans_le hb)
  | om => exact CSet.Om_mem (CSet.one_mem a b)
  | atom hs => exact wcAt_mem hs ha hb
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **Every code over `ρ` with the atoms `At_C` is in the code set `C` of `Vy.vySup`.** -/
theorem wcCode_vyC {ρ c : Ordinal.{0}} (hc : GxCl ρ (Ld.ldAt S (Om ω + 1) ρ) c) : c ∈ Vy.vyC S ρ :=
  fun a b ha hb => CSet.add_mem (ConjT.OmW_mem S a b)
    (wcMul_mem (Ls.lsTh_opow 2) (Ls.lsTh_mem ha 2) c (wcCode_mem hc a b ha hb))

/-- **`C ⊆ Cl(A, ρ)`**: a member of the code set is in the hull of `μ` (when `Ω_ω < A`). -/
theorem wcVyC_hull {μ c : Ordinal.{0}} (hA : Om ω < ConjT.Aη S (cdEta S μ)) (hc : c ∈ Vy.vyC S (upsilon μ)) :
    c ∈ cdHull S μ := by
  have h := hc (ConjT.Aη S (cdEta S μ)) (upsilon μ) hA le_rfl
  have h2 : Lc.lcTh S 2 * c ∈ S.CSet (ConjT.Aη S (cdEta S μ)) (upsilon μ) := by
    have := (Rx.rxCDec _ h).1 _ (ConjT.OmW_mem S _ _) le_self_add
    rwa [Ordinal.add_sub_cancel] at this
  exact wcDiv_mem (Ls.lsTh_opow 2) (Ls.lsTh_mem hA 2) c h2

/-- The order type is monotone in the set. -/
theorem wcOtp_sub {A B : Set Ordinal.{0}} (h : A ⊆ B) (m : Ordinal.{0}) : cdOtp A m ≤ cdOtp B m :=
  Vy.vyOtp_of_map (Vy.vyEnum A m) (fun _ hx => h (Vy.vyEnum_spec hx).1)
    (fun _ hx => (Vy.vyEnum_spec hx).2.1) (fun _ _ hyx hx => Vy.vyEnum_lt hx hyx)

/-! ## The upper bound: `otp(C ∩ m) ≤ ψ_{Ω₁}(A + m)` -/

section Upper

variable {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
  (hω : upsilon μ < Nc.ncL S ω)
include hR hc hω

theorem wcX_pv : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
  rw [← Lw.lw_L_eq]; exact hR.2.2.1

/-- `A_{η_μ}` is in its own closure. -/
theorem wcOwn : ConjT.Aη S (cdEta S μ) ∈
    S.CSet (ConjT.Aη S (cdEta S μ)) (S.psi (ConjT.Aη S (cdEta S μ)) (Om 1)) := by
  obtain ⟨hg, -, hpv⟩ := Ra.raName hR
  obtain ⟨n, hn⟩ := Bc.bcC_cof (S := S) _ hω
  have h1 : Nm.Pv S (cdEta S μ) < Bc.bcC S (n + 1) := by
    rw [hpv]; exact hn.trans_le (Bc.bcC_mono (S := S) (Nat.le_succ n))
  exact Sf.sfOwn hg (Sf.sfA_lt h1).2

theorem wcOmW_lt_A : Om ω < ConjT.Aη S (cdEta S μ) := by
  have h0 : (0 : Ordinal.{0}) < upsilon μ := (Le.leRho hR.1 (wcX_pv hR hc hω)).1.1
  have := Ru.ruExp_lt (z := 0) hR hc h0
  rwa [mul_zero, add_zero] at this

/-- **`otp(C ∩ m) ≤ Θ_μ(m) ≤ ψ_{Ω₁}(A + m)` for every `m`.** -/
theorem wcOtp_le_psi (m : Ordinal.{0}) :
    cdOtp (Vy.vyC S (upsilon μ)) m ≤ cdTheta S μ m ∧
      cdTheta S μ m ≤ S.psi (ConjT.Aη S (cdEta S μ) + m) (Om 1) :=
  ⟨wcOtp_sub (fun _ h => wcVyC_hull (wcOmW_lt_A hR hc hω) h) m,
    Ld.ldTheta_le_psi hR.1 (wcX_pv hR hc hω) (wcOwn hR hc hω) m⟩

/-- `υ_{μ+1} = ψ_{Ω₁}(A + θ)`. -/
theorem wcUps1 : upsilon (μ + 1) = S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S) (Om 1) := by
  have h1 : (1 : Ordinal.{0}) ≤ upsilon μ :=
    Order.one_le_iff_pos.2 (Le.leRho hR.1 (wcX_pv hR hc hω)).1.1
  rw [Rg.rgUps_eq hR h1, mul_one]

/-- **`otp(C ∩ θ) ≤ Θ_μ(θ) ≤ υ_{μ+1}`.** -/
theorem wcOtp_th :
    cdOtp (Vy.vyC S (upsilon μ)) (ConjT.th S) ≤ cdTheta S μ (ConjT.th S) ∧
      cdTheta S μ (ConjT.th S) ≤ upsilon (μ + 1) := by
  rw [wcUps1 hR hc hω]; exact wcOtp_le_psi hR hc hω _

end Upper

/-! ## `VyPast` at one restart -/

/-- **`VyPast` at the restart `μ` and the code level `k`**: a limit `X ≤ Ω₁` beyond `g' + ω²·2`, with `η_μ + y` good
below `X`, and `X ≤ otp(C ∩ θ_{k+1})`. -/
def VyPastAt (S : InaccSeq.{0}) (μ : Ordinal.{0}) (k : ℕ) : Prop :=
  ∃ X, IsSuccLimit X ∧ X ≤ Om 1 ∧ ω ^ ω ^ (upsilon (μ + 1) + 1) + ω ^ 2 * 2 < X ∧
    (∀ y < X, Bt.Good S (cdEta S μ + y)) ∧ X ≤ cdOtp (Vy.vyC S (upsilon μ)) (Lc.lcTh S (k + 1))

theorem wc_lcTh1 : Lc.lcTh S (0 + 1) = ConjT.th S := by
  unfold Lc.lcTh ConjT.th; norm_num

theorem wcUps_lt_g (u : Ordinal.{0}) (hu : ω ^ u = u) : u < ω ^ ω ^ (u + 1) + ω ^ 2 * 2 := by
  have h1 : u < ω ^ (u + 1) := by
    conv_lhs => rw [← hu]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one u)
  have h2 : ω ^ (u + 1) ≤ ω ^ ω ^ (u + 1) := right_le_opow _ one_lt_omega0
  exact (h1.trans_le h2).trans_le le_self_add

/-- **NO-GO for `VyPast` at the code level `θ₁ = θ`**: at every Range restart `μ` with a code `G_{k+1}+1` below
`L(ω)`, `otp(C ∩ θ) ≤ υ_{μ+1} < g' + ω²·2`, so `VyPastAt S μ 0` is false. -/
theorem wcNoPast0 {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) : ¬ VyPastAt S μ 0 := by
  rintro ⟨X, -, -, hgt, -, hX⟩
  rw [wc_lcTh1] at hX
  obtain ⟨h1, h2⟩ := wcOtp_th hR hc hω
  have hu : ω ^ upsilon (μ + 1) = upsilon (μ + 1) := by
    have hl : (0 : Ordinal.{0}) < μ + 1 := lt_of_le_of_lt zero_le (lt_add_one μ)
    exact upsPt_inE (upsPt_upsilon hl)
  exact absurd ((hX.trans (h1.trans h2)).trans_lt (wcUps_lt_g _ hu)) (not_lt.2 hgt.le)

/-- **Non-vacuity of `wcNoPast0`**: below `L(1)` the Range restarts with code `G_{k+1}+1` are cofinal
(`Ls.lsNames_L`), and at each of them `VyPastAt S μ 0` is false. -/
theorem wcNoPast0_cof (k : ℕ) : ∀ γ < Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}), ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    cdCode S μ = Ls.lsG S (k + 1) + 1 ∧ ¬ VyPastAt S μ 0 := by
  intro γ hγ
  obtain ⟨μ, hR, hγμ, hlt, hc⟩ := Ls.lsNames_L (S := S) 0 k γ hγ
  have hω : upsilon μ < Nc.ncL S ω := hlt.trans (Bc.bcC_lt (S := S) 0)
  exact ⟨μ, hR, hγμ, hc, wcNoPast0 hR hc hω⟩

/-! ## The positive side at the code levels `θ_{k+2}` -/

/-- **The first reading**: `υ_{μ+1} ≤ Θ_C(θ)` (the codes over `ρ_μ` with the atoms of `Cl(Ω_ω+1, ρ_μ)` below `θ`
have order type at least `υ_{μ+1}`). -/
def WcRead0 (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  upsilon (μ + 1) ≤ gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S)

/-- `X = ω^{ω^{u+1}+1}`. -/
noncomputable def wcX (u : Ordinal.{0}) : Ordinal.{0} := ω ^ (ω ^ (u + 1) + 1)

theorem wcX_gt (u : Ordinal.{0}) : ω ^ ω ^ (u + 1) + ω ^ 2 * 2 < wcX u := by
  have hP := isPrincipal_add_omega0_opow (ω ^ (u + 1) + 1)
  refine hP ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)) ?_
  have h3 : ω ^ 2 * 2 < ω ^ (3 : Ordinal.{0}) := by
    have e : (ω : Ordinal.{0}) ^ (3 : Ordinal.{0}) = ω ^ 2 * ω := by
      rw [show (3 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) + 1 by norm_num, opow_add, opow_one, opow_natCast]
    rw [e]
    exact (mul_lt_mul_iff_right₀ (pow_pos omega0_pos 2)).2 (by exact_mod_cast natCast_lt_omega0 2)
  refine h3.trans_le (opow_le_opow_right omega0_pos ?_)
  have hω3 : (3 : Ordinal.{0}) ≤ ω := (by exact_mod_cast natCast_lt_omega0 3 : (3 : Ordinal.{0}) < ω).le
  exact hω3.trans ((left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u))).trans le_self_add)

theorem wcX_limit (u : Ordinal.{0}) : IsSuccLimit (wcX u) :=
  isSuccLimit_opow_left isSuccLimit_omega0 (by
    intro h; exact absurd h (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one _))))

theorem wcSC_opow {s x : Ordinal.{0}} (hs : SC s) (hx : x < s) : ω ^ x < s := by
  have := hs.2 0 hs.1 x hx; rwa [veblen_zero_apply] at this

theorem wcSC_one {s : Ordinal.{0}} (hs : SC s) : 1 < s := by
  have := wcSC_opow hs hs.1; rwa [opow_zero] at this

theorem wcX_lt_SC {s u : Ordinal.{0}} (hs : SC s) (hu : u < s) : wcX u < s :=
  wcSC_opow hs (hs.isPrincipal (wcSC_opow hs (hs.isPrincipal hu (wcSC_one hs))) (wcSC_one hs))

section Pos

variable {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
  (hc : cdCode S μ = Ls.lsG S (k + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω)
include hR hc hω

/-- **`WcRead0 ⇔ Θ_C(θ) = υ_{μ+1}`** (the codes of `At_C` lie in `C`, and `otp(C ∩ θ) ≤ υ_{μ+1}`). -/
theorem wcRead0_iff : WcRead0 S μ ↔
    gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S) = upsilon (μ + 1) := by
  have hle : gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) (ConjT.th S) ≤ upsilon (μ + 1) := by
    obtain ⟨h1, h2⟩ := wcOtp_th hR hc hω
    exact (wcOtp_sub (fun _ h => wcCode_vyC h) _).trans (h1.trans h2)
  exact ⟨fun h => le_antisymm hle h, fun h => h.ge⟩

/-- **`WcRead0 ⇒ Θ_μ(θ) = υ_{μ+1}`**: the reading of `θ` by the full hull is then exactly `υ_{μ+1}`. -/
theorem wcRead0_theta (hr : WcRead0 S μ) : cdTheta S μ (ConjT.th S) = upsilon (μ + 1) := by
  obtain ⟨h1, h2⟩ := wcOtp_th hR hc hω
  refine le_antisymm h2 (hr.trans ?_)
  exact (wcOtp_sub (fun _ h => wcCode_vyC h) _).trans h1

/-- **`WcRead0 ⇒ ω^{ω^{υ_{μ+1}+1}+1} ≤ otp(C ∩ θ_{k+2})`**: the codes below `ω^{ω^{θ+1}+1} < Ω₂ < θ_{k+2}` read up to
`ω^{ω^{Θ_C(θ)+1}+1}` (`φ`-law). -/
theorem wcPast (hr : WcRead0 S μ) :
    wcX (upsilon (μ + 1)) ≤ cdOtp (Vy.vyC S (upsilon μ)) (Lc.lcTh S (k + 1 + 1)) := by
  have hX := wcX_pv hR hc hω
  obtain ⟨hZ, hZ1⟩ := Le.leRho hR.1 hX
  set Z := upsilon μ with hZdef
  set At := Ld.ldAt S (Om ω + 1) Z with hAtdef
  have hAt : GxAt At := Ld.ldAt_GxAt _ _
  have hθ : GxCl Z At (ConjT.th S) :=
    GxCl.atom ⟨Om ω, ConjT.OmW_mem S _ _, lt_add_one _, rfl⟩
  have hZ1' : (1 : Ordinal.{0}) < Z := wcSC_one hZ
  have h1 : GxCl Z At 1 := GxCl.small hZ1'
  have hθ1 : GxCl Z At (ConjT.th S + 1) := GxCl.add hθ h1
  have hw : GxCl Z At (ω ^ (ConjT.th S + 1)) := GxCl.opow hZ.1 hθ1
  have hw1 : GxCl Z At (ω ^ (ConjT.th S + 1) + 1) := GxCl.add hw h1
  set m0 := ω ^ (ω ^ (ConjT.th S + 1) + 1) with hm0
  have hm0C : GxCl Z At m0 := GxCl.opow hZ.1 hw1
  have hg1 : gxTh Z At 1 = 1 := gxTh_small hZ1'.le
  have hread : gxTh Z At m0 = wcX (gxTh Z At (ConjT.th S)) := by
    rw [hm0, gxTh_opow hZ hAt hw1, gxTh_add hZ hAt hw, gxTh_opow hZ hAt hθ1, gxTh_add hZ hAt hθ, hg1]
    rfl
  have hle : wcX (upsilon (μ + 1)) ≤ gxTh Z At m0 := by
    rw [hread]
    exact opow_le_opow_right omega0_pos
      (add_le_add_left (opow_le_opow_right omega0_pos (add_le_add_left hr 1)) 1)
  -- `m0 < Ω₂ < θ_{k+2}`
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hm0lt : m0 < Om (1 + 1) := wcX_lt_SC Ld.ldOm2_SC hθ2
  have hOm2 : Om (1 + 1 : Ordinal.{0}) < Lc.lcTh S (k + 1 + 1) := by
    have h := (psiS_bounds (S := S) (Om ω) ((k + 1 + 1 : ℕ) : Ordinal.{0})).1
    refine (Om_le_Om.2 ?_).trans_lt h
    have : ((1 + 1 : ℕ) : Ordinal.{0}) ≤ ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by
      exact_mod_cast (show 1 + 1 ≤ k + 1 + 1 by omega)
    simpa using this
  refine Vy.vyOtp_of_map (Ru.ruInv Z At) (fun x hx => ?_) (fun x hx => ?_) (fun y x hyx hx => ?_)
  · exact wcCode_vyC (Ru.ruInv_spec (hx.trans_le hle)).1
  · exact ((Ru.ruInv_spec (hx.trans_le hle)).2.1.trans hm0lt).trans hOm2
  · exact Ru.ruInv_lt (hx.trans_le hle) hyx

/-- **Goodness below `υ_{μ+2}`**: `η_μ + y` is good for every `y < ω^{ω^{υ_{μ+1}+1}+1}`. -/
theorem wcGood : ∀ y < wcX (upsilon (μ + 1)), Bt.Good S (cdEta S μ + y) := by
  obtain ⟨hg, -, hpv⟩ := Ra.raName hR
  set η := cdEta S μ with hηdef
  have hE : ∀ e, 1 < Nm.Pv S e := fun e => So.soOne_lt_E (Sl.slPv_E (S := S) e)
  have hg1 : Bt.Good S (η + 1) := Rz.rz_good_shift hg (hE _)
  have hu : upsilon (μ + 1) = Nm.Pv S (η + 1) := by
    rw [wcUps1 hR hc hω]
    show _ = S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ConjT.A_succ]
  have h12 : Nm.Pv S (η + 1) < Nm.Pv S (η + 1 + 1) := Nm.Pv_lt_succ hg1
  have hXlt : wcX (upsilon (μ + 1)) < Nm.Pv S (η + 1 + 1) := by
    rw [hu]; exact wcX_lt_SC (Nm.Pv_SC S _) h12
  intro y hy
  refine Rz.rz_good_shift hg ?_
  rcases lt_or_ge y 2 with h2 | h2
  · have h2le : (2 : Ordinal.{0}) ≤ Nm.Pv S (η + y) := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact Order.add_one_le_of_lt (hE _)
    exact h2.trans_le h2le
  · have hle : η + 1 + 1 ≤ η + y := by
      rw [add_assoc, one_add_one_eq_two]; exact (add_le_add_iff_left η).2 h2
    exact (hy.trans hXlt).trans_le (Nm.Pv_mono hle)

/-- **`WcRead0 ⇒ VyPastAt S μ (k+1)`** with `X = ω^{ω^{υ_{μ+1}+1}+1}`. -/
theorem wcPastAt (hr : WcRead0 S μ) : VyPastAt S μ (k + 1) := by
  have hX := wcX_pv hR hc hω
  have hu1 : upsilon (μ + 1) < Om 1 := by
    rw [wcUps1 hR hc hω]; exact psi_lt Low.InR_Om_one _
  exact ⟨wcX (upsilon (μ + 1)), wcX_limit _, (wcX_lt_SC Ph.ph_SC_Om1 hu1).le, wcX_gt _,
    wcGood hR hc hω, wcPast hR hc hω hr⟩

/-- **THE SUPPLY PAST THE FIRST INNER `υ`-POINT FROM `WcRead0`**: `υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)` with
`X = ω^{ω^{υ_{μ+1}+1}+1} > g' + ω²·2`. -/
theorem wcSup (hr : WcRead0 S μ) :
    ω ^ ω ^ (upsilon (μ + 1) + 1) + ω ^ 2 * 2 < wcX (upsilon (μ + 1)) ∧
      upsilon (μ + wcX (upsilon (μ + 1))) ≤ cdTheta S μ (Ls.lsG S (k + 1 + 1)) ∧
      upsilon (μ + wcX (upsilon (μ + 1))) ≤ cdR S μ := by
  have hu1 : upsilon (μ + 1) < Om 1 := by
    rw [wcUps1 hR hc hω]; exact psi_lt Low.InR_Om_one _
  exact ⟨wcX_gt _, Vy.vySup (k + 1) hR hc (wcX_limit _) (wcGood hR hc hω)
    (wcX_lt_SC Ph.ph_SC_Om1 hu1).le (wcPast hR hc hω hr)⟩

end Pos

#print axioms wcMul_mem
#print axioms wcDiv_mem
#print axioms wcCode_vyC
#print axioms wcVyC_hull
#print axioms wcOtp_le_psi
#print axioms wcOtp_th
#print axioms wcNoPast0
#print axioms wcNoPast0_cof
#print axioms wcRead0_iff
#print axioms wcRead0_theta
#print axioms wcPast
#print axioms wcGood
#print axioms wcPastAt
#print axioms wcSup

end Googology.Trans.PoR.InaccPsi.R2.Wc
