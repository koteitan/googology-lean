import Googology.Trans.PoR.InaccPsi.R2.SjCl

/-!
# The second half of the bridge: the closure condition of an atom argument gives `Sg.SgOwnT`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, codes = `Le.LeCl Ω₂ Q`.

* `sjCode_ltT` (a coefficient with the closure condition lies below `T_{G c}`), `sjValCl` (**the value of a term
  with `Sg.SgOwnT` is a code above `T_{e(val)}`**);
* `SjDesc Q e` (**descent along an evaluation**: a code in `[e u, e V)` gives a code in `[u, V)`), `SjTop E e t`
  (`E < e(P + W^{R+1})` for `t = P + W^R·c`);
* `sjWalk` (**the walk through a normal-form term**: at a base with the data of `Sj.sjCode`, if every evaluation
  bottom has the descent property, then `Sg.SgOwnT`: for a limit `η ≤ c` with `T_{G η} ≤ η`, `Sj.sjCode` gives a
  code `z ∈ [G η, E]` over `T_{G η}`, the descent a code `w ∈ [P + W^R·η, P + W^{R+1})`, `w - P` a code because
  `P` is one (its own coefficients are handled first), and the digit `log(w - P) mod Ω₂ ≥ log η ≥ T_{G η}` is a
  code `< Ω₂`, hence `< T_{G η}`: contradiction);
* `sjOwnT` (**THE BRIDGE, SECOND HALF**: `E ∈ H_λ`, `E < ε_{Ω₂+1}`, `E` a code above `T_E`, at a proper base:
  `Sg.SgOwnT β X₀ id (sgTmH E)`), `sjOwn` (with `Sg.sgBridge`: `Sg.SgOwn β X₀ id (sgTmH E)`).

No new axiom.  New definitions: `SjDesc`, `SjTop`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **The descent property of an evaluation `e` at `Q`.** -/
def SjDesc (Q : Ordinal.{0}) (e : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ u V z, LeCl (Om (1 + 1)) Q z → e u ≤ z → z < e V → ∃ w, LeCl (Om (1 + 1)) Q w ∧ u ≤ w ∧ w < V

/-- `E < e(P + W^{R+1})` for the term `P + W^R·c`. -/
def SjTop (E : Ordinal.{0}) (e : Ordinal.{0} → Ordinal.{0}) : SgT → Prop
  | .zero => True
  | .term P R _ => E < e (sgV P + leWe (sgV R + 1))

/-- A coefficient with the closure condition lies below `T_{G c}`. -/
theorem sjCode_ltT {G : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G) {c b X0 : Ordinal.{0}}
    (h : SgLimT S G c b X0) : c < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) := by
  have hT : SC (S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hωT : ω < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) := Lw.lw_omega_lt_SC hT
  have ec : c = ω * (c / ω) + c % ω := (Ordinal.div_add_mod c ω).symm
  have hr : c % ω < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) :=
    (Ordinal.mod_lt c omega0_ne_zero).trans hωT
  rcases eq_or_ne (c / ω) 0 with h0 | h0
  · calc c = c % ω := by conv_lhs => rw [ec, h0, mul_zero, zero_add]
      _ < _ := hr
  have hlim : IsSuccLimit (ω * (c / ω)) := isSuccLimit_mul_left isSuccLimit_omega0 (pos_iff_ne_zero.2 h0)
  have hle : ω * (c / ω) ≤ c := Ordinal.mul_div_le c ω
  have h2 : ω * (c / ω) < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) :=
    (h _ hle hlim).trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (hG hle)))))).1
  calc c = ω * (c / ω) + c % ω := ec
    _ < _ := hT.isPrincipal h2 hr

/-- **The value of a term with `SgOwnT` is a code above `T_{e(val)}`.** -/
theorem sjValCl {l b X0 : Ordinal.{0}} : ∀ (t : SgT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    SgWF S l t → SgOwnT S b X0 e t →
    ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (sgV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (sgV t)
  | .zero, _, _, _, _ => fun Q hQ _ => LeCl.zero hQ.1
  | .term P R c, e, he, ⟨hPw, hRw, _, hc1, _⟩, ⟨hPo, hRo, hco⟩ => by
    intro Q hQ hc'
    have hTmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe (e x))) (Om (1 + 1)) ≤
        S.psi (b + leWe (X0 + leWe (e y))) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (he h)))))).1
    have heR : Monotone (fun r => e (sgV P + leWe r)) := fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hG : Monotone (fun z => e (sgV P + leWe (sgV R) * z)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))
    have hPT := hTmono (show sgV P ≤ sgV (SgT.term P R c) from le_self_add)
    have hRT := hTmono (show sgV P + leWe (sgV R) ≤ sgV (SgT.term P R c) from
      (add_le_add_iff_left _).2 (by simpa using leMulWe_mono (e := sgV R) hc1))
    have hcT : c < S.psi (b + leWe (X0 + leWe (e (sgV (SgT.term P R c))))) (Om (1 + 1)) := sjCode_ltT hG hco
    have hP3 := sjValCl P e he hPw hPo Q hQ (hPT.trans hc')
    have hR3 := sjValCl R _ heR hRw hRo Q hQ (hRT.trans hc')
    exact LeCl.add hP3 (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ hR3) ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))

/-- `SjDesc` at the identity. -/
theorem sjDesc_id (Q : Ordinal.{0}) : SjDesc Q (fun y => y) := fun _ _ z hz h1 h2 => ⟨z, hz, h1, h2⟩

/-- `SjTop` of a term at its own value under the identity. -/
theorem sjTop_self {l : Ordinal.{0}} : ∀ t : SgT, SgWF S l t → SjTop (sgV t) (fun y => y) t
  | .zero, _ => trivial
  | .term P R c, ⟨_, _, _, _, hcW⟩ => by
    show sgV P + leWe (sgV R) * c < sgV P + leWe (sgV R + 1)
    rw [leWe_succ]
    exact (add_lt_add_iff_left _).2 (leMulWe_lt hcW)

section Walk

variable {l : Ordinal.{0}} {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **The walk through a normal-form term.** -/
theorem sjWalk : ∀ (t : SgT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → SgWF S l t → SjNF t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    e (sgV t) ≤ E → SjTop E e t → SgOwnT S β X0 e t
  | .zero, _, _, _, _, _, _, _ => trivial
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPn, hRn, hPR⟩, hD, hEt, hTop => by
    have hTop' : E < e (sgV P + leWe (sgV R + 1)) := hTop
    have hTm : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
        S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono h))))).1
    have hWR : leWe (sgV R) ≤ leWe (sgV R) * c := by simpa using leMulWe_mono (e := sgV R) hc1
    -- (1) the prefix
    have hPle : e (sgV P) ≤ E := (he (le_self_add : sgV P ≤ sgV P + leWe (sgV R) * c)).trans hEt
    have hPtop : SjTop E e P := by
      cases P with
      | zero => trivial
      | term P' R' c' =>
        obtain ⟨-, -, -, -, hc'W⟩ := hPw
        have hRR' : sgV R < sgV R' := hPR.1
        show E < e (sgV P' + leWe (sgV R' + 1))
        refine hTop'.trans_le (he ?_)
        show sgV P' + leWe (sgV R') * c' + leWe (sgV R + 1) ≤ sgV P' + leWe (sgV R' + 1)
        calc sgV P' + leWe (sgV R') * c' + leWe (sgV R + 1)
            ≤ sgV P' + leWe (sgV R') * c' + leWe (sgV R') :=
              (add_le_add_iff_left _).2 (leWe_mono (Order.add_one_le_of_lt hRR'))
          _ = sgV P' + leWe (sgV R') * (c' + 1) := by rw [add_assoc, mul_add_one]
          _ ≤ sgV P' + leWe (sgV R') * Om (1 + 1) :=
              (add_le_add_iff_left _).2 (leMulWe_mono (Order.add_one_le_of_lt hc'W))
          _ = sgV P' + leWe (sgV R' + 1) := by rw [leWe_succ]
    have hPo := sjWalk P e he hPw hPn hD hPle hPtop
    have hPcl := sjValCl P e he hPw hPo
    -- (2) the exponent
    have he' : Monotone (fun r => e (sgV P + leWe r)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e (sgV P + leWe 0)))) (Om (1 + 1)) ≤ Q →
        SjDesc Q (fun r => e (sgV P + leWe r)) := by
      intro Q hQ hQb u V z hz h1 h2
      obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ ((hTm (he zero_le)).trans hQb) _ _ z hz h1 h2
      have hPQ : LeCl (Om (1 + 1)) Q (sgV P) := hPcl Q hQ ((hTm (he le_self_add)).trans hQb)
      have hPw' : sgV P ≤ w := le_self_add.trans hw1
      have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
      have e1 : sgV P + (w - sgV P) = w := Ordinal.add_sub_cancel_of_le hPw'
      have h3 : leWe u ≤ w - sgV P := (add_le_add_iff_left (sgV P)).1 (by rw [e1]; exact hw1)
      have h4 : w - sgV P < leWe V := (add_lt_add_iff_left (sgV P)).1 (by rw [e1]; exact hw2)
      obtain ⟨h5, h6⟩ := sjLogW h3 h4
      exact ⟨_, sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC _ hwP).2, h5, h6⟩
    have hRle : e (sgV P + leWe (sgV R)) ≤ E := (he ((add_le_add_iff_left _).2 hWR)).trans hEt
    have hRtop : SjTop E (fun r => e (sgV P + leWe r)) R := by
      cases R with
      | zero => trivial
      | term R'' R2 c'' =>
        obtain ⟨-, -, -, -, hc''W⟩ := hRw
        show E < e (sgV P + leWe (sgV R'' + leWe (sgV R2 + 1)))
        refine hTop'.trans_le (he ((add_le_add_iff_left _).2 (leWe_mono ?_)))
        show sgV R'' + leWe (sgV R2) * c'' + 1 ≤ sgV R'' + leWe (sgV R2 + 1)
        calc sgV R'' + leWe (sgV R2) * c'' + 1 ≤ sgV R'' + leWe (sgV R2) * c'' + leWe (sgV R2) :=
              (add_le_add_iff_left _).2 (Order.one_le_iff_pos.2 (leWe_pos _))
          _ = sgV R'' + leWe (sgV R2) * (c'' + 1) := by rw [add_assoc, mul_add_one]
          _ ≤ sgV R'' + leWe (sgV R2) * Om (1 + 1) :=
              (add_le_add_iff_left _).2 (leMulWe_mono (Order.add_one_le_of_lt hc''W))
          _ = sgV R'' + leWe (sgV R2 + 1) := by rw [leWe_succ]
    have hRo := sjWalk R _ he' hRw hRn hD' hRle hRtop
    -- (3) the coefficient
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    by_contra hQη
    push Not at hQη
    set y := e (sgV P + leWe (sgV R) * η) with hy_def
    set Q := S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) with hQ_def
    have hQ : SC Q := SC_psi (InR_Om_succ 1) _
    have hyE : y ≤ E := (he ((add_le_add_iff_left _).2 (leMulWe_mono hη))).trans hEt
    obtain ⟨z, hz1, hz2, hz⟩ := sjCode hβd hβown hX0cl hX0G3 hEcl hyE
    have hzV : z < e (sgV P + leWe (sgV R + 1)) := hz2.trans_lt hTop'
    obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ (hTm (he zero_le)) _ _ z hz hz1 hzV
    have hPQ : LeCl (Om (1 + 1)) Q (sgV P) := hPcl Q hQ (hTm (he le_self_add))
    have hPw' : sgV P ≤ w := le_self_add.trans hw1
    have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
    have e1 : sgV P + (w - sgV P) = w := Ordinal.add_sub_cancel_of_le hPw'
    have h3 : leWe (sgV R) * η ≤ w - sgV P := (add_le_add_iff_left (sgV P)).1 (by rw [e1]; exact hw1)
    have h4 : w - sgV P < leWe (sgV R + 1) := (add_lt_add_iff_left (sgV P)).1 (by rw [e1]; exact hw2)
    have hη0 : η ≠ 0 := hlim.ne_bot
    have hm0 : w - sgV P ≠ 0 := (lt_of_lt_of_le (mul_pos (leWe_pos _) (pos_iff_ne_zero.2 hη0)) h3).ne'
    have hL : LeCl (Om (1 + 1)) Q (log ω (w - sgV P)) := (leClDec hQ ldOm2_SC _ hwP).2
    have hL1 : Om (1 + 1) * sgV R + log ω η ≤ log ω (w - sgV P) := by
      refine le_log_of_opow_le one_lt_omega0 ?_
      rw [opow_add]
      exact (mul_le_mul_right (opow_log_le_self ω hη0) _).trans h3
    have hL2 : log ω (w - sgV P) < Om (1 + 1) * sgV R + Om (1 + 1) := by
      have h := (lt_opow_iff_log_lt one_lt_omega0 hm0).1 h4
      rwa [mul_add_one] at h
    have hd : LeCl (Om (1 + 1)) Q (log ω (w - sgV P) % Om (1 + 1)) := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1)) hL
      rwa [gg_SC_eps ldOm2_SC] at h
    have hRL : Om (1 + 1) * sgV R ≤ log ω (w - sgV P) := le_self_add.trans hL1
    have eL : Om (1 + 1) * sgV R + (log ω (w - sgV P) - Om (1 + 1) * sgV R) = log ω (w - sgV P) :=
      Ordinal.add_sub_cancel_of_le hRL
    have hdlt : log ω (w - sgV P) - Om (1 + 1) * sgV R < Om (1 + 1) :=
      (add_lt_add_iff_left _).1 (by rw [eL]; exact hL2)
    have hdge : log ω η ≤ log ω (w - sgV P) - Om (1 + 1) * sgV R :=
      (add_le_add_iff_left _).1 (by rw [eL]; exact hL1)
    have hmod : log ω (w - sgV P) % Om (1 + 1) = log ω (w - sgV P) - Om (1 + 1) * sgV R := by
      conv_lhs => rw [← eL]
      rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdlt]
    rw [hmod] at hd
    have hdQ := LeCl.lt_of_lt hQ hd hdlt
    have hlogQ : log ω Q = Q := by
      conv_lhs => rw [← gg_SC_eps hQ]
      exact log_opow one_lt_omega0 Q
    have hQlog : Q ≤ log ω η := by
      have h := log_mono_right ω hQη
      rwa [hlogQ] at h
    exact absurd (hQlog.trans hdge) (not_le.2 hdQ)

end Walk

section Bridge

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
  (hEH : E ∈ cdHull S l) (hE : E < veblen 1 (Om (1 + 1) + 1))

include hl hX hβd hβown hX0cl hX0G3 hEcl hEH hE

/-- **THE BRIDGE, SECOND HALF: the closure condition of an atom argument gives `SgOwnT`.** -/
theorem sjOwnT : SgOwnT S β X0 (fun y => y) (sgTmH E) := by
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  obtain ⟨-, hn, -⟩ := sjTmH_nf E hE
  have htop := sjTop_self (sgTmH E) hw
  rw [hv] at htop
  exact sjWalk hβd hβown hX0cl hX0G3 hEcl (sgTmH E) (fun y => y) (fun _ _ h => h) hw hn
    (fun Q _ _ => sjDesc_id Q) (by rw [hv]) htop

/-- **The own predicate of the derivation at a proper base from the closure condition.** -/
theorem sjOwn (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) :
    SgOwn S β X0 (fun y => y) (sgTmH E) := by
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  exact sgBridge hl hX (Es := E) hβd hβown hX0m hX0cl hX0G3 (sgTmH E) SgC.hole trivial hw
    trivial (sjOwnT hl hX hβd hβown hX0cl hX0G3 hEcl hEH hE) (by rw [hv]; exact le_rfl)

end Bridge

end Googology.Trans.PoR.InaccPsi.R2.Sj
