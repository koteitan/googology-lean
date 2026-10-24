import Googology.Trans.PoR.InaccPsi.R2.SwNF

/-!
# The bridge with leaves: the closure condition gives the level statement at every `1 ≤ E < ε_{Ω₂+ω}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, codes = `Le.LeCl Ω₂ Q`,
`CL E b X₀ = Sn.SnCL S E b X₀` (`E` a code over every strongly critical `Q ≥ T_E(b, X₀)`), `Θ̂ = Sw.swTh`.

* `SwOwnT` (`Sg.SgLimT` at every coefficient, `True` at the leaves), `swBridge` (**`SwOwnT` gives `SwOwn` at a
  proper base**, `Sg.sgSq_supAt` on the path shapes `Sw.swShp_path`);
* `swValCl`, `SwTopT`, `swWalk` (**the walk through a normal-form term**: as `Sj.sjWalk`; a leaf has no
  coefficient), `swOwnT` (**the closure condition of `E` gives `SwOwnT` of its normal-form term**);
* `swLevT_all` (**THE TOP LAW AT EVERY `1 ≤ E < ε_{Ω₂+ω}` OF `H_λ` UNDER THE CLOSURE CONDITION**:
  `Θ(ψ_{Ω₂}(β + W^{X₀ + W^E})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Θ̂ E}})`), `swLev` (**`Sc.ScLev (CL E) E (Θ̂ E)`**).

No new axiom.  New definitions: `SwOwnT`, `SwTopT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

/-- **The closure condition at every coefficient of a term.** -/
def SwOwnT (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → SwT → Prop
  | _, .zero => True
  | _, .eps _ => True
  | e, .term P R c => SwOwnT S b X0 e P ∧ SwOwnT S b X0 (fun r => e (swV P + leWe r)) R ∧
      SgLimT S (fun z => e (swV P + leWe (swV R) * z)) c b X0

/-- `E < e(P + W^{R+1})` for the term `P + W^R·c`. -/
def SwTopT (E : Ordinal.{0}) (e : Ordinal.{0} → Ordinal.{0}) : SwT → Prop
  | .zero => True
  | .eps _ => True
  | .term P R _ => E < e (swV P + leWe (swV R + 1))

variable {S : InaccSeq.{0}}

section Bridge

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {β X0 Es : Ordinal.{0}}
  (hβd : leWe (X0 + leWe Es) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe Es) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe Es < S.psi 0 (Om (1 + 1 + 1)))

include hl hX hβd hβown hX0m hX0cl hX0G3

/-- **THE BRIDGE: the closure condition gives the derivation's own predicate at a proper base.** -/
theorem swBridge : ∀ (t : SwT) (K : SwC), SwWFC S l K → SwWF S l t → SwOwnC S β X0 K →
    SwOwnT S β X0 (swE K) t → swE K (swV t) ≤ Es → SwOwn S β X0 (swE K) t
  | .zero, _, _, _, _, _, _ => trivial
  | .eps _, _, _, _, _, _, _ => trivial
  | .term P R c, K, hKw, ⟨hPw, hRw, hc, hc1, hcW⟩, hKo, ⟨hPT, hRT, hcT⟩, hEs => by
    have hPle : swE K (swV P) ≤ Es := (swE_mono K (le_self_add : swV P ≤ swV P + leWe (swV R) * c)).trans hEs
    have hPo := swBridge P K hKw hPw hKo hPT hPle
    have hKPo : SwOwnC S β X0 (SwC.pfx K P) := ⟨hKo, hPo⟩
    have hRle : swE (SwC.lft (SwC.pfx K P)) (swV R) ≤ Es := by
      refine (swE_mono K ((add_le_add_iff_left _).2 ?_)).trans hEs
      simpa using leMulWe_mono (e := swV R) hc1
    have hRo := swBridge R (SwC.lft (SwC.pfx K P)) ⟨hKw, hPw⟩ hRw hKPo hRT hRle
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    have hsh := swShp_path hl hX (K := SwC.pfx K P) (F := R) ⟨hKw, hPw⟩ hRw hKPo hRo
    set g : Ordinal.{0} → Ordinal.{0} := fun z => swE (SwC.pfx K P) (leWe (swV R) * z) with hg
    have hGst : StrictMono (fun z => leWe (g z)) := fun _ _ h => leWe_lt (hsh.st h)
    have hgη : g η ≤ Es := (swE_mono (SwC.pfx K P) (leMulWe_mono hη)).trans hEs
    have hd1 : (1 : Ordinal.{0}) ≤ Om 1 := (gg_one_lt_of_SC Ph.ph_SC_Om1).le
    have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (hsh.st.monotone hd1)))))).1
    have hWle : leWe (X0 + leWe (g η)) ≤ leWe (X0 + leWe Es) :=
      leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hgη))
    exact sgSq_supAt (G := fun z => leWe (g z)) (Gs := leWe (swE (SwC.pfx K P) (leWe (swV R + 1)))) hGst
      (fun d hd => hβown d (hd.trans hWle)) hX0m
      (fun x c' hx hc' => leWe_mem (hsh.mem x c' hx (hbot.trans hc')))
      (fun x hx => leWe_mono (hsh.lt x hx).le)
      (fun Q hQ hc' => scShCl_lift hQ hsh.inf (hsh.cl Q hQ (hbot.trans hc')))
      ((leWe_dvd ((add_le_add_iff_left X0).2 (leWe_mono hgη))).trans hβd) hX0cl
      (lt_of_le_of_lt ((add_le_add_iff_left X0).2 (leWe_mono hgη)) hX0G3)
      (hcT η hη hlim)

end Bridge

/-- **The value of a term with `SwOwnT` is a code above `T_{e(val)}`.** -/
theorem swValCl {l b X0 : Ordinal.{0}} : ∀ (t : SwT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    SwWF S l t → SwOwnT S b X0 e t →
    ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (swV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (swV t)
  | .zero, _, _, _, _ => fun Q hQ _ => LeCl.zero hQ.1
  | .eps k, _, _, _, _ => fun Q hQ _ => swL_cl hQ k
  | .term P R c, e, he, ⟨hPw, hRw, _, hc1, _⟩, ⟨hPo, hRo, hco⟩ => by
    intro Q hQ hc'
    have hTmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe (e x))) (Om (1 + 1)) ≤
        S.psi (b + leWe (X0 + leWe (e y))) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (he h)))))).1
    have heR : Monotone (fun r => e (swV P + leWe r)) := fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hG : Monotone (fun z => e (swV P + leWe (swV R) * z)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))
    have hPT := hTmono (show swV P ≤ swV (SwT.term P R c) from le_self_add)
    have hRT := hTmono (show swV P + leWe (swV R) ≤ swV (SwT.term P R c) from
      (add_le_add_iff_left _).2 (by simpa using leMulWe_mono (e := swV R) hc1))
    have hcT : c < S.psi (b + leWe (X0 + leWe (e (swV (SwT.term P R c))))) (Om (1 + 1)) := sjCode_ltT hG hco
    have hP3 := swValCl P e he hPw hPo Q hQ (hPT.trans hc')
    have hR3 := swValCl R _ heR hRw hRo Q hQ (hRT.trans hc')
    exact LeCl.add hP3 (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ hR3) ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))

/-- `SwTopT` of a term at its own value under the identity. -/
theorem swTopT_self {l : Ordinal.{0}} : ∀ t : SwT, SwWF S l t → SwTopT (swV t) (fun y => y) t
  | .zero, _ => trivial
  | .eps _, _ => trivial
  | .term P R c, ⟨_, _, _, _, hcW⟩ => by
    show swV P + leWe (swV R) * c < swV P + leWe (swV R + 1)
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

/-- **The walk through a normal-form term with leaves.** -/
theorem swWalk : ∀ (t : SwT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → SwWF S l t → SwNF t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    e (swV t) ≤ E → SwTopT E e t → SwOwnT S β X0 e t
  | .zero, _, _, _, _, _, _, _ => trivial
  | .eps _, _, _, _, _, _, _, _ => trivial
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPn, hRn, hPR⟩, hD, hEt, hTop => by
    have hTop' : E < e (swV P + leWe (swV R + 1)) := hTop
    have hTm : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
        S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono h))))).1
    have hWR : leWe (swV R) ≤ leWe (swV R) * c := by simpa using leMulWe_mono (e := swV R) hc1
    -- (1) the prefix
    have hPle : e (swV P) ≤ E := (he (le_self_add : swV P ≤ swV P + leWe (swV R) * c)).trans hEt
    have hPtop : SwTopT E e P := by
      cases P with
      | zero => trivial
      | eps _ => trivial
      | term P' R' c' =>
        obtain ⟨-, -, -, -, hc'W⟩ := hPw
        have hRR' : swV R < swV R' := hPR.1
        show E < e (swV P' + leWe (swV R' + 1))
        refine hTop'.trans_le (he ?_)
        show swV P' + leWe (swV R') * c' + leWe (swV R + 1) ≤ swV P' + leWe (swV R' + 1)
        calc swV P' + leWe (swV R') * c' + leWe (swV R + 1)
            ≤ swV P' + leWe (swV R') * c' + leWe (swV R') :=
              (add_le_add_iff_left _).2 (leWe_mono (Order.add_one_le_of_lt hRR'))
          _ = swV P' + leWe (swV R') * (c' + 1) := by rw [add_assoc, mul_add_one]
          _ ≤ swV P' + leWe (swV R') * Om (1 + 1) :=
              (add_le_add_iff_left _).2 (leMulWe_mono (Order.add_one_le_of_lt hc'W))
          _ = swV P' + leWe (swV R' + 1) := by rw [leWe_succ]
    have hPo := swWalk P e he hPw hPn hD hPle hPtop
    have hPcl := swValCl P e he hPw hPo
    -- (2) the exponent
    have he' : Monotone (fun r => e (swV P + leWe r)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e (swV P + leWe 0)))) (Om (1 + 1)) ≤ Q →
        SjDesc Q (fun r => e (swV P + leWe r)) := by
      intro Q hQ hQb u V z hz h1 h2
      obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ ((hTm (he zero_le)).trans hQb) _ _ z hz h1 h2
      have hPQ : LeCl (Om (1 + 1)) Q (swV P) := hPcl Q hQ ((hTm (he le_self_add)).trans hQb)
      have hPw' : swV P ≤ w := le_self_add.trans hw1
      have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
      have e1 : swV P + (w - swV P) = w := Ordinal.add_sub_cancel_of_le hPw'
      have h3 : leWe u ≤ w - swV P := (add_le_add_iff_left (swV P)).1 (by rw [e1]; exact hw1)
      have h4 : w - swV P < leWe V := (add_lt_add_iff_left (swV P)).1 (by rw [e1]; exact hw2)
      obtain ⟨h5, h6⟩ := sjLogW h3 h4
      exact ⟨_, sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC _ hwP).2, h5, h6⟩
    have hRle : e (swV P + leWe (swV R)) ≤ E := (he ((add_le_add_iff_left _).2 hWR)).trans hEt
    have hRtop : SwTopT E (fun r => e (swV P + leWe r)) R := by
      cases R with
      | zero => trivial
      | eps _ => trivial
      | term R'' R2 c'' =>
        obtain ⟨-, -, -, -, hc''W⟩ := hRw
        show E < e (swV P + leWe (swV R'' + leWe (swV R2 + 1)))
        refine hTop'.trans_le (he ((add_le_add_iff_left _).2 (leWe_mono ?_)))
        show swV R'' + leWe (swV R2) * c'' + 1 ≤ swV R'' + leWe (swV R2 + 1)
        calc swV R'' + leWe (swV R2) * c'' + 1 ≤ swV R'' + leWe (swV R2) * c'' + leWe (swV R2) :=
              (add_le_add_iff_left _).2 (Order.one_le_iff_pos.2 (leWe_pos _))
          _ = swV R'' + leWe (swV R2) * (c'' + 1) := by rw [add_assoc, mul_add_one]
          _ ≤ swV R'' + leWe (swV R2) * Om (1 + 1) :=
              (add_le_add_iff_left _).2 (leMulWe_mono (Order.add_one_le_of_lt hc''W))
          _ = swV R'' + leWe (swV R2 + 1) := by rw [leWe_succ]
    have hRo := swWalk R _ he' hRw hRn hD' hRle hRtop
    -- (3) the coefficient
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    by_contra hQη
    push Not at hQη
    set y := e (swV P + leWe (swV R) * η) with hy_def
    set Q := S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) with hQ_def
    have hQ : SC Q := SC_psi (InR_Om_succ 1) _
    have hyE : y ≤ E := (he ((add_le_add_iff_left _).2 (leMulWe_mono hη))).trans hEt
    obtain ⟨z, hz1, hz2, hz⟩ := sjCode hβd hβown hX0cl hX0G3 hEcl hyE
    have hzV : z < e (swV P + leWe (swV R + 1)) := hz2.trans_lt hTop'
    obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ (hTm (he zero_le)) _ _ z hz hz1 hzV
    have hPQ : LeCl (Om (1 + 1)) Q (swV P) := hPcl Q hQ (hTm (he le_self_add))
    have hPw' : swV P ≤ w := le_self_add.trans hw1
    have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
    have e1 : swV P + (w - swV P) = w := Ordinal.add_sub_cancel_of_le hPw'
    have h3 : leWe (swV R) * η ≤ w - swV P := (add_le_add_iff_left (swV P)).1 (by rw [e1]; exact hw1)
    have h4 : w - swV P < leWe (swV R + 1) := (add_lt_add_iff_left (swV P)).1 (by rw [e1]; exact hw2)
    have hη0 : η ≠ 0 := hlim.ne_bot
    have hm0 : w - swV P ≠ 0 := (lt_of_lt_of_le (mul_pos (leWe_pos _) (pos_iff_ne_zero.2 hη0)) h3).ne'
    have hL : LeCl (Om (1 + 1)) Q (log ω (w - swV P)) := (leClDec hQ ldOm2_SC _ hwP).2
    have hL1 : Om (1 + 1) * swV R + log ω η ≤ log ω (w - swV P) := by
      refine le_log_of_opow_le one_lt_omega0 ?_
      rw [opow_add]
      exact (mul_le_mul_right (opow_log_le_self ω hη0) _).trans h3
    have hL2 : log ω (w - swV P) < Om (1 + 1) * swV R + Om (1 + 1) := by
      have h := (lt_opow_iff_log_lt one_lt_omega0 hm0).1 h4
      rwa [mul_add_one] at h
    have hd : LeCl (Om (1 + 1)) Q (log ω (w - swV P) % Om (1 + 1)) := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1)) hL
      rwa [gg_SC_eps ldOm2_SC] at h
    have hRL : Om (1 + 1) * swV R ≤ log ω (w - swV P) := le_self_add.trans hL1
    have eL : Om (1 + 1) * swV R + (log ω (w - swV P) - Om (1 + 1) * swV R) = log ω (w - swV P) :=
      Ordinal.add_sub_cancel_of_le hRL
    have hdlt : log ω (w - swV P) - Om (1 + 1) * swV R < Om (1 + 1) :=
      (add_lt_add_iff_left _).1 (by rw [eL]; exact hL2)
    have hdge : log ω η ≤ log ω (w - swV P) - Om (1 + 1) * swV R :=
      (add_le_add_iff_left _).1 (by rw [eL]; exact hL1)
    have hmod : log ω (w - swV P) % Om (1 + 1) = log ω (w - swV P) - Om (1 + 1) * swV R := by
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

section All

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The closure condition of `E < ε_{Ω₂+ω}` at a proper base gives the own predicate of its normal-form term.** -/
theorem swOwn_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < swTop S) : SwOwn S β X0 (fun y => y) (swTm E) := by
  obtain ⟨hw, hv⟩ := swTm_spec hl hX E hEH hE
  obtain ⟨-, hn, -⟩ := swTm_nf (S := S) E hE
  have htop := swTopT_self (swTm E) hw
  rw [hv] at htop
  have hT : SwOwnT S β X0 (fun y => y) (swTm E) :=
    swWalk hβd hβown hX0cl hX0G3 hEcl (swTm E) (fun y => y) (fun _ _ h => h) hw hn
      (fun Q _ _ => sjDesc_id Q) (by rw [hv]) htop
  exact swBridge hl hX (Es := E) hβd hβown hX0m hX0cl hX0G3 (swTm E) SwC.hole trivial hw trivial hT
    (by rw [hv]; exact le_rfl)

/-- **THE LEVEL STATEMENT AT EVERY `1 ≤ E < ε_{Ω₂+ω}` OF `H_λ` WITH THE CLOSURE CONDITION**:
`Sc.ScLev (CL E) E (Θ̂ E)`. -/
theorem swLev {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < swTop S) :
    ScLev S l (Sn.SnCL S E) E (swTh S l E) := by
  obtain ⟨hw, hv⟩ := swTm_spec hl hX E hEH hE
  have hL := swLev_term hl hX (swTm E) hw (by rw [hv]; exact hE1)
  rw [hv] at hL
  intro b X0 Xh0 hoff hd hG3 hG hcl β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb'
  rw [add_zero] at hβd hβown
  have hOw : SwOwn S β X0 (fun y => y) (swTm E) :=
    swOwn_of_cl hl hX hβd hβown hX0m hX0cl (le_self_add.trans_lt hG3)
      (fun Q hQ hQ' => hcl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hbβ _)).1.trans hQ')) hEH hE
  exact hL β X0 Xh0 hoffβ hd hG3 hG hOw β Â hb le_rfl hÂ hbase

end All

end Googology.Trans.PoR.InaccPsi.R2.Sw
