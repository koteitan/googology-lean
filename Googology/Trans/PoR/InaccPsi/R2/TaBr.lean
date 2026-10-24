import Googology.Trans.PoR.InaccPsi.R2.TaNF

/-!
# The bridge with Veblen nodes: the closure condition gives the level statement at every `1 ≤ E < E_Γ`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, codes = `Le.LeCl Ω₂ Q`,
`CL E b X₀ = Sn.SnCL S E b X₀` (`E` a code over every strongly critical `Q ≥ T_E(b, X₀)`), `Θ̂ = Ta.taTh`,
`E_Γ = φ(Γ₀, Ω₂ + 1)` (`Ta.taTop`).

* `TaOwnT` (`Sg.SgLimT` at every coefficient, through the nodes), `taBridge` (**`TaOwnT` gives `TaOwn` at a
  proper base**, `Sg.sgSq_supAt` on the path shapes `Ta.taShp_path`);
* `taValCl`, `TaTopT`, `taUB` (the upper bound of a term), `taDesc_node` (**the descent property passes through
  a node**: the index of a code is a code, `Ta.taCl_idx`), `taWalk` (**the walk through a normal-form term**),
  `taOwn_of_cl` (**the closure condition of `E` gives `TaOwn` of its normal-form term**);
* `taLev` (**THE LEVEL STATEMENT `Sc.ScLev (CL E) E (Θ̂ E)` AT EVERY `1 ≤ E < E_Γ` OF `H_λ`**).

No new axiom.  New definitions: `TaOwnT`, `TaTopT`, `taUB`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

/-- **The closure condition at every coefficient of a term.** -/
def TaOwnT (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => TaOwnT S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R c => TaOwnT S b X0 e P ∧ TaOwnT S b X0 (fun r => e (taV P + leWe r)) R ∧
      SgLimT S (fun z => e (taV P + leWe (taV R) * z)) c b X0

/-- `E < e(P + W^{R+1})` for the term `P + W^R·c`, through the nodes. -/
def TaTopT (E : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => TaTopT E (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R _ => E < e (taV P + leWe (taV R + 1))

/-- **The upper bound of a term**: `P + W^{R+1}` for `P + W^R·c`, through the nodes. -/
noncomputable def taUB : TaT → Ordinal.{0}
  | .zero => 1
  | .phi a Y => veblen a (Om (1 + 1) + taUB Y)
  | .term P R _ => taV P + leWe (taV R + 1)

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
theorem taBridge : ∀ (t : TaT) (K : TaC), TaWFC S l K → TaWF S l t → TaOwnC S β X0 K →
    TaOwnT S β X0 (taE K) t → taE K (taV t) ≤ Es → TaOwn S β X0 (taE K) t
  | .zero, _, _, _, _, _, _ => trivial
  | .phi a Y, K, hKw, ⟨ha, hYw, _, _⟩, hKo, hT, hEs => taBridge Y (TaC.phi K a) ⟨hKw, ha⟩ hYw hKo hT hEs
  | .term P R c, K, hKw, ⟨hPw, hRw, hc, hc1, hcW⟩, hKo, ⟨hPT, hRT, hcT⟩, hEs => by
    have hPle : taE K (taV P) ≤ Es := (taE_mono K (le_self_add : taV P ≤ taV P + leWe (taV R) * c)).trans hEs
    have hPo := taBridge P K hKw hPw hKo hPT hPle
    have hKPo : TaOwnC S β X0 (TaC.pfx K P) := ⟨hKo, hPo⟩
    have hRle : taE (TaC.lft (TaC.pfx K P)) (taV R) ≤ Es := by
      refine (taE_mono K ((add_le_add_iff_left _).2 ?_)).trans hEs
      simpa using leMulWe_mono (e := taV R) hc1
    have hRo := taBridge R (TaC.lft (TaC.pfx K P)) ⟨hKw, hPw⟩ hRw hKPo hRT hRle
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    have hsh := (taShp_path hl hX (K := TaC.pfx K P) (F := R) ⟨hKw, hPw⟩ hRw hKPo hRo).shp
    set g : Ordinal.{0} → Ordinal.{0} := fun z => taE (TaC.pfx K P) (leWe (taV R) * z) with hg
    have hGst : StrictMono (fun z => leWe (g z)) := fun _ _ h => leWe_lt (hsh.st h)
    have hgη : g η ≤ Es := (taE_mono (TaC.pfx K P) (leMulWe_mono hη)).trans hEs
    have hd1 : (1 : Ordinal.{0}) ≤ Om 1 := (gg_one_lt_of_SC Ph.ph_SC_Om1).le
    have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (hsh.st.monotone hd1)))))).1
    have hWle : leWe (X0 + leWe (g η)) ≤ leWe (X0 + leWe Es) :=
      leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hgη))
    exact sgSq_supAt (G := fun z => leWe (g z)) (Gs := leWe (taE (TaC.pfx K P) (leWe (taV R + 1)))) hGst
      (fun d hd => hβown d (hd.trans hWle)) hX0m
      (fun x c' hx hc' => leWe_mem (hsh.mem x c' hx (hbot.trans hc')))
      (fun x hx => leWe_mono (hsh.lt x hx).le)
      (fun Q hQ hc' => scShCl_lift hQ hsh.inf (hsh.cl Q hQ (hbot.trans hc')))
      ((leWe_dvd ((add_le_add_iff_left X0).2 (leWe_mono hgη))).trans hβd) hX0cl
      (lt_of_le_of_lt ((add_le_add_iff_left X0).2 (leWe_mono hgη)) hX0G3)
      (hcT η hη hlim)

end Bridge

/-- **The value of a term with `TaOwnT` is a code above `T_{e(val)}`.** -/
theorem taValCl {l b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TaWF S l t → TaOwnT S b X0 e t →
    ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (taV t)
  | .zero, _, _, _, _ => fun Q hQ _ => LeCl.zero hQ.1
  | .phi a Y, e, he, ⟨ha, hYw, _, _⟩, hT => fun Q hQ hc' =>
    LeCl.phi (LeCl.small (taSm_lt_SC ha hQ))
      (LeCl.add LeCl.om (taValCl Y _ (fun _ _ h => he (taNode_mono _ a h)) hYw hT Q hQ hc'))
  | .term P R c, e, he, ⟨hPw, hRw, _, hc1, _⟩, ⟨hPo, hRo, hco⟩ => by
    intro Q hQ hc'
    have hTmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe (e x))) (Om (1 + 1)) ≤
        S.psi (b + leWe (X0 + leWe (e y))) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (he h)))))).1
    have heR : Monotone (fun r => e (taV P + leWe r)) := fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hG : Monotone (fun z => e (taV P + leWe (taV R) * z)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))
    have hPT := hTmono (show taV P ≤ taV (TaT.term P R c) from le_self_add)
    have hRT := hTmono (show taV P + leWe (taV R) ≤ taV (TaT.term P R c) from
      (add_le_add_iff_left _).2 (by simpa using leMulWe_mono (e := taV R) hc1))
    have hcT : c < S.psi (b + leWe (X0 + leWe (e (taV (TaT.term P R c))))) (Om (1 + 1)) := sjCode_ltT hG hco
    have hP3 := taValCl P e he hPw hPo Q hQ (hPT.trans hc')
    have hR3 := taValCl R _ heR hRw hRo Q hQ (hRT.trans hc')
    exact LeCl.add hP3 (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ hR3) ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))

/-- `TaTopT` of a term at its own value under a strictly monotone evaluation. -/
theorem taTopT_self {l : Ordinal.{0}} : ∀ t : TaT, TaWF S l t → ∀ e : Ordinal.{0} → Ordinal.{0}, StrictMono e →
    TaTopT (e (taV t)) e t
  | .zero, _, _, _ => trivial
  | .phi a Y, ⟨_, hYw, _, _⟩, e, he =>
    taTopT_self Y hYw _ (fun _ _ h => he ((veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 h)))
  | .term P R c, ⟨_, _, _, _, hcW⟩, e, he => by
    show e (taV P + leWe (taV R) * c) < e (taV P + leWe (taV R + 1))
    exact he ((add_lt_add_iff_left _).2 (rvWe_lt_succ hcW))

/-- An upper bound gives `TaTopT`. -/
theorem taTopT_of_ub {E : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), E < e (taUB t) → TaTopT E e t
  | .zero, _, _ => trivial
  | .phi _ Y, _, h => taTopT_of_ub Y _ h
  | .term _ _ _, _, h => h

/-- The value of a well-formed term is below its upper bound. -/
theorem taV_lt_ub {l : Ordinal.{0}} : ∀ t : TaT, TaWF S l t → taV t < taUB t
  | .zero, _ => zero_lt_one
  | .phi _ Y, ⟨_, hYw, _, _⟩ => (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 (taV_lt_ub Y hYw))
  | .term _ _ _, ⟨_, _, _, _, hcW⟩ => (add_lt_add_iff_left _).2 (rvWe_lt_succ hcW)

/-- A node prefix `P = φ(a, Ω₂ + Y)` with an exponent `r < P` after it: `P + W^{r+1} < ub P`. -/
theorem taPhi_ub {l a r : Ordinal.{0}} {Y : TaT} (hw : TaWF S l (TaT.phi a Y)) (hr : r < taV (TaT.phi a Y)) :
    taV (TaT.phi a Y) + leWe (r + 1) < taUB (TaT.phi a Y) := by
  obtain ⟨ha, hYw, hY1, _⟩ := hw
  have hlt := taV_lt_ub (TaT.phi a Y) ⟨ha, hYw, hY1, ‹_›⟩
  have hp := Ph.ph_veblen_prin a (Om (1 + 1) + taUB Y)
  have hlim : IsSuccLimit (taV (TaT.phi a Y)) := taVeb_lim (taSm_ne0 ha)
  have hW : leWe (r + 1) < taV (TaT.phi a Y) := by
    have h := leWe_lt (hlim.add_one_lt hr)
    have e : leWe (taV (TaT.phi a Y)) = taV (TaT.phi a Y) := taWe_veb (taSm_ne0 ha) hY1
    rwa [e] at h
  exact hp hlt (hW.trans hlt)

/-- **The descent property passes through a node.** -/
theorem taDesc_node {Q a : Ordinal.{0}} (hQ : SC Q) (ha : TaSm a) {e : Ordinal.{0} → Ordinal.{0}}
    (hD : SjDesc Q e) : SjDesc Q (fun y => e (veblen a (Om (1 + 1) + y))) := by
  intro u V z hz h1 h2
  obtain ⟨w, hw, hw1, hw2⟩ := hD _ _ z hz h1 h2
  have h0 : veblen a 0 ≤ w := ((veblen_le_veblen_iff_right).2 zero_le).trans hw1
  obtain ⟨u', hu', hu1, hu2⟩ := taCl_idx ldOm2_SC (taSm_lt_Om2 ha) w hw h0
  have hlo : Om (1 + 1) + u ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (hw1.trans_lt hu2))
  have hhi : u' < Om (1 + 1) + V := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hw2)
  have hΩu' : Om (1 + 1) ≤ u' := le_self_add.trans hlo
  have hV0 : 0 < V := pos_iff_ne_zero.2 fun h => by
    rw [h, add_zero] at hhi; exact absurd hΩu' (not_le.2 hhi)
  exact ⟨u' - Om (1 + 1), (leClDec hQ ldOm2_SC u' hu').1 _ LeCl.om hΩu', Ordinal.le_sub_of_add_le hlo,
    Ordinal.sub_lt_of_lt_add hhi hV0⟩

section Walk

variable {l : Ordinal.{0}} {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **The walk through a normal-form term with Veblen nodes.** -/
theorem taWalk : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TaWF S l t → TaNF t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    e (taV t) ≤ E → TaTopT E e t → TaOwnT S β X0 e t
  | .zero, _, _, _, _, _, _, _ => trivial
  | .phi a Y, e, he, ⟨ha, hYw, _, _⟩, hn, hD, hEt, hTop =>
    taWalk Y (fun y => e (veblen a (Om (1 + 1) + y))) (fun _ _ h => he (taNode_mono _ a h)) hYw hn
      (fun Q hQ hQb => taDesc_node hQ ha (hD Q hQ ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (he zero_le)))))).1.trans hQb))) hEt hTop
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPn, hRn, hPR⟩, hD, hEt, hTop => by
    have hTop' : E < e (taV P + leWe (taV R + 1)) := hTop
    have hTm : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
        S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono h))))).1
    have hWR : leWe (taV R) ≤ leWe (taV R) * c := by simpa using leMulWe_mono (e := taV R) hc1
    -- (1) the prefix
    have hPle : e (taV P) ≤ E := (he (le_self_add : taV P ≤ taV P + leWe (taV R) * c)).trans hEt
    have hPtop : TaTopT E e P := by
      cases P with
      | zero => trivial
      | phi a' Y' => exact taTopT_of_ub _ _ (hTop'.trans_le (he (taPhi_ub hPw hPR).le))
      | term P' R' c' =>
        obtain ⟨-, -, -, -, hc'W⟩ := hPw
        have hRR' : taV R < taV R' := hPR.1
        show E < e (taV P' + leWe (taV R' + 1))
        refine hTop'.trans_le (he ?_)
        show taV P' + leWe (taV R') * c' + leWe (taV R + 1) ≤ taV P' + leWe (taV R' + 1)
        calc taV P' + leWe (taV R') * c' + leWe (taV R + 1)
            ≤ taV P' + leWe (taV R') * c' + leWe (taV R') :=
              (add_le_add_iff_left _).2 (leWe_mono (Order.add_one_le_of_lt hRR'))
          _ = taV P' + leWe (taV R') * (c' + 1) := by rw [add_assoc, mul_add_one]
          _ ≤ taV P' + leWe (taV R') * Om (1 + 1) :=
              (add_le_add_iff_left _).2 (leMulWe_mono (Order.add_one_le_of_lt hc'W))
          _ = taV P' + leWe (taV R' + 1) := by rw [leWe_succ]
    have hPo := taWalk P e he hPw hPn hD hPle hPtop
    have hPcl := taValCl P e he hPw hPo
    -- (2) the exponent
    have he' : Monotone (fun r => e (taV P + leWe r)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e (taV P + leWe 0)))) (Om (1 + 1)) ≤ Q →
        SjDesc Q (fun r => e (taV P + leWe r)) := by
      intro Q hQ hQb u V z hz h1 h2
      obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ ((hTm (he zero_le)).trans hQb) _ _ z hz h1 h2
      have hPQ : LeCl (Om (1 + 1)) Q (taV P) := hPcl Q hQ ((hTm (he le_self_add)).trans hQb)
      have hPw' : taV P ≤ w := le_self_add.trans hw1
      have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
      have e1 : taV P + (w - taV P) = w := Ordinal.add_sub_cancel_of_le hPw'
      have h3 : leWe u ≤ w - taV P := (add_le_add_iff_left (taV P)).1 (by rw [e1]; exact hw1)
      have h4 : w - taV P < leWe V := (add_lt_add_iff_left (taV P)).1 (by rw [e1]; exact hw2)
      obtain ⟨h5, h6⟩ := sjLogW h3 h4
      exact ⟨_, sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC _ hwP).2, h5, h6⟩
    have hRle : e (taV P + leWe (taV R)) ≤ E := (he ((add_le_add_iff_left _).2 hWR)).trans hEt
    have hRtop : TaTopT E (fun r => e (taV P + leWe r)) R :=
      taTopT_of_ub R _ (hTop'.trans_le (he ((add_le_add_iff_left _).2
        (leWe_mono (Order.add_one_le_of_lt (taV_lt_ub R hRw))))))
    have hRo := taWalk R _ he' hRw hRn hD' hRle hRtop
    -- (3) the coefficient
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    by_contra hQη
    push Not at hQη
    set y := e (taV P + leWe (taV R) * η) with hy_def
    set Q := S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) with hQ_def
    have hQ : SC Q := SC_psi (InR_Om_succ 1) _
    have hyE : y ≤ E := (he ((add_le_add_iff_left _).2 (leMulWe_mono hη))).trans hEt
    obtain ⟨z, hz1, hz2, hz⟩ := sjCode hβd hβown hX0cl hX0G3 hEcl hyE
    have hzV : z < e (taV P + leWe (taV R + 1)) := hz2.trans_lt hTop'
    obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ (hTm (he zero_le)) _ _ z hz hz1 hzV
    have hPQ : LeCl (Om (1 + 1)) Q (taV P) := hPcl Q hQ (hTm (he le_self_add))
    have hPw' : taV P ≤ w := le_self_add.trans hw1
    have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
    have e1 : taV P + (w - taV P) = w := Ordinal.add_sub_cancel_of_le hPw'
    have h3 : leWe (taV R) * η ≤ w - taV P := (add_le_add_iff_left (taV P)).1 (by rw [e1]; exact hw1)
    have h4 : w - taV P < leWe (taV R + 1) := (add_lt_add_iff_left (taV P)).1 (by rw [e1]; exact hw2)
    have hη0 : η ≠ 0 := hlim.ne_bot
    have hm0 : w - taV P ≠ 0 := (lt_of_lt_of_le (mul_pos (leWe_pos _) (pos_iff_ne_zero.2 hη0)) h3).ne'
    have hL : LeCl (Om (1 + 1)) Q (log ω (w - taV P)) := (leClDec hQ ldOm2_SC _ hwP).2
    have hL1 : Om (1 + 1) * taV R + log ω η ≤ log ω (w - taV P) := by
      refine le_log_of_opow_le one_lt_omega0 ?_
      rw [opow_add]
      exact (mul_le_mul_right (opow_log_le_self ω hη0) _).trans h3
    have hL2 : log ω (w - taV P) < Om (1 + 1) * taV R + Om (1 + 1) := by
      have h := (lt_opow_iff_log_lt one_lt_omega0 hm0).1 h4
      rwa [mul_add_one] at h
    have hd : LeCl (Om (1 + 1)) Q (log ω (w - taV P) % Om (1 + 1)) := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1)) hL
      rwa [gg_SC_eps ldOm2_SC] at h
    have hRL : Om (1 + 1) * taV R ≤ log ω (w - taV P) := le_self_add.trans hL1
    have eL : Om (1 + 1) * taV R + (log ω (w - taV P) - Om (1 + 1) * taV R) = log ω (w - taV P) :=
      Ordinal.add_sub_cancel_of_le hRL
    have hdlt : log ω (w - taV P) - Om (1 + 1) * taV R < Om (1 + 1) :=
      (add_lt_add_iff_left _).1 (by rw [eL]; exact hL2)
    have hdge : log ω η ≤ log ω (w - taV P) - Om (1 + 1) * taV R :=
      (add_le_add_iff_left _).1 (by rw [eL]; exact hL1)
    have hmod : log ω (w - taV P) % Om (1 + 1) = log ω (w - taV P) - Om (1 + 1) * taV R := by
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

/-- **The closure condition of `E < E_Γ` at a proper base gives the own predicate of its normal-form term.** -/
theorem taOwn_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < taTop S) : TaOwn S β X0 (fun y => y) (taTm E) := by
  obtain ⟨hw, hv⟩ := taTm_spec hl hX E hEH hE
  obtain ⟨hn, -⟩ := taTm_nf hl hX E hEH hE
  have htop := taTopT_self (taTm E) hw (fun y => y) strictMono_id
  rw [hv] at htop
  have hT : TaOwnT S β X0 (fun y => y) (taTm E) :=
    taWalk hβd hβown hX0cl hX0G3 hEcl (taTm E) (fun y => y) (fun _ _ h => h) hw hn
      (fun Q _ _ => sjDesc_id Q) (by rw [hv]) htop
  exact taBridge hl hX (Es := E) hβd hβown hX0m hX0cl hX0G3 (taTm E) TaC.hole trivial hw trivial hT
    (by rw [hv]; exact le_rfl)

/-- **THE LEVEL STATEMENT AT EVERY `1 ≤ E < E_Γ` OF `H_λ` WITH THE CLOSURE CONDITION**:
`Sc.ScLev (CL E) E (Θ̂ E)`. -/
theorem taLev {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < taTop S) :
    ScLev S l (Sn.SnCL S E) E (taTh S l E) := by
  obtain ⟨hw, hv⟩ := taTm_spec hl hX E hEH hE
  have hL := taLev_term hl hX (taTm E) hw (by rw [hv]; exact hE1)
  rw [hv] at hL
  intro b X0 Xh0 hoff hd hG3 hG hcl β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb'
  rw [add_zero] at hβd hβown
  have hOw : TaOwn S β X0 (fun y => y) (taTm E) :=
    taOwn_of_cl hl hX hβd hβown hX0m hX0cl (le_self_add.trans_lt hG3)
      (fun Q hQ hQ' => hcl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hbβ _)).1.trans hQ')) hEH hE
  exact hL β X0 Xh0 hoffβ hd hG3 hG hOw β Â hb le_rfl hÂ hbase

end All

end Googology.Trans.PoR.InaccPsi.R2.Ta
