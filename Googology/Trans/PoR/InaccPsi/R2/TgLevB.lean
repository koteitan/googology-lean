import Googology.Trans.PoR.InaccPsi.R2.TgWalk

/-!
# The enclosing levels below the bottom of every coefficient

`W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `G = φ(Ω₂, 1)`, `CL E` the closure condition.  A coefficient `c` of
`P + W^R·c` evaluated by `e` has the **bottom** `e(P + W^R)` (the value at `c = 1`): the shapes of the derivation
rules (`Sc.ScShp`, `Ta.TaShp`) and of the bridge (`Sg.sgSq_supAt`) pass through every enclosing node `φ(a, Ω₂ + ·)`
and need its level below `T` at the bottom (`Td.tdShp_vebC`: `a < bot`).

* `TgLevB` (**every enclosing level below `T` at the bottom of every coefficient**: `A` the largest enclosing
  level), `tgWe_G` (`W^G = G`), `tgAdd_le_G`, `tgOm_add_G`;
* `tgWalkB` (**THE WALK FOR THE BOTTOMS**: the invariant "`A < T_{e(u)}` whenever `e(u) ≤ E < e(V)`, `1 ≤ u`,
  `V ≤ G`" passes into a node `φ(a, Ω₂ + ·)` by `Tg.tgLevOwnF`, the code gap up to `G`), `tgLevB_of_cl`
  (**THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TgLevB 0 id` OF ITS NORMAL-FORM
  TERM**: at every coefficient, every enclosing code level is below `T` at the bottom).

No new axiom.  New definition: `TgLevB`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

/-- **Every enclosing level below `T` at the bottom of every coefficient** (`A` the largest enclosing level). -/
def TgLevB (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, _, .zero => True
  | A, e, .phi a Y => TgLevB S b X0 (max A a) (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | A, e, .term P R _ => TgLevB S b X0 A e P ∧ TgLevB S b X0 A (fun r => e (taV P + leWe r)) R ∧
      A < S.psi (b + leWe (X0 + leWe (e (taV P + leWe (taV R))))) (Om (1 + 1))

variable {S : InaccSeq.{0}}

theorem tgOm_lt_G : Om (1 + 1 : Ordinal.{0}) < veblen (Om (1 + 1)) 1 := by
  conv_lhs => rw [← ldOm2_SC.veblen_zero]
  exact (veblen_lt_veblen_iff_right).2 zero_lt_one

theorem tgOm_add_G : Om (1 + 1 : Ordinal.{0}) + veblen (Om (1 + 1)) 1 = veblen (Om (1 + 1)) 1 := by
  have hE : ω ^ veblen (Om (1 + 1 : Ordinal.{0})) 1 = veblen (Om (1 + 1)) 1 := gg_veblen_eps ldOm2_SC.1.ne'
  have h1 : (Om (1 + 1) : Ordinal.{0}) < ω ^ veblen (Om (1 + 1 : Ordinal.{0})) 1 := by rw [hE]; exact tgOm_lt_G
  exact Ordinal.add_of_omega0_opow_le h1 hE.le

/-- `W^G = G` for `G = φ(Ω₂, 1)`. -/
theorem tgWe_G : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := by
  unfold leWe; rw [taK_mul_veb ldOm2_SC ldOm2_SC.1.ne' tgOm_lt_G, gg_veblen_eps ldOm2_SC.1.ne']

theorem tgAdd_le_G {P V : Ordinal.{0}} (hP : P < veblen (Om (1 + 1)) 1) (hV : V ≤ veblen (Om (1 + 1)) 1) :
    P + V ≤ veblen (Om (1 + 1)) 1 := by
  rcases eq_or_lt_of_le hV with rfl | hlt
  · have hE : ω ^ veblen (Om (1 + 1 : Ordinal.{0})) 1 = veblen (Om (1 + 1)) 1 := gg_veblen_eps ldOm2_SC.1.ne'
    have h1 : P < ω ^ veblen (Om (1 + 1 : Ordinal.{0})) 1 := by rw [hE]; exact hP
    exact (Ordinal.add_of_omega0_opow_le h1 hE.le).le
  · exact (Ph.ph_veblen_prin _ _ hP hlt).le

theorem tgNode_le_G {a V : Ordinal.{0}} (haW : a < Om (1 + 1)) (hV : V ≤ veblen (Om (1 + 1)) 1) :
    veblen a (Om (1 + 1) + V) ≤ veblen (Om (1 + 1)) 1 := by
  have h1 : Om (1 + 1) + V ≤ veblen (Om (1 + 1)) 1 := by
    calc Om (1 + 1) + V ≤ Om (1 + 1) + veblen (Om (1 + 1)) 1 := (add_le_add_iff_left _).2 hV
      _ = veblen (Om (1 + 1)) 1 := tgOm_add_G
  calc veblen a (Om (1 + 1) + V) ≤ veblen a (veblen (Om (1 + 1)) 1) := (veblen_le_veblen_iff_right).2 h1
    _ = veblen (Om (1 + 1)) 1 := veblen_veblen_of_lt haW 1

section Walk

variable {l : Ordinal.{0}} {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
  (hEG : E < veblen (Om (1 + 1)) 1)

include hβd hβown hX0cl hX0G3 hEcl hEG

/-- **THE WALK FOR THE BOTTOMS**: the invariant of the enclosing levels passes into every node by the code gap
`Tg.tgGapF`; at every coefficient it gives `A < T` at the bottom. -/
theorem tgWalkB : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}) (A : Ordinal.{0}), Monotone e → (∀ x, x ≤ e x) →
    TgWF S l t → TgNX t → TaNF t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    (∀ u V, 1 ≤ u → V ≤ veblen (Om (1 + 1)) 1 → e u ≤ E → E < e V →
      A < S.psi (β + leWe (X0 + leWe (e u))) (Om (1 + 1))) →
    e (taV t) ≤ E → TaTopT E e t → TgLevB S β X0 A e t
  | .zero, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .phi a Y, e, A, he, hinf, ⟨_, _, haW, hYw, _, _⟩, ⟨_, hYnx⟩, hn, hD, hInv, hEt, hTop => by
    have he' : Monotone (fun y => e (veblen a (Om (1 + 1) + y))) := fun _ _ h => he (taNode_mono _ a h)
    have hinf' : ∀ x, x ≤ e (veblen a (Om (1 + 1) + x)) :=
      fun x => (le_add_self.trans (right_le_veblen a _)).trans (hinf _)
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe ((fun y => e (veblen a (Om (1 + 1) + y))) 0)))
        (Om (1 + 1)) ≤ Q → SjDesc Q (fun y => e (veblen a (Om (1 + 1) + y))) :=
      fun Q hQ hQb => tgDesc_node hQ haW (hD Q hQ ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (he zero_le)))))).1.trans hQb))
    have hInv' : ∀ u V, 1 ≤ u → V ≤ veblen (Om (1 + 1)) 1 → e (veblen a (Om (1 + 1) + u)) ≤ E →
        E < e (veblen a (Om (1 + 1) + V)) →
        max A a < S.psi (β + leWe (X0 + leWe (e (veblen a (Om (1 + 1) + u))))) (Om (1 + 1)) := by
      intro u V hu hV h1 h2
      have hVn := tgNode_le_G haW hV
      have hΩu : Om (1 + 1) < veblen a (Om (1 + 1) + u) :=
        (lt_add_of_pos_right _ (zero_lt_one.trans_le hu)).trans_le (right_le_veblen _ _)
      exact max_lt (hInv _ _ (Order.one_le_iff_pos.2 veblen_pos) hVn h1 h2)
        (tgLevOwnF hβd hβown hX0cl hX0G3 hEcl he hD hΩu hVn h1 h2)
    exact tgWalkB Y _ (max A a) he' hinf' hYw hYnx hn hD' hInv' hEt hTop
  | .term P R c, e, A, he, hinf, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPx, hRx⟩, ⟨hPn, hRn, hPR⟩, hD, hInv, hEt, hTop => by
    have hTop' : E < e (taV P + leWe (taV R + 1)) := hTop
    have hTm : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
        S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono h))))).1
    have hWR : leWe (taV R) ≤ leWe (taV R) * c := by simpa using leMulWe_mono (e := taV R) hc1
    have hvG : taV (TaT.term P R c) < veblen (Om (1 + 1)) 1 := ((hinf _).trans hEt).trans_lt hEG
    have hPG : taV P < veblen (Om (1 + 1)) 1 :=
      (le_self_add : taV P ≤ taV P + leWe (taV R) * c).trans_lt hvG
    have hRG : taV R < veblen (Om (1 + 1)) 1 :=
      ((taLe_We _).trans (hWR.trans (le_add_self : leWe (taV R) * c ≤ taV P + leWe (taV R) * c))).trans_lt hvG
    -- (1) the prefix
    have hPle : e (taV P) ≤ E := (he (le_self_add : taV P ≤ taV P + leWe (taV R) * c)).trans hEt
    have hPtop : TaTopT E e P := by
      cases P with
      | zero => trivial
      | phi a' Y' => exact taTopT_of_ub _ _ (hTop'.trans_le (he (tgPhi_ub hPw hPR).le))
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
    have hPB := tgWalkB P e A he hinf hPw hPx hPn hD hInv hPle hPtop
    have hPo := tgWalk hβd hβown hX0cl hX0G3 hEcl P e he hPw hPx hPn hD hPle hPtop
    have hPcl := tgValCl P e he hPw hPo
    -- (2) the exponent
    have he' : Monotone (fun r => e (taV P + leWe r)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hinf' : ∀ x, x ≤ e (taV P + leWe x) := fun x => ((taLe_We x).trans le_add_self).trans (hinf _)
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
    have hInv' : ∀ u V, 1 ≤ u → V ≤ veblen (Om (1 + 1)) 1 → e (taV P + leWe u) ≤ E →
        E < e (taV P + leWe V) → A < S.psi (β + leWe (X0 + leWe (e (taV P + leWe u)))) (Om (1 + 1)) :=
      fun u V _ hV h1 h2 => hInv _ _ ((Order.one_le_iff_pos.2 (leWe_pos u)).trans le_add_self)
        (tgAdd_le_G hPG ((leWe_mono hV).trans_eq tgWe_G)) h1 h2
    have hRle : e (taV P + leWe (taV R)) ≤ E := (he ((add_le_add_iff_left _).2 hWR)).trans hEt
    have hRtop : TaTopT E (fun r => e (taV P + leWe r)) R :=
      taTopT_of_ub R _ (hTop'.trans_le (he ((add_le_add_iff_left _).2
        (leWe_mono (Order.add_one_le_of_lt (tgV_lt_ub R hRw))))))
    have hRB := tgWalkB R _ A he' hinf' hRw hRx hRn hD' hInv' hRle hRtop
    -- (3) the bottom of the coefficient
    have hRG1 : taV R + 1 ≤ veblen (Om (1 + 1)) 1 :=
      Order.add_one_le_of_lt hRG
    refine ⟨hPB, hRB, hInv _ _ ((Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self)
      (tgAdd_le_G hPG ((leWe_mono hRG1).trans_eq tgWe_G)) hRle hTop'⟩

end Walk

section All

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TgLevB 0 id` OF ITS NORMAL-FORM
TERM**: at every coefficient every enclosing code level is below `T` at the bottom of the coefficient. -/
theorem tgLevB_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < veblen (Om (1 + 1)) 1) : TgLevB S β X0 0 (fun y => y) (taTm E) := by
  obtain ⟨hw, hnx, hv⟩ := tgTm_spec hl hX E hEH hE
  obtain ⟨hn, -⟩ := tgTm_nf hl hX E hEH hE
  have htop := tgTopT_self (taTm E) hw (fun y => y) strictMono_id
  rw [hv] at htop
  exact tgWalkB hβd hβown hX0cl hX0G3 hEcl hE (taTm E) (fun y => y) 0 (fun _ _ h => h) (fun _ => le_rfl) hw hnx hn
    (fun Q _ _ => sjDesc_id Q) (fun u _ _ _ _ _ => (SC_psi (InR_Om_succ 1) _).1) (by rw [hv]) htop

end All

end Googology.Trans.PoR.InaccPsi.R2.Tg
