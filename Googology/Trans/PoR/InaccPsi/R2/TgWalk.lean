import Googology.Trans.PoR.InaccPsi.R2.TgNF

/-!
# The walk with code levels: the closure condition gives the own condition of every node level

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, codes = `Le.LeCl Ω₂ Q`, `CL E` the
closure condition (`E` a code over every strongly critical `Q ≥ T_E`), `Sj.SjDesc` the descent property.

* `TgOwnT` (**the closure form of `TgOwn`**: the level condition `a < T` at every node, `Sg.SgLimT` at every
  coefficient), `tgValCl` (the value of a term with `TgOwnT` is a code above `T_{e(val)}`);
* `tgV_lt_ub`, `tgTopT_self`, `tgPhi_ub`, `tgTop_ub` (**the top of a nonzero term is its upper bound**),
  `tgUB_lt` (**the upper bound of the argument stays below the node**: `Ω₂ + ub Y < φ(a, Ω₂ + Y)` for a node off
  its fixed points), `tgDesc_node` (**the descent passes through a node with any level `a < Ω₂`**);
* `tgWalk` (**THE WALK WITH CODE LEVELS**: at a node the level condition comes from `Tg.tgLevOwn`, i.e. from the
  code gap `Tg.tgGap` below the level; at a coefficient as in `Ta.taWalk`);
* `tgOwnT_of_cl` (**THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TgOwnT` OF ITS
  NORMAL-FORM TERM WITH CODE LEVELS**: every node level `a` of `E` is below `T` at its node, every coefficient has
  `Sg.SgLimT`), `tgLev_lt_T` (the outer level of a node `E = φ(a, y)` is below `T_E`).

No new axiom.  New definition: `TgOwnT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

/-- **The closure form of the own predicate with code levels**: `a < T` at every node, `Sg.SgLimT` at every
coefficient. -/
def TgOwnT (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => a < S.psi (b + leWe (X0 + leWe (e (veblen a (Om (1 + 1) + taV Y))))) (Om (1 + 1)) ∧
      TgOwnT S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R c => TgOwnT S b X0 e P ∧ TgOwnT S b X0 (fun r => e (taV P + leWe r)) R ∧
      SgLimT S (fun z => e (taV P + leWe (taV R) * z)) c b X0

variable {S : InaccSeq.{0}}

/-- **The value of a term with `TgOwnT` is a code above `T_{e(val)}`.** -/
theorem tgValCl {l b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TgWF S l t → TgOwnT S b X0 e t →
    ∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (taV t)
  | .zero, _, _, _, _ => fun Q hQ _ => LeCl.zero hQ.1
  | .phi a Y, e, he, ⟨_, _, _, hYw, _, _⟩, ⟨haT, hT⟩ => fun Q hQ hc' =>
    LeCl.phi (LeCl.small (haT.trans_le hc'))
      (LeCl.add LeCl.om (tgValCl Y _ (fun _ _ h => he (taNode_mono _ a h)) hYw hT Q hQ hc'))
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
    have hP3 := tgValCl P e he hPw hPo Q hQ (hPT.trans hc')
    have hR3 := tgValCl R _ heR hRw hRo Q hQ (hRT.trans hc')
    exact LeCl.add hP3 (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ hR3) ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))

/-! ## Upper bounds and tops -/

/-- The value of a well-formed term is below its upper bound. -/
theorem tgV_lt_ub {l : Ordinal.{0}} : ∀ t : TaT, TgWF S l t → taV t < taUB t
  | .zero, _ => zero_lt_one
  | .phi _ Y, ⟨_, _, _, hYw, _, _⟩ => (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 (tgV_lt_ub Y hYw))
  | .term _ _ _, ⟨_, _, _, _, hcW⟩ => (add_lt_add_iff_left _).2 (rvWe_lt_succ hcW)

/-- `TaTopT` of a term at its own value under a strictly monotone evaluation. -/
theorem tgTopT_self {l : Ordinal.{0}} : ∀ t : TaT, TgWF S l t → ∀ e : Ordinal.{0} → Ordinal.{0}, StrictMono e →
    TaTopT (e (taV t)) e t
  | .zero, _, _, _ => trivial
  | .phi a Y, ⟨_, _, _, hYw, _, _⟩, e, he =>
    tgTopT_self Y hYw _ (fun _ _ h => he ((veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 h)))
  | .term P R c, ⟨_, _, _, _, hcW⟩, e, he => by
    show e (taV P + leWe (taV R) * c) < e (taV P + leWe (taV R + 1))
    exact he ((add_lt_add_iff_left _).2 (rvWe_lt_succ hcW))

/-- A node prefix `P = φ(a, Ω₂ + Y)` with an exponent `r < P` after it: `P + W^{r+1} < ub P`. -/
theorem tgPhi_ub {l a r : Ordinal.{0}} {Y : TaT} (hw : TgWF S l (TaT.phi a Y)) (hr : r < taV (TaT.phi a Y)) :
    taV (TaT.phi a Y) + leWe (r + 1) < taUB (TaT.phi a Y) := by
  have hlt := tgV_lt_ub (TaT.phi a Y) hw
  obtain ⟨_, ha1, _, _, hY1, _⟩ := hw
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  have hp := Ph.ph_veblen_prin a (Om (1 + 1) + taUB Y)
  have hlim : IsSuccLimit (taV (TaT.phi a Y)) := taVeb_lim ha0
  have hW : leWe (r + 1) < taV (TaT.phi a Y) := by
    have h := leWe_lt (hlim.add_one_lt hr)
    have e : leWe (taV (TaT.phi a Y)) = taV (TaT.phi a Y) := taWe_veb ha0 hY1
    rwa [e] at h
  exact hp hlt (hW.trans hlt)

/-- **The top of a nonzero well-formed term is its upper bound.** -/
theorem tgTop_ub {l E : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), TgWF S l t → 1 ≤ taV t →
    TaTopT E e t → E < e (taUB t)
  | .zero, _, _, h, _ => absurd h (not_le.2 zero_lt_one)
  | .phi _ Y, _, ⟨_, _, _, hYw, hY1, _⟩, _, h => tgTop_ub Y _ hYw hY1 h
  | .term _ _ _, _, _, _, h => h

/-- **The upper bound of the argument stays below the node**: `Ω₂ + ub t < φ(a, Ω₂ + t)` for `1 ≤ a` and a node
off its fixed points. -/
theorem tgUB_lt {l : Ordinal.{0}} : ∀ t : TaT, TgWF S l t → TgNX t → 1 ≤ taV t → ∀ a, 1 ≤ a →
    Om (1 + 1) + taV t < veblen a (Om (1 + 1) + taV t) → Om (1 + 1) + taUB t < veblen a (Om (1 + 1) + taV t)
  | .zero, _, _, h, _, _, _ => absurd h (not_le.2 zero_lt_one)
  | .term P R c, ⟨_, _, _, hc1, _⟩, _, h1, a, ha1, hlt => by
    have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
    set M := veblen a (Om (1 + 1) + taV (TaT.term P R c)) with hM
    have hWM : leWe M = M := taWe_veb ha0 h1
    have hlim : IsSuccLimit M := taVeb_lim ha0
    have hvM : taV (TaT.term P R c) < M := le_add_self.trans_lt hlt
    have hRv : taV R ≤ taV (TaT.term P R c) := by
      have h2 : leWe (taV R) ≤ leWe (taV R) * c := by simpa using leMulWe_mono (e := taV R) hc1
      exact (taLe_We _).trans (h2.trans le_add_self)
    have hW : leWe (taV R + 1) < M := by
      have h := leWe_lt (hlim.add_one_lt (hRv.trans_lt hvM)); rwa [hWM] at h
    have hP : taV P < M := (le_self_add : taV P ≤ taV P + leWe (taV R) * c).trans_lt hvM
    have hΩ : Om (1 + 1) < M := le_self_add.trans_lt hlt
    show Om (1 + 1) + (taV P + leWe (taV R + 1)) < M
    exact Ph.ph_veblen_prin a _ hΩ (Ph.ph_veblen_prin a _ hP hW)
  | .phi a' Y', ⟨_, ha1', _, hYw, hY1, _⟩, ⟨hnx, hYnx⟩, _, a, _, hlt => by
    have ha0' : a' ≠ 0 := (zero_lt_one.trans_le ha1').ne'
    set N := veblen a' (Om (1 + 1) + taV Y') with hN
    have hIH : Om (1 + 1) + taUB Y' < N := tgUB_lt Y' hYw hYnx hY1 a' ha1' hnx
    have hΩN : Om (1 + 1) < N := le_self_add.trans_lt hnx
    have hWN : leWe N = N := taWe_veb ha0' hY1
    have habs : Om (1 + 1) + N = N := by
      unfold leWe at hWN
      have h1 : Om (1 + 1) < ω ^ (Om (1 + 1) * N) := by rw [hWN]; exact hΩN
      have h2 : ω ^ (Om (1 + 1) * N) ≤ N := hWN.le
      exact Ordinal.add_of_omega0_opow_le h1 h2
    show Om (1 + 1) + veblen a' (Om (1 + 1) + taUB Y') < veblen a (Om (1 + 1) + N)
    have hlt' : N < veblen a N := by
      have h := hlt; change Om (1 + 1) + N < veblen a (Om (1 + 1) + N) at h; rwa [habs] at h
    rw [habs]
    have haa : a' ≤ a := by
      by_contra h
      push Not at h
      have hfix : veblen a N = N := veblen_veblen_of_lt h _
      rw [hfix] at hlt'; exact lt_irrefl _ hlt'
    have hub : veblen a' (Om (1 + 1) + taUB Y') < veblen a N :=
      ((veblen_lt_veblen_iff_right).2 hIH).trans_le (veblen_left_monotone N haa)
    exact Ph.ph_veblen_prin a N (hΩN.trans hlt') hub

/-- **The descent passes through a node with any level `a < Ω₂`.** -/
theorem tgDesc_node {Q a : Ordinal.{0}} (hQ : SC Q) (haW : a < Om (1 + 1)) {e : Ordinal.{0} → Ordinal.{0}}
    (hD : SjDesc Q e) : SjDesc Q (fun y => e (veblen a (Om (1 + 1) + y))) := by
  intro u V z hz h1 h2
  obtain ⟨w, hw, hw1, hw2⟩ := hD _ _ z hz h1 h2
  have h0 : veblen a 0 ≤ w := ((veblen_le_veblen_iff_right).2 zero_le).trans hw1
  obtain ⟨u', hu', hu1, hu2⟩ := taCl_idx ldOm2_SC haW w hw h0
  have hlo : Om (1 + 1) + u ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (hw1.trans_lt hu2))
  have hhi : u' < Om (1 + 1) + V := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hw2)
  have hΩu' : Om (1 + 1) ≤ u' := le_self_add.trans hlo
  have hV0 : 0 < V := pos_iff_ne_zero.2 fun h => by
    rw [h, add_zero] at hhi; exact absurd hΩu' (not_le.2 hhi)
  exact ⟨u' - Om (1 + 1), (leClDec hQ ldOm2_SC u' hu').1 _ LeCl.om hΩu', Ordinal.le_sub_of_add_le hlo,
    Ordinal.sub_lt_of_lt_add hhi hV0⟩

/-! ## The walk -/

section Walk

variable {l : Ordinal.{0}} {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **THE WALK WITH CODE LEVELS through a normal-form term.** -/
theorem tgWalk : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TgWF S l t → TgNX t → TaNF t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    e (taV t) ≤ E → TaTopT E e t → TgOwnT S β X0 e t
  | .zero, _, _, _, _, _, _, _, _ => trivial
  | .phi a Y, e, he, ⟨_, ha1, haW, hYw, hY1, _⟩, ⟨hnx, hYnx⟩, hn, hD, hEt, hTop => by
    have he' : Monotone (fun y => e (veblen a (Om (1 + 1) + y))) := fun _ _ h => he (taNode_mono _ a h)
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe ((fun y => e (veblen a (Om (1 + 1) + y))) 0)))
        (Om (1 + 1)) ≤ Q → SjDesc Q (fun y => e (veblen a (Om (1 + 1) + y))) :=
      fun Q hQ hQb => tgDesc_node hQ haW (hD Q hQ ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (he zero_le)))))).1.trans hQb))
    refine ⟨?_, tgWalk Y _ he' hYw hYnx hn hD' hEt hTop⟩
    exact tgLevOwn hβd hβown hX0cl hX0G3 hEcl he hD haW haW le_self_add hnx
      (tgUB_lt Y hYw hYnx hY1 a ha1 hnx) hEt (tgTop_ub Y _ hYw hY1 hTop)
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPx, hRx⟩, ⟨hPn, hRn, hPR⟩, hD, hEt, hTop => by
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
    have hPo := tgWalk P e he hPw hPx hPn hD hPle hPtop
    have hPcl := tgValCl P e he hPw hPo
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
        (leWe_mono (Order.add_one_le_of_lt (tgV_lt_ub R hRw))))))
    have hRo := tgWalk R _ he' hRw hRx hRn hD' hRle hRtop
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

/-- **THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TgOwnT` OF ITS NORMAL-FORM
TERM WITH CODE LEVELS**: every node level is below `T` at its node, every coefficient has `Sg.SgLimT`. -/
theorem tgOwnT_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < veblen (Om (1 + 1)) 1) : TgOwnT S β X0 (fun y => y) (taTm E) := by
  obtain ⟨hw, hnx, hv⟩ := tgTm_spec hl hX E hEH hE
  obtain ⟨hn, -⟩ := tgTm_nf hl hX E hEH hE
  have htop := tgTopT_self (taTm E) hw (fun y => y) strictMono_id
  rw [hv] at htop
  exact tgWalk hβd hβown hX0cl hX0G3 hEcl (taTm E) (fun y => y) (fun _ _ h => h) hw hnx hn
    (fun Q _ _ => sjDesc_id Q) (by rw [hv]) htop

/-- **The outer level of a `W`-fixed point `E = φ(a, y)` below `φ(Ω₂, 1)` is below `T_E`** (under the closure
condition at a proper base). -/
theorem tgLev_lt_T {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen (Om (1 + 1)) 1) (hfix : ¬ sgLW E < E) :
    invVeblen₁ E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) := by
  obtain ⟨_, _, hΩy, hyE, hval⟩ := tdNode_nfW hE1 hE hfix
  have hc : ¬ (0 < E ∧ sgLW E < E) := fun h => hfix h.2
  have hT := tgOwnT_of_cl hl hX hβd hβown hX0cl hX0G3 hEcl hEH hE
  obtain ⟨-, -, hv⟩ := tgTm_spec hl hX E hEH hE
  rw [taTm_node hc ⟨hΩy, hyE⟩] at hT hv
  have h := hT.1
  have e : veblen (invVeblen₁ E) (Om (1 + 1) + taV (taTm (invVeblen₂ E - Om (1 + 1)))) = E := hv
  rw [e] at h
  exact h

end All

end Googology.Trans.PoR.InaccPsi.R2.Tg
