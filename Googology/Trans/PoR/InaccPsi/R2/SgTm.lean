import Googology.Trans.PoR.InaccPsi.R2.SgSub

/-!
# Exponent terms, contexts, their own predicates and their data

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`),
`T_E(b) = ψ_{Ω₂}(b + W^E)` (`Le.leTe`), `SQ_j(G) = Sc.scSq S (z ↦ W^{G z}) X₀ b j`.

* `SgT` (**exponent terms**): `zero` and `term P R c` with the value `P + W^R·c` (`sgV`) and the image
  `P̂ + Ω^{R̂}·Θ c` (`sgI`); no normal-form condition: `P` is any term.
* `SgC` (**contexts**): `hole`, `pfx K Q` (`y ↦ K(Q + y)`) and `lft K` (`y ↦ K(W^y)`), evaluated by `sgE`
  (image side `sgEh`).
* `SgWF` (codes `1 ≤ c < Ω₂` at every coefficient), `SgLimC` (**the limit condition of a coefficient `c` at the
  truncation `G`**: every limit `η ≤ c` lies below some `SQ_j(G)`), `SgOwn` (**the own predicate of a term at an
  evaluation `e`**: every coefficient `c` of `P + W^R·c` satisfies the limit condition at `z ↦ e(P + W^R·z)`,
  the exponent `R` at `r ↦ e(P + W^r)`), `SgOwnC` (the same for the prefixes of a context).
* `sgSq_mono_fun`, `sgLimC_mono`, `sgOwn_mono` (monotone in the base, the offset and the evaluation),
  `sgCode_lt` (**a coefficient with the limit condition lies below `T_{X₀ + W^{G c}}(b)`**), `sgV_hull`,
  `sgDat` (**the data of an own term: value and image in `Cl(0, ·)` and codes `LeCl` above the bottom
  `T_{X₀ + W^{e(val)}}(b)`**).

No new axiom.  New definitions: `SgT`, `SgC`, `sgV`, `sgI`, `sgE`, `sgEh`, `SgWF`, `SgWFC`, `SgLimC`, `SgOwn`,
`SgOwnC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

/-- **Exponent terms**: `zero`, `term P R c = P + W^R·c`. -/
inductive SgT : Type 1
  | zero : SgT
  | term : SgT → SgT → Ordinal.{0} → SgT

/-- **Contexts**: `hole`, `pfx K Q = K(Q + _)`, `lft K = K(W^_)`. -/
inductive SgC : Type 1
  | hole : SgC
  | pfx : SgC → SgT → SgC
  | lft : SgC → SgC

/-- The value of a term. -/
noncomputable def sgV : SgT → Ordinal.{0}
  | .zero => 0
  | .term P R c => sgV P + leWe (sgV R) * c

/-- The image of a term (`Ω₂ ↦ Ω₁`, codes read by `Θ`). -/
noncomputable def sgI (S : InaccSeq.{0}) (l : Ordinal.{0}) : SgT → Ordinal.{0}
  | .zero => 0
  | .term P R c => sgI S l P + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c

/-- The evaluation of a context. -/
noncomputable def sgE : SgC → Ordinal.{0} → Ordinal.{0}
  | .hole, y => y
  | .pfx K Q, y => sgE K (sgV Q + y)
  | .lft K, y => sgE K (leWe y)

/-- The image evaluation of a context. -/
noncomputable def sgEh (S : InaccSeq.{0}) (l : Ordinal.{0}) : SgC → Ordinal.{0} → Ordinal.{0}
  | .hole, v => v
  | .pfx K Q, v => sgEh S l K (sgI S l Q + v)
  | .lft K, v => sgEh S l K (leOe v)

/-- Codes `1 ≤ c < Ω₂` at every coefficient. -/
def SgWF (S : InaccSeq.{0}) (l : Ordinal.{0}) : SgT → Prop
  | .zero => True
  | .term P R c => SgWF S l P ∧ SgWF S l R ∧ GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < Om (1 + 1)

/-- Every prefix of a context is well formed. -/
def SgWFC (S : InaccSeq.{0}) (l : Ordinal.{0}) : SgC → Prop
  | .hole => True
  | .pfx K Q => SgWFC S l K ∧ SgWF S l Q
  | .lft K => SgWFC S l K

/-- **The limit condition of a coefficient `c` at the truncation `G`.** -/
def SgLimC (S : InaccSeq.{0}) (G : Ordinal.{0} → Ordinal.{0}) (c b X0 : Ordinal.{0}) : Prop :=
  ∀ η, η ≤ c → IsSuccLimit η → ∃ j, η < scSq S (fun z => leWe (G z)) X0 b j

/-- **The own predicate of a term at the evaluation `e`.** -/
def SgOwn (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → SgT → Prop
  | _, .zero => True
  | e, .term P R c => SgOwn S b X0 e P ∧ SgOwn S b X0 (fun r => e (sgV P + leWe r)) R ∧
      SgLimC S (fun z => e (sgV P + leWe (sgV R) * z)) c b X0

/-- The own predicate of the prefixes of a context. -/
def SgOwnC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : SgC → Prop
  | .hole => True
  | .pfx K Q => SgOwnC S b X0 K ∧ SgOwn S b X0 (sgE K) Q
  | .lft K => SgOwnC S b X0 K

variable {S : InaccSeq.{0}}

theorem sgE_mono : ∀ K : SgC, Monotone (sgE K)
  | .hole => fun _ _ h => h
  | .pfx K Q => fun _ _ h => sgE_mono K ((add_le_add_iff_left (sgV Q)).2 h)
  | .lft K => fun _ _ h => sgE_mono K (leWe_mono h)

theorem sgE_strictMono : ∀ K : SgC, StrictMono (sgE K)
  | .hole => fun _ _ h => h
  | .pfx K Q => fun _ _ h => sgE_strictMono K ((add_lt_add_iff_left (sgV Q)).2 h)
  | .lft K => fun _ _ h => sgE_strictMono K (leWe_lt h)

/-- `SQ_j` is monotone in the shape. -/
theorem sgSq_mono_fun {G G' : Ordinal.{0} → Ordinal.{0}} (hG' : Monotone G') (hle : ∀ z, G z ≤ G' z)
    (X0 b : Ordinal.{0}) : ∀ j, scSq S G X0 b j ≤ scSq S G' X0 b j
  | 0 => le_rfl
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
      ((add_le_add_iff_left X0).2 ((hle _).trans (hG' (sgSq_mono_fun hG' hle X0 b j))))))).1

theorem sgLimC_mono {G G' : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G) (hG' : Monotone G')
    (hle : ∀ z, G z ≤ G' z) {c b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0')
    (h : SgLimC S G c b X0) : SgLimC S G' c b' X0' := by
  intro η hη hlim
  obtain ⟨j, hj⟩ := h η hη hlim
  have hm : Monotone (fun z => leWe (G z)) := fun _ _ h => leWe_mono (hG h)
  have hm' : Monotone (fun z => leWe (G' z)) := fun _ _ h => leWe_mono (hG' h)
  exact ⟨j, hj.trans_le (((scSq_mono_base hm hb j).trans (scSq_mono_off hm hX j)).trans
    (sgSq_mono_fun hm' (fun z => leWe_mono (hle z)) X0' b' j))⟩

theorem sgLimC_le {G : Ordinal.{0} → Ordinal.{0}} {c c' b X0 : Ordinal.{0}} (h : SgLimC S G c' b X0) (hc : c ≤ c') :
    SgLimC S G c b X0 := fun η hη hlim => h η (hη.trans hc) hlim

/-- **The own predicate is monotone in the base, the offset and the evaluation.** -/
theorem sgOwn_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ (t : SgT) (e e' : Ordinal.{0} → Ordinal.{0}), Monotone e → Monotone e' → (∀ y, e y ≤ e' y) →
      SgOwn S b X0 e t → SgOwn S b' X0' e' t
  | .zero, _, _, _, _, _, _ => trivial
  | .term P R c, e, e', he, he', hle, ⟨hP, hR, hc⟩ => by
    refine ⟨sgOwn_mono hb hX P e e' he he' hle hP,
      sgOwn_mono hb hX R _ _ (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
      sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => hle _) hb hX hc⟩

theorem sgOwnC_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ K : SgC, SgOwnC S b X0 K → SgOwnC S b' X0' K
  | .hole, _ => trivial
  | .pfx K Q, ⟨hK, hQ⟩ => ⟨sgOwnC_mono hb hX K hK,
      sgOwn_mono hb hX Q _ _ (sgE_mono K) (sgE_mono K) (fun _ => le_rfl) hQ⟩
  | .lft K, hK => sgOwnC_mono hb hX K hK

/-- **A coefficient with the limit condition lies below `T_{X₀ + W^{G c}}(b)`.** -/
theorem sgCode_lt {G : Ordinal.{0} → Ordinal.{0}} (hG : Monotone G) {c b X0 : Ordinal.{0}}
    (h : SgLimC S G c b X0) : c < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) := by
  have hT : SC (S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hωT : ω < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) := Lw.lw_omega_lt_SC hT
  have hm : Monotone (fun z => leWe (G z)) := fun _ _ h => leWe_mono (hG h)
  have ec : c = ω * (c / ω) + c % ω := (Ordinal.div_add_mod c ω).symm
  have hr : c % ω < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) :=
    (Ordinal.mod_lt c omega0_ne_zero).trans hωT
  rcases eq_or_ne (c / ω) 0 with h0 | h0
  · calc c = c % ω := by conv_lhs => rw [ec, h0, mul_zero, zero_add]
      _ < _ := hr
  have hlim : IsSuccLimit (ω * (c / ω)) := isSuccLimit_mul_left isSuccLimit_omega0 (pos_iff_ne_zero.2 h0)
  have hle : ω * (c / ω) ≤ c := Ordinal.mul_div_le c ω
  obtain ⟨j, hj⟩ := h _ hle hlim
  have h1 := scSq_gt hm j _ hj
  have h2 : ω * (c / ω) < S.psi (b + leWe (X0 + leWe (G c))) (Om (1 + 1)) :=
    h1.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2
      (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono (hG hle)))))).1
  calc c = ω * (c / ω) + c % ω := ec
    _ < _ := hT.isPrincipal h2 hr

section Data

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem sgV_hull : ∀ t : SgT, SgWF S l t → sgV t ∈ cdHull S l
  | .zero, _ => CSet.zero_mem _ _
  | .term P R c, ⟨hP, hR, hc, _, hcW⟩ =>
    CSet.add_mem (sgV_hull P hP) (leMulWe_mem (sgV_hull R hR) ((ldHull_iff hl hX hcW).2 hc))

omit hl hX in
/-- **The data of an own term above the bottom `T_{X₀ + W^{e(val)}}(b)`.** -/
theorem sgDat {b X0 : Ordinal.{0}} : ∀ (t : SgT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → SgWF S l t →
    SgOwn S b X0 e t →
    (∀ c, S.psi (b + leWe (X0 + leWe (e (sgV t)))) (Om (1 + 1)) ≤ c → sgV t ∈ S.CSet 0 c) ∧
    (∀ c, gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (sgV t)))) (Om (1 + 1))) ≤ c →
      sgI S l t ∈ S.CSet 0 c) ∧
    (∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (sgV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (sgV t)) ∧
    (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (sgV t)))) (Om (1 + 1))) ≤ Q →
      LeCl (Om 1) Q (sgI S l t))
  | .zero, _, _, _, _ => ⟨fun _ _ => CSet.zero_mem _ _, fun _ _ => CSet.zero_mem _ _,
      fun Q hQ _ => LeCl.zero hQ.1, fun Q hQ _ => LeCl.zero hQ.1⟩
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPo, hRo, hco⟩ => by
    set T := S.psi (b + leWe (X0 + leWe (e (sgV (SgT.term P R c))))) (Om (1 + 1)) with hT
    have hval : sgV (SgT.term P R c) = sgV P + leWe (sgV R) * c := rfl
    have himg : sgI S l (SgT.term P R c) = sgI S l P + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c := rfl
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
    obtain ⟨hP1, hP2, hP3, hP4⟩ := sgDat P e he hPw hPo
    obtain ⟨hR1, hR2, hR3, hR4⟩ := sgDat R _ heR hRw hRo
    have hcT : c < T := sgCode_lt hG hco
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < gxTh (upsilon l) (ldAtR S l) T := gxTh_lt hc hcT
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_, fun Q hQ hc' => ?_, fun Q hQ hc' => ?_⟩
    · rw [hval]
      exact CSet.add_mem (hP1 c' (hPT.trans hc')) (leMulWe_mem (hR1 c' (hRT.trans hc')) (CSet.of_lt (hcT.trans_le hc')))
    · rw [himg]
      exact CSet.add_mem (hP2 c' ((gxTh_mono hPT).trans hc'))
        (leMulOe_mem (hR2 c' ((gxTh_mono hRT).trans hc')) (CSet.of_lt (hΘc.trans_le hc')))
    · rw [hval]
      exact LeCl.add (hP3 Q hQ (hPT.trans hc')) (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ (hR3 Q hQ (hRT.trans hc')))
        ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))
    · rw [himg]
      exact LeCl.add (hP4 Q hQ ((gxTh_mono hPT).trans hc'))
        (rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (hR4 Q hQ ((gxTh_mono hRT).trans hc'))) Ph.ph_SC_Om1 _
          (LeCl.small (hΘc.trans_le hc')))

end Data

end Googology.Trans.PoR.InaccPsi.R2.Sg
