import Googology.Trans.PoR.InaccPsi.R2.SgSup

/-!
# The bridge: own at its own level (closure form) gives the derivation's own predicate at a proper base

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(b) = ψ_{Ω₂}(b + W^E)`.

* `SgLimT` (**the closure condition of a coefficient `c` at the truncation `G`**: every limit `η ≤ c` lies below
  `T_{X₀ + W^{G η}}(b)`, i.e. the code is own at the level of the exponent truncated at it), `SgOwnT` (the same at
  every coefficient of a term, with the truncations of `Sg.SgOwn`);
* `sgBridge` (**at a base `β` with `W^{X₀ + W^{E*}} ∣ β`, `β` own for `d ≤ W^{X₀ + W^{E*}}`, the offset data of
  `X₀` and `X₀ + W^{E*} < ψ_{Ω₃}(0)`, the closure condition `SgOwnT` of a term `t` in an own context `K` with
  `K(val t) ≤ E*` gives `Sg.SgOwn`**: each limit `η` goes below some `SQ_j` by `Sg.sgSq_supAt` on the path shape
  `ζ ↦ K(P + W^R·ζ)`);
* `sgLevT_all` (**THE TOP LAW AT EVERY `1 ≤ E < ε_{Ω₂+1}` of `H_λ` with the closure own condition at the
  bases**: `Θ(ψ_{Ω₂}(β + W^{X₀ + W^E})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Θ̂ E}})` whenever every base `β ≥ b` of
  `Ro.RoBaseE (X₀ + W^E) 0` has `SgOwnT β X₀ id (sgTmH E)`), `sgSh_all` (**the shift `(X₀ + W^E, X̂₀ + Ω^{Θ̂ E})`
  is own relative to `b`**, `Rv.RvSh`, under `SgOwn b X₀ id (sgTmH E)`), `sgTop0` (**the reading of the atoms
  `Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^E})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{Θ̂ E}})`** for `1 ≤ E < ε_{Ω₂+1}`).

No new axiom.  New definitions: `SgLimT`, `SgOwnT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

/-- **The closure condition of a coefficient `c` at the truncation `G`.** -/
def SgLimT (S : InaccSeq.{0}) (G : Ordinal.{0} → Ordinal.{0}) (c b X0 : Ordinal.{0}) : Prop :=
  ∀ η, η ≤ c → IsSuccLimit η → η < S.psi (b + leWe (X0 + leWe (G η))) (Om (1 + 1))

/-- **The closure condition at every coefficient of a term.** -/
def SgOwnT (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → SgT → Prop
  | _, .zero => True
  | e, .term P R c => SgOwnT S b X0 e P ∧ SgOwnT S b X0 (fun r => e (sgV P + leWe r)) R ∧
      SgLimT S (fun z => e (sgV P + leWe (sgV R) * z)) c b X0

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
theorem sgBridge : ∀ (t : SgT) (K : SgC), SgWFC S l K → SgWF S l t → SgOwnC S β X0 K →
    SgOwnT S β X0 (sgE K) t → sgE K (sgV t) ≤ Es → SgOwn S β X0 (sgE K) t
  | .zero, _, _, _, _, _, _ => trivial
  | .term P R c, K, hKw, ⟨hPw, hRw, hc, hc1, hcW⟩, hKo, ⟨hPT, hRT, hcT⟩, hEs => by
    have hPle : sgE K (sgV P) ≤ Es := (sgE_mono K (le_self_add : sgV P ≤ sgV P + leWe (sgV R) * c)).trans hEs
    have hPo := sgBridge P K hKw hPw hKo hPT hPle
    have hKPo : SgOwnC S β X0 (SgC.pfx K P) := ⟨hKo, hPo⟩
    have hRle : sgE (SgC.lft (SgC.pfx K P)) (sgV R) ≤ Es := by
      refine (sgE_mono K ((add_le_add_iff_left _).2 ?_)).trans hEs
      simpa using leMulWe_mono (e := sgV R) hc1
    have hRo := sgBridge R (SgC.lft (SgC.pfx K P)) ⟨hKw, hPw⟩ hRw hKPo hRT hRle
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    -- the path shape `ζ ↦ K(P + W^R·ζ)` at the base `β`
    have hsh := sgShp_path hl hX (K := SgC.pfx K P) (F := R) ⟨hKw, hPw⟩ hRw hKPo hRo
    set g : Ordinal.{0} → Ordinal.{0} := fun z => sgE (SgC.pfx K P) (leWe (sgV R) * z) with hg
    have hGst : StrictMono (fun z => leWe (g z)) := fun _ _ h => leWe_lt (hsh.st h)
    have hηW : η < Om (1 + 1) := hη.trans_lt hcW
    have hgη : g η ≤ Es := (sgE_mono (SgC.pfx K P) (leMulWe_mono hη)).trans hEs
    have hd1 : (1 : Ordinal.{0}) ≤ Om 1 := (gg_one_lt_of_SC Ph.ph_SC_Om1).le
    have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (hsh.st.monotone hd1)))))).1
    have hWle : leWe (X0 + leWe (g η)) ≤ leWe (X0 + leWe Es) :=
      leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hgη))
    exact sgSq_supAt (G := fun z => leWe (g z)) (Gs := leWe (sgE (SgC.pfx K P) (leWe (sgV R + 1)))) hGst
      (fun d hd => hβown d (hd.trans hWle)) hX0m
      (fun x c' hx hc' => leWe_mem (hsh.mem x c' hx (hbot.trans hc')))
      (fun x hx => leWe_mono (hsh.lt x hx).le)
      (fun Q hQ hc' => scShCl_lift hQ hsh.inf (hsh.cl Q hQ (hbot.trans hc')))
      ((leWe_dvd ((add_le_add_iff_left X0).2 (leWe_mono hgη))).trans hβd) hX0cl
      (lt_of_le_of_lt ((add_le_add_iff_left X0).2 (leWe_mono hgη)) hX0G3)
      (hcT η hη hlim)

end Bridge

section All

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE TOP LAW AT EVERY `1 ≤ E < ε_{Ω₂+1}` of `H_λ` with the closure own condition at the bases.** -/
theorem sgLevT_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hT : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → SgOwnT S β X0 (fun y => y) (sgTmH E)) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) 0 := by
  intro β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb'
  rw [add_zero] at hβd hβown
  have hOw : SgOwn S β X0 (fun y => y) (sgTmH E) :=
    sgBridge hl hX (Es := E) hβd hβown hX0m hX0cl (le_self_add.trans_lt hG3) (sgTmH E) SgC.hole trivial hw
      trivial (hT β hbβ hb) (by rw [hv]; exact le_rfl)
  exact sgLev_all hl hX hEH hE1 hE β X0 Xh0 hoffβ hd hG3 hG hOw β Â hb le_rfl hÂ hbase

/-- **The shift `(X₀ + W^E, X̂₀ + Ω^{Θ̂ E})` is own relative to `b`** under the own predicate of `E`. -/
theorem sgSh_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    {b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hOw : SgOwn S b X0 (fun y => y) (sgTmH E)) :
    RvSh S l b (X0 + leWe E) (Xh0 + leOe (sgThH S l E)) :=
  scShLev hoff ((scDer_sound hl hX (sgDer_all hl hX hEH hE1 hE)).2.dat b X0 hOw) hG3 hG

/-- **The reading of the atoms `ψ_{Ω₂}(β + W^{W^E})`, `1 ≤ E < ε_{Ω₂+1}`**:
`Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^E})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{Θ̂ E}})` at a base `β` of `Ro.RoBaseE (W^E) 0` with a reading
`Θ(ψ_{Ω₂} β) = ψ_{Ω₁} Â`, when the closure own condition holds at the bases `≥ β`. -/
theorem sgTop0 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1))
    (hG3 : leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : leOe (sgThH S l E) + Om 1 < S.psi 0 (Om (1 + 1))) {β Â : Ordinal.{0}}
    (hb : RoBaseE S l (leWe E) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    (hT : ∀ β', β ≤ β' → RoBaseE S l (leWe E) 0 β' → SgOwnT S β' 0 (fun y => y) (sgTmH E)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (leWe E)) (Om (1 + 1))) =
      S.psi (Â + leOe (leOe (sgThH S l E))) (Om 1) := by
  have h := sgLevT_all hl hX hEH hE1 hE (b := β) (X0 := 0) (Xh0 := 0) (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
    (by rwa [zero_add]) (by rwa [zero_add]) (fun β' h1 h2 => hT β' h1 (by rwa [zero_add] at h2))
    β Â (by rwa [zero_add]) le_rfl hÂ hbase
  unfold leTe at h
  rwa [add_zero, zero_add, gxTh_zero, add_zero, zero_add] at h

end All

end Googology.Trans.PoR.InaccPsi.R2.Sg
