import Googology.Trans.PoR.InaccPsi.R2.RoK

/-!
# The own arguments over a family of shifts, and THE BLOCK LAW for them

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `G = ψ_{Ω₂}(0)`.
`Sh` is a family of shifts (pairs `(X, X̂)`, e.g. `{(Ω₂·k, Ω₁·k) | k ≥ 1}`).

`RoOwn S λ Sh X e β c v` (**`c` is an own argument of exponent `X + e` over `β`, level-1 image `v`**):
* `low`: `(0, e, c, v)` for `Le.LeOwnH S λ e β c v` (the exponents below `Ω₂`);
* `succ`: `(X, e + 1, W^{X+e}·γ + c', Ω^{X̂+Θ e}·Θ γ + v')` for `(X, X̂) ∈ Sh`, codes `e`, `γ ≠ 0`,
  `γ < T_{X+e+1}(β)` and `(X', e', c', v')` own over `β + W^{X+e}·γ` with either `X' = X`, `e' ≤ e`, or
  `X' + Ω₂ ≤ X` and `e' < T_{X'+Ω₂}(β + W^{X+e}·γ)` (a lower shift, whose exponents are own there).
So `v` reads the base-`Ω₂` digits and their exponents `X + e` at base `Ω₁`: `X ↦ X̂`, `e ↦ Θ e`.

* `roGx_lt_Om2`, `roLeOwn_lt` (the codes are below `Ω₂`), `roOwn_sh` (the shift of an own argument is `0` or in
  `Sh`), `roBase_lower` (**a base of exponent `X + e` is a base of every lower shift `X'` at its own exponents**);
* `roOwnRead` (**THE BLOCK LAW: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + v)`, `Â + v` own, `c < W^{X+e}`, `v < G`** for every
  own `(X, e, c, v)` over a base `β` of shift `X` and exponent `e` with `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own, given
  the top law `RoTop` at every shift of `Sh` and every code);
* `roOwn_own`, `roOwn_mem` (an own argument is own in the closure sense, in the hull, below `A_{η_λ}`).

No new axiom.  New definition: `RoOwn`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-- **The own arguments of exponent `X + e` over `β`, with their level-1 images**, over a family `Sh` of shifts. -/
inductive RoOwn (S : InaccSeq.{0}) (l : Ordinal.{0}) (Sh : Ordinal.{0} → Ordinal.{0} → Prop) :
    Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | low {e β c v : Ordinal.{0}} : LeOwnH S l e β c v → RoOwn S l Sh 0 e β c v
  | succ {X Xh e X' e' β γ c' v : Ordinal.{0}} : Sh X Xh → GxCl (upsilon l) (ldAtR S l) e →
      GxCl (upsilon l) (ldAtR S l) γ → γ ≠ 0 → γ < leTe S (X + e + 1) β →
      ((X' = X ∧ e' ≤ e) ∨
        (X' + Om (1 + 1) ≤ X ∧ e' < leTe S (X' + Om (1 + 1)) (β + leWe (X + e) * γ))) →
      RoOwn S l Sh X' e' (β + leWe (X + e) * γ) c' v →
      RoOwn S l Sh X (e + 1) β (leWe (X + e) * γ + c')
        (leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ + v)

/-- The codes are below `Ω₂`. -/
theorem roGx_lt_Om2 {l x : Ordinal.{0}} (hρ1 : upsilon l < Om 1) (hx : GxCl (upsilon l) (ldAtR S l) x) :
    x < Om (1 + 1) := by
  induction hx with
  | small h => exact (h.trans hρ1).trans gg_Om1_lt_Om2
  | om => exact gg_Om1_lt_Om2
  | atom hs =>
    obtain ⟨a, -, -, rfl⟩ := hs
    exact psi_lt (InR_Om_succ 1) _
  | add _ _ ihx ihy => exact ldOm2_SC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact ldOm2_SC.2 _ ihx _ ihy

theorem roLeOwn_lt {l e β c v : Ordinal.{0}} (hρ1 : upsilon l < Om 1) (h : LeOwnH S l e β c v) :
    e < Om (1 + 1) := by
  cases h with
  | zero => exact ldOm2_SC.1
  | one => exact (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
  | succ hec _ _ _ _ _ _ => exact ldOm2_SC.isSuccLimit.succ_lt (roGx_lt_Om2 hρ1 hec)

/-- The shift of an own argument is `0` or in the family. -/
theorem roOwn_sh {l : Ordinal.{0}} {Sh : Ordinal.{0} → Ordinal.{0} → Prop} {X e β c v : Ordinal.{0}}
    (h : RoOwn S l Sh X e β c v) : X = 0 ∨ ∃ Xh, Sh X Xh := by
  cases h with
  | low _ => exact Or.inl rfl
  | succ hsh _ _ _ _ _ _ => exact Or.inr ⟨_, hsh⟩

/-- **A base of exponent `X + e` is a base of a lower shift `X'` (`X' + Ω₂ ≤ X`) at every own exponent `e'`.** -/
theorem roBase_lower {l X e X' e' β : Ordinal.{0}} (hX' : X' = 0 ∨ ∃ Xh', RoSh S X' Xh')
    (hb : RoBaseE S l X e β) (hXX : X' + Om (1 + 1) ≤ X) (he' : e' < leTe S (X' + Om (1 + 1)) β) :
    RoBaseE S l X' e' β := by
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  have he'W : e' < Om (1 + 1) := he'.trans (leTe_lt_Om2 _ _)
  have hle1 : X' + e' ≤ X' + Om (1 + 1) := (add_le_add_iff_left X').2 he'W.le
  have hle2 : X' + Om (1 + 1) ≤ X + e := hXX.trans le_self_add
  have hdW : leWe (X' + Om (1 + 1)) ∣ β := (leWe_dvd hle2).trans hβd
  have hownW : ∀ d, d ≤ leWe (X' + Om (1 + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
    fun d hd => hβown d (hd.trans (leWe_mono hle2))
  refine ⟨(leWe_dvd (hle1.trans hle2)).trans hβd, hβH,
    lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono (hle1.trans hle2))) hβA,
    fun d hd => hβown d (hd.trans (leWe_mono (hle1.trans hle2))), fun e'' _ h'' => ?_⟩
  have he'' := h''.trans_lt he'
  rcases hX' with rfl | ⟨Xh', hs'⟩
  · rw [zero_add] at hdW hownW he'' ⊢
    exact rnTW_gt hownW hdW he''
  · exact roTW_gt hs' hownW hdW he''

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Sh : Ordinal.{0} → Ordinal.{0} → Prop}
  (hSh : ∀ X Xh, Sh X Xh → RoSh S X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e)

include hl hX hSh

/-- The base of the lower own argument of a `succ`. -/
theorem roBase_next {X Xh e X' e' β γ : Ordinal.{0}} (hsh : Sh X Xh) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγT : γ < leTe S (X + e + 1) β)
    (hcond : (X' = X ∧ e' ≤ e) ∨
      (X' + Om (1 + 1) ≤ X ∧ e' < leTe S (X' + Om (1 + 1)) (β + leWe (X + e) * γ)))
    (hX' : X' = 0 ∨ ∃ Xh', RoSh S X' Xh') (hb : RoBaseE S l X (e + 1) β) :
    RoBaseE S l X e (β + leWe (X + e) * γ) ∧ RoBaseE S l X' e' (β + leWe (X + e) * γ) := by
  obtain ⟨hs, -⟩ := hSh X Xh hsh
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hbsub := roBaseE_sub hs hl hX hb hec ((ldHull_iff hl hX hγW).2 hγc) hγT
  refine ⟨hbsub, ?_⟩
  rcases hcond with ⟨rfl, he'e⟩ | ⟨hXX, he'⟩
  · exact roBaseE_mono he'e hbsub
  · exact roBase_lower hX' hbsub hXX he'

/-- **THE BLOCK LAW** for the own arguments over a family of shifts. -/
theorem roOwnRead {X e β c v : Ordinal.{0}} (h : RoOwn S l Sh X e β c v) : ∀ Â, RoBaseE S l X e β →
    Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + c) (Om (1 + 1))) = S.psi (Â + v) (Om 1) ∧
    Â + v ∈ S.CSet (Â + v) (S.psi (Â + v) (Om 1)) ∧ c < leWe (X + e) ∧ v < S.psi 0 (Om (1 + 1)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  induction h with
  | @low e β c v hown =>
    intro Â hb hÂ hbase
    have hbE : LeBaseE S l e β := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [zero_add] at h1 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨e1, own, hv, hc⟩ := leOwnRead hl hX hown Â hbE hÂ hbase
    refine ⟨e1, own, by rwa [zero_add], ?_⟩
    rcases eq_or_ne e 0 with rfl | he0
    · rw [gxTh_zero, leOe_zero] at hv
      exact hv.trans_le (Order.one_le_iff_pos.2 hG1.1)
    have heW := roLeOwn_lt hρ1 hown
    have hec := leOwnH_code hl hX hown heW
    have hT := leTopE hl hX e hec (Order.one_le_iff_ne_zero.2 he0) β Â hbE hÂ hbase
    have heT : e < leTe S e β := hbE.2.2.2.2 e hec le_rfl
    have hΘe : gxTh (upsilon l) (ldAtR S l) e < Om 1 := by
      refine (gxTh_lt hec heT).trans ?_
      rw [hT]; exact psi_lt Low.InR_Om_one _
    exact hv.trans (leOe_lt_SC hG1 hΩG1 (hΘe.trans hΩG1)).1
  | @succ X Xh e X' e' β γ c' v hsh hec hγc hγ0 hγT hcond hsub ih =>
    intro Â hb hÂ hbase
    obtain ⟨hs, hT⟩ := hSh X Xh hsh
    have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec (lt_add_one e).le
    have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
    obtain ⟨eγ, ownγ⟩ := roStepA hs hl hX hec (hT e hec heW) hb hÂ hbase γ hγc hγT
    obtain ⟨hbsub, hb'⟩ := roBase_next hl hX hSh hsh hec hγc hγT hcond
      (by rcases roOwn_sh hsub with h0 | ⟨Xh', h'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨Xh', (hSh _ _ h').1⟩) hb
    obtain ⟨e2, own2, hc', hv'⟩ := ih _ hb' ownγ eγ
    rw [← add_assoc β, ← add_assoc Â]
    refine ⟨e2, own2, ?_, ?_⟩
    · have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
      have hle : X' + e' ≤ X + e := by
        rcases hcond with ⟨rfl, he'e⟩ | ⟨hXX, he'⟩
        · exact (add_le_add_iff_left X').2 he'e
        · exact ((add_le_add_iff_left X').2 (he'.trans (leTe_lt_Om2 _ _)).le).trans (hXX.trans le_self_add)
      have hc'e : c' < leWe (X + e) := hc'.trans_le (leWe_mono hle)
      rw [← add_assoc, leWe_succ]
      calc leWe (X + e) * γ + c' < leWe (X + e) * γ + leWe (X + e) := (add_lt_add_iff_left _).2 hc'e
        _ = leWe (X + e) * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe (X + e) * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hγW)
    · obtain ⟨hβd, -, hβown⟩ := roBase_succ hb
      obtain ⟨hEC, hEG, hEL⟩ := roE_data hs hexp
      have hγs : γ < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := roTe_gt hβown hEC hβd hEG hEL hγT
      have hes : e < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := by
        refine hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
        calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
          _ ≤ leWe (X + e) * γ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hγ0)
      have hlt1 : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e) * γ) (Om (1 + 1))) < Om 1 := by
        rw [eγ]; exact psi_lt Low.InR_Om_one _
      have hΘe := (gxTh_lt hec hes).trans hlt1
      have hΘγ := (gxTh_lt hγc hγs).trans hlt1
      have hy : Xh + gxTh (upsilon l) (ldAtR S l) e < S.psi 0 (Om (1 + 1)) :=
        ((add_lt_add_iff_left Xh).2 hΘe).trans hs.ltG
      have hO := (leOe_lt_SC hG1 hΩG1 hy).1
      exact hG1.isPrincipal (ldMul_lt_SC hG1 hO (hΘγ.trans hΩG1)) hv'

/-- An own argument is own in the closure sense. -/
theorem roOwn_own {X e β c v : Ordinal.{0}} (h : RoOwn S l Sh X e β c v) :
    RoBaseE S l X e β → β + c ∈ S.CSet (β + c) (S.psi (β + c) (Om (1 + 1))) := by
  induction h with
  | @low e β c v hown =>
    intro hb
    have hbE : LeBaseE S l e β := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [zero_add] at h1 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    exact leOwnH_own hl hX hown hbE
  | @succ X Xh e X' e' β γ c' v hsh hec hγc hγ0 hγT hcond hsub ih =>
    intro hb
    obtain ⟨-, hb'⟩ := roBase_next hl hX hSh hsh hec hγc hγT hcond
      (by rcases roOwn_sh hsub with h0 | ⟨Xh', h'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨Xh', (hSh _ _ h').1⟩) hb
    rw [← add_assoc]
    exact ih hb'

/-- An own argument is in the hull and below `A_{η_λ}`. -/
theorem roOwn_mem {X e β c v : Ordinal.{0}} (h : RoOwn S l Sh X e β c v) :
    RoBaseE S l X e β → β + c ∈ cdHull S l ∧ β + c < ConjT.Aη S (cdEta S l) := by
  induction h with
  | @low e β c v hown =>
    intro hb
    have hbE : LeBaseE S l e β := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [zero_add] at h1 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    exact leOwnH_mem hl hX hown hbE
  | @succ X Xh e X' e' β γ c' v hsh hec hγc hγ0 hγT hcond hsub ih =>
    intro hb
    obtain ⟨-, hb'⟩ := roBase_next hl hX hSh hsh hec hγc hγT hcond
      (by rcases roOwn_sh hsub with h0 | ⟨Xh', h'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨Xh', (hSh _ _ h').1⟩) hb
    rw [← add_assoc]
    exact ih hb'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ro
