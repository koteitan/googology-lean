import Googology.Trans.PoR.InaccPsi.R2.RvLevL

/-!
# The own arguments over a family of shifts INDEXED BY THE BASE, and THE BLOCK LAW for them

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `G = ψ_{Ω₂}(0)`.
`Sh b X X̂` is a family of shifts indexed by the base `b` (the shift `X` is own relative to `b`, `Rv.RvSh`, and has
the top law at the bases `≥ b`, `Rv.RvTop`).  Unlike `Ro.RoOwn` (one family for every base), the shift of a digit
at the base `β` is taken from `Sh β`: so the codes inside the shift may be larger than `ψ_{Ω₂}(W^X)`, only below
`ψ_{Ω₂}(β + W^X)`.

`RwOwn S λ Sh X e β c v` (**`c` is an own argument of exponent `X + e` over `β`, level-1 image `v`**):
* `low`: `(0, e, c, v)` for `Le.LeOwnH S λ e β c v`;
* `succ`: `(X, e + 1, W^{X+e}·γ + c', Ω^{X̂+Θ e}·Θ γ + v')` for `Sh β X X̂`, codes `e`, `γ ≠ 0`,
  `γ < T_{X+e+1}(β)`, and `(X', e', c', v')` own over `β + W^{X+e}·γ` with `X' = X`, `e' ≤ e`, or `X' + Ω₂ ≤ X`,
  `e' < T_{X'+Ω₂}(β + W^{X+e}·γ)`.

* `rwOwn_sh`, `rwBase_lower` (a base of exponent `X + e` is a base of a lower relative shift at its own exponents),
  `rwBase_next`;
* `rwOwnRead` (**THE BLOCK LAW: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + v)`, `Â + v` own, `c < W^{X+e}`, `v < G`**);
* `rwOwn_own`, `rwOwn_mem` (an own argument is own in the closure sense, in the hull, below `A_{η_λ}`).

No new axiom.  New definition: `RwOwn`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

/-- **The own arguments of exponent `X + e` over `β`, with their level-1 images**, over a family `Sh` of shifts
indexed by the base. -/
inductive RwOwn (S : InaccSeq.{0}) (l : Ordinal.{0}) (Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop) :
    Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | low {e β c v : Ordinal.{0}} : LeOwnH S l e β c v → RwOwn S l Sh 0 e β c v
  | succ {X Xh e X' e' β γ c' v : Ordinal.{0}} : Sh β X Xh → GxCl (upsilon l) (ldAtR S l) e →
      GxCl (upsilon l) (ldAtR S l) γ → γ ≠ 0 → γ < leTe S (X + e + 1) β →
      ((X' = X ∧ e' ≤ e) ∨
        (X' + Om (1 + 1) ≤ X ∧ e' < leTe S (X' + Om (1 + 1)) (β + leWe (X + e) * γ))) →
      RwOwn S l Sh X' e' (β + leWe (X + e) * γ) c' v →
      RwOwn S l Sh X (e + 1) β (leWe (X + e) * γ + c')
        (leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ + v)

/-- The shift of an own argument is `0` or in the family at its base. -/
theorem rwOwn_sh {l : Ordinal.{0}} {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop} {X e β c v : Ordinal.{0}}
    (h : RwOwn S l Sh X e β c v) : X = 0 ∨ ∃ Xh, Sh β X Xh := by
  cases h with
  | low _ => exact Or.inl rfl
  | succ hsh _ _ _ _ _ _ => exact Or.inr ⟨_, hsh⟩

/-- **A base of exponent `X + e` is a base of a lower shift `X'` (`X' + Ω₂ ≤ X`), own relative to `b' ≤ β`, at
every own exponent `e'`.** -/
theorem rwBase_lower {l X e X' e' β b' : Ordinal.{0}} (hX' : X' = 0 ∨ ∃ Xh', RvSh S l b' X' Xh')
    (hbβ : b' ≤ β) (hb : RoBaseE S l X e β) (hXX : X' + Om (1 + 1) ≤ X)
    (he' : e' < leTe S (X' + Om (1 + 1)) β) : RoBaseE S l X' e' β := by
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
  · exact rvTW_gt hs' hownW hbβ hdW he''

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Sh : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}
  (hSh : ∀ b X Xh, Sh b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e)

include hl hX hSh

/-- The base of the lower own argument of a `succ`. -/
theorem rwBase_next {X Xh e X' e' β γ : Ordinal.{0}} (hsh : Sh β X Xh) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγT : γ < leTe S (X + e + 1) β)
    (hcond : (X' = X ∧ e' ≤ e) ∨
      (X' + Om (1 + 1) ≤ X ∧ e' < leTe S (X' + Om (1 + 1)) (β + leWe (X + e) * γ)))
    (hX' : X' = 0 ∨ ∃ Xh', Sh (β + leWe (X + e) * γ) X' Xh') (hb : RoBaseE S l X (e + 1) β) :
    RoBaseE S l X e (β + leWe (X + e) * γ) ∧ RoBaseE S l X' e' (β + leWe (X + e) * γ) := by
  obtain ⟨hs, -⟩ := hSh β X Xh hsh
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hbsub := rvBaseE_sub hs le_rfl hl hX hb hec ((ldHull_iff hl hX hγW).2 hγc) hγT
  refine ⟨hbsub, ?_⟩
  rcases hcond with ⟨rfl, he'e⟩ | ⟨hXX, he'⟩
  · exact roBaseE_mono he'e hbsub
  · refine rwBase_lower (b' := β + leWe (X + e) * γ) ?_ le_rfl hbsub hXX he'
    rcases hX' with h0 | ⟨Xh', h'⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh', (hSh _ _ _ h').1⟩

/-- **THE BLOCK LAW** for the own arguments over a base-indexed family of shifts. -/
theorem rwOwnRead {X e β c v : Ordinal.{0}} (h : RwOwn S l Sh X e β c v) : ∀ Â, RoBaseE S l X e β →
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
    obtain ⟨hs, hT⟩ := hSh β X Xh hsh
    have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec (lt_add_one e).le
    have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
    obtain ⟨eγ, ownγ⟩ := rvStepA hs hl hX hec (hT e hec heW) hb le_rfl hÂ hbase γ hγc hγT
    obtain ⟨hbsub, hb'⟩ := rwBase_next hl hX hSh hsh hec hγc hγT hcond (rwOwn_sh hsub) hb
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
      obtain ⟨hEC, hEG, hEL⟩ := rvE_data hs le_rfl hexp
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
theorem rwOwn_own {X e β c v : Ordinal.{0}} (h : RwOwn S l Sh X e β c v) :
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
    obtain ⟨-, hb'⟩ := rwBase_next hl hX hSh hsh hec hγc hγT hcond (rwOwn_sh hsub) hb
    rw [← add_assoc]
    exact ih hb'

/-- An own argument is in the hull and below `A_{η_λ}`. -/
theorem rwOwn_mem {X e β c v : Ordinal.{0}} (h : RwOwn S l Sh X e β c v) :
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
    obtain ⟨-, hb'⟩ := rwBase_next hl hX hSh hsh hec hγc hγT hcond (rwOwn_sh hsub) hb
    rw [← add_assoc]
    exact ih hb'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw
