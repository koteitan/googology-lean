import Googology.Trans.PoR.InaccPsi.R2.ZiPlatR

/-!
# MOVING SHIFTS: `B_n` maps the shift `X` of `λ` to a shift `X'` of `λ'`

`W^x = leWe x`, `Ω^x = leOe x`, `B_n = Bc.bcB S n`, `e^{X,β}_m = Yd.ydEB S X β m`.  A shift whose coefficient is a code
(`X = P + Ω₂·ξ`, `ξ` a code of `λ`) is moved by `B_n` to `X' = P + Ω₂·B_n ξ`, its image `X̂ = P̂ + Ω₁·Θ_λ ξ` to
`X̂' = P̂ + Ω₁·Θ_{λ'}(B_n ξ)`.  `ZiShB S n X X̂ X' X̂'`: `X̂, X̂' ≠ 0`, `B_n(Ω₂·X) = Ω₂·X'`, `B_n(Ω₁·X̂) = Ω₁·X̂'` (with
the domain facts); `Ro.RoShB S X X̂` is the case `X' = X`, `X̂' = X̂` at every `n` (`ziShB_of_ro`).

* `ziB_We` (**`B_n(W^{X+e}·γ) = W^{X'+B_n e}·B_n γ`**; `Ro.roB_We` is `X' = X`),
* `ziB_Oe` (**`B_n(Ω^{X̂+y}·x) = Ω^{X̂'+B_n y}·B_n x`**; `Ro.roB_Oe` is `X̂' = X̂`),
* `ziFixBr` (**`B_n e^{X,β}_m = e^{X',B_n β}_m`**; `Zd.zdFixBr` is `X' = X`, membership in every closure above `β`),
* `ziOwnMoveBr` (**THE OWN CLAUSE MOVES** for a moving shift; `Zd.zdOwnMoveBr` is `X' = X`).

No new axiom.  New definition: `ZiShB` (the move data of a moving shift).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd
  Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

/-- **The move data of a moving shift** `(X, X̂) ↦ (X', X̂')` under `B_n`. -/
def ZiShB (S : InaccSeq.{0}) (n : ℕ) (X Xh X' Xh' : Ordinal.{0}) : Prop :=
  Xh ≠ 0 ∧ Xh' ≠ 0 ∧ MvD S (Om (1 + 1) * X) ∧ Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * X' ∧
    MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * Xh'

/-- A fixed shift is a moving shift with `X' = X`, `X̂' = X̂`. -/
theorem ziShB_of_ro {X Xh : Ordinal.{0}} (h : RoShB S X Xh) (n : ℕ) : ZiShB S n X Xh X Xh := by
  obtain ⟨a, b, c, d⟩ := h.2 n
  exact ⟨h.1, h.1, a, b, c, d⟩

/-- **`B_n(W^{X+e}·γ) = W^{X'+B_n e}·B_n γ`** for a moving shift (`Ro.roB_We` is `X' = X`). -/
theorem ziB_We {n : ℕ} {X Xh X' Xh' : Ordinal.{0}} (hX0 : X ≠ 0) (hB : ZiShB S n X Xh X' Xh')
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {e γ : Ordinal.{0}} (he : P e) (hγ : P γ) :
    MvD S (leWe (X + e)) ∧ Bc.bcB S n (leWe (X + e)) = leWe (X' + Bc.bcB S n e) ∧
      MvD S (leWe (X + e) * γ) ∧ Bc.bcB S n (leWe (X + e) * γ) = leWe (X' + Bc.bcB S n e) * Bc.bcB S n γ := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDWe, hBWe⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 P hPD hPdec hPW e he
  obtain ⟨-, -, hDWX, hBWX, -, -⟩ := hB
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDWX hDWe
  rw [hBWX, hBWe] at hBK
  obtain ⟨hD, hBo⟩ := ldB_opow (n := n) hDK
  have hWX : Om (1 + 1) ≤ Om (1 + 1) * X := le_mul_left _ (pos_iff_ne_zero.2 hX0)
  have h := leB_mulOp2 (n := n) hDK P hPD hPdec
    (fun z hz => ((hPW z hz).trans_le hWX).trans_le le_self_add) γ hγ
  rw [hBK] at h hBo
  unfold leWe
  rw [mul_add, mul_add]
  exact ⟨hD, hBo, h⟩

/-- **`B_n(Ω^{X̂+y}·x) = Ω^{X̂'+B_n y}·B_n x`** for a moving shift, countable `y`, `x` below `c_{n+1}`. -/
theorem ziB_Oe {n : ℕ} {X Xh X' Xh' : Ordinal.{0}} (hB : ZiShB S n X Xh X' Xh') {y x : Ordinal.{0}} (hy1 : y < Om 1)
    (hyc : y < Bc.bcC S (n + 1)) (hx1 : x < Om 1) (hxc : x < Bc.bcC S (n + 1)) :
    MvD S (leOe (Xh + y) * x) ∧ Bc.bcB S n (leOe (Xh + y) * x) = leOe (Xh' + Bc.bcB S n y) * Bc.bcB S n x := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDy, hBy⟩ := leB_mulOm1 (S := S) (n := n) hy1 hyc
  obtain ⟨h0, -, -, -, hDX, hBX⟩ := hB
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDX hDy
  rw [hBX, hBy] at hBK
  have hΩX : Om (1 : Ordinal.{0}) ≤ Om 1 * Xh := le_mul_left _ (pos_iff_ne_zero.2 h0)
  have h := leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => (hz.1.trans_le hΩX).trans_le le_self_add) x ⟨hx1, hxc⟩
  rw [hBK] at h
  unfold leOe
  rw [mul_add, mul_add]
  exact h


section Data

variable {n : ℕ} {X Xh X' Xh' : Ordinal.{0}} (hX0 : X ≠ 0) (hShB : ZiShB S n X Xh X' Xh')
include hX0 hShB

/-- **`B_n e^{X,β}_m = e^{X',B_n β}_m`** for a moving shift `X ↦ X'` with relative membership (`β` normal in the domain). -/
theorem ziFixBr {β : Ordinal.{0}} (hXr : ZiMemR S β X)
    (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) :
    ∀ m, MvD S (ydEB S X β m) ∧ Bc.bcB S n (ydEB S X β m) = ydEB S X' (Bc.bcB S n β) m
  | 0 => by
    rw [ydEB_zero, ydEB_zero]
    have hc : (0 : Ordinal.{0}) < Bc.bcC S n := (Lw.lw_L_SC S _).1
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_fix' S n 0 hc⟩
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨hDm, hBm⟩ := ziFixBr hXr hDβ hβ m
    set P : Ordinal.{0} → Prop := fun x => x = 0 ∨ (x = ydEB S X β m ∧ SC x) with hP
    have hPD : ∀ x, P x → MvD S x := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact mvD_of_lt (Lw.lw_L_SC S ω).1
      · exact hDm
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := by
      rintro x (rfl | ⟨hx, hxS⟩) hx0
      · exact absurd rfl hx0
      · have hl : log ω x = x := by
          conv_lhs => rw [← gg_SC_eps hxS]
          exact log_opow one_lt_omega0 x
        rw [hl, gg_SC_eps hxS, Ordinal.sub_self]
        exact ⟨Or.inr ⟨hx, hxS⟩, Or.inl rfl⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact ldOm2_SC.1
      · exact ydEB_lt_Om2 X β m
    have hPm : P (ydEB S X β m) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨rfl, ydEB_SC X β j⟩
    obtain ⟨hDW, hBW, -, -⟩ := ziB_We (n := n) hX0 hShB P hPD hPdec hPW hPm hPm
    rw [hBm] at hBW
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    rw [hBW] at hBa
    have hown : β + leWe (X + ydEB S X β m) ∈ S.CSet (β + leWe (X + ydEB S X β m))
        (S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) := by
      refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβ)
        (leWe_mem (CSet.add_mem (hXr _ _ (lt_add_of_pos_right β (leWe_pos _))
          (psi_mono hκ2 (add_le_add_right (leWe_mono le_self_add) β)).1) (CSet.of_lt ?_)))
      rw [← ydEB_succ]; exact ziEBr_lt_succ hXr hβ m
    obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
    rw [hBa] at hBs
    rw [ydEB_succ, ydEB_succ]
    exact ⟨hDs, hBs⟩

/-- **THE OWN CLAUSE MOVES** for a moving shift `X ↦ X'` (relative membership over `β` and over `B_n β`). -/
theorem ziOwnMoveBr {β e : Ordinal.{0}} (hXr : ZiMemR S β X)
    (hXr' : ZiMemR S (Bc.bcB S n β) X')
    (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hDe : MvD S e)
    (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X' + Om (1 + 1))) (Om (1 + 1)) ∧
      ∀ e'', e'' ≤ Bc.bcB S n e → e'' < S.psi (Bc.bcB S n β + leWe (X' + e'')) (Om (1 + 1)) := by
  obtain ⟨m, hm⟩ := ziLtTopBr hXr hβ he
  obtain ⟨hDm, hBm⟩ := ziFixBr hX0 hShB hXr hDβ hβ m
  have h := (mvB_lt_iff (k := n) hDe hDm).2 hm
  rw [hBm] at h
  have hB' : Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X' + Om (1 + 1))) (Om (1 + 1)) :=
    h.trans_le (ydEB_le_top _ _ m)
  exact ⟨hB', (ziOwnBr_iff hXr' (ydNormB n hDβ hβ) _).2 hB'⟩

end Data

end Googology.Trans.PoR.InaccPsi.R2.Zi
