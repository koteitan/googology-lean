import Googology.Trans.PoR.InaccPsi.R2.WaRoad

/-!
# `CxEQtop` split at `δ_λ·ω`: the reading move below, EQ only above

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ν_C = nuC`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`,
`k_λ = Cd.cdk λ`, `Θ_λ = Cd.cdTheta S λ`, `m_λ = Cd.cdCode S λ`, `r(λ) = k_λ(Θ_λ(m_λ))`, `θ⁺ = Lj.ljThP S`,
`M_W = Rn.rnMW S`.

* `wdk_eq` (**`k_λ(x) = δ_λ + x` for every `x < δ_λ·ω`** when `δ_λ < ν_C`; extends `Mv.mvk_eq` from `x < δ_λ`):
  the points of `(δ_λ, δ_λ·ω)` are decomposable, so every `δ_λ + x < δ_λ·ω` is closed;
* `wdk_move` (**`k_{λ'}(B_n p) = B_n(k_λ(p))` for every `p < δ_λ·ω`**, `δ_λ < L(n+2)`, `L(ω+1) ≤ ν_C`);
* `WdThLow S` (the reading move `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at the long codes with `Θ_λ(m_λ) < δ_λ·ω`) and
  `WdEQfar S` (EQ at the long codes with `δ_λ·ω ≤ Θ_λ(m_λ)`); `wdEQtop_iff`: **under `L(ω+1) ≤ ν_C`,
  `CxEQtop ⇔ WdThLow ∧ WdEQfar`**;
* `wdFar_MW` (**a far code is `> M_W`**), `WdThHi S` (the reading move at codes `≥ θ⁺` with `Θ < δ·ω`),
  `wdRn_of` (**`WdThHi`, `WdEQfar` give `Rn.RnThMoveM ∧ Rn.RnEQhi2`**), `wdLj_iff` (**`Lj.LjEQhi ⇔ WdThHi ∧ WdEQfar`**):
  `RnThMoveM` and the part of `RnEQhi2` with `Θ_λ(m_λ) < δ_λ·ω` are one reading-move statement; EQ is needed only
  where `Θ_λ(m_λ) ≥ δ_λ·ω`;
* `WdAtWall S` (**the wall statement**: `Ux.UxAtMove26` less the two conjuncts `B_n s < θ⁺` and
  `Θ_λ(s) < L(n+2)`, which hold for every atom `s ≤ θ`), `wdAtMove26_of_wall`, `wdWall_iff`.

New definitions: the hypothesis names `WdThLow`, `WdEQfar`, `WdThHi`, `WdAtWall`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## Ordinal facts -/

theorem wd_opow_of_indec {a : Ordinal.{0}} (h : Indec a) : ∃ e : Ordinal.{0}, a = ω ^ e := by
  obtain ⟨h0, hp⟩ := indec_iff.1 h
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h' | ⟨e, he⟩
  · exact absurd h' h0
  · exact ⟨e, he.symm⟩

/-- An indecomposable `a > δ` (`δ` indecomposable) is at least `δ·ω`. -/
theorem wd_mulw_le {δ a : Ordinal.{0}} (hδ : Indec δ) (ha : Indec a) (h : δ < a) : δ * ω ≤ a := by
  obtain ⟨e, rfl⟩ := wd_opow_of_indec hδ
  obtain ⟨f, rfl⟩ := wd_opow_of_indec ha
  have hef : e < f := (opow_lt_opow_iff_right one_lt_omega0).1 h
  rw [← opow_succ]
  exact opow_le_opow_right omega0_pos (Order.succ_le_of_lt hef)

/-- `δ + x < δ·ω` for `x < δ·ω` (`δ` indecomposable). -/
theorem wd_add_lt_mulw {δ x : Ordinal.{0}} (hδ : Indec δ) (hx : x < δ * ω) : δ + x < δ * ω := by
  obtain ⟨e, he⟩ := wd_opow_of_indec hδ
  have hδw : δ < δ * ω := by
    have h0 : 0 < δ := pos_iff_ne_zero.2 (indec_iff.1 hδ).1
    have := (mul_lt_mul_iff_right₀ h0).2 one_lt_omega0
    rwa [mul_one] at this
  have hP : IsPrincipal (· + ·) (δ * ω) := by
    rw [he, ← opow_succ]; exact isPrincipal_add_omega0_opow _
  exact hP hδw hx

theorem wdDelta_indec {l : Ordinal.{0}} (hl : IsRestartIdx l) : Indec (cdDelta l) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  exact inE_indec (upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans le_self_add))))

theorem wdDelta_pos {l : Ordinal.{0}} (hl : IsRestartIdx l) : 0 < cdDelta l :=
  pos_iff_ne_zero.2 (indec_iff.1 (wdDelta_indec hl)).1

theorem wdL_indec (S : InaccSeq.{0}) : Indec (Nc.ncL S ω) :=
  indec_iff.2 ⟨(Lw.lw_L_SC S ω).1.ne', (Lw.lw_L_SC S ω).isPrincipal⟩

/-! ## The closed points on `[δ_λ, δ_λ·ω)` -/

/-- **Every `δ_λ + x` with `x < δ_λ·ω` is closed relative to `λ`** when `δ_λ < ν_C`. -/
theorem wdClosed {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hC : cdDelta l < nuC)
    (hx : x < cdDelta l * ω) : cdClosed l (cdDelta l + x) := by
  have hI := wdDelta_indec hl
  have hδw : cdDelta l + x < cdDelta l * ω := wd_add_lt_mulw hI hx
  refine ⟨le_self_add, fun a ha hay g hag => ?_⟩
  by_cases had : a ≤ cdDelta l
  · exact (mvCap hl hC ha had g hag).trans le_self_add
  · have hδa : cdDelta l < a := not_le.1 had
    have hga : g ≤ a := by
      by_contra hlt
      have hIa := indec_of_lt1 hag (not_le.1 hlt)
      exact absurd (wd_mulw_le hI hIa hδa) (not_le.2 (lt_of_le_of_lt hay hδw))
    exact hga.trans hay

/-- **`k_λ(x) = δ_λ + x` for `x < δ_λ·ω`** when `δ_λ < ν_C`. -/
theorem wdk_eq {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hC : cdDelta l < nuC)
    (hx : x < cdDelta l * ω) : cdk l x = cdDelta l + x :=
  cdk_interval (fun _ hy => Or.inl (wdClosed hl hC (lt_of_le_of_lt hy hx))) x le_rfl

/-- `B_n(δ·k) = B_n(δ)·k` below `L(ω)`. -/
theorem wdB_mul {n : ℕ} {δ : Ordinal.{0}} (hδ : δ < Nc.ncL S ω) :
    ∀ k : ℕ, δ * (k : Ordinal.{0}) < Nc.ncL S ω →
      Bc.bcB S n (δ * (k : Ordinal.{0})) = Bc.bcB S n δ * (k : Ordinal.{0}) := by
  intro k
  induction k with
  | zero => intro _; simp [Bc.bcB_zero]
  | succ k IH =>
    intro hk
    have e : δ * ((k + 1 : ℕ) : Ordinal.{0}) = δ * (k : Ordinal.{0}) + δ := by
      rw [Nat.cast_succ, mul_add_one]
    have hk' : δ * (k : Ordinal.{0}) < Nc.ncL S ω := by
      refine lt_of_le_of_lt ?_ hk
      rw [e]; exact le_self_add
    rw [e, Bc.bcB_add hk' hδ, IH hk', Nat.cast_succ, mul_add_one]

/-- `p < δ·ω` gives `p < δ·(k+1)` for some `k < ω`. -/
theorem wd_lt_mul_nat {δ p : Ordinal.{0}} (hδ : δ ≠ 0) (hp : p < δ * ω) :
    ∃ k : ℕ, p < δ * ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hq : p / δ < ω := (Ordinal.lt_mul_iff_div_lt hδ).1 hp
  obtain ⟨k, hk⟩ := lt_omega0.1 hq
  refine ⟨k, ?_⟩
  have := Ordinal.lt_mul_succ_div p hδ
  rwa [hk, Order.succ_eq_add_one, ← Nat.cast_succ] at this

/-- **`k_{λ'}(B_n p) = B_n(k_λ(p))` for `p < δ_λ·ω`** (`δ_λ < L(n+2)`, `L(ω+1) ≤ ν_C`, `B_n ρ_λ = ρ_{λ'}`). -/
theorem wdk_move (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p : Ordinal.{0}}
    (hl : IsRestartIdx l) (hl' : IsRestartIdx l') (h1 : Bc.bcC S n < upsilon l)
    (hδr : cdDelta l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (hp : p < cdDelta l * ω) : cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
  have hδC : cdDelta l < nuC := (hδr.trans (Cx.cxC_lt_L1 n)).trans_le hν
  have hδL : cdDelta l < Nc.ncL S ω := hδr.trans (Bc.bcC_lt S (n + 1))
  have hwL : cdDelta l * ω ≤ Nc.ncL S ω := wd_mulw_le (wdDelta_indec hl) (wdL_indec S) hδL
  have hpL : p < Nc.ncL S ω := hp.trans_le hwL
  have hD := mvDelta_move hl h1 hδr hB
  obtain ⟨k, hk⟩ := wd_lt_mul_nat (wdDelta_pos hl).ne' hp
  have hkL : cdDelta l * ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω :=
    ((mul_lt_mul_iff_right₀ (wdDelta_pos hl)).2 (natCast_lt_omega0 _)).trans_le hwL
  have hBp : Bc.bcB S n p < cdDelta l' * ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [← hD, ← wdB_mul hδL _ hkL]; exact (Bc.bcB_lt_iff hpL hkL).2 hk
  have hBp' : Bc.bcB S n p < cdDelta l' * ω :=
    hBp.trans ((mul_lt_mul_iff_right₀ (wdDelta_pos hl')).2 (natCast_lt_omega0 _))
  have hδ' : cdDelta l' < nuC := by
    rw [← hD]; exact (Bc.bcB_bound' S n _ hδr).trans_le hν
  rw [wdk_eq hl hδC hp, Bc.bcB_add hδL hpL, hD, wdk_eq hl' hδ' hBp']

/-! ## The split of `SfEQlong` / `CxEQtop` at `δ_λ·ω` -/

/-- **The reading move at the long codes whose reading is below `δ_λ·ω`.** -/
def WdThLow (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **EQ at the long codes whose reading is at least `δ_λ·ω`** (the far codes). -/
def WdEQfar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdDelta l * ω ≤ cdTheta S l (cdCode S l) → Bc.bcB S n (cdR S l) = cdR S l'

/-- **`WdThLow` and `WdEQfar` give `SfEQlong`** (given `L(ω+1) ≤ ν_C`). -/
theorem wdEQlong_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hT : WdThLow S) (hF : WdEQfar S) : Sf.SfEQlong S := by
  intro n l l' hR h1 hr hl' hB hm
  by_cases hw : cdTheta S l (cdCode S l) < cdDelta l * ω
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hΘ := hT n l l' hR h1 hr hl' hB hm hw
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← wdk_move hν hR.1 hl' h1 hδr hB hw, hΘ]
  · exact hF n l l' hR h1 hr hl' hB hm (not_lt.1 hw)

/-- **`SfEQlong` gives `WdThLow`** (given `L(ω+1) ≤ ν_C`; `k_{λ'}` is injective). -/
theorem wdThLow_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : Sf.SfEQlong S) : WdThLow S := by
  intro n l l' hR h1 hr hl' hB hm hw
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hE : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) :=
    h n l l' hR h1 hr hl' hB hm
  rw [← wdk_move hν hR.1 hl' h1 hδr hB hw] at hE
  exact (cdk_inj l').1 hE

theorem wdEQfar_of (h : Sf.SfEQlong S) : WdEQfar S :=
  fun n l l' hR h1 hr hl' hB hm _ => h n l l' hR h1 hr hl' hB hm

/-- **Under `L(ω+1) ≤ ν_C`: `CxEQtop ⇔ WdThLow ∧ WdEQfar`.** -/
theorem wdEQtop_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Cx.CxEQtop S ↔ WdThLow S ∧ WdEQfar S := by
  rw [Wa.waEQtop_iff hν]
  exact ⟨fun h => ⟨wdThLow_of hν h, wdEQfar_of h⟩, fun h => wdEQlong_of hν h.1 h.2⟩

/-! ## The split of `RnThMoveM ∧ RnEQhi2` -/

/-- **A far code is above `M_W`.** -/
theorem wdFar_MW {n : ℕ} {l : Ordinal.{0}} (hR : CdRange S l) (hr : cdR S l < Bc.bcC S (n + 1))
    (hw : cdDelta l * ω ≤ cdTheta S l (cdCode S l)) : Rn.rnMW S < cdCode S l := by
  by_contra h
  have h1 := Rn.rnTheta_lt_delta_R hR hr (not_lt.1 h)
  exact absurd (h1.trans_le (le_mul_left _ omega0_pos)) (not_lt.2 hw)

/-- **The reading move at the codes `≥ θ⁺` whose reading is below `δ_λ·ω`.** -/
def WdThHi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Lj.ljThP S ≤ cdCode S l → cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`WdThHi` and `WdEQfar` give `RnThMoveM` and `RnEQhi2`** (given `L(ω+1) ≤ ν_C`). -/
theorem wdRn_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hT : WdThHi S) (hF : WdEQfar S) :
    Rn.RnThMoveM S ∧ Rn.RnEQhi2 S := by
  refine ⟨fun n l l' hR h1 hr hl' hB hm hP hM => ?_, fun n l l' hR h1 hr hl' hB hm hM => ?_⟩
  · exact hT n l l' hR h1 hr hl' hB hm hP
      ((Rn.rnTheta_lt_delta_R hR hr hM).trans_le (le_mul_left _ omega0_pos))
  · have hP : Lj.ljThP S ≤ cdCode S l := Rn.rnThP_le_MW.trans hM.le
    by_cases hw : cdTheta S l (cdCode S l) < cdDelta l * ω
    · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
      have hΘ := hT n l l' hR h1 hr hl' hB hm hP hw
      show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
      rw [← wdk_move hν hR.1 hl' h1 hδr hB hw, hΘ]
    · exact hF n l l' hR h1 hr hl' hB hm (not_lt.1 hw)

/-- **`LjEQhi` gives `WdThHi` and `WdEQfar`** (given `L(ω+1) ≤ ν_C`). -/
theorem wdHi_of_lj (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : Lj.LjEQhi S) : WdThHi S ∧ WdEQfar S := by
  refine ⟨fun n l l' hR h1 hr hl' hB hm hP hw => ?_, fun n l l' hR h1 hr hl' hB hm hw => ?_⟩
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hE : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) :=
      h n l l' hR h1 hr hl' hB hm hP
    rw [← wdk_move hν hR.1 hl' h1 hδr hB hw] at hE
    exact (cdk_inj l').1 hE
  · exact h n l l' hR h1 hr hl' hB hm (Rn.rnThP_le_MW.trans (wdFar_MW hR hr hw).le)

/-- **Under `L(ω+1) ≤ ν_C`: `LjEQhi ⇔ WdThHi ∧ WdEQfar`.** -/
theorem wdLj_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Lj.LjEQhi S ↔ WdThHi S ∧ WdEQfar S :=
  ⟨wdHi_of_lj hν, fun h => Rn.rnLjEQhi_of hν (wdRn_of hν h.1 h.2).1 (wdRn_of hν h.1 h.2).2⟩

/-- `SfEQlong` gives `LjEQhi` (a restriction). -/
theorem wdLj_of_long (h : Sf.SfEQlong S) : Lj.LjEQhi S :=
  fun n l l' hR h1 hr hl' hB hm _ => h n l l' hR h1 hr hl' hB hm

/-! ## The wall statement -/

/-- **The atom move at the atoms `ψ_{Ω₂}(Y₃) ≤ s ≤ θ`, reduced to its wall part**: membership in the domain of
`B_n`, the image is an atom at `λ'`, and the reading equation. -/
def WdAtWall (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Le.leFWW S ≤ cdCode S l → cdCode S l < Lj.ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`WdAtWall` gives `Ux.UxAtMove26`**: `B_n s ≤ B_n θ = θ < θ⁺` and `Θ_λ(s) ≤ Θ_λ(M_W) < δ_λ ≤ r(λ)`. -/
theorem wdAtMove26_of_wall (h : WdAtWall S) : Ux.UxAtMove26 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsY hsθ IH
  obtain ⟨hD, hmem, heq⟩ := h n l l' hR h1 hr hl' hB hm hF hK s hs hsY hsθ IH
  refine ⟨hD, hmem, ?_, ?_, heq⟩
  · obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
    rcases hsθ.lt_or_eq with hlt | he
    · exact (((mvB_lt_iff hD hDθ).2 hlt).trans_eq hBθ).trans Lj.ljTh_lt_ThP
    · rw [he, hBθ]; exact Lj.ljTh_lt_ThP
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
    obtain ⟨hX, hown⟩ := ldOwnA hR.1 h2
    have hθM : ConjT.th S ≤ Rn.rnMW S := Lj.ljTh_lt_ThP.le.trans Rn.rnThP_le_MW
    have hs2 : s ≤ Om (1 + 1) := hsθ.trans (Lj.ljTh_lt_ThP.trans Lj.ljThP_lt_Om2).le
    rw [← ldTheta hR.1 hX hs2]
    exact (Rn.rnTheta_lt_delta hR.1 hX hown (hsθ.trans hθM)).trans hδr

/-- **`WdAtWall ⇔ UxAtMove26`.** -/
theorem wdWall_iff : WdAtWall S ↔ Ux.UxAtMove26 S := by
  refine ⟨wdAtMove26_of_wall, fun h n l l' hR h1 hr hl' hB hm hF hK s hs hsY hsθ IH => ?_⟩
  obtain ⟨hD, hmem, -, -, heq⟩ := h n l l' hR h1 hr hl' hB hm hF hK s hs hsY hsθ IH
  exact ⟨hD, hmem, heq⟩

end Googology.Trans.PoR.InaccPsi.R2.Wd
