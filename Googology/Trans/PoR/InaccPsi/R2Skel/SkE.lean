import Googology.Trans.PoR.InaccPsi.R2.WdRoad

/-!
# Skeleton of part EQ: the hypotheses `(hν → WdThLow)` and `(hν → WdEQfar)` of `Wd.wdRoadL`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ν_C = nuC`, `hν := L(ω+1) ≤ ν_C`,
`ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `k_λ = Cd.cdk λ` (enumeration of the closed set `K_λ = Cd.cdK λ`),
`Θ_λ = Cd.cdTheta S λ`, `m_λ = Cd.cdCode S λ`, `r(λ) = k_λ(Θ_λ(m_λ))`, `θ⁺ = Lj.ljThP S`, `M_W = Rn.rnMW S`.
A window `(n, λ, λ')`: `CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart, `B_n ρ_λ = ρ_{λ'}`, `ρ_λ < m_λ`.
A far window: also `δ_λ·ω ≤ Θ_λ(m_λ)`.

Tree (indent = child):
* `skEQ` REDUCED: `(hν → WdThLow) ∧ (hν → WdEQfar)` from `hRead`.
  * `skThLow` REDUCED: `WdThLow` from `hRead` and `skEQfar` (`waEQtop_ux`, `wdRn_of`, `wdEQtop_iff`).
  * `skEQfar` REDUCED: `WdEQfar` from `skThFar` and `skKFar`.
    * `skThFar` OPEN: the reading move at the far codes.
    * `skKFar` REDUCED: `k_{λ'}(B_n p) = B_n(k_λ p)` for `δ_λ·ω ≤ p ≤ Θ_λ(m_λ)`, by induction on `p`
      (base `p < δ_λ·ω`: `Wd.wdk_move`).
      * `skKClosed` OPEN: `B_n` of a successor closed point is closed at `λ'`.
      * `skKGap` OPEN: no closed point of `λ'` strictly between the images of two consecutive closed points of `λ`.
      * `skKLim` OPEN: the limit step.
Guards and links (PROVED): `skNoIdx` (the index-keeping move `k_{λ'}(p) = B_n(k_λ p)` is false at `p = ρ_λ`),
`skThFar_of_top` / `skThHi_of_top` (one reading move at every code `≥ θ⁺` gives both `skThFar` and `WdThHi`),
`skThFar_of_EQ` (`CdEQ` and `skKFar` give `skThFar`: non-vacuity against the road's target).
-/

set_option autoImplicit false

namespace R2Skel.SkE

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Hypothesis names -/

/-- A window `(n, λ, λ')`. -/
def SkWin (S : InaccSeq.{0}) (n : ℕ) (l l' : Ordinal.{0}) : Prop :=
  CdRange S l ∧ Bc.bcC S n < upsilon l ∧ cdR S l < Bc.bcC S (n + 1) ∧ IsRestartIdx l' ∧
    Bc.bcB S n (upsilon l) = upsilon l' ∧ upsilon l < cdCode S l

/-- The reading move at the far codes (`δ_λ·ω ≤ Θ_λ(m_λ)`). -/
def SkThFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → cdDelta l * ω ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at every code `m_λ ≥ θ⁺` (no bound on `Θ_λ(m_λ)`). -/
def SkThTop (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → Lj.ljThP S ≤ cdCode S l →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The move of `k` at the far indices: `k_{λ'}(B_n p) = B_n(k_λ p)` for `δ_λ·ω ≤ p ≤ Θ_λ(m_λ)`. -/
def SkKFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

/-- The image of a successor closed point is closed at `λ'`. -/
def SkKClosed (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdk l (q + 1)) ∈ cdK l'

/-- No closed point of `λ'` lies strictly between `B_n(k_λ q)` and `B_n(k_λ(q+1))`. -/
def SkKGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    ∀ z ∈ cdK l', Bc.bcB S n (cdk l q) < z → ¬ z < Bc.bcB S n (cdk l (q + 1))

/-- The limit step of the `k`-move. -/
def SkKLim (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, IsSuccLimit p → cdDelta l * ω ≤ p →
    p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

/-! ## Small facts -/

theorem sk_cdR_eq (l : Ordinal.{0}) : cdR S l = cdk l (cdTheta S l (cdCode S l)) := rfl

theorem sk_one_lt (n : ℕ) : (1 : Ordinal.{0}) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
  one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))

/-! ## Open leaves -/

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (no Lean value of Θ above M_W; no no-go applies; ⇔ WdEQfar given SkKFar: SkEX.skexTh_of_EQfar)
∀ far window: B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})  (codes m_λ > M_W; no value of Θ_λ above M_W is known). -/
theorem skThFar (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkThFar S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (implied by the parent SkKFar: SkEX.skexClosed_of_far; no refutation found)
δ_λ·ω ≤ q+1 ≤ Θ_λ(m_λ) ⇒ B_n(k_λ(q+1)) ∈ K_{λ'}  (lh ≤ B_n k_λ(q+1) at every a ∈ (ρ_{λ'}, B_n k_λ(q+1)], images or not). -/
theorem skKClosed (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKClosed S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (implied by the parent SkKFar: SkEX.skexGap_of_far; no refutation found)
z ∈ K_{λ'} ⇒ ¬ (B_n k_λ(q) < z < B_n k_λ(q+1))  (each non-image z in the gap has some a ≤ z with lh(a) > z). -/
theorem skKGap (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKGap S := by sorry

/-- STATUS: OPEN
SIZE: L
REFUTE: SURVIVED (implied by the parent SkKFar: SkEX.skexLim_of_far; discontinuity of B_n gives no contradiction)
p limit, δ_λ·ω ≤ p ≤ Θ_λ(m_λ), (∀ q < p, k_{λ'}(B_n q) = B_n k_λ(q)) ⇒ k_{λ'}(B_n p) = B_n k_λ(p). -/
theorem skKLim (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKLim S := by sorry

/-! ## Reduced nodes -/

/-- STATUS: PROVED (Wd.wdk_move, Bc.bcB_add, Bc.bcB_fixN, Bc.bcB_lt_iff, Ordinal.enumOrd_succ_le)
SIZE: S
closed-move ∧ gap ∧ limit-step ⇒ ∀ p ≤ Θ_λ(m_λ), k_{λ'}(B_n p) = B_n(k_λ p). -/
theorem skKFar_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : SkKClosed S) (hG : SkKGap S) (hL : SkKLim S) :
    SkKFar S := by
  intro n l l' hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hW : SkWin S n l l' := ⟨hR, h1, hr, hl', hB, hm⟩
  set T := cdTheta S l (cdCode S l) with hT
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hkL : ∀ p ≤ T, cdk l p < Nc.ncL S ω := fun p hp =>
    (((cdk_strictMono l).monotone hp).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have hpL : ∀ p ≤ T, p < Nc.ncL S ω := fun p hp => ((cdk_strictMono l).id_le p).trans_lt (hkL p hp)
  have key : ∀ p, p ≤ T → cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
    intro p
    induction p using WellFoundedLT.induction with
    | ind p IH =>
    intro hp
    by_cases hlow : p < cdDelta l * ω
    · exact Wd.wdk_move hν hR.1 hl' h1 hδr hB hlow
    have hfar : cdDelta l * ω ≤ p := not_lt.1 hlow
    rcases zero_or_succ_or_isSuccLimit p with h0 | ⟨q, rfl⟩ | hlim
    · subst h0
      exact absurd (mul_pos (Wd.wdDelta_pos hR.1) omega0_pos) (not_lt.2 hfar)
    · rw [Order.succ_eq_add_one] at hp hfar IH ⊢
      have hq : q ≤ T := (le_self_add).trans hp
      have hqp : q < q + 1 := lt_add_one q
      have IHq := IH q hqp hq
      have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω :=
        one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
      have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (sk_one_lt n)
      have hBs : Bc.bcB S n (q + 1) = Bc.bcB S n q + 1 := by
        rw [Bc.bcB_add (hpL q hq) h1L, hB1]
      have hxy : Bc.bcB S n (cdk l q) < Bc.bcB S n (cdk l (q + 1)) :=
        (Bc.bcB_lt_iff (hkL q hq) (hkL (q + 1) hp)).2 ((cdk_strictMono l) hqp)
      have hmem := hC n l l' hW q hfar hp
      rw [hBs]
      refine le_antisymm ?_ ?_
      · have := enumOrd_succ_le (cdK_unbdd l') hmem (by rw [← IHq] at hxy; exact hxy)
        rwa [Order.succ_eq_add_one] at this
      · have hz : cdk l' (Bc.bcB S n q + 1) ∈ cdK l' := cdk_mem l' _
        have hgt : Bc.bcB S n (cdk l q) < cdk l' (Bc.bcB S n q + 1) := by
          rw [← IHq]; exact (cdk_strictMono l') (lt_add_one _)
        exact not_lt.1 (hG n l l' hW q hfar hp _ hz hgt)
    · exact hL n l l' hW p hlim hfar hp (fun q hq => IH q hq (hq.le.trans hp))
  exact fun p _ hp => key p hp

/-- STATUS: REDUCED
SIZE: L
∀ far window, ∀ δ_λ·ω ≤ p ≤ Θ_λ(m_λ): k_{λ'}(B_n p) = B_n(k_λ p)  (children skKClosed, skKGap, skKLim). -/
theorem skKFar (hν : Nc.ncL S (ω + 1) ≤ nuC) : SkKFar S :=
  skKFar_of hν (skKClosed hν) (skKGap hν) (skKLim hν)

/-- STATUS: PROVED (definitions only)
SIZE: S
far reading move ∧ far k-move ⇒ WdEQfar:  B_n r(λ) = B_n k_λ(Θ) = k_{λ'}(B_n Θ) = k_{λ'}(Θ') = r(λ'). -/
theorem skEQfar_of (hT : SkThFar S) (hK : SkKFar S) : Wd.WdEQfar S := by
  intro n l l' hR h1 hr hl' hB hm hw
  have hW : SkWin S n l l' := ⟨hR, h1, hr, hl', hB, hm⟩
  rw [sk_cdR_eq, sk_cdR_eq, ← hK n l l' hW _ hw le_rfl, hT n l l' hW hw]

/-- STATUS: REDUCED
SIZE: L
hν ⇒ WdEQfar  (children skThFar, skKFar). -/
theorem skEQfar : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S :=
  fun hν => skEQfar_of (skThFar hν) (skKFar hν)

/-- STATUS: PROVED (Wa.waEQtop_ux, Wd.wdAtMove26_of_wall, Wd.wdRn_of, Wd.wdEQtop_iff)
SIZE: S
(hν → WdAtWall ∧ WdThHi) ∧ (hν → WdEQfar) ⇒ (hν → WdThLow). -/
theorem skThLow_of (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S := by
  intro hν
  have hrn := Wd.wdRn_of hν (hRead hν).2 (hF hν)
  exact ((Wd.wdEQtop_iff hν).1
    (Wa.waEQtop_ux hν (Wd.wdAtMove26_of_wall (hRead hν).1) hrn.1 hrn.2)).1

/-- STATUS: REDUCED
SIZE: L
hRead ⇒ (hν → WdThLow)  (children hRead, skEQfar). -/
theorem skThLow (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) :
    Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S :=
  skThLow_of hRead skEQfar

/-- STATUS: REDUCED
SIZE: L
TOP NODE. hRead: hν → WdAtWall ∧ WdThHi  ⇒  (hν → WdThLow) ∧ (hν → WdEQfar). -/
theorem skEQ (hRead : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S ∧ Wd.WdThHi S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S) :=
  ⟨skThLow hRead, skEQfar⟩

/-! ## Guards and links -/

/-- STATUS: PROVED (Wd.wdk_move, Cd.cdk_inj, Bc.bcB_base, Bc.bcB_lt_iff)
SIZE: S
NO-GO for the index-keeping move: in a window, k_{λ'}(ρ_λ) ≠ B_n(k_λ(ρ_λ)), since B_n k_λ(ρ_λ) = k_{λ'}(ρ_{λ'})
and ρ_λ < L(ω) < ρ_{λ'}.  So the far move must move the index (as in SkKFar). -/
theorem skNoIdx (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hW : SkWin S n l l') :
    cdk l' (upsilon l) ≠ Bc.bcB S n (cdk l (upsilon l)) := by
  obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hρδ : upsilon l < cdDelta l * ω :=
    (cdRho_lt_delta l).trans_le (le_mul_left _ omega0_pos)
  rw [← Wd.wdk_move hν hR.1 hl' h1 hδr hB hρδ, hB, Ne, cdk_inj]
  intro he
  have hρL : upsilon l < Nc.ncL S ω :=
    ((cdRho_lt_delta l).trans hδr).trans (Bc.bcC_lt S (n + 1))
  have hcL : Bc.bcC S n < Nc.ncL S ω := Bc.bcC_lt S n
  have h2 : Bc.bcB S n (Bc.bcC S n) < Bc.bcB S n (upsilon l) := (Bc.bcB_lt_iff hcL hρL).2 h1
  have h3 : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := Bc.bcB_base n
  rw [h3, hB, ← he] at h2
  exact lt_asymm h2 hρL

/-- STATUS: PROVED (Wd.wdFar_MW, Rn.rnThP_le_MW)
SIZE: S
the reading move at every code ≥ θ⁺ gives the far reading move (far codes are > M_W ≥ θ⁺). -/
theorem skThFar_of_top (h : SkThTop S) : SkThFar S := by
  intro n l l' hW hw
  have hW' := hW
  obtain ⟨hR, -, hr, -, -, -⟩ := hW
  exact h n l l' hW' (Rn.rnThP_le_MW.trans (Wd.wdFar_MW hR hr hw).le)

/-- STATUS: PROVED (definitions only)
SIZE: S
the reading move at every code ≥ θ⁺ gives WdThHi. -/
theorem skThHi_of_top (h : SkThTop S) : Wd.WdThHi S :=
  fun n l l' hR h1 hr hl' hB hm hP _ => h n l l' ⟨hR, h1, hr, hl', hB, hm⟩ hP

/-- STATUS: PROVED (Wa.waEQtop_of_EQ, Wa.waEQtop_iff, Cd.cdk_inj)
SIZE: S
NON-VACUITY: hν ∧ CdEQ (the road's target) ∧ SkKFar ⇒ SkThFar. -/
theorem skThFar_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : SkKFar S) : SkThFar S := by
  intro n l l' hW hw
  have hlong := (Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)
  have hW' := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hlong n l l' hR h1 hr hl' hB hm
  rw [sk_cdR_eq, sk_cdR_eq, ← hK n l l' hW' _ hw le_rfl, cdk_inj] at hE
  exact hE

/-- STATUS: PROVED (Wa.waEQtop_iff, Wa.waEQtop_of_EQ)
SIZE: S
NON-VACUITY: hν ∧ CdEQ ∧ SkThFar ⇒ k_{λ'}(B_n Θ) = B_n k_λ(Θ) at Θ = Θ_λ(m_λ) (the top index of SkKFar). -/
theorem skKTop_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hT : SkThFar S) {n : ℕ}
    {l l' : Ordinal.{0}} (hW : SkWin S n l l') (hw : cdDelta l * ω ≤ cdTheta S l (cdCode S l)) :
    cdk l' (Bc.bcB S n (cdTheta S l (cdCode S l))) = Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) := by
  have hlong := (Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)
  have hW' := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hlong n l l' hR h1 hr hl' hB hm
  rw [hT n l l' hW' hw, ← sk_cdR_eq]
  exact hE.symm

end R2Skel.SkE
