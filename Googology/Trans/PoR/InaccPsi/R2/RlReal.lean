import Googology.Trans.PoR.InaccPsi.R2.RlCopy
import Googology.Trans.PoR.InaccPsi.R2.RlBound
import Googology.Trans.PoR.InaccPsi.R2.CvNamed

/-!
# The realizer maps with configuration-dependent domains, and the road from them

`L(ξ) = Nc.ncL S ξ`, `m* = L(0)`, `P' = Nc.ncPp S`, `ρ_λ = υ_λ`, `r(λ) = cdR S λ`, Range = `CdRange`,
LOWER = `CdLOWER`.  `Cv.CvReal` asks for maps on the whole of `[a, t)` and is false at every named
restart (`Rl.rlNoReal_m`, `rlNoReal_n`, `rlNoReal_w`, `rlNoReal_cross`).  Here the realizer maps are
those of `Rl.rlLe1_of_maps`: indexed by any type `ι`, the map `D_i` lives on `[0, c_i) ∪ E_i`, and every
finite closed configuration has an index whose domain contains it.

* `RlReal S a b` (**the realizer maps**): the clauses of `rlLe1_of_maps` except the pairs at `a` and
  from below, plus: `μ_i` a restart of the Range, `D_i(a) = ρ_{μ_i}` when `a ∈ E_i`, `D_i(y) ≤ r(μ_i)`
  on `E_i`, and `D_i` keeps `≤₁`, `≤₂` on the pairs `a < y < y'` of `E_i`;
  `rlReal_of_cv`: `CvReal → RlReal` (so `RlReal` is weaker);
* `rlLe1_of_real`: LOWER, `CvNoPair a b`, `RlReal S a b` give `a ≤₁ b`; `RlRealCof`,
  `rlLe1_of_realCof`;
* `rlCL_of_real` ((CL)), `rlCROSS_of_real` (CROSS), `rlM_of_real` (`m* ≤₁ L(1)`), `rlT_of_real` (T),
  `rlNamed_of_real` (`CxNamed`), `rlRoad_front`, `rlRoad_rz` (`Cx.cxRoad_front`, `Cx.cxRoad_rz` with
  `CxNamed` replaced by these realizer maps);
* the clause `≤₂` of a realizer map below `ν_C`: `rlD2_of_std` (a `≤₂`-pair below `ν_C` is standard,
  `std_of_lt_nuC`; if `D` sends it to a standard pair below `L(ω+1)`, `CxStdPairTop` makes the image a
  `≤₂`-pair).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx
  Googology.Trans.PoR.InaccPsi.R2.Cv

/-- **The realizer maps for `a ≤₁ b`, with configuration-dependent domains.** -/
def RlReal (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∃ (ι : Type) (c : ι → Ordinal.{0}) (E : ι → Set Ordinal.{0}) (D : ι → Ordinal.{0} → Ordinal.{0})
    (μ : ι → Ordinal.{0}),
    (∀ i, c i < a) ∧ (∀ i, ∀ y ∈ E i, a ≤ y ∧ y < b) ∧
    (∀ X Y : Finset Ordinal.{0}, (∀ x ∈ X, x < a) → (∀ y ∈ Y, a ≤ y ∧ y < b) →
      Closed ↑(X ∪ Y) → ∃ i, (∀ x ∈ X, x < c i) ∧ ∀ y ∈ Y, y ∈ E i) ∧
    (∀ i, StrictMonoOn (D i) (E i)) ∧
    (∀ i, ∀ x ∈ RlDom (c i) (E i), ∀ y ∈ RlDom (c i) (E i), ∀ z ∈ RlDom (c i) (E i),
      (x + y = z ↔ D i x + D i y = D i z)) ∧
    (∀ i, ∀ y ∈ E i, DecompR0 (D i y) → DecompR0 y) ∧
    (∀ i, ∀ x < c i, D i x = x) ∧
    (∀ i, ∀ y ∈ E i, c i ≤ D i y ∧ D i y < a) ∧
    (∀ i, CdRange S (μ i) ∧ (a ∈ E i → D i a = upsilon (μ i)) ∧ ∀ y ∈ E i, D i y ≤ cdR S (μ i)) ∧
    (∀ i, ∀ y ∈ E i, ∀ y' ∈ E i, a < y → y < y' →
      (le1 y y' → le1 (D i y) (D i y')) ∧ (le2 y y' → le2 (D i y) (D i y')))

variable {S : InaccSeq.{0}}

/-- **`CvReal` gives `RlReal`** (full domains `E_k = [a, b)`). -/
theorem rlReal_of_cv {a b : Ordinal.{0}} (h : CvReal S a b) : RlReal S a b := by
  obtain ⟨c, D, μ, hca, hcof, hDm, hDadd, hDdec, hDfix, hDwin, hDμ, hin⟩ := h
  refine ⟨ℕ, c, fun _ => Ico a b, D, μ, hca, fun _ y hy => hy, ?_, hDm,
    fun k x hx y hy z hz => hDadd k x hx y hy z hz, fun k y hy => hDdec k y hy.1 hy.2, hDfix,
    fun k y hy => hDwin k y hy.1 hy.2,
    fun k => ⟨(hDμ k).2.1, fun _ => (hDμ k).1, fun y hy => (hDμ k).2.2 y hy.1 hy.2⟩,
    fun k y _ y' hy' hay hyy' => hin k y y' hay hyy' hy'.2⟩
  intro X Y hX hY _
  obtain ⟨k, hk⟩ : ∃ k, ∀ x ∈ X, x < c k := by
    rcases X.eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨k, hk⟩ := hcof _ (hX _ (X.max'_mem hne))
      exact ⟨k, fun x hx => (X.le_max' x hx).trans_lt hk⟩
  exact ⟨k, hk, fun y hy => hY y hy⟩

/-- **`a ≤₁ b` from the realizer maps**, LOWER and `CvNoPair a b`. -/
theorem rlLe1_of_real (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : RlReal S a b) : le1 a b := by
  obtain ⟨ι, c, E, D, μ, hca, hE, hex, hDm, hDadd, hDdec, hDfix, hDwin, hDμ, hin⟩ := hR
  refine rlLe1_of_maps hab hca hE hex hDm hDadd hDdec hDfix hDwin ?_ ?_ ?_
  · intro i y hy y' hy' hyy' h1
    rcases eq_or_lt_of_le (hE i y hy).1 with hya | hay
    · subst hya
      obtain ⟨hrange, e, hle⟩ := hDμ i
      have hlow : le1 (upsilon (μ i)) (cdR S (μ i)) := hL _ hrange
      have hmono : D i a < D i y' := hDm i hy hy' hyy'
      rw [e hy] at hmono ⊢
      exact le1_of_le_of_le1 hmono.le (hle y' hy') hlow
    · exact (hin i y hy y' hy' hay hyy').1 h1
  · intro i y hy y' hy' hyy' h2
    rcases eq_or_lt_of_le (hE i y hy).1 with hya | hay
    · subst hya
      exact absurd h2 (hP.2 y' hyy' (hE i y' hy').2)
    · exact (hin i y hy y' hy' hay hyy').2 h2
  · intro i x hx y hy h2
    exact absurd h2 (hP.1 x y (hx.trans (hca i)) (hE i y hy).1 (hE i y hy).2)

/-- Realizer maps for cofinally many targets `t ≤ b`. -/
def RlRealCof (S : InaccSeq.{0}) (a b : Ordinal.{0}) : Prop :=
  ∀ y, a ≤ y → y < b → ∃ t, y < t ∧ t ≤ b ∧ RlReal S a t

theorem rlRealCof_of_cv {a b : Ordinal.{0}} (h : CvRealCof S a b) : RlRealCof S a b := fun y hy hyb => by
  obtain ⟨t, h1, h2, h3⟩ := h y hy hyb
  exact ⟨t, h1, h2, rlReal_of_cv h3⟩

/-- **`a ≤₁ b` from realizer maps for cofinal targets.** -/
theorem rlLe1_of_realCof (hL : CdLOWER S) {a b : Ordinal.{0}} (hab : a ≤ b) (hP : CvNoPair a b)
    (hR : RlRealCof S a b) : le1 a b :=
  le1_of_cofinal hab fun y hay hyb => by
    obtain ⟨t, hyt, htb, hRt⟩ := hR y hay hyb
    exact ⟨t, hyt, rlLe1_of_real hL (hay.trans hyt.le) (cvNoPair_mono hP htb) hRt⟩

/-- **(CL) from the realizer maps at the restarts `L(n+1)`.** -/
theorem rlCL_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))) : CdCL S := by
  intro n
  obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
  exact rlLe1_of_realCof hL (Pp.ppL_lt_succ n).le
    (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (h n)

/-- **CROSS from the realizer maps at `L(n+1)` with the targets `P(Ω_ω + P'·(n+1) + c')`**, `c'`
cofinal in `P'`; hence (CL). -/
theorem rlCROSS_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : ∀ n : ℕ, ∀ c < Nc.ncPp S, ∃ c', c ≤ c' ∧ c' < Nc.ncPp S ∧
      RlReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c'))) :
    CdCROSS S ∧ CdCL S := by
  have hX : CdCROSS S := by
    intro n c hc
    obtain ⟨c', hcc', hc'P, hR⟩ := h n c hc
    obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have h1 : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤
        Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') := by
      rw [Lw.lw_L_eq S]; exact Pv_mono le_self_add
    have h2 : Pv S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + c') ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have e2 : ((n + 2 : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) + 1 := Nat.cast_succ (n + 1)
      rw [e2, Pp.ppL_succ_eq]
      exact Pv_mono (add_le_add_right hc'P.le _)
    refine ⟨c', hcc', hc'P, rlLe1_of_real hL h1 (cvNoPair_of_nu hl e ?_) hR⟩
    exact h2.trans ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)
  exact ⟨hX, cxCROSS_iff.1 hX⟩

/-- **`m* ≤₁ L(1)` from the realizer maps at `m*`.** -/
theorem rlM_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1)) : le1 (Nc.ncL S 0) (Nc.ncL S 1) := by
  obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
  exact rlLe1_of_realCof hL (Pp.ppL_mono zero_le)
    (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) h

/-- **`T` from the realizer maps at `L(ω)`** and `CvNoPair` there. -/
theorem rlT_of_real (hL : CdLOWER S) (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (h : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxT S :=
  rlLe1_of_realCof hL (Qq.qqL_lt_succ S).le hP h

/-- **The crossing relations at the named restarts from the realizer maps.** -/
theorem rlNamed_of_real (hL : CdLOWER S) (hlow : Nc.ncL S ω ≤ nuC)
    (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxNamed S :=
  ⟨rlM_of_real hL hlow h0, rlCL_of_real hL hlow hn, rlT_of_real hL hP hw⟩

/-- **The road with `CxNamed` replaced by the realizer maps** (`Cx.cxRoad_front`). -/
theorem rlRoad_front (hU : CdUPPER S) (hL : CdLOWER S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cxRoad_front hU hL hV hEQ htop hups
    (rlNamed_of_real hL (cdLow_enum hU hV) h0 hn hP hw) hmove hstd

/-- **The reduced road (`Cx.cxRoad_rz`) with `CxNamed` replaced by the realizer maps.** -/
theorem rlRoad_rz (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (h0 : RlRealCof S (Nc.ncL S 0) (Nc.ncL S 1))
    (hn : ∀ n : ℕ, RlRealCof S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : RlRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hL' := Rz.rzLOWER_of_rest hL
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (rlNamed_of_real hL' (cdLow_enum hU' hV') h0 hn hP hw) hmove hstd

/-- **The clause `≤₂` of a realizer map below `ν_C`**: a `≤₂`-pair `y < y' < ν_C` is standard; if `D`
keeps it increasing, sends it to a standard pair, and the image lies below `L(ω+1)`, then the image is
a `≤₂`-pair (`CxStdPairTop`). -/
theorem rlD2_of_std (hstd : CxStdPairTop S) {D : Ordinal.{0} → Ordinal.{0}} {y y' : Ordinal.{0}}
    (hy' : y' < nuC) (hyy : y < y') (hD : D y < D y') (hDb : D y' < Nc.ncL S (ω + 1))
    (hmove : IsStd y y' → IsStd (D y) (D y')) (h2 : le2 y y') : le2 (D y) (D y') :=
  cxStdPair_of_top hstd _ _ hD hDb (hmove (std_of_lt_nuC hy' hyy h2))

end Googology.Trans.PoR.InaccPsi.R2.Rl
