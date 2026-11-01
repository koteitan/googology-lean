import Googology.Trans.PoR.InaccPsi.R2.SkEXLeaf

/-!
# The closed points of `K_λ` past `δ_λ·ω`: blocks, the gap leaf, and the reduction of `SkKFar`

`L(ξ) = Nc.ncL S ξ`, `c_n = L(n+1)`, `B_n = Bc.bcB S n`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `K_λ = Cd.cdK λ`,
`k_λ = Cd.cdk λ`, `Θ_λ = Cd.cdTheta S λ`, `m_λ = Cd.cdCode S λ`.  A window is `R2Skel.SkEX.SkWin S n λ λ'`.

* `xgK_add` (**blocks**): `y ∈ K_λ`, `Z < y·ω` ⇒ `y + Z ∈ K_λ` (the points `y + Z`, `0 < Z < y·ω`, are
  decomposable, so by `indec_of_lt1` they reach only themselves);
* `xgk_add`: `k_λ(q + Z) = k_λ(q) + Z` for `Z < k_λ(q)·ω`; `xgk_succ`: `k_λ(q+1) = k_λ(q) + 1`;
* `xgKGap`: **the gap leaf `R2Skel.SkEX.SkKGap` holds with no hypothesis**;
* `xgk_reach`: at an index `p` with `δ_λ ≤ p`, `ρ_λ < p`, `k_λ(q) < p` for every `q < p` (a cofinal index), and an
  `R₂^C`-reach `r` of `p`: `k_λ(p) = r`;
* `xgReach_nonUps`: at a non-`υ`-point `p ∈ (c_n, c_{n+1})` the `R₂^C`-reach moves with `B_n`
  (`Lh.lhSk_reach`, `Wa.waLhMove`, `Tp.tpUpsRefl`);
* `xgKFar_of`: **`SkKFar` from two leaves**: `XgKCof` (at a cofinal index `p`, `K_{λ'}` is cofinal below `B_n p`)
  and `XgKReach` (at a cofinal index `p` that is a `υ`-point, the reach of `p` moves with `B_n`);
* `xgCof_of_cont`: `XgKCof` at the indices where `B_n` is continuous;
* `xgCof_of_far`: `SkKFar ∧ XgKReach ⇒ XgKCof` (the leaf asks nothing beyond the parent and the reach move).

New definitions: the hypothesis names `XgKCof`, `XgKReach`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Blocks of closed points -/

theorem xgDelta_pos (l : Ordinal.{0}) : 0 < cdDelta l := by
  unfold cdDelta
  exact Lh.lhInE_pos (upsPt_inE (upsPt_upsilon (lt_of_lt_of_le zero_lt_one le_add_self)))

theorem xgK_pos {l y : Ordinal.{0}} (hy : y ∈ cdK l) : 0 < y := by
  rcases hy with h | h
  · exact (xgDelta_pos l).trans_le h.1
  · exact (xgDelta_pos l).trans_le h.2

/-- `y + Z` is decomposable for `0 < y`, `0 < Z < y·ω`. -/
theorem xg_not_indec {y Z : Ordinal.{0}} (hy : 0 < y) (hZ0 : 0 < Z) (hZ : Z < y * ω) :
    ¬ Indec (y + Z) := by
  intro h
  have hP := (indec_iff.1 h).2
  have h1 : y < y + Z := lt_add_of_pos_right y hZ0
  have h2 : Z < y + Z := by
    refine lt_of_le_of_ne le_add_self fun e => ?_
    exact absurd (add_eq_right_iff_mul_omega0_le.1 e.symm) (not_le.2 hZ)
  exact lt_irrefl _ (hP h1 h2)

/-- **Blocks**: `y ∈ K_λ` and `Z < y·ω` give `y + Z ∈ K_λ`. -/
theorem xgK_add {l y Z : Ordinal.{0}} (hy : y ∈ cdK l) (hZ : Z < y * ω) : y + Z ∈ cdK l := by
  have hy0 := xgK_pos hy
  rcases hy with h | h
  · refine Or.inl ⟨h.1.trans le_self_add, fun a ha haz g hag => ?_⟩
    by_cases hay : a ≤ y
    · exact (h.2 a ha hay g hag).trans le_self_add
    · have hya : y < a := not_le.1 hay
      by_contra hg
      have hag' : a < g := lt_of_le_of_lt haz (not_le.1 hg)
      have hI := indec_of_lt1 hag hag'
      obtain ⟨W, rfl⟩ := exists_add_of_le hya.le
      have hW0 : 0 < W := pos_iff_ne_zero.2 fun e => by rw [e, add_zero] at hya; exact lt_irrefl _ hya
      have hWZ : W ≤ Z := (add_le_add_iff_left y).1 haz
      exact xg_not_indec hy0 hW0 (hWZ.trans_lt hZ) hI
  · exact Or.inr ⟨h.1.trans le_self_add, h.2.trans le_self_add⟩

/-- On a run `[k_λ(q), k_λ(q) + c]` inside `K_λ`, `k_λ(q + Z) = k_λ(q) + Z`. -/
theorem xgk_shift {l q c : Ordinal.{0}} (hK : ∀ Z ≤ c, cdk l q + Z ∈ cdK l) :
    ∀ Z ≤ c, cdk l (q + Z) = cdk l q + Z := by
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z IH =>
  intro hZ
  refine le_antisymm ?_ ?_
  · refine enumOrd_le_of_forall_lt (hK Z hZ) fun b hb => ?_
    show cdk l b < cdk l q + Z
    rcases lt_or_ge b q with hbq | hbq
    · exact ((cdk_strictMono l) hbq).trans_le le_self_add
    · obtain ⟨W, rfl⟩ := exists_add_of_le hbq
      have hWZ : W < Z := (add_lt_add_iff_left q).1 hb
      rw [IH W hWZ (hWZ.le.trans hZ)]
      exact (add_lt_add_iff_left _).2 hWZ
  · have hge : cdk l q ≤ cdk l (q + Z) := (cdk_strictMono l).monotone le_self_add
    obtain ⟨W, hW⟩ := exists_add_of_le hge
    rw [hW]
    refine (add_le_add_iff_left _).2 (not_lt.1 fun hWZ => ?_)
    have e1 := IH W hWZ (hWZ.le.trans hZ)
    have e2 : q + W = q + Z := (cdk_inj l).1 (e1.trans hW.symm)
    have e3 : W = Z := le_antisymm ((add_le_add_iff_left q).1 e2.le) ((add_le_add_iff_left q).1 e2.ge)
    exact lt_irrefl _ (e3 ▸ hWZ)

/-- **`k_λ(q + Z) = k_λ(q) + Z` for `Z < k_λ(q)·ω`.** -/
theorem xgk_add {l q Z : Ordinal.{0}} (hZ : Z < cdk l q * ω) : cdk l (q + Z) = cdk l q + Z :=
  xgk_shift (fun W hW => xgK_add (cdk_mem l q) (hW.trans_lt hZ)) Z le_rfl

theorem xg_lt_mulw {y : Ordinal.{0}} (hy : 0 < y) (m : ℕ) : y * (m : Ordinal.{0}) < y * ω :=
  (mul_lt_mul_iff_right₀ hy).2 (natCast_lt_omega0 m)

/-- **`k_λ(q+1) = k_λ(q) + 1`.** -/
theorem xgk_succ (l q : Ordinal.{0}) : cdk l (q + 1) = cdk l q + 1 := by
  have h := xg_lt_mulw (xgK_pos (cdk_mem l q)) 1
  rw [Nat.cast_one, mul_one] at h
  exact xgk_add ((Order.one_le_iff_pos.2 (xgK_pos (cdk_mem l q))).trans_lt h)

theorem xg_mul_nat_lt {L a : Ordinal.{0}} (hP : IsPrincipal (· + ·) L) (ha : a < L) :
    ∀ m : ℕ, a * (m : Ordinal.{0}) < L := by
  intro m
  induction m with
  | zero => simpa using zero_le.trans_lt ha
  | succ m IH => rw [Nat.cast_succ, mul_add_one]; exact hP IH ha

theorem xgB_le {n : ℕ} {x y : Ordinal.{0}} (hx : x < Nc.ncL S ω) (hy : y < Nc.ncL S ω) (h : x ≤ y) :
    Bc.bcB S n x ≤ Bc.bcB S n y := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact ((Bc.bcB_lt_iff hx hy).2 h).le

/-! ## The gap leaf -/

/-- **`SkKGap` holds**: `B_n(k_λ(q+1)) = B_n(k_λ q) + 1`, so nothing lies strictly between the two images. -/
theorem xgKGap : R2Skel.SkEX.SkKGap S := by
  intro n l l' hW q _ hq z _ h1 h2
  obtain ⟨-, -, hr, -, -, -⟩ := hW
  have hqT : q ≤ cdTheta S l (cdCode S l) := le_self_add.trans hq
  have hkL : cdk l q < Nc.ncL S ω :=
    (((cdk_strictMono l).monotone hqT).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω :=
    one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 :=
    Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  rw [xgk_succ, Bc.bcB_add hkL h1L, hB1] at h2
  exact absurd (Order.add_one_le_of_lt h1) (not_le.2 h2)

/-! ## The value of `k_λ` at a cofinal index -/

/-- At a cofinal index `p` (`k_λ(q) < p` for `q < p`) with a reach `r` of `p`, `r ∈ K_λ`. -/
theorem xgReach_mem {l p r : Ordinal.{0}} (hδ : cdDelta l ≤ p) (hcof : ∀ q < p, cdk l q < p)
    (hpΩ : p < Om1) (hr : IsReach R2C p r) : r ∈ cdK l := by
  have hpr : p ≤ r := le1_le hr.1
  refine Or.inl ⟨hδ.trans hpr, fun a ha har g hag => ?_⟩
  rcases lt_or_ge a p with hap | hpa
  · have hka : cdk l a < p := hcof a hap
    have hcl : cdClosed l (cdk l a) := cdk_closed (hka.trans hpΩ)
    exact (hcl.2 a ha ((cdk_strictMono l).id_le a) g hag).trans (hka.le.trans hpr)
  · exact hr.2 g (le1_trans (le1_of_le_of_le1 hpa har hr.1) hag)

/-- **At a cofinal index `p` with reach `r < Ω₁`: `k_λ(p) = r`.** -/
theorem xgk_reach {l p r : Ordinal.{0}} (hδ : cdDelta l ≤ p) (hρ : upsilon l < p)
    (hcof : ∀ q < p, cdk l q < p) (hr : IsReach R2C p r) (hrΩ : r < Om1) : cdk l p = r := by
  have hpr : p ≤ r := le1_le hr.1
  have hrK := xgReach_mem hδ hcof (hpr.trans_lt hrΩ) hr
  have hle : cdk l p ≤ r := enumOrd_le_of_forall_lt hrK fun b hb => (hcof b hb).trans_le hpr
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hcl : cdClosed l (cdk l p) := cdk_closed (hle.trans_lt hrΩ)
  exact absurd (hcl.2 p hρ ((cdk_strictMono l).id_le p) r hr.1) (not_le.2 hlt)

/-- `L(ω) < Ω₁` under `L(ω+1) ≤ ν_C`. -/
theorem xgL_lt_Om1 (hν : Nc.ncL S (ω + 1) ≤ nuC) : Nc.ncL S ω < Om1 :=
  ((Qq.qqL_lt_succ S).trans_le hν).trans_le nuC_le_Om1

/-- **The reach moves at the non-`υ`-points of a window** (`R₁⁺` there, `Wa.waLhMove`). -/
theorem xgReach_nonUps (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {p : Ordinal.{0}}
    (hcn : Bc.bcC S n < p) (hpC : p < Bc.bcC S (n + 1)) (hU : ¬ UpsPt p) :
    ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
  have hpν : p < nuC := (hpC.trans (Cx.cxC_lt_L1 n)).trans_le hν
  obtain ⟨r, hr⟩ := Lh.lhR1_exists (hpν.trans_le nuC_le_Om1) hU
  have hm := Wa.waLhMove (S := S) n p r hcn hpC hU hr
  have hBU : ¬ UpsPt (Bc.bcB S n p) := fun h => hU (Tp.tpUpsRefl Sf.sfShiftAll hcn.le hpC h)
  have hBν : Bc.bcB S n p < nuC := (Bc.bcB_bound' S n p hpC).trans_le hν
  exact ⟨r, (Lh.lhSk_reach hpν hU).2 hr, (Lh.lhSk_reach hBν hBU).2 hm⟩

/-! ## The two leaves and the reduction -/

/-- **Leaf (cofinality at the image)**: at a cofinal far index `p` of a window, with the move below `p`,
`K_{λ'}` is cofinal below `B_n p`: `k_{λ'}(Q) < B_n p` for every `Q < B_n p`. -/
def XgKCof (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p

/-- **Leaf (reach move at the inner `υ`-points)**: at a cofinal far index `p` of a window that is a `υ`-point,
`p` has an `R₂^C`-reach `r` and `B_n p` has the reach `B_n r`. -/
def XgKReach (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l q < p) → UpsPt p →
    ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r)

/-- Window facts used below. -/
theorem xgWin_facts (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}}
    (hW : R2Skel.SkEX.SkWin S n l l') {p : Ordinal.{0}} (hfar : cdDelta l * ω ≤ p)
    (hp : p ≤ cdTheta S l (cdCode S l)) :
    cdk l p < Bc.bcC S (n + 1) ∧ p < Bc.bcC S (n + 1) ∧ cdDelta l ≤ p ∧ upsilon l < p ∧
      Bc.bcC S n < p ∧ cdDelta l' ≤ Bc.bcB S n p ∧ upsilon l' < Bc.bcB S n p := by
  obtain ⟨hR, h1, hr, -, hB, -⟩ := hW
  have hkC : cdk l p < Bc.bcC S (n + 1) := ((cdk_strictMono l).monotone hp).trans_lt hr
  have hpC : p < Bc.bcC S (n + 1) := ((cdk_strictMono l).id_le p).trans_lt hkC
  have hpL : p < Nc.ncL S ω := hpC.trans (Bc.bcC_lt S (n + 1))
  have hδp : cdDelta l ≤ p := (le_mul_left _ omega0_pos).trans hfar
  have hρp : upsilon l < p := (cdRho_lt_delta l).trans_le hδp
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hδL : cdDelta l < Nc.ncL S ω := hδr.trans (Bc.bcC_lt S (n + 1))
  have hρL : upsilon l < Nc.ncL S ω := (cdRho_lt_delta l).trans hδL
  refine ⟨hkC, hpC, hδp, hρp, h1.trans hρp, ?_, ?_⟩
  · rw [← Mv.mvDelta_move hR.1 h1 hδr hB]; exact xgB_le hδL hpL hδp
  · rw [← hB]; exact (Bc.bcB_lt_iff hρL hpL).2 hρp

/-- **`SkKFar` from `XgKCof` and `XgKReach`** (under `L(ω+1) ≤ ν_C`).  Induction on `p`: below `δ_λ·ω` by
`Wd.wdk_move`; if `k_λ(p) < k_λ(q)·ω` for some `q < p`, then `p = q + Z` inside a block (`xgk_add` on both
sides); otherwise `p` is a cofinal index and `k_λ(p)` is the reach of `p` (`xgk_reach` on both sides). -/
theorem xgKFar_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : XgKCof S) (hRe : XgKReach S) : R2Skel.SkEX.SkKFar S := by
  intro n l l' hW
  have hW0 := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  set T := cdTheta S l (cdCode S l) with hT
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hkC : ∀ p ≤ T, cdk l p < Bc.bcC S (n + 1) := fun p hp =>
    ((cdk_strictMono l).monotone hp).trans_lt hr
  have hkL : ∀ p ≤ T, cdk l p < Nc.ncL S ω := fun p hp => (hkC p hp).trans (Bc.bcC_lt S (n + 1))
  have hpL : ∀ p ≤ T, p < Nc.ncL S ω := fun p hp => ((cdk_strictMono l).id_le p).trans_lt (hkL p hp)
  have hLP : IsPrincipal (· + ·) (Nc.ncL S ω) := (indec_iff.1 (Wd.wdL_indec S)).2
  have key : ∀ p, p ≤ T → cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
    intro p
    induction p using WellFoundedLT.induction with
    | ind p IH =>
    intro hp
    by_cases hlow : p < cdDelta l * ω
    · exact Wd.wdk_move hν hR.1 hl' h1 hδr hB hlow
    have hfar : cdDelta l * ω ≤ p := not_lt.1 hlow
    by_cases hA : ∃ q < p, cdk l p < cdk l q * ω
    · obtain ⟨q, hqp, hpq⟩ := hA
      have hqT : q ≤ T := hqp.le.trans hp
      have hle : cdk l q ≤ cdk l p := (cdk_strictMono l).monotone hqp.le
      obtain ⟨Z, hZ⟩ := exists_add_of_le hle
      have hZw : Z < cdk l q * ω := lt_of_le_of_lt le_add_self (hZ ▸ hpq)
      have hpe : p = q + Z := (cdk_inj l).1 (hZ.trans (xgk_add hZw).symm)
      have hZL : Z < Nc.ncL S ω := lt_of_le_of_lt le_add_self (hZ ▸ hkL p hp)
      have IHq := IH q hqp hqT
      have hpos : 0 < Bc.bcB S n (cdk l q) := by rw [← IHq]; exact xgK_pos (cdk_mem l' _)
      have hBZ : Bc.bcB S n Z < cdk l' (Bc.bcB S n q) * ω := by
        obtain ⟨m, hm'⟩ := Wd.wd_lt_mul_nat (xgK_pos (cdk_mem l q)).ne' hZw
        have hmL : cdk l q * ((m + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω :=
          xg_mul_nat_lt hLP (hkL q hqT) _
        rw [IHq]
        calc Bc.bcB S n Z < Bc.bcB S n (cdk l q * ((m + 1 : ℕ) : Ordinal.{0})) :=
              (Bc.bcB_lt_iff hZL hmL).2 hm'
          _ = Bc.bcB S n (cdk l q) * ((m + 1 : ℕ) : Ordinal.{0}) := Wd.wdB_mul (hkL q hqT) _ hmL
          _ < Bc.bcB S n (cdk l q) * ω := xg_lt_mulw hpos _
      calc cdk l' (Bc.bcB S n p) = cdk l' (Bc.bcB S n q + Bc.bcB S n Z) := by
            rw [hpe, Bc.bcB_add (hpL q hqT) hZL]
        _ = cdk l' (Bc.bcB S n q) + Bc.bcB S n Z := xgk_add hBZ
        _ = Bc.bcB S n (cdk l q) + Bc.bcB S n Z := by rw [IHq]
        _ = Bc.bcB S n (cdk l q + Z) := (Bc.bcB_add (hkL q hqT) hZL).symm
        _ = Bc.bcB S n (cdk l p) := by rw [← hZ]
    · push Not at hA
      have hcof : ∀ q < p, cdk l q < p := by
        intro q hqp
        have hq0 := xgK_pos (cdk_mem l q)
        have h2 : cdk l q * ((2 : ℕ) : Ordinal.{0}) < cdk l q * ω := xg_lt_mulw hq0 2
        have h2' : cdk l q + cdk l q < cdk l q * ω := by
          have e2 : cdk l q * ((2 : ℕ) : Ordinal.{0}) = cdk l q + cdk l q := by
            rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
          rw [e2] at h2; exact h2
        have hlt : cdk l q < cdk l q * ω := (lt_add_of_pos_right _ hq0).trans h2'
        have e := xgk_add hlt
        have h3 : cdk l (q + cdk l q) < cdk l p := by rw [e]; exact h2'.trans_le (hA q hqp)
        exact le_add_self.trans_lt ((cdk_strictMono l).lt_iff_lt.1 h3)
      obtain ⟨-, hpC, hδp, hρp, hcn, hBδ, hBρ⟩ := xgWin_facts hν hW0 hfar hp
      have hkΩ : cdk l p < Om1 := (hkL p hp).trans (xgL_lt_Om1 hν)
      have hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q) := fun q hq =>
        IH q hq (hq.le.trans hp)
      have hcof' := hC n l l' hW0 p hfar hp hcof hIH
      obtain ⟨r, hr1, hr2⟩ : ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
        by_cases hU : UpsPt p
        · exact hRe n l l' hW0 p hfar hp hcof hU
        · exact xgReach_nonUps hν hcn hpC hU
      -- `k_λ(p) = r`
      have hle : cdk l p ≤ r :=
        enumOrd_le_of_forall_lt (xgReach_mem hδp hcof ((cdk_strictMono l).id_le p |>.trans_lt hkΩ) hr1)
          fun b hb => (hcof b hb).trans_le (le1_le hr1.1)
      have hk : cdk l p = r := by
        refine le_antisymm hle (not_lt.1 fun hlt => ?_)
        have hcl : cdClosed l (cdk l p) := cdk_closed hkΩ
        exact absurd (hcl.2 p hρp ((cdk_strictMono l).id_le p) r hr1.1) (not_le.2 hlt)
      have hrC : r < Bc.bcC S (n + 1) := hk ▸ hkC p hp
      have hBrΩ : Bc.bcB S n r < Om1 :=
        ((Bc.bcB_bound' S n r hrC).trans_le hν).trans_le nuC_le_Om1
      rw [hk, xgk_reach hBδ hBρ hcof' hr2 hBrΩ]
  exact fun p _ hp => key p hp

/-- **`XgKCof` where `B_n` is continuous at `p`** (every `Q < B_n p` is below some `B_n q`, `q < p`). -/
theorem xgCof_of_cont {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q))
    (hcont : ∀ Q < Bc.bcB S n p, ∃ q < p, Q ≤ Bc.bcB S n q) :
    ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p := by
  obtain ⟨-, -, hr, -, -, -⟩ := hW
  have hkL : ∀ x ≤ cdTheta S l (cdCode S l), cdk l x < Nc.ncL S ω := fun x hx =>
    (((cdk_strictMono l).monotone hx).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have hpL : p < Nc.ncL S ω := ((cdk_strictMono l).id_le p).trans_lt (hkL p hp)
  intro Q hQ
  obtain ⟨q, hqp, hQq⟩ := hcont Q hQ
  have hkq : cdk l q < Nc.ncL S ω := (hcof q hqp).trans hpL
  calc cdk l' Q ≤ cdk l' (Bc.bcB S n q) := (cdk_strictMono l').monotone hQq
    _ = Bc.bcB S n (cdk l q) := hIH q hqp
    _ < Bc.bcB S n p := (Bc.bcB_lt_iff hkq hpL).2 (hcof q hqp)

/-- **Non-vacuity of `XgKCof`**: it follows from the parent `SkKFar` and the leaf `XgKReach`. -/
theorem xgCof_of_far (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : R2Skel.SkEX.SkKFar S) (hRe : XgKReach S) :
    XgKCof S := by
  intro n l l' hW p hfar hp hcof _ Q hQ
  obtain ⟨hkC, hpC, hδp, hρp, hcn, -, hBρ⟩ := xgWin_facts hν hW hfar hp
  have hkΩ : cdk l p < Om1 :=
    (hkC.trans (Bc.bcC_lt S (n + 1))).trans (xgL_lt_Om1 hν)
  obtain ⟨r, hr1, hr2⟩ : ∃ r, IsReach R2C p r ∧ IsReach R2C (Bc.bcB S n p) (Bc.bcB S n r) := by
    by_cases hU : UpsPt p
    · exact hRe n l l' hW p hfar hp hcof hU
    · exact xgReach_nonUps hν hcn hpC hU
  have hle : cdk l p ≤ r :=
    enumOrd_le_of_forall_lt (xgReach_mem hδp hcof ((cdk_strictMono l).id_le p |>.trans_lt hkΩ) hr1)
      fun b hb => (hcof b hb).trans_le (le1_le hr1.1)
  have hk : cdk l p = r := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    exact absurd ((cdk_closed hkΩ).2 p hρp ((cdk_strictMono l).id_le p) r hr1.1) (not_le.2 hlt)
  have hrC : r < Bc.bcC S (n + 1) := hk ▸ hkC
  have hBrΩ : Bc.bcB S n r < Om1 := ((Bc.bcB_bound' S n r hrC).trans_le hν).trans_le nuC_le_Om1
  have hKp : cdk l' (Bc.bcB S n p) = Bc.bcB S n r := by rw [hK n l l' hW p hfar hp, hk]
  have hQlt : cdk l' Q < Bc.bcB S n r := hKp ▸ (cdk_strictMono l') hQ
  by_contra hge
  have hcl : cdClosed l' (cdk l' Q) := cdk_closed (hQlt.trans hBrΩ)
  exact absurd (hcl.2 _ hBρ (not_lt.1 hge) _ hr2.1) (not_le.2 hQlt)

/-- **Under `L(ω+1) ≤ ν_C` and `XgKReach`: `SkKFar ⇔ XgKCof`.** -/
theorem xgKFar_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) (hRe : XgKReach S) : R2Skel.SkEX.SkKFar S ↔ XgKCof S :=
  ⟨fun h => xgCof_of_far hν h hRe, fun h => xgKFar_of hν h hRe⟩

end Googology.Trans.PoR.InaccPsi.R2.Xg
