import Googology.Trans.PoR.InaccPsi.R2.MwGam

/-!
# The index among the ordinals off `P_{k+1}` moves with `B_n`

`B_n = Bc.bcB S n`, `φ_k = veblen k`, `P_m` the range of `φ_m` (`R2.VzP`), `ind_τ(β) = phInd k τ β` the order type of
`{x ∈ (τ, β) | x ∉ P_{k+1}}` (`R2.PhLev`).  `X` is a strongly critical ordinal below `L(ω)`.

* `mwLastP` (**the last point of `P_{k+1}` below `β`**): for `τ ∈ P_{k+1}`, `τ < β ∉ P_{k+1}`, there is a largest
  `p ∈ P_{k+1} ∩ [τ, β)` (`P_{k+1}` is closed: `φ_k` is normal);
* `mwIter_nfix`, `mwIter_lt`, `mwIter_B` (**`B_n(φ_k^j(p+1)) = φ_k^j(B_n p + 1)`** for `p ∈ P_{k+1}`, `p < X`);
* `mwGap_move` (**the gap moves**): no point of `P_{k+1}` in `(p, p + 1 + δ]` gives none in `(B_n p, B_n p + 1 + B_n δ]`
  (`δ` is below the least point of `P_{k+1}` above `p`, which is `sup_j φ_k^j(p+1)`);
* `mwInd_move` (**`ind_{τ'}(B_n β) = B_n(ind_τ(β))`** for a strongly critical `τ < β < X`, `β ∉ P_{k+1}`, `B_n τ = τ'`;
  also `τ' < B_n β ∉ P_{k+1}`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

theorem mw_SC_P (k : ℕ) {τ : Ordinal.{0}} (hτ : SC τ) : VzP (k + 1) τ :=
  vzP_succ.2 (hτ.veblen_right (ph_nat_lt hτ k))

/-- **The last point of `P_{k+1}` below `β`.** -/
theorem mwLastP {k : ℕ} {τ β : Ordinal.{0}} (hτ : VzP (k + 1) τ) (hτβ : τ < β) (hβ : ¬ VzP (k + 1) β) :
    ∃ p, VzP (k + 1) p ∧ τ ≤ p ∧ p < β ∧ ∀ z, p < z → z < β → ¬ VzP (k + 1) z := by
  set s : Set Ordinal.{0} := {q | VzP (k + 1) q ∧ τ ≤ q ∧ q < β} with hs
  have hne : s.Nonempty := ⟨τ, hτ, le_rfl, hτβ⟩
  have hbdd : BddAbove s := ⟨β, fun q hq => hq.2.2.le⟩
  have hfix : veblen (k : Ordinal.{0}) (sSup s) = sSup s := by
    rw [(isNormal_veblen (k : Ordinal.{0})).map_sSup hne hbdd]
    congr 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩; rw [vzP_succ.1 hq'.1]; exact hq'
    · intro hq; exact ⟨q, hq, vzP_succ.1 hq.1⟩
  have hP : VzP (k + 1) (sSup s) := vzP_succ.2 hfix
  have hle : sSup s ≤ β := csSup_le hne fun q hq => hq.2.2.le
  have hlt : sSup s < β := lt_of_le_of_ne hle fun e => hβ (e ▸ hP)
  refine ⟨sSup s, hP, le_csSup hbdd ⟨hτ, le_rfl, hτβ⟩, hlt, fun z hpz hzβ hz => ?_⟩
  have := le_csSup hbdd ⟨hz, (le_csSup hbdd ⟨hτ, le_rfl, hτβ⟩).trans hpz.le, hzβ⟩
  exact absurd hpz (not_lt.2 this)

/-- The iterates `φ_k^j(p+1)` are not fixed points of `φ_k`. -/
theorem mwIter_nfix {k : ℕ} (hk : 1 ≤ k) (p : Ordinal.{0}) :
    ∀ j : ℕ, veblen (k : Ordinal.{0}) ((veblen (k : Ordinal.{0}))^[j] (p + 1)) ≠
      (veblen (k : Ordinal.{0}))^[j] (p + 1)
  | 0 => by
    intro h
    exact ph_P_succ_not (k := k) p (vzP_succ.2 h)
  | j + 1 => by
    intro h
    rw [Function.iterate_succ_apply'] at h
    exact mwIter_nfix hk p j ((veblen_injective _) h)

theorem mwIter_ge {k : ℕ} (p : Ordinal.{0}) :
    ∀ j : ℕ, p + 1 ≤ (veblen (k : Ordinal.{0}))^[j] (p + 1)
  | 0 => le_rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact (mwIter_ge p j).trans (right_le_veblen _ _)

theorem mwIter_lt {k : ℕ} (hk : 1 ≤ k) {p X : Ordinal.{0}} (hX : SC X) (hpX : p < X) (j : ℕ) :
    (veblen (k : Ordinal.{0}))^[j] (p + 1) < X := by
  have hXf : veblen (k : Ordinal.{0}) X = X := hX.veblen_right (ph_nat_lt hX k)
  have hle : (veblen (k : Ordinal.{0}))^[j] (p + 1) ≤ X :=
    (iterate_le_nfp _ _ j).trans (nfp_le_fp (isNormal_veblen _).strictMono.monotone
      (Order.add_one_le_of_lt hpX) hXf.le)
  refine lt_of_le_of_ne hle fun e => mwIter_nfix hk p j ?_
  rw [e]; exact hXf

theorem mwB_one (n : ℕ) : Bc.bcB S n (1 : Ordinal.{0}) = 1 := by
  have := mwB_nat (S := S) n 1; rwa [Nat.cast_one] at this

theorem mwB_succ {n : ℕ} {p : Ordinal.{0}} (hp : p < Nc.ncL S ω) :
    Bc.bcB S n (p + 1) = Bc.bcB S n p + 1 := by
  rw [Bc.bcB_add hp (by have := mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this), mwB_one]

/-- **`B_n(φ_k^j(p+1)) = φ_k^j(B_n p + 1)`.** -/
theorem mwIter_B {n k : ℕ} (hk : 1 ≤ k) {p X : Ordinal.{0}} (hkp : (k : Ordinal.{0}) < p) (hX : SC X)
    (hpX : p < X) (hXL : X < Nc.ncL S ω) :
    ∀ j : ℕ, Bc.bcB S n ((veblen (k : Ordinal.{0}))^[j] (p + 1)) =
      (veblen (k : Ordinal.{0}))^[j] (Bc.bcB S n p + 1)
  | 0 => by
    simp only [Function.iterate_zero, id]
    exact mwB_succ (hpX.trans hXL)
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hyX := mwIter_lt hk hX hpX j
    have hky : (k : Ordinal.{0}) < (veblen (k : Ordinal.{0}))^[j] (p + 1) :=
      hkp.trans ((lt_add_one p).trans_le (mwIter_ge p j))
    rw [(mwB_veblen_nat (k := n) (mvD_of_lt (hyX.trans hXL)) hky (mwIter_nfix hk p j)).2,
      mwIter_B hk hkp hX hpX hXL j]

/-- **The gap moves**: no point of `P_{k+1}` in `(p, p + 1 + δ]` gives none in `(B_n p, B_n p + 1 + B_n δ]`. -/
theorem mwGap_move {n k : ℕ} (hk : 1 ≤ k) {p δ X : Ordinal.{0}} (hkp : (k : Ordinal.{0}) < p)
    (hX : SC X) (hβX : p + 1 + δ < X) (hXL : X < Nc.ncL S ω)
    (hgap : ∀ z, z ≤ δ → ¬ VzP (k + 1) (p + 1 + z)) :
    ∀ z, z ≤ Bc.bcB S n δ → ¬ VzP (k + 1) (Bc.bcB S n p + 1 + z) := by
  set f := veblen (k : Ordinal.{0}) with hf
  have hfm : Monotone f := (isNormal_veblen _).strictMono.monotone
  have hpX : p < X := ((lt_add_one p).trans_le (le_self_add : p + 1 ≤ p + 1 + δ)).trans hβX
  have hδX : δ < X := lt_of_le_of_lt le_add_self hβX
  -- `δ` is below the least point of `P_{k+1}` above `p`
  have hδq : δ < nfp f (p + 1) := by
    by_contra hle
    push Not at hle
    have hqP : VzP (k + 1) (nfp f (p + 1)) := vzP_succ.2 (nfp_fp (isNormal_veblen _) _)
    have hpq : p + 1 < nfp f (p + 1) :=
      lt_of_le_of_ne (le_nfp _ _) fun e => ph_P_succ_not (k := k) p (e ▸ hqP)
    have hprin : IsPrincipal (· + ·) (nfp f (p + 1)) := by
      have hE : ω ^ nfp f (p + 1) = nfp f (p + 1) := ph_P_E hqP
      rw [← hE]; exact isPrincipal_add_omega0_opow _
    have e : p + 1 + nfp f (p + 1) = nfp f (p + 1) := hprin.add_eq_right hpq
    exact hgap _ hle (by rw [e]; exact hqP)
  obtain ⟨j, hj⟩ := (lt_nfp_iff (f := f)).1 hδq
  have hjX := mwIter_lt hk hX hpX j
  have hBδ : Bc.bcB S n δ < f^[j] (Bc.bcB S n p + 1) := by
    rw [← mwIter_B (n := n) hk hkp hX hpX hXL j]
    exact (Bc.bcB_lt_iff (hδX.trans hXL) (hjX.trans hXL)).2 hj
  intro z hz hP
  set w := Bc.bcB S n p + 1 + z with hw
  have hwq : nfp f (Bc.bcB S n p + 1) ≤ w :=
    nfp_le_fp hfm (by rw [hw]; exact le_self_add) (vzP_succ.1 hP).le
  have hzw : z < w :=
    lt_of_le_of_lt hz (hBδ.trans_le ((iterate_le_nfp _ _ j).trans hwq))
  have hpw : Bc.bcB S n p + 1 < w := by
    rcases (le_self_add : Bc.bcB S n p + 1 ≤ w).lt_or_eq with h | h
    · exact h
    · exfalso; exact ph_P_succ_not (k := k) _ (by rw [h]; exact hP)
  have hprin : IsPrincipal (· + ·) w := by
    have hE : ω ^ w = w := ph_P_E hP
    rw [← hE]; exact isPrincipal_add_omega0_opow _
  have h3 : Bc.bcB S n p + 1 + z < w := hprin hpw hzw
  exact absurd h3 (by rw [← hw]; exact lt_irrefl _)

/-- **`ind_{τ'}(B_n β) = B_n(ind_τ(β))`**, with `τ' < B_n β ∉ P_{k+1}`. -/
theorem mwInd_move {n k : ℕ} (hk : 1 ≤ k) {τ τ' β X : Ordinal.{0}} (hτ : SC τ)
    (hB : Bc.bcB S n τ = τ') (hτβ : τ < β) (hβ : ¬ VzP (k + 1) β) (hX : SC X) (hβX : β < X)
    (hXL : X < Nc.ncL S ω) :
    τ' < Bc.bcB S n β ∧ ¬ VzP (k + 1) (Bc.bcB S n β) ∧
      phInd k τ' (Bc.bcB S n β) = Bc.bcB S n (phInd k τ β) := by
  have hL : ∀ {y}, y < X → y < Nc.ncL S ω := fun h => h.trans hXL
  obtain ⟨p, hpP, hτp, hpβ, hmax⟩ := mwLastP (mw_SC_P k hτ) hτβ hβ
  obtain ⟨δ, hδ⟩ := exists_add_of_le (Order.add_one_le_of_lt hpβ)
  have hkp : (k : Ordinal.{0}) < p := (ph_nat_lt hτ k).trans_le hτp
  have hpX : p < X := hpβ.trans hβX
  have hgap : ∀ z, z ≤ δ → ¬ VzP (k + 1) (p + 1 + z) := by
    intro z hz
    rcases hz.lt_or_eq with hz | rfl
    · refine hmax _ ((lt_add_one p).trans_le le_self_add) ?_
      rw [hδ]; exact (add_lt_add_iff_left _).2 hz
    · rw [← hδ]; exact hβ
  have hgap' : ∀ z < δ, ¬ VzP (k + 1) (p + 1 + z) := fun z hz => hgap z hz.le
  have hβX' : p + 1 + δ < X := hδ ▸ hβX
  have hp1L : p + 1 < Nc.ncL S ω := hL ((le_self_add : p + 1 ≤ p + 1 + δ).trans_lt hβX')
  have hδL : δ < Nc.ncL S ω := hL ((le_add_self : δ ≤ p + 1 + δ).trans_lt hβX')
  have hBβ : Bc.bcB S n β = Bc.bcB S n p + 1 + Bc.bcB S n δ := by
    rw [hδ, Bc.bcB_add hp1L hδL, mwB_succ (hL hpX)]
  have hgapB := mwGap_move (n := n) hk hkp hX hβX' hXL hgap
  have hBP : VzP (k + 1) (Bc.bcB S n p) := vzP_succ.2 (mwB_fix (mvD_of_lt (hL hpX)) (vzP_succ.1 hpP))
  have hτβ' : τ' < Bc.bcB S n β := by
    rw [← hB]; exact (Bc.bcB_lt_iff (hL (hτβ.trans hβX)) (hL hβX)).2 hτβ
  refine ⟨hτβ', by rw [hBβ]; exact hgapB _ le_rfl, ?_⟩
  rcases hτp.lt_or_eq with hlt | heq
  · -- `p > τ`
    have hτ'p : τ' < Bc.bcB S n p := by
      rw [← hB]; exact (Bc.bcB_lt_iff (hL (hτp.trans_lt hpβ |>.trans hβX)) (hL hpX)).2 hlt
    rw [hδ, phInd_above hpP hlt hgap', ← hδ, hBβ, phInd_above hBP hτ'p fun z hz => hgapB z hz.le,
      Bc.bcB_add (hL hpX) hδL]
  · -- `p = τ`
    subst heq
    rw [hδ, phInd_low hgap', ← hδ, hBβ, hB, phInd_low fun z hz => by
      have := hgapB z hz.le; rwa [hB] at this]

end Googology.Trans.PoR.InaccPsi.R2.Mw
