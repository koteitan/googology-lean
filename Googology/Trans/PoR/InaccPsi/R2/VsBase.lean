import Googology.Trans.PoR.InaccPsi.R2.VpOwn
import Googology.Trans.PoR.InaccPsi.R2.VbMove

/-!
# The gap at `Ω_{s+2}` and the `B_n` moves one cardinal up, for every finite `s ≥ 1`

`W = Ω_{s+1} = Om (s + 1)`, `V = Ω_{s+2} = Om (s + 1 + 1)`, `ψ_π = S.psi · π`, `B_n = Bc.bcB S n`, `MvD` its normal-form
domain, `K⁽ˢ⁾_q = Ul.UlK S s q`, `ulDat S κ x` the largest leaf of the normal form of `x` below `κ`.  The statements of
`Vp.VpGap` and of the `Ω₂`-part of `Vp.VpDat` with `1` replaced by a finite `s` (the proofs of `Vp` are written at
`s = 1`; the lemmas they use are generic in `s`):

* `vs_fix_ge` (**a nonzero fixed point of `Ω` is `≥ V`**), `vs_gap_eq` (**the only strongly critical ordinal in
  `[ψ_V(K), ψ_V(K + 1))` is `ψ_V(K)`**, `K` own for `ψ_V`), `vs_gap_K`, `vs_gap_C` (**a member `x` of `K⁽ˢ⁾_v`, resp.
  `Cl(a, b)` (`v, b ≤ W`), in that gap gives `ψ_V(K) ∈ K⁽ˢ⁾_v`, resp. `Cl(a, b)`**);
* `vsW_D` (**`Ω_{s+1} ∈ MvD`, `B_n Ω_{s+1} = Ω_{s+1}`**), `vs_s_B` (**`B_n s = s`**), `vsB_psi` (**`B_n(ψ_W α) =
  ψ_W(B_n α)`, `B_n α` own** for own `α ∈ MvD`), `vsDatW_B` (**`ulDat W (B_n x) = B_n (ulDat W x)`**), `vsK_B`
  (**`B_n x ∈ K⁽ˢ⁾_{B_n q} ↔ x ∈ K⁽ˢ⁾_q`** for `q`, `B_n q` strongly critical in `(Ω_s, W]`), `vsB_W` (**`B_n(W^γ·D) =
  W^{B_n γ}·B_n D`**), `vsB_Wpow`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## The gap -/

/-- **A nonzero fixed point of `Ω` is `≥ Ω_{s+2}`.** -/
theorem vs_fix_ge (hs : s < ω) {x : Ordinal.{0}} (hx : Om x = x) (hx0 : x ≠ 0) :
    (Om (s + 1 + 1) : Ordinal.{0}) ≤ x := by
  by_contra h
  push Not at h
  have h1 : x < s + 1 + 1 := by rw [← hx] at h; exact Om_lt_Om.1 h
  have h2 : (ω : Ordinal.{0}) ≤ x := by
    rw [← hx]; exact Vp.vp_omega_le_Om1.trans (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  exact absurd (h1.trans (Ui.ui_s1_lt_omega (Ui.ui_s1_lt_omega hs))) (not_lt.2 h2)

/-- **The only strongly critical ordinal in `[ψ_V(K), ψ_V(K + 1))` is `ψ_V(K)`** (`K` own for `ψ_V`). -/
theorem vs_gap_eq (hs : s < ω) {K x : Ordinal.{0}} (hK : K ∈ S.CSet K (S.psi K (Om (s + 1 + 1)))) (hSC : SC x)
    (h1 : S.psi K (Om (s + 1 + 1)) ≤ x) (h2 : x < S.psi (K + 1) (Om (s + 1 + 1))) :
    x = S.psi K (Om (s + 1 + 1)) := by
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  rcases h1.lt_or_eq with hlt | heq
  · exfalso
    have hx2 : Om (s + 1) < x := (Ui.ui_L_lt_psi (s := s + 1) K).trans hlt
    obtain ⟨E, hE, hEx⟩ := Ui.ui_own_of_SC (s := s + 1) (Ui.ui_s1_lt_omega hs) hSC hx2 h2
    have h3 : K < E := (Ui.ui_own_lt_iff (s := s + 1) hK hE).1 (by rw [hEx]; exact hlt)
    have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (s + 1 + 1))) :=
      CSet.add_mem ((psi_mono hκV le_self_add).2 hK) (CSet.one_mem _ _)
    have h4 : E < K + 1 := (Ui.ui_own_lt_iff (s := s + 1) hE hown1).1 (by rw [hEx]; exact h2)
    exact absurd (Order.lt_add_one_iff.1 h4) (not_le.2 h3)
  · exact heq.symm

/-- `Ω_x ∉ (Ω_{s+1}, Ω_{s+2})`. -/
theorem vs_Om_gap {x : Ordinal.{0}} (h1 : Om (s + 1) < Om x) (h2 : Om x < Om (s + 1 + 1)) : False := by
  have a1 := Om_lt_Om.1 h1
  have a2 := Om_lt_Om.1 h2
  exact absurd (Order.lt_add_one_iff.1 a2) (not_le.2 a1)

/-- **`x ∈ K⁽ˢ⁾_v`** (`v ≤ W`) **with `x ∈ [ψ_V(K), ψ_V(K + 1))` gives `ψ_V(K) ∈ K⁽ˢ⁾_v`.** -/
theorem vs_gap_K (hs : s < ω) {v K : Ordinal.{0}} (hv : v ≤ Om (s + 1))
    (hK : K ∈ S.CSet K (S.psi K (Om (s + 1 + 1)))) :
    ∀ x, UlK S s v x → S.psi K (Om (s + 1 + 1)) ≤ x → x < S.psi (K + 1) (Om (s + 1 + 1)) →
      UlK S s v (S.psi K (Om (s + 1 + 1))) := by
  have hW : Om (s + 1) < S.psi K (Om (s + 1 + 1)) := Ui.ui_L_lt_psi (s := s + 1) K
  have hV : S.psi (K + 1) (Om (s + 1 + 1)) < Om (s + 1 + 1) := Ui.ui_psi_lt (s := s + 1) _
  have hSCt : SC (S.psi K (Om (s + 1 + 1))) := Ui.ui_psi_SC (s := s + 1) K
  intro x hx
  induction hx with
  | small h => intro h1 _; exact absurd ((h.trans_le hv).trans hW) (not_lt.2 h1)
  | zero => intro h1 _; exact absurd h1 (not_le.2 (lt_of_le_of_lt zero_le hW))
  | inacc n =>
    intro _ h2; exact absurd ((vs_fix_ge hs (S.fix n) (Vp.vp_I_ne n)).trans_lt (h2.trans hV)) (lt_irrefl _)
  | inaccW =>
    intro _ h2; exact absurd ((vs_fix_ge hs S.Om_Iw S.Iw_ne_zero).trans_lt (h2.trans hV)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (s + 1 + 1)) ≤ x
    · exact ihx hxt (le_self_add.trans_lt h2)
    by_cases hyt : S.psi K (Om (s + 1 + 1)) ≤ y
    · exact ihy hyt (le_add_self.trans_lt h2)
    push Not at hxt hyt
    exact absurd ((Lq.lq_SC_indec hSCt).add_lt hxt hyt) (not_lt.2 h1)
  | @phi x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (s + 1 + 1)) ≤ x
    · exact ihx hxt ((left_le_veblen x y).trans_lt h2)
    by_cases hyt : S.psi K (Om (s + 1 + 1)) ≤ y
    · exact ihy hyt ((right_le_veblen x y).trans_lt h2)
    push Not at hxt hyt
    exact absurd (hSCt.2 x hxt y hyt) (not_lt.2 h1)
  | om _ _ =>
    intro h1 h2
    exact (vs_Om_gap (hW.trans_le h1) (h2.trans hV)).elim
  | @coll π e hπ hπW hKπ hKe _ _ =>
    intro h1 h2
    rw [← vs_gap_eq hs hK (SC_psi hπ e) h1 h2]
    exact UlK.coll hπ hπW hKπ hKe

/-- **`x ∈ Cl(a, b)`** (`b ≤ W`) **with `x ∈ [ψ_V(K), ψ_V(K + 1))` gives `ψ_V(K) ∈ Cl(a, b)`.** -/
theorem vs_gap_C (hs : s < ω) {a b K : Ordinal.{0}} (hb : b ≤ Om (s + 1))
    (hK : K ∈ S.CSet K (S.psi K (Om (s + 1 + 1)))) :
    ∀ x, x ∈ S.CSet a b → S.psi K (Om (s + 1 + 1)) ≤ x → x < S.psi (K + 1) (Om (s + 1 + 1)) →
      S.psi K (Om (s + 1 + 1)) ∈ S.CSet a b := by
  have hW : Om (s + 1) < S.psi K (Om (s + 1 + 1)) := Ui.ui_L_lt_psi (s := s + 1) K
  have hV : S.psi (K + 1) (Om (s + 1 + 1)) < Om (s + 1 + 1) := Ui.ui_psi_lt (s := s + 1) _
  have hSCt : SC (S.psi K (Om (s + 1 + 1))) := Ui.ui_psi_SC (s := s + 1) K
  intro x hx
  induction hx with
  | small h => intro h1 _; exact absurd ((h.trans_le hb).trans hW) (not_lt.2 h1)
  | zero => intro h1 _; exact absurd h1 (not_le.2 (lt_of_le_of_lt zero_le hW))
  | inacc n =>
    intro _ h2; exact absurd ((vs_fix_ge hs (S.fix n) (Vp.vp_I_ne n)).trans_lt (h2.trans hV)) (lt_irrefl _)
  | inaccW =>
    intro _ h2; exact absurd ((vs_fix_ge hs S.Om_Iw S.Iw_ne_zero).trans_lt (h2.trans hV)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (s + 1 + 1)) ≤ x
    · exact ihx hxt (le_self_add.trans_lt h2)
    by_cases hyt : S.psi K (Om (s + 1 + 1)) ≤ y
    · exact ihy hyt (le_add_self.trans_lt h2)
    push Not at hxt hyt
    exact absurd ((Lq.lq_SC_indec hSCt).add_lt hxt hyt) (not_lt.2 h1)
  | @phi x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (s + 1 + 1)) ≤ x
    · exact ihx hxt ((left_le_veblen x y).trans_lt h2)
    by_cases hyt : S.psi K (Om (s + 1 + 1)) ≤ y
    · exact ihy hyt ((right_le_veblen x y).trans_lt h2)
    push Not at hxt hyt
    exact absurd (hSCt.2 x hxt y hyt) (not_lt.2 h1)
  | om _ _ =>
    intro h1 h2
    exact (vs_Om_gap (hW.trans_le h1) (h2.trans hV)).elim
  | @coll π e hπ hcπ hce _ _ =>
    intro h1 h2
    rw [← vs_gap_eq hs hK (SC_psi hπ e.1) h1 h2]
    exact Clos.coll hπ hcπ hce

/-! ## The `B_n` moves at `W = Ω_{s+1}` -/

/-- **`Ω_{s+1} ∈ MvD` and `B_n Ω_{s+1} = Ω_{s+1}`** for finite `s`. -/
theorem vsW_D (hs : s < ω) {n : ℕ} : MvD S (Om (s + 1)) ∧ Bc.bcB S n (Om (s + 1)) = Om (s + 1) := by
  obtain ⟨m, rfl⟩ := lt_omega0.1 hs
  have e : ((m : Ordinal.{0}) + 1) = ((m + 1 : ℕ) : Ordinal.{0}) := by norm_cast
  rw [e]
  exact Vb.vbB_Om (S := S) (n := n) (Nat.le_add_left 1 m)

/-- **`s ∈ MvD` and `B_n s = s`** for finite `s`. -/
theorem vs_s_B (hs : s < ω) {n : ℕ} : MvD S s ∧ Bc.bcB S n s = s := by
  obtain ⟨m, rfl⟩ := lt_omega0.1 hs
  exact ⟨Vb.vbDnat m, Mw.mwB_nat n m⟩

/-- **`B_n(ψ_W α) = ψ_W(B_n α)`**, and `B_n α` is own, for own `α ∈ MvD` (`1 ≤ s < ω`). -/
theorem vsB_psi (hs : s < ω) (hs0 : s ≠ 0) {n : ℕ} {α : Ordinal.{0}} (hDα : MvD S α)
    (hown : α ∈ S.CSet α (S.psi α (Om (s + 1)))) :
    MvD S (S.psi α (Om (s + 1))) ∧ Bc.bcB S n (S.psi α (Om (s + 1))) = S.psi (Bc.bcB S n α) (Om (s + 1)) ∧
      Bc.bcB S n α ∈ S.CSet (Bc.bcB S n α) (S.psi (Bc.bcB S n α) (Om (s + 1))) := by
  obtain ⟨hDs, hBs⟩ := vs_s_B (S := S) (n := n) hs
  have h := Ug.ugB_psiS (n := n) hs0 hDs hDα hown
  rw [hBs] at h
  exact h

theorem vs_Om1_le_W : (Om 1 : Ordinal.{0}) ≤ Om (s + 1) := Om_le_Om.2 le_add_self

/-- **`ulDat W (B_n x) = B_n (ulDat W x)`** for `x ∈ MvD`. -/
theorem vsDatW_B (hs : s < ω) {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) :
    MvD S (ulDat S (Om (s + 1)) x) ∧ ulDat S (Om (s + 1)) (Bc.bcB S n x) = Bc.bcB S n (ulDat S (Om (s + 1)) x) :=
  Vp.vpDat_B vs_Om1_le_W (vsW_D (S := S) (n := n) hs).1 (vsW_D (S := S) (n := n) hs).2 hx

/-- **`B_n x ∈ K⁽ˢ⁾_{B_n q} ↔ x ∈ K⁽ˢ⁾_q`** for `x, q ∈ MvD`, `q` and `B_n q` strongly critical in `(Ω_s, W]`. -/
theorem vsK_B (hs : s < ω) {n : ℕ} {x q : Ordinal.{0}} (hx : MvD S x) (hqD : MvD S q) (hq : SC q)
    (h1q : Om s < q) (hq2 : q ≤ Om (s + 1)) (hBq : SC (Bc.bcB S n q)) (h1Bq : Om s < Bc.bcB S n q)
    (hBq2 : Bc.bcB S n q ≤ Om (s + 1)) :
    UlK S s (Bc.bcB S n q) (Bc.bcB S n x) ↔ UlK S s q x := by
  have hBx : Bc.bcB S n x ∈ ⋃ a, S.CSet a 0 := by
    unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)
  rw [Uo.uo_K_iff_dat hs hBq h1Bq hBq2 hBx, Uo.uo_K_iff_dat hs hq h1q hq2 hx.1]
  obtain ⟨hDd, hB⟩ := vsDatW_B (n := n) hs hx
  rw [hB]
  exact mvB_lt_iff hDd hqD

/-- **`B_n(W^γ·D) = W^{B_n γ}·B_n D`** for `γ, D ∈ MvD`. -/
theorem vsB_W (hs : s < ω) {n : ℕ} {γ D : Ordinal.{0}} (hγ : MvD S γ) (hD : MvD S D) :
    MvD S (Om (s + 1) ^ γ * D) ∧
      Bc.bcB S n (Om (s + 1) ^ γ * D) = Om (s + 1) ^ Bc.bcB S n γ * Bc.bcB S n D := by
  obtain ⟨hDO, hBO⟩ := vsW_D (S := S) (n := n) hs
  have hO : ω ^ (Om (s + 1) : Ordinal.{0}) = Om (s + 1) := Ui.ui_W_opow s
  obtain ⟨hDm, hBm⟩ := Vj.vjB_mulOp (n := n) hDO γ hγ
  rw [hO] at hDm
  rw [hO, hBO, hO] at hBm
  have h := Vj.vjB_mulOp (n := n) hDm D hD
  rw [hBm, ← Ui.ui_W_eq s, ← Ui.ui_W_eq s] at h
  exact h

/-- **`B_n(W^γ) = W^{B_n γ}`** for `γ ∈ MvD`. -/
theorem vsB_Wpow (hs : s < ω) {n : ℕ} {γ : Ordinal.{0}} (hγ : MvD S γ) :
    MvD S (Om (s + 1) ^ γ) ∧ Bc.bcB S n (Om (s + 1) ^ γ) = Om (s + 1) ^ Bc.bcB S n γ := by
  have h := vsB_W (n := n) hs hγ (Rk.rk_one_D (S := S))
  rw [mul_one, Mw.mwB_one, mul_one] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Vs
