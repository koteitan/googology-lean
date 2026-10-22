import Googology.Trans.PoR.InaccPsi.R2.LeBlk

/-!
# The reading moves below `F_{ω²} = ψ_{Ω₂}(Ω₂^ω)`, and the road with the moves at the codes `F_{ω²} ≤ m_λ ≤ θ·ω`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `h_k` = `Le.leH`, `W^k = Ω₂^k`, `Ω^k = Ω₁^k`.

* `leB_mulOp` (**`B_n(ω^K·x) = ω^K·B_n(x)`** for `B_n K = K` and every `x < K` in a class of `MvD` closed under `log`
  and the tail: `B_n(W^k·γ) = W^k·B_n γ`, `B_n(Ω^k·x) = Ω^k·B_n x`), `leB_W`, `leB_O`;
* `leOwn_own`, `leOwn_mem` (an own argument is own in the closure sense, in the hull, below `A_{η_λ}`), `leB_top`
  (`B_n(T_k(β)) = T_k(B_n β)`);
* `leDigMove` (**the digits move**: if the codes below `ψ_{Ω₂}(β + c)` move, then `B_n c` is own at `λ'` over `B_n β`
  and `B_n(h_k(c)) = h'_k(B_n c)`), `leAtMove_Fw` (**every atom below `F_{ω²}` moves** once the codes below it move),
  `leThMove_Fw` (**`MxThMove` at every long code `m_λ < F_{ω²}`**, no hypothesis);
* `LeThMoveT S` (a hypothesis name): the reading moves at the codes `F_{ω²} ≤ m_λ ≤ θ·ω`; `leThMoveS_of_T`,
  `leThMoveT_of_S` (equivalent to `Ld.LdThMoveS`), `leRoadT` (**the road**).

No new axiom.  New definition: the hypothesis name `LeThMoveT`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-! ## `B_n(ω^K·x) = ω^K·B_n(x)` -/

/-- **`B_n(ω^K·x) = ω^K·B_n(x)`** for `B_n K = K` and every `x < K` in a class `P ⊆ MvD` closed under `log` and the
tail. -/
theorem leB_mulOp {n : ℕ} {K : Ordinal.{0}} (hDK : MvD S K) (hBK : Bc.bcB S n K = K)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPK : ∀ x, P x → x < K) :
    ∀ x, P x → MvD S (ω ^ K * x) ∧ Bc.bcB S n (ω ^ K * x) = ω ^ K * Bc.bcB S n x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hDx := hPD x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨by rw [mul_zero]; exact hDx, by rw [mul_zero, Bc.bcB_zero, mul_zero]⟩
  obtain ⟨hPg, hPr⟩ := hPdec x hx hx0
  set g := log ω x with hg
  have hlead : ω ^ g ≤ x := opow_log_le_self ω hx0
  have hxlt : x < ω ^ g * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
  have hdec : ω ^ g + (x - ω ^ g) = x := Ordinal.add_sub_cancel_of_le hlead
  have hrx : x - ω ^ g < x := by
    refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
    have h' : ω ^ g + x = x := by
      calc ω ^ g + x = ω ^ g + (x - ω ^ g) := by rw [e]
        _ = x := hdec
    have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
    exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
  have hDg := hPD _ hPg
  have hDr := hPD _ hPr
  obtain ⟨hDκr, hBκr⟩ := IH _ hrx hPr
  obtain ⟨hDog, hBog⟩ := ldB_opow (n := n) hDg
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDog hDr
  rw [hdec] at hBx
  obtain ⟨hDK', hBK'⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBK'
  obtain ⟨hDKg, hBKg⟩ := mvB_add (k := n) hDK hDg
  rw [hBK] at hBKg
  have hlt := hPK x hx
  rcases eq_or_ne g 0 with hg0 | hg0
  · have hl : ω ^ K * ω ^ g = ω ^ K := by rw [hg0, opow_zero, mul_one]
    have e : ω ^ K * x = ω ^ K + ω ^ K * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, hl]
    have hB1 : Bc.bcB S n (ω ^ g) = 1 := by rw [hg0, opow_zero, mwB_one]
    have hBx' : Bc.bcB S n x = 1 + Bc.bcB S n (x - ω ^ g) := by rw [hBx, hB1]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDK' hDκr
    rw [e, hBx', mul_add, mul_one]
    exact ⟨hDs, by rw [hBs, hBK', hBκr]⟩
  · have hne : ω ^ (K + g) ≠ K + g := by
      intro h
      have hgK : g < K := (log_le_self ω x).trans_lt hlt
      have h1 : K + g < K * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        exact (add_lt_add_iff_left K).2 hgK
      have h2 : K * 2 ≤ ω ^ (K + g) := by
        rw [opow_add]
        have h3 : (ω : Ordinal.{0}) ≤ ω ^ g := by
          have := (opow_le_opow_iff_right one_lt_omega0).2 (Order.one_le_iff_ne_zero.2 hg0)
          rwa [opow_one] at this
        calc K * 2 ≤ ω ^ K * 2 := mul_le_mul_left (right_le_opow K one_lt_omega0) 2
          _ ≤ ω ^ K * ω := mul_le_mul_right (natCast_lt_omega0 2).le _
          _ ≤ ω ^ K * ω ^ g := mul_le_mul_right h3 _
      rw [h] at h2
      exact absurd h1 (not_lt.2 h2)
    obtain ⟨hDl, hBl⟩ := mvB_opow (k := n) hDKg hne
    have e : ω ^ K * x = ω ^ (K + g) + ω ^ K * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, opow_add]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDl hDκr
    rw [e, hBx, hBog, mul_add]
    refine ⟨hDs, ?_⟩
    rw [hBs, hBl, hBKg, hBκr, opow_add]

theorem leB_natMul {n : ℕ} {x : Ordinal.{0}} (hD : MvD S x) (hB : Bc.bcB S n x = x) :
    ∀ m : ℕ, MvD S (x * (m : Ordinal.{0})) ∧ Bc.bcB S n (x * (m : Ordinal.{0})) = x * (m : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_zero n⟩
  | m + 1 => by
    obtain ⟨hD', hB'⟩ := leB_natMul hD hB m
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD' hD
    rw [Nat.cast_succ, mul_add_one]
    exact ⟨hDs, by rw [hBs, hB', hB]⟩

/-- `B_n(W^k·γ) = W^k·B_n γ` for every `γ < Ω₂` in a class of `MvD` closed under `log` and the tail. -/
theorem leB_W {n : ℕ} (k : ℕ) (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1)) :
    ∀ x, P x → MvD S (leW k * x) ∧ Bc.bcB S n (leW k * x) = leW k * Bc.bcB S n x := by
  rcases k with _ | j
  · intro x hx; rw [leW_zero, one_mul, one_mul]; exact ⟨hPD x hx, rfl⟩
  · obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    obtain ⟨hDK, hBK⟩ := leB_natMul (n := n) hD2 hB2 (j + 1)
    have hpos : (0 : Ordinal.{0}) < ((j + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast Nat.succ_pos j
    exact leB_mulOp hDK hBK P hPD hPdec fun x hx => (hPW x hx).trans_le (le_mul_left _ hpos)

/-- `B_n(Ω^k·x) = Ω^k·B_n x` for every countable `x < c_{n+1}`. -/
theorem leB_O {n : ℕ} (k : ℕ) {x : Ordinal.{0}} (hx1 : x < Om 1) (hxc : x < Bc.bcC S (n + 1)) :
    MvD S (leO k * x) ∧ Bc.bcB S n (leO k * x) = leO k * Bc.bcB S n x := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  rcases k with _ | j
  · rw [leO_zero, one_mul, one_mul]; exact ⟨mvD_of_lt (hxc.trans hLw), rfl⟩
  · obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    obtain ⟨hDK, hBK⟩ := leB_natMul (n := n) hDO hBO (j + 1)
    have hpos : (0 : Ordinal.{0}) < ((j + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast Nat.succ_pos j
    exact leB_mulOp hDK hBK (fun y => y < Om 1 ∧ y < Bc.bcC S (n + 1))
      (fun y hy => mvD_of_lt (hy.2.trans hLw))
      (fun y hy _ => ⟨⟨(log_le_self ω y).trans_lt hy.1, (log_le_self ω y).trans_lt hy.2⟩,
        ⟨(Ordinal.sub_le_self _ _).trans_lt hy.1, (Ordinal.sub_le_self _ _).trans_lt hy.2⟩⟩)
      (fun y hy => hy.1.trans_le (le_mul_left _ hpos)) x ⟨hx1, hxc⟩

/-- `W^k` is fixed by `B_n`. -/
theorem leB_Wfix {n : ℕ} (k : ℕ) : MvD S (leW k) ∧ Bc.bcB S n (leW k) = leW k := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := leB_natMul (n := n) hD2 hB2 k
  obtain ⟨hD, hB⟩ := ldB_opow (n := n) hDK
  unfold leW; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-! ## Own arguments in the hull -/

section Own

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- An own argument is own in the closure sense. -/
theorem leOwn_own : ∀ (k : ℕ) (β c : Ordinal.{0}), LeBase S l k β → LeOwn S l k β c →
    β + c ∈ S.CSet (β + c) (S.psi (β + c) (Om (1 + 1))) := by
  intro k
  induction k with
  | zero =>
    intro β c hb hc
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    obtain ⟨hβd, -, -, hβown⟩ := hb
    rw [e1] at hβd hβown
    exact ldOwn hβown hβd hc.2
  | succ k IHk =>
    intro β c hb hc
    obtain ⟨γ, c', rfl, hγc, hγT, hc'⟩ := hc
    have hγW : γ < Om (1 + 1) := hγT.trans (leT_lt_Om2 _ _)
    rw [← add_assoc]
    exact IHk _ c' (leBase_sub hb ((ldHull_iff hl hX hγW).2 hγc) hγT) hc'

/-- An own argument is in the hull and below `A_{η_λ}`. -/
theorem leOwn_mem : ∀ (k : ℕ) (β c : Ordinal.{0}), LeBase S l k β → LeOwn S l k β c →
    β + c ∈ cdHull S l ∧ β + c < ConjT.Aη S (cdEta S l) := by
  intro k
  induction k with
  | zero =>
    intro β c hb hc
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    obtain ⟨-, hβH, hβA, -⟩ := hb
    rw [e1] at hβA
    have hc2 : c < Om (1 + 1) := hc.2.trans (ldTop_lt_Om2 β)
    exact ⟨CSet.add_mem hβH ((ldHull_iff hl hX hc2).2 hc.1), ((add_lt_add_iff_left β).2 hc2).trans hβA⟩
  | succ k IHk =>
    intro β c hb hc
    obtain ⟨γ, c', rfl, hγc, hγT, hc'⟩ := hc
    have hγW : γ < Om (1 + 1) := hγT.trans (leT_lt_Om2 _ _)
    rw [← add_assoc]
    exact IHk _ c' (leBase_sub hb ((ldHull_iff hl hX hγW).2 hγc) hγT) hc'

end Own

/-- `B_n(T_k(β)) = T_k(B_n β)` for a base `β`. -/
theorem leB_top {n : ℕ} {l : Ordinal.{0}} (k : ℕ) {β : Ordinal.{0}} (hb : LeBase S l k β) (hDβ : MvD S β) :
    MvD S (leT S k β) ∧ Bc.bcB S n (leT S k β) = leT S k (Bc.bcB S n β) := by
  obtain ⟨-, -, -, hβown⟩ := hb
  obtain ⟨hDW, hBW⟩ := leB_Wfix (S := S) (n := n) (k + 1)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDW
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDs (CSet.add_mem (hβown _ le_rfl) (leW_mem _ _ _))
  refine ⟨hDT, ?_⟩
  unfold leT; rw [hBT, hBs, hBW]

/-! ## The digits move -/

/-- **The digits move**: if the codes below `ψ_{Ω₂}(β + c)` move, then `B_n c` is own at `λ'` over `B_n β` and
`B_n(h_k(c)) = h'_k(B_n c)`. -/
theorem leDigMove {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ (k : ℕ) (β c : Ordinal.{0}), LeBase S l k β → MvD S β → LeOwn S l k β c →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + c) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S c ∧ MvD S (β + c) ∧ Bc.bcB S n (β + c) = Bc.bcB S n β + Bc.bcB S n c ∧
      LeOwn S l' k (Bc.bcB S n β) (Bc.bcB S n c) ∧ MvD S (leH S l k c) ∧
      Bc.bcB S n (leH S l k c) = leH S l' k (Bc.bcB S n c) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  intro k
  induction k with
  | zero =>
    intro β c hb hDβ hc IH
    have hb' := hb
    have e1 : leW (0 + 1) = Om (1 + 1) := leW_one
    obtain ⟨hβd, -, -, hβown⟩ := hb
    rw [e1] at hβd hβown
    obtain ⟨hcg, hcF⟩ := hc
    obtain ⟨hDc, hBc, hΘX, hΘe⟩ := IH c hcg (ldTop_gt hβown hβd hcF)
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hDT, hBT⟩ := leB_top (n := n) 0 hb' hDβ
    rw [leT_zero, leT_zero] at hBT
    rw [leT_zero] at hDT
    refine ⟨hDc, hDs, hBs, ⟨hBc, ?_⟩, mvD_of_lt (hΘX.trans hLw), hΘe.symm⟩
    rw [← hBT]; exact (mvB_lt_iff (k := n) hDc hDT).2 hcF
  | succ k IHk =>
    intro β c hb hDβ hc IH
    have hb' := hb
    obtain ⟨hβd, -, -, hβown⟩ := hb
    obtain ⟨γ, c', rfl, hγc, hγT, hc'⟩ := hc
    have hγW : γ < Om (1 + 1) := hγT.trans (leT_lt_Om2 _ _)
    have hγs : γ < S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) := leT_gt hβown hβd hγT
    have hle : S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) ≤ S.psi (β + (leW (k + 1) * γ + c')) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) (by rw [← add_assoc]; exact le_self_add)).1
    obtain ⟨hDγ, hBγc, hΘγX, hΘγ⟩ := IH γ hγc (hγs.trans_le hle)
    -- `B_n(W^{k+1}·γ) = W^{k+1}·B_n γ`
    obtain ⟨hDμγ, hBμγ⟩ := leB_W (n := n) (k + 1)
      (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (β + (leW (k + 1) * γ + c')) (Om (1 + 1)) ∧
        x < Om (1 + 1))
      (fun x hx => (IH x hx.1 hx.2.1).1)
      (fun x hx hx0 => by
        obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
        have hlx : log ω x ≤ x := log_le_self ω x
        have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
        exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
          ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
            (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩)
      (fun x hx => hx.2.2) γ ⟨hγc, hγs.trans_le hle, hγW⟩
    obtain ⟨hDβ', hBβ'⟩ := mvB_add (k := n) hDβ hDμγ
    have hb2 := leBase_sub hb' ((ldHull_iff hl hX hγW).2 hγc) hγT
    obtain ⟨hDc', -, -, hown', hDh', hBh'⟩ := IHk _ c' hb2 hDβ' hc' (fun x hx hxs => IH x hx (by
      rw [← add_assoc]; exact hxs))
    obtain ⟨hDc, hBc⟩ := mvB_add (k := n) hDμγ hDc'
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hDT, hBT⟩ := leB_top (n := n) (k + 1) hb' hDβ
    have hBγT : Bc.bcB S n γ < leT S (k + 1) (Bc.bcB S n β) := by
      rw [← hBT]; exact (mvB_lt_iff (k := n) hDγ hDT).2 hγT
    rw [hBβ', hBμγ] at hown'
    have hΘγ1 : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := hΘγX.trans hc1
    obtain ⟨hDOΘ, hBOΘ⟩ := leB_O (S := S) (n := n) (k + 1) hΘγ1 hΘγX
    obtain ⟨hDsum, hBsum⟩ := mvB_add (k := n) hDOΘ hDh'
    have hHc := leH_succ_eq (S := S) l k (γ := γ) (leOwn_lt k hc')
    have hHc' := leH_succ_eq (S := S) l' k (γ := Bc.bcB S n γ) (leOwn_lt k hown')
    refine ⟨hDc, hDs, hBs, ?_, ?_, ?_⟩
    · rw [hBc, hBμγ]
      exact ⟨Bc.bcB S n γ, Bc.bcB S n c', rfl, hBγc, hBγT, hown'⟩
    · rw [hHc]; exact hDsum
    · rw [hHc, hBc, hBμγ, hHc', hBsum, hBOΘ, hΘγ, hBh']

/-! ## The atoms below `F_{ω²}` move -/

theorem leWw_lt_OmW : ω ^ (Om (1 + 1 : Ordinal.{0}) * ω) < Om ω := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  exact ldOpow_lt_SC hSC (ldMul_lt_SC hSC ldOm2_lt_OmW (Lw.lw_omega_lt_SC hSC))

theorem leFw_SC : SC (leFw S) := SC_psi (InR_Om_succ 1) _
theorem leFw_lt_Om2 : leFw S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem leOm1_lt_Fw : Om (1 : Ordinal.{0}) < leFw S := (psiS_bounds (S := S) _ 1).1

theorem leWw_mem (a b : Ordinal.{0}) : ω ^ (Om (1 + 1 : Ordinal.{0}) * ω) ∈ S.CSet a b := by
  have h := CSet.phi_mem (S := S) (CSet.zero_mem a b) (ldW2_mem a b)
  rwa [veblen_zero_apply] at h

theorem leFw_lt_th : leFw S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) leWw_lt_OmW (leWw_mem _ _)

theorem leW_lt_Ww (k : ℕ) : leW k < ω ^ (Om (1 + 1 : Ordinal.{0}) * ω) :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (natCast_lt_omega0 k))

theorem leG2_le_Fw : ldG2 S ≤ leFw S := by
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  have h := (leW_lt_Ww 2).le
  have e : leW 2 = Om (1 + 1) * Om (1 + 1) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, leW_succ, leW_one]
  rwa [e] at h

/-- **Every atom below `F_{ω²}` moves** once the codes below it move. -/
theorem leAtMove_Fw {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hl' : IsRestartIdx l')
    (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ s ∈ ldAtR S l, s < leFw S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < leFw S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < leFw S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro s hs hsF IHx
  obtain ⟨k, c, hc, rfl, hth, hown, hbd⟩ := leTh_Fw hl hX hA hρ s hs hsF
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  obtain ⟨hDc, -, -, hBc', hDh, hBh⟩ := leDigMove (n := n) (l' := l') hl hX k 0 c (leBase_zero l k) hD0 hc
    (fun x hx hxs => by
      rw [zero_add] at hxs
      obtain ⟨h1, h2, -, h4, h5⟩ := IHx x hx hxs
      exact ⟨h1, h2, h4, h5⟩)
  rw [Bc.bcB_zero] at hBc'
  have hownc : c ∈ S.CSet c (S.psi c (Om (1 + 1))) := by
    have := leOwn_own hl hX k 0 c (leBase_zero l k) hc; rwa [zero_add] at this
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hownc
  have hownB : Bc.bcB S n c ∈ S.CSet (Bc.bcB S n c) (S.psi (Bc.bcB S n c) (Om (1 + 1))) := by
    have := leOwn_own hl' hX' k 0 _ (leBase_zero l' k) hBc'; rwa [zero_add] at this
  obtain ⟨hBH, hBA⟩ := leOwn_mem hl' hX' k 0 _ (leBase_zero l' k) hBc'
  rw [zero_add] at hBH hBA
  have hBW : Bc.bcB S n c < ω ^ (Om (1 + 1 : Ordinal.{0}) * ω) := (leOwn_lt k hBc').trans (leW_lt_Ww _)
  -- the reading at `λ'`
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  obtain ⟨hth', -, -⟩ := (leBlk hl' hX' k 0 (A' + 1) (leBase_zero l' k) hA'1 (ldBlk_zero hA' hρ')).1 _ hBc'
  rw [zero_add] at hth'
  -- `d = 1 + h_k(c) ≤ θ`
  have hθ1 : leO (k + 1) ≤ ConjT.th S :=
    (leO_lt_G1 (S := S) (k + 1)).le.trans (psi_mono (S := S) (InR_Om_succ 1) zero_le).1
  have hdθ : 1 + leH S l k c ≤ ConjT.th S := by
    refine (isPrincipal_add_omega0_opow _ ?_ hbd).le.trans hθ1
    exact one_lt_omega0.trans_le (left_le_opow ω (mul_pos (Om_pos one_ne_zero) (by exact_mod_cast Nat.succ_pos k)))
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1 hDh
  have hownd : A + (1 + leH S l k c) ∈ S.CSet (A + (1 + leH S l k c)) (S.psi (A + (1 + leH S l k c)) (Om 1)) := by
    rw [← add_assoc]; exact hown
  refine ⟨hDs, ?_, ?_, ?_, ?_⟩
  · rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩
  · rw [hBs]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) hBW ((psi_mono (S := S) (InR_Om_succ 1) hBW.le).2 hownB)
  · rw [hth, add_assoc]; exact hbX _ hdθ
  · rw [hBs, hth', hth, add_assoc A, hBψ _ hDd hownd hdθ, hBd, mwB_one, hBh, add_assoc]

/-- **`MxThMove` at every long code `m_λ < F_{ω²}`.** -/
theorem leThMove_Fw {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < leFw S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have hWA : Om ω ≤ A := le_self_add
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : leFw S ≤ cdPi S η := (psi_mono (S := S) (InR_Om_succ 1) (leWw_lt_OmW.le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heF : e < leFw S := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heF.trans leFw_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hρSC : SC (upsilon l) := hρA ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDe, -, hBeF, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw leFw_SC leOm1_lt_Fw.le
    (leAtMove_Fw hl hl' hX hX' hown hA' hρA hρA' hbX hBψ) e hge heF
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeF.trans leFw_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeF.trans leFw_lt_Om2).le]
  exact hEq.symm

/-! ## The remaining reading moves and the road -/

/-- **The reading moves at the codes `F_{ω²} ≤ m_λ ≤ θ·ω`.** -/
def LeThMoveT (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFw S ≤ cdCode S l → cdCode S l ≤ ConjT.th S * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`LeThMoveT` gives `LdThMoveS`.** -/
theorem leThMoveS_of_T (h : LeThMoveT S) : LdThMoveS S := by
  intro n l l' hR h1 hr hl' hB hm hG hw
  by_cases hK : cdCode S l < leFw S
  · exact leThMove_Fw hR h1 hr hl' hB
      (ldGam_lt_Fw.trans_le (ldFw_le_G2.trans (hG.trans (cdCodeOf_le_exp S _)))) hK
  · exact h n l l' hR h1 hr hl' hB hm (not_lt.1 hK) hw

/-- `LdThMoveS` gives `LeThMoveT` (so `LeThMoveT` is not the stronger hypothesis). -/
theorem leThMoveT_of_S (h : LdThMoveS S) : LeThMoveT S :=
  fun n l l' hR h1 hr hl' hB hm hF hw => h n l l' hR h1 hr hl' hB hm (leG2_le_Fw.trans hF) hw

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LeThMoveT` and `L(ω+1) ≤ ν_C → LdEQhi`.** -/
theorem leRoadT (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LeThMoveT S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LdEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ldRoadS hU hO hL hV hN hlh (fun hν => leThMoveS_of_T (hth hν)) hhi

/-- **Satisfiability**: `LeThMoveT` follows from `MxThMoveW` and `MxEQth` (given `L(ω+1) ≤ ν_C`), so the hypotheses of
`leRoadT` follow from those of `Mx.mxRoad5`. -/
theorem leThMoveT_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : MxThMoveW S) (hE : MxEQth S) : LeThMoveT S :=
  leThMoveT_of_S (ldThMoveS_of_R (ldThMoveR_of hν hW hE))

end Googology.Trans.PoR.InaccPsi.R2.Le
