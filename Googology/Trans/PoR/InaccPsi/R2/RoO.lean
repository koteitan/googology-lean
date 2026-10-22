import Googology.Trans.PoR.InaccPsi.R2.RoLim

/-!
# The shifts `X = Ω₂·α`, `1 ≤ α < ω^ω`: one induction over the shifts, the atoms below `ψ_{Ω₂}(Ω₂^{Ω₂·ω^ω})`
move, and the road with the atoms in `[ψ_{Ω₂}(Ω₂^{Ω₂·ω^ω}), θ]`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`F_α = ψ_{Ω₂}(W^{Ω₂·α})`.

* `roSmall_mem`, `roSmall_cl` (the ordinals below `ω^ω` are in every `Cl(a, b)` and are codes `Le.LeCl`);
* `roShO` (the family `{(Ω₂·α, Ω₁·α) | 1 ≤ α < ω^ω}`), `roSh_o` (shifts), `roShO_B` (fixed by `B_n`);
* `roTopO` (**`RoTop (Ω₂·α) (Ω₁·α) 0` for every `1 ≤ α < ω^ω`**, ONE induction on `α`: `Rn.rnTopW` at `α = 1`,
  the pull-back `Ro.roTopW` at successors, the limit shift `Ro.roTopLimSh` at limits), `roShO_sh`;
* `roClsO` (**the atoms below `T_{Ω₂·α}(β)` are own**, the same induction with `Ro.roClsW`, `Ro.roClsLimSh`);
* `roRepO`, `roReadO` (**`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`; e.g.
  `Θ_λ(F_α) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·α})`, `roTh_o0`), `roAtMoveO` (**every atom `ψ_{Ω₂}(0) < s ≤ F_α` moves**);
* `RoAtMove4 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `s ≤ θ` above every `F_α`, `α < ω^ω`;
  `roAtMove2_of4` (**`RoAtMove4` gives `Rn.RnAtMove2`**), `roAtMove4_of`, `roRoadF` (**the road**), `roRoadF_hyps`.

No new axiom.  New definitions: `roShO`, the hypothesis name `RoAtMove4`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-! ## The ordinals below `ω^ω` -/

theorem roSmall_log {α : Ordinal.{0}} (hα : α < ω ^ ω) (h0 : α ≠ 0) : log ω α < α := by
  have hlead : ω ^ log ω α ≤ α := opow_log_le_self ω h0
  rcases lt_or_ge α ω with h | h
  · have h1 : log ω α < 1 := by
      have : ω ^ log ω α < ω ^ (1 : Ordinal.{0}) := by rw [opow_one]; exact hlead.trans_lt h
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rw [Order.lt_one_iff] at h1
    rw [h1]; exact pos_iff_ne_zero.2 h0
  · exact ((opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hα)).trans_le h

theorem roSmall_mem : ∀ α : Ordinal.{0}, α < ω ^ ω → ∀ a b, α ∈ S.CSet a b := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα a b
  rcases eq_or_ne α 0 with rfl | h0
  · exact CSet.zero_mem a b
  have hlog := roSmall_log hα h0
  have hlead : ω ^ log ω α ≤ α := opow_log_le_self ω h0
  have hop : ω ^ log ω α ∈ S.CSet a b := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (IH _ hlog (hlog.trans hα) a b)
    rwa [veblen_zero_apply] at this
  rw [← Ordinal.add_sub_cancel_of_le hlead]
  exact CSet.add_mem hop (IH _ (leRest_lt h0) ((leRest_lt h0).trans hα) a b)

theorem roSmall_cl {κ Q : Ordinal.{0}} (hQ : 0 < Q) : ∀ α : Ordinal.{0}, α < ω ^ ω → LeCl κ Q α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  rcases eq_or_ne α 0 with rfl | h0
  · exact LeCl.zero hQ
  have hlog := roSmall_log hα h0
  have hlead : ω ^ log ω α ≤ α := opow_log_le_self ω h0
  rw [← Ordinal.add_sub_cancel_of_le hlead]
  exact LeCl.add (LeCl.opow hQ (IH _ hlog (hlog.trans hα))) (IH _ (leRest_lt h0) ((leRest_lt h0).trans hα))

theorem roOO_lt_SC {G : Ordinal.{0}} (hG : SC G) : (ω ^ ω : Ordinal.{0}) < G :=
  ldOpow_lt_SC hG (Lw.lw_omega_lt_SC hG)

theorem roOO_lt_Om1 : (ω ^ ω : Ordinal.{0}) < Om 1 := roOO_lt_SC Ph.ph_SC_Om1

theorem roSucc_lt_OO {α : Ordinal.{0}} (hα : α < ω ^ ω) : α + 1 < ω ^ ω :=
  isPrincipal_add_omega0_opow ω hα (one_lt_omega0.trans_le (by
    have := opow_le_opow_right (a := ω) omega0_pos (one_lt_omega0 : (1 : Ordinal.{0}) < ω).le
    rwa [opow_one] at this))

/-! ## The family `{(Ω₂·α, Ω₁·α) | 1 ≤ α < ω^ω}` -/

/-- **The family of shifts `{(Ω₂·α, Ω₁·α) | 1 ≤ α < ω^ω}`.** -/
def roShO (X Xh : Ordinal.{0}) : Prop :=
  ∃ α : Ordinal.{0}, 1 ≤ α ∧ α < ω ^ ω ∧ X = Om (1 + 1) * α ∧ Xh = Om 1 * α

theorem roMulK_mem {κ α : Ordinal.{0}} (hκ : SC κ) (hκC : ∀ a b, κ ∈ S.CSet a b) (hα : α < ω ^ ω) (a b : Ordinal.{0}) :
    κ * α ∈ S.CSet a b := by
  have e : κ * α = ω ^ κ * α := by rw [gg_SC_eps hκ]
  rw [e]; exact leMulOp_mem (hκC a b) α (roSmall_mem α hα a b)

/-- **`(Ω₂·α, Ω₁·α)` is a shift** for `1 ≤ α < ω^ω`. -/
theorem roSh_o {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) : RoSh S (Om (1 + 1) * α) (Om 1 * α) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hα0 : α ≠ 0 := (Order.one_le_iff_ne_zero.1 h1)
  refine ⟨mul_ne_zero ldOm2_SC.1.ne' hα0, dvd_mul_right _ _,
    roMulK_mem ldOm2_SC mxOm2_mem hα, roMulK_mem Ph.ph_SC_Om1 (fun a b => CSet.Om_mem (CSet.one_mem a b)) hα,
    ?_, ?_, fun Q hQ => LeCl.mulK hQ ldOm2_SC α (roSmall_cl hQ.1 α hα),
    fun Q hQ => LeCl.mulK hQ Ph.ph_SC_Om1 α (roSmall_cl hQ.1 α hα)⟩
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG3 hWG3 ((roSucc_lt_OO hα).trans (roOO_lt_SC hG3))
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG1 hΩG1 ((roSucc_lt_OO hα).trans (roOO_lt_SC hG1))

/-- `B_n(κ·(κ·α)) = κ·(κ·α)` for `κ ∈ {Ω₁, Ω₂}` fixed by `B_n`, `α < ω^ω`. -/
theorem roB_KKa {n : ℕ} {κ α : Ordinal.{0}} (hκ : SC κ) (hOOκ : (ω ^ ω : Ordinal.{0}) < κ)
    (hDκ : MvD S κ) (hBκ : Bc.bcB S n κ = κ) (hα : α < ω ^ ω) :
    MvD S (κ * (κ * α)) ∧ Bc.bcB S n (κ * (κ * α)) = κ * (κ * α) := by
  have hLw : (ω ^ ω : Ordinal.{0}) < Nc.ncL S ω := roOO_lt_SC (Lw.lw_L_SC S ω)
  have hc : (ω ^ ω : Ordinal.{0}) < Bc.bcC S n := roOO_lt_SC (Lw.lw_L_SC S _)
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDκ hDκ
  rw [hBκ] at hBK
  have e : κ * (κ * α) = ω ^ (κ + κ) * α := by rw [← mul_assoc, opow_add, gg_SC_eps hκ]
  have h := leB_mulOp2 (n := n) hDK (fun z => z < ω ^ ω) (fun z hz => mvD_of_lt (hz.trans hLw))
    (fun z hz _ => ⟨(log_le_self ω z).trans_lt hz, (Ordinal.sub_le_self _ _).trans_lt hz⟩)
    (fun z hz => (hz.trans hOOκ).trans_le le_self_add) α hα
  rw [hBK, Bc.bcB_fix' S n α (hα.trans hc)] at h
  rw [e]; exact h

/-- **The family is fixed by every `B_n`.** -/
theorem roShO_B : ∀ X Xh, roShO X Xh → RoShB S X Xh := by
  rintro X Xh ⟨α, h1, hα, rfl, rfl⟩
  have hα0 : α ≠ 0 := (Order.one_le_iff_ne_zero.1 h1)
  refine ⟨mul_ne_zero (Om_pos one_ne_zero).ne' hα0, fun n => ?_⟩
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨h1, h2⟩ := roB_KKa (n := n) ldOm2_SC (roOO_lt_Om1.trans gg_Om1_lt_Om2) hD2 hB2 hα
  obtain ⟨h3, h4⟩ := roB_KKa (n := n) Ph.ph_SC_Om1 roOO_lt_Om1 hD1 hB1 hα
  exact ⟨h1, h2, h3, h4⟩

theorem roShO_X {X Xh : Ordinal.{0}} (h : roShO X Xh) : X + Om (1 + 1) < Om ω := by
  obtain ⟨α, -, hα, rfl, rfl⟩ := h
  rw [← mul_add_one]
  exact ldMul_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW ((roSucc_lt_OO hα).trans (roOO_lt_SC (SC_Om omega0_ne_zero)))

theorem roShO_mem {X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh', roShO X Xh') (a b : Ordinal.{0}) :
    X ∈ S.CSet a b := by
  rcases h with rfl | ⟨Xh', α, -, hα, rfl, -⟩
  · exact CSet.zero_mem _ _
  · exact roMulK_mem ldOm2_SC mxOm2_mem hα a b

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`RoTop (Ω₂·α) (Ω₁·α) 0` for every `1 ≤ α < ω^ω`** (one induction on `α`). -/
theorem roTopO : ∀ α : Ordinal.{0}, 1 ≤ α → α < ω ^ ω → RoTop S l (Om (1 + 1) * α) (Om 1 * α) 0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro h1 hα
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨α0, hα0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hα0
    subst hα0
    rcases eq_or_ne α0 0 with rfl | h00
    · have h := roTop_one (S := S) hl hX
      rw [Nat.cast_one] at h
      rwa [zero_add]
    · have hα0' : α0 < ω ^ ω := (lt_add_one α0).trans hα
      have hs := roSh_o (S := S) (Order.one_le_iff_ne_zero.2 h00) hα0'
      have h := roTopW hs hl hX (roTopE hs hl hX (IH α0 (lt_add_one α0) (Order.one_le_iff_ne_zero.2 h00) hα0'))
      rwa [← mul_add_one, ← mul_add_one] at h
  · refine roTopLimSh hl hX (roSh_o h1 hα) (fun x _ hx => ?_) (fun z hz => ?_)
    · have hq : x / Om (1 + 1) < α := (Ordinal.lt_mul_iff_div_lt hW0).1 hx
      have hq1 := hlim.succ_lt hq
      refine ⟨Om (1 + 1) * (x / Om (1 + 1) + 1), Om 1 * (x / Om (1 + 1) + 1),
        mul_le_mul_right hq1.le _, ?_, (mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 hq1,
        roMulK_mem Ph.ph_SC_Om1 (fun a b => CSet.Om_mem (CSet.one_mem a b)) (hq1.trans hα),
        IH _ hq1 le_add_self (hq1.trans hα)⟩
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0
    · have hq : z / Om 1 < α := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hz
      have hq1 := hlim.succ_lt hq
      refine ⟨Om (1 + 1) * (z / Om 1 + 1), Om 1 * (z / Om 1 + 1),
        (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hq1, ?_, roMulK_mem ldOm2_SC mxOm2_mem (hq1.trans hα),
        IH _ hq1 le_add_self (hq1.trans hα)⟩
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add z hΩ0

theorem roShO_sh : ∀ X Xh, roShO X Xh → RoSh S X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e := by
  rintro X Xh ⟨α, h1, hα, rfl, rfl⟩
  exact ⟨roSh_o h1 hα, roTopE (roSh_o h1 hα) hl hX (roTopO hl hX α h1 hα)⟩

/-- **The atoms below `T_{Ω₂·α}(β)` are own** for every `1 ≤ α < ω^ω`. -/
theorem roClsO : ∀ α : Ordinal.{0}, 1 ≤ α → α < ω ^ ω → ∀ β, RoBaseE S l (Om (1 + 1) * α) 0 β →
    RoClsAt S l roShO (Om (1 + 1) * α) 0 β := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro h1 hα
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨α0, hα0⟩ | hlim
  · subst h0; exact absurd h1 (by simp)
  · rw [succ_eq_add_one] at hα0
    subst hα0
    rcases eq_or_ne α0 0 with rfl | h00
    · intro β hb
      rw [zero_add] at hb ⊢
      have hb1 : RoBaseE S l (Om (1 + 1) * ((1 : ℕ) : Ordinal.{0})) 0 β := by rwa [Nat.cast_one]
      have h := roCls_one (Sh := roShO) hl hX hb1
      rwa [Nat.cast_one] at h
    · have hα0' : α0 < ω ^ ω := (lt_add_one α0).trans hα
      have hsh : roShO (Om (1 + 1) * α0) (Om 1 * α0) := ⟨α0, Order.one_le_iff_ne_zero.2 h00, hα0', rfl, rfl⟩
      have h := roClsW hl hX (roShO_sh hl hX) hsh
        (roClsE hl hX (roShO_sh hl hX) hsh (IH α0 (lt_add_one α0) (Order.one_le_iff_ne_zero.2 h00) hα0'))
      rwa [← mul_add_one] at h
  · refine roClsLimSh hl hX (roShO_sh hl hX) (fun x _ hx => ?_)
    have hq : x / Om (1 + 1) < α := (Ordinal.lt_mul_iff_div_lt hW0).1 hx
    have hq1 := hlim.succ_lt hq
    refine ⟨Om (1 + 1) * (x / Om (1 + 1) + 1), Om 1 * (x / Om (1 + 1) + 1),
      ⟨_, le_add_self, hq1.trans hα, rfl, rfl⟩, ?_, ?_, IH _ hq1 le_add_self (hq1.trans hα)⟩
    · rw [← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hq1) _
    · rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0

/-- **Every atom `s ≤ F_α` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`.** -/
theorem roRepO {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hsα : s ≤ S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, roShO X Xh) ∧ RoOwn S l roShO X e 0 c v ∧
      RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  have hsh : roShO (Om (1 + 1) * α) (Om 1 * α) := ⟨α, h1, hα, rfl, rfl⟩
  have hαW : Om (1 + 1) * α < Om ω := (lt_add_of_pos_right _ ldOm2_SC.1).trans (roShO_X hsh)
  rcases hsα.lt_or_eq with hlt | rfl
  · have hb : RoBaseE S l (Om (1 + 1) * α) 0 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, add_zero]; exact (roWe_lt_OmW hαW).trans_le le_self_add
      · obtain rfl : e' = 0 := le_antisymm h' zero_le
        exact (SC_psi (InR_Om_succ 1) _).1
    have hlt' : s < leTe S (Om (1 + 1) * α + 0) 0 := by
      unfold leTe; rwa [add_zero, zero_add]
    rcases roClsO hl hX α h1 hα 0 hb s hs hlt' with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
    · exact Or.inl h
    · rw [zero_add] at e1
      exact Or.inr ⟨X', e', c, v, roOwn_sh hown, hown, hbo, e1⟩
  · obtain ⟨hρSC, -⟩ := leRho hl hX
    have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
    have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
    have h1T : (1 : Ordinal.{0}) < leTe S (Om (1 + 1) * α + 0 + 1) 0 := roOne_lt_Te _ _
    have hXW : Om (1 + 1) ≤ Om (1 + 1) * α := le_mul_left _ (Order.one_le_iff_pos.1 h1)
    have hown := roTop_own (l := l) (Sh := roShO) hsh hXW hc0 hc1 one_ne_zero h1T
    have hb : RoBaseE S l (Om (1 + 1) * α) (0 + 1) 0 := by
      refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
      · rw [zero_add, zero_add]
        refine (roWe_lt_OmW ((Om_isPrincipal omega0_ne_zero) hαW ?_)).trans_le le_self_add
        exact one_lt_omega0.trans (Lw.lw_omega_lt_SC (SC_Om omega0_ne_zero))
      · rw [zero_add] at h' ⊢
        exact (h'.trans_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1))).trans
          (psiS_bounds (S := S) _ 1).1
    refine Or.inr ⟨_, _, _, _, Or.inr ⟨_, hsh⟩, hown, hb, ?_⟩
    rw [add_zero, mul_one, add_zero]

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0`. -/
theorem roReadO {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RoOwn S l roShO X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, -, hv⟩ := roOwnRead hl hX (roShO_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hv⟩

/-- **`Θ_λ(F_α) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁·α})`** for every `1 ≤ α < ω^ω`. -/
theorem roTh_o0 {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (Om 1 * α)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hsh : roShO (Om (1 + 1) * α) (Om 1 * α) := ⟨α, h1, hα, rfl, rfl⟩
  have hαW : Om (1 + 1) * α < Om ω := (lt_add_of_pos_right _ ldOm2_SC.1).trans (roShO_X hsh)
  have hb : RoBaseE S l (Om (1 + 1) * α) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW hαW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have h := roTopO hl hX α h1 hα 0 (A + 1) hb hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

/-- `B_n(F_α) = F_α`. -/
theorem roB_Fa {n : ℕ} {α : Ordinal.{0}} (h1 : 1 ≤ α) (hα : α < ω ^ ω) :
    MvD S (S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))) = S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1)) := by
  obtain ⟨-, hB⟩ := roShO_B (S := S) _ _ (⟨α, h1, hα, rfl, rfl⟩ : roShO (Om (1 + 1) * α) (Om 1 * α))
  obtain ⟨hDX, hBX, -, -⟩ := hB n
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDX
  rw [hBX] at hBW
  have hown : leWe (Om (1 + 1) * α) ∈ S.CSet (leWe (Om (1 + 1) * α))
      (S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))) :=
    leWe_mem (roMulK_mem ldOm2_SC mxOm2_mem hα _ _)
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDW hown
  refine ⟨hDT, ?_⟩
  unfold leWe
  rw [hBT, hBW]

theorem roFa_lt_th {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1)) < ConjT.th S := by
  have hαW : Om (1 + 1) * α < Om ω :=
    ldMul_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW (hα.trans (roOO_lt_SC (SC_Om omega0_ne_zero)))
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (roWe_lt_OmW hαW) (leWe_mem (roMulK_mem ldOm2_SC mxOm2_mem hα _ _))

/-- **Every atom `ψ_{Ω₂}(0) < s ≤ F_α` moves** once the codes below it move (`1 ≤ α < ω^ω`). -/
theorem roAtMoveO {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α < ω ^ ω) (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hs0 : S.psi 0 (Om (1 + 1)) < s) (hsα : s ≤ S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  rcases roRepO hl hX hα1 hα s hs hsα with hle | ⟨X, e, c, v, hXs, hown, hb, rfl⟩
  · exact absurd hs0 (not_lt.2 hle)
  obtain ⟨e1, own1, hv⟩ := roReadO hl hX hA hρ hown hb
  obtain ⟨hDe, hDc, -, -, hDv, hown'⟩ := roDigMove (n := n) (l' := l') hl hX (roShO_sh hl hX) roShO_B hown hb
    hD0 (fun x hx hxs => by
      obtain ⟨a, b, -, d, e⟩ := IH x hx (by rwa [zero_add] at hxs)
      exact ⟨a, b, d, e⟩)
  rw [Bc.bcB_zero] at hown'
  have hXs' : X = 0 ∨ ∃ Xh, RoSh S X Xh := by
    rcases hXs with h0 | ⟨Xh, β, hβ1, hβ, rfl, rfl⟩
    · exact Or.inl h0
    · exact Or.inr ⟨_, roSh_o hβ1 hβ⟩
  have hXW : X + Om (1 + 1) < Om ω := by
    rcases hXs with rfl | ⟨Xh, h⟩
    · rw [zero_add]; exact ldOm2_lt_OmW
    · exact roShO_X h
  have hXB : X = 0 ∨ ∃ Xh, RoShB S X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, roShO_B _ _ h⟩
  have hec := roOwn_code hl hX hown
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) 0 := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left 0).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := roB_WeW (S := S) (n := n) hXB
  obtain ⟨hD0W, hB0W⟩ := mvB_add (k := n) hD0 hDWW
  rw [Bc.bcB_zero, hBWW] at hB0W
  have hTown : 0 + leWe (X + Om (1 + 1)) ∈ S.CSet (0 + leWe (X + Om (1 + 1)))
      (S.psi (0 + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (CSet.zero_mem _ _) (leWe_mem (CSet.add_mem (roShO_mem hXs _ _) (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hD0W hTown
  rw [hB0W] at hBT
  have hBeT : Bc.bcB S n e < leTe S (X + Om (1 + 1)) 0 := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' X (Bc.bcB S n e) 0 := roBase0 hXs' hXW hBeT
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  obtain ⟨e1', -, -, -⟩ := roOwnRead hl' hX' (roShO_sh hl' hX') hown' (A' + 1) hb' hA'1 (ldBlk_zero hA' hρ')
  rw [zero_add] at e1'
  have hcown := roOwn_own hl hX (roShO_sh hl hX) hown hb
  rw [zero_add] at hcown
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hcown
  obtain ⟨hBH, hBA⟩ := roOwn_mem hl' hX' (roShO_sh hl' hX') hown' hb'
  rw [zero_add] at hBH hBA
  obtain ⟨hDF, hBF⟩ := roB_Fa (S := S) (n := n) hα1 hα
  have hvθ : 1 + v ≤ ConjT.th S :=
    (hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) hv).le.trans rnG_le_th
  have hownd : A + (1 + v) ∈ S.CSet (A + (1 + v)) (S.psi (A + (1 + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  obtain ⟨hD1v, hB1v⟩ := mvB_add (k := n) hD1 hDv
  rw [mwB_one] at hB1v
  refine ⟨hDs, by rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩, ?_, by rw [e1, add_assoc]; exact hbX _ hvθ, ?_⟩
  · have h := leB_le (n := n) hDs hDF hsα
    rw [hBF] at h
    exact (h.trans_lt (roFa_lt_th hα)).trans ljTh_lt_ThP
  · rw [hBs, e1', e1, add_assoc A, hBψ _ hD1v hownd hvθ, hB1v, add_assoc]

/-- **`LjAtMove` for the atoms `s ≤ θ` above every `F_α = ψ_{Ω₂}(Ω₂^{Ω₂·α})`, `1 ≤ α < ω^ω`.** -/
def RoAtMove4 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l,
      (∀ α : Ordinal.{0}, 1 ≤ α → α < ω ^ ω → S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1)) < s) →
      s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RoAtMove4` gives `RnAtMove2`.** -/
theorem roAtMove2_of4 (h : RoAtMove4 S) : RnAtMove2 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hs1 hsθ IH
  by_cases hex : ∃ α : Ordinal.{0}, 1 ≤ α ∧ α < ω ^ ω ∧
      s ≤ S.psi (leWe (Om (1 + 1) * α)) (Om (1 + 1))
  · obtain ⟨α, hα1, hα, hsα⟩ := hex
    have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) zero_le).1 hs1
    exact roAtMoveO hR h1 hr hl' hB hα1 hα s hs hs0 hsα IH
  · push Not at hex
    exact h n l l' hR h1 hr hl' hB hm hF hK s hs (fun α hα1 hα => hex α hα1 hα) hsθ IH

/-- **`RnAtMove2` gives `RoAtMove4`.** -/
theorem roAtMove4_of (h : RnAtMove2 S) : RoAtMove4 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsα hsθ IH
  have h2 : (2 : Ordinal.{0}) < ω ^ ω :=
    (natCast_lt_omega0 2).trans_le (by
      have := opow_le_opow_right (a := ω) omega0_pos (one_lt_omega0 : (1 : Ordinal.{0}) < ω).le
      rwa [opow_one] at this)
  have hF2 := hsα 2 one_le_two h2
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num
  have hT := (roT1_lt_F2 (S := S))
  rw [e2] at hT
  exact h n l l' hR h1 hr hl' hB hm hF hK s hs (hT.trans hF2) hsθ IH

/-- **The road with `RoAtMove4`, `RnThMoveM` and `RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem roRoadF (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RoAtMove4 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rnRoadD hU hO hL hV hN hlh (fun hν => roAtMove2_of4 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `roRoadF` follows from that of `Rn.rnRoadD`. -/
theorem roRoadF_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RnAtMove2 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RoAtMove4 S :=
  fun hν => roAtMove4_of (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Ro
