import Googology.Trans.PoR.InaccPsi.R2.SnCls

/-!
# The family `SnG` moves under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `Θ̂ = Sg.sgThH S λ`,
`Θ̂' = Sg.sgThH S λ'`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`, `ε = ε_{Ω₂+1}`.

* `snB_lev` (**`B_n(Ω₂·(X₀ + W^E·y)) = Ω₂·(X₀_B + W^{B_n E}·B_n y)`** whenever `B_n(Ω₂·E) = Ω₂·B_n E`, for `y` in a
  class closed under the Cantor decomposition; no bound `E < Ω₂`), `snB_levO` (the same for
  `Ω₁·(X̂₀ + Ω^a·b)`, `b < c_{n+1}`, whenever `B_n(Ω₁·a) = Ω₁·B_n a`);
* `snEE_B` (**`B_n(EE_j(X₀, β, E)) = EE_j(X₀_B, B_n β, B_n E)`** for an exponent `E` with `E ∈ Cl(0, T_E)`);
* `snG_B` (**every member `SnG β X X̂ E` whose codes below `ψ_{Ω₂}(β + W^X)` move gives the member
  `SnG' (B_n β) X_B X̂_B (B_n E)` at `λ'`, with `B_n(Ω₂·X) = Ω₂·X_B`, `B_n(Ω₁·X̂) = Ω₁·X̂_B`**; the exponent move
  and the transfer of the closure condition are `Sj.sjB_thH`), `snShG_B` (**the hypothesis `hShB` of
  `Rw.rwDigMove` for `snShG`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-- **`B_n(Ω₂·(X₀ + W^E·y)) = Ω₂·(X₀_B + W^{B_n E}·B_n y)`** when `B_n(Ω₂·E) = Ω₂·B_n E`. -/
theorem snB_lev {n : ℕ} {X0 X0B E : Ordinal.{0}} (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B)
    (hDE : MvD S (Om (1 + 1) * E)) (hBE : Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) {y : Ordinal.{0}} (hy : P y) :
    MvD S (Om (1 + 1) * (X0 + leWe E * y)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe E * y)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) * Bc.bcB S n y) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDE
  rw [hB2, hBE] at hBK
  obtain ⟨hDm, hBm⟩ := sjB_mulOp (n := n) hDK P hPD hPdec y hy
  have eK : ∀ z : Ordinal.{0}, Om (1 + 1) * leWe z = ω ^ (Om (1 + 1) + Om (1 + 1) * z) := fun z => by
    unfold leWe; rw [opow_add, gg_SC_eps ldOm2_SC]
  have e1 : ∀ Y z w : Ordinal.{0},
      Om (1 + 1) * (Y + leWe z * w) = Om (1 + 1) * Y + ω ^ (Om (1 + 1) + Om (1 + 1) * z) * w :=
    fun Y z w => by rw [mul_add, ← mul_assoc, eK]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDm
  rw [e1, e1]
  exact ⟨hDs, by rw [hBs, hBX0, hBm, hBK]⟩

/-- **`B_n(Ω₁·(X̂₀ + Ω^a·b)) = Ω₁·(X̂₀_B + Ω^{B_n a}·B_n b)`** when `B_n(Ω₁·a) = Ω₁·B_n a`, `b < c_{n+1}`. -/
theorem snB_levO {n : ℕ} {Xh0 Xh0B a b : Ordinal.{0}} (hDX0 : MvD S (Om 1 * Xh0))
    (hBX0 : Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B)
    (hDa : MvD S (Om 1 * a)) (hBa : Bc.bcB S n (Om 1 * a) = Om 1 * Bc.bcB S n a)
    (hb : b < Bc.bcC S (n + 1)) :
    MvD S (Om 1 * (Xh0 + leOe a * b)) ∧
      Bc.bcB S n (Om 1 * (Xh0 + leOe a * b)) = Om 1 * (Xh0B + leOe (Bc.bcB S n a) * Bc.bcB S n b) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDO hDa
  rw [hBO, hBa] at hBK
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDm, hBm⟩ := sjB_mulOp (n := n) hDK (fun x => x < Bc.bcC S (n + 1))
    (fun x hx => mvD_of_lt (hx.trans hLw))
    (fun x hx _ => ⟨(log_le_self ω x).trans_lt hx, (Ordinal.sub_le_self _ _).trans_lt hx⟩) b hb
  have eK : ∀ z : Ordinal.{0}, Om 1 * leOe z = ω ^ (Om 1 + Om 1 * z) := fun z => by
    unfold leOe; rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  have e1 : ∀ Y z w : Ordinal.{0}, Om 1 * (Y + leOe z * w) = Om 1 * Y + ω ^ (Om 1 + Om 1 * z) * w :=
    fun Y z w => by rw [mul_add, ← mul_assoc, eK]
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDm
  rw [e1, e1]
  exact ⟨hDs, by rw [hBs, hBX0, hBm, hBK]⟩

/-- **`B_n(EE_j(X₀, β, E)) = EE_j(X₀_B, B_n β, B_n E)`** for an exponent with `E ∈ Cl(0, T_E(β))`. -/
theorem snEE_B {n : ℕ} {X0 X0B β E : Ordinal.{0}} (hDβ : MvD S β) (hβo : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B)
    (hDE : MvD S (Om (1 + 1) * E)) (hBE : Bc.bcB S n (Om (1 + 1) * E) = Om (1 + 1) * Bc.bcB S n E)
    (hem : E ∈ S.CSet 0 (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)))) :
    ∀ j, MvD S (rvEE S X0 β E j) ∧ Bc.bcB S n (rvEE S X0 β E j) = rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j
  | 0 => mvB_Om1
  | j + 1 => by
    obtain ⟨hDy, hBy⟩ := snEE_B hDβ hβo hX0m hDX0 hBX0 hDE hBE hem j
    set y := rvEE S X0 β E j with hy_def
    obtain ⟨hQD, hQdec, -⟩ := rwPair_cls (S := S) (rvEE_SC j) (rvEE_lt_Om2 j) hDy
    obtain ⟨hDW1, hBW1⟩ := snB_lev (S := S) (n := n) hDX0 hBX0 hDE hBE (fun x => x = 0 ∨ x = y)
      hQD hQdec (Or.inr rfl)
    obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDW1
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    have hβown : ∀ d, d ≤ leWe (X0 + leWe (E + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
      fun d _ => CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo
    have hlt := scEE_lt_succ hβown hX0m hem j
    have hown : β + leWe (X0 + leWe E * y) ∈
        S.CSet (β + leWe (X0 + leWe E * y)) (S.psi (β + leWe (X0 + leWe E * y)) (Om (1 + 1))) := by
      refine CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo)
        (leWe_mem (CSet.add_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m)
          (leMulWe_mem (scEE_e_mem hem (rvEE_one_le j)) (CSet.of_lt hlt))))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hown
    refine ⟨hDT, ?_⟩
    show Bc.bcB S n (S.psi (β + ω ^ (Om (1 + 1) * (X0 + leWe E * y))) (Om (1 + 1))) =
      S.psi (Bc.bcB S n β + ω ^ (Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) *
        rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j))) (Om (1 + 1))
    rw [hBT, hBa, hBW, hBW1, ← hBy]

section Main

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **Every member of the family `SnG` moves** to a member at `λ'` over `B_n β`. -/
theorem snG_B {β X Xh E : Ordinal.{0}} (h : SnG S l β X Xh E) : MvD S β →
    β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ MvD S E ∧ ∃ XB XhB, SnG S l' (Bc.bcB S n β) XB XhB (Bc.bcB S n E) ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  -- the class of codes below a bound
  have hcls : ∀ (B : Ordinal.{0}),
      (∀ x, (GxCl (upsilon l) (ldAtR S l) x ∧ x < B ∧ x < Om (1 + 1)) → x ≠ 0 →
        (GxCl (upsilon l) (ldAtR S l) (log ω x) ∧ log ω x < B ∧ log ω x < Om (1 + 1)) ∧
        (GxCl (upsilon l) (ldAtR S l) (x - ω ^ log ω x) ∧ x - ω ^ log ω x < B ∧
          x - ω ^ log ω x < Om (1 + 1))) := fun B x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  -- one step: the term `W^E·ζ` over an offset `X₀ ↦ X₀_B`
  have hstep : ∀ {X0 Xh0 X0B Xh0B E ζ : Ordinal.{0}}, 1 ≤ E → E ∈ cdHull S l →
      E < veblen 1 (Om (1 + 1) + 1) → SnCL S E β X0 →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β E j) →
      MvD S β → β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))) →
      MvD S (Om (1 + 1) * X0) → Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B →
      MvD S (Om 1 * Xh0) → Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 ∧
      MvD S E ∧ 1 ≤ Bc.bcB S n E ∧ Bc.bcB S n E ∈ cdHull S l' ∧
      Bc.bcB S n E < veblen 1 (Om (1 + 1) + 1) ∧ SnCL S (Bc.bcB S n E) (Bc.bcB S n β) X0B ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n ζ) ∧ Bc.bcB S n ζ ≠ 0 ∧
      (∃ j, Bc.bcB S n ζ < rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j) ∧
      MvD S (Om (1 + 1) * (X0 + leWe E * ζ)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe E * ζ)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) * Bc.bcB S n ζ) ∧
      MvD S (Om 1 * (Xh0 + leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ)) ∧
      Bc.bcB S n (Om 1 * (Xh0 + leOe (sgThH S l E) * gxTh (upsilon l) (ldAtR S l) ζ)) =
        Om 1 * (Xh0B + leOe (sgThH S l' (Bc.bcB S n E)) * gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ζ)) := by
    intro X0 Xh0 X0B Xh0B E ζ h1 hEH hE hcl hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0 hDXh0 hBXh0 IH
    obtain ⟨j, hj⟩ := hj
    have hζ1 : 1 ≤ ζ := Order.one_le_iff_ne_zero.2 hζ0
    have hζown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) := rvEE_gt j ζ hj
    set T := S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) with hT_def
    have hTSC : SC T := SC_psi (InR_Om_succ 1) _
    have hTle : T ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2 (by
        calc leWe E = leWe E * 1 := (mul_one _).symm
          _ ≤ leWe E * ζ := leMulWe_mono hζ1))))).1
    have hET : LeCl (Om (1 + 1)) T E := hcl T hTSC le_rfl
    obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, -, hDΘ1, hBΘ1, hΘmove⟩ :=
      sjB_thH hl hX hl' hX' hTSC (fun x hx hxT => by
        obtain ⟨a, b, c, d⟩ := IH x hx (hxT.trans_le hTle); exact ⟨a, b, c, d⟩) E hEH hE hET
    obtain ⟨hDζ, hBζc, hΘζc, hΘζ⟩ := IH ζ hζ hζown
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hζ0)
      rw [gxTh_zero] at this; exact this.ne'
    have hBζ0 : Bc.bcB S n ζ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDζ).2 (pos_iff_ne_zero.2 hζ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    have hB1E : 1 ≤ Bc.bcB S n E := by have := leB_le (n := n) hD1 hDE h1; rwa [mwB_one] at this
    have hem : E ∈ S.CSet 0 T := sjCl_mem hET
    -- the class of codes below the top
    set PB : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
      x < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hPB_def
    have hPBD : ∀ x, PB x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
    have hPBdec := hcls (S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)))
    have hPζ : PB ζ := ⟨hζ, hζown, hj.trans (rvEE_lt_Om2 j)⟩
    have hP1 : PB 1 := ⟨GxCl.small (gg_one_lt_of_SC hρSC), (gg_one_lt_of_SC (SC_psi (InR_Om_succ 1) _)),
      gg_one_lt_of_SC ldOm2_SC⟩
    -- the level bounds move
    obtain ⟨hDEE, hBEE⟩ := snEE_B (S := S) (n := n) hDβ hβo hX0m hDX0 hBX0 hDE2 hBE2 hem j
    have hBlt := (mvB_lt_iff (k := n) hDζ hDEE).2 hj
    rw [hBEE] at hBlt
    obtain ⟨hDW, hBW⟩ := snB_lev (S := S) (n := n) hDX0 hBX0 hDE2 hBE2 PB hPBD hPBdec hPζ
    -- the closure condition moves
    obtain ⟨hDW1, hBW1⟩ := snB_lev (S := S) (n := n) hDX0 hBX0 hDE2 hBE2 PB hPBD hPBdec hP1
    rw [mul_one, mwB_one, mul_one] at hBW1
    rw [mul_one] at hDW1
    obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDW1
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDo
    have hTown : β + leWe (X0 + leWe E) ∈ S.CSet (β + leWe (X0 + leWe E)) T :=
      CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo)
        (leWe_mem (CSet.add_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m) (leWe_mem (sjCl_mem hET))))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hTown
    have hBTe : Bc.bcB S n T = S.psi (Bc.bcB S n β + leWe (X0B + leWe (Bc.bcB S n E))) (Om (1 + 1)) := by
      rw [hT_def]
      show Bc.bcB S n (S.psi (β + ω ^ (Om (1 + 1) * (X0 + leWe E))) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + ω ^ (Om (1 + 1) * (X0B + leWe (Bc.bcB S n E)))) (Om (1 + 1))
      rw [hBT, hBa, hBo, hBW1]
    have hclB : SnCL S (Bc.bcB S n E) (Bc.bcB S n β) X0B := fun Q hQ hQ' =>
      hBcl hDT Q hQ (by rw [hBTe]; exact hQ')
    -- the image moves
    obtain ⟨hDO, hBO⟩ := snB_levO (S := S) (n := n) hDXh0 hBXh0 hDΘ1 hBΘ1 hΘζc
    refine ⟨mul_ne_zero (leOe_pos _).ne' hΘ0, hDE, hB1E, hBEH, hBEε, hclB, hBζc, hBζ0, ⟨j, hBlt⟩,
      hDW, hBW, hDO, ?_⟩
    rw [hBO, hΘζ, hΘmove]
  intro hDβ hβo IH
  induction h with
  | @one E ζ h1 hEH hE hcl hζ hζ0 hj =>
    have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (β + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
    obtain ⟨hne, hDE, hB1, hBEH, hBEε, hBcl, hBc, hB0, hBj, hDW, hBW, hDO, hBO⟩ :=
      hstep (X0B := 0) (Xh0B := 0) h1 hEH hE hcl hζ hζ0 hj hDβ hβo hX0m (by rw [mul_zero]; exact hD0)
        (by rw [mul_zero, Bc.bcB_zero]) (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero]) (by
        intro x hx hxs; rw [zero_add] at hxs; exact IH x hx hxs)
    simp only [zero_add] at hDW hBW hDO hBO
    exact ⟨hne, hDE, _, _, SnG.one hB1 hBEH hBEε hBcl hBc hB0 hBj, hDW, hBW, hDO, hBO⟩
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hEH hE hcl hζ hζ0 hj ih =>
    have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
    obtain ⟨-, hDE0, X0B, Xh0B, hF0, hDX0, hBX0, hDXh0, hBXh0⟩ := ih (fun x hx hxs => IH x hx (hxs.trans_le hle0))
    have hX0m := (snG_sh hl hX h0).1.mem
    obtain ⟨hne, hDE, hB1, hBEH, hBEε, hBcl, hBc, hB0, hBj, hDW, hBW, hDO, hBO⟩ :=
      hstep h1 hEH hE hcl hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0 hDXh0 hBXh0 IH
    have hBEE : Bc.bcB S n E < Bc.bcB S n E0 := (mvB_lt_iff (k := n) hDE hDE0).2 hEE
    refine ⟨?_, hDE, _, _, SnG.add hF0 hB1 hBEE hBEH hBEε hBcl hBc hB0 hBj, hDW, hBW, hDO, hBO⟩
    intro h'
    exact hne (le_antisymm (h' ▸ le_add_self) zero_le)

/-- **The hypothesis `hShB` of `Rw.rwDigMove` for the family `snShG`.** -/
theorem snShG_B : ∀ b X Xh, snShG S l b X Xh → MvD S b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (b + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, snShG S l' (Bc.bcB S n b) XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  rintro b X Xh ⟨E, hE⟩ hDb hbo IH
  obtain ⟨hne, -, XB, XhB, hF, h3, h4, h5, h6⟩ := snG_B hl hX hl' hX' hE hDb hbo IH
  exact ⟨hne, XB, XhB, ⟨_, hF⟩, h3, h4, h5, h6⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sn
