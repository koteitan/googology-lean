import Googology.Trans.PoR.InaccPsi.R2.RwFCls

/-!
# The family `RwF` moves under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `EE_j(X₀, β, f) = Rv.rvEE S X₀ β f j`.

* `rwB_lev` (**`B_n(Ω₂·(X₀ + W^f·y)) = Ω₂·(X₀_B + W^{B_n f}·B_n y)`** for a countable `f < c_{n+1}` and `y` in a
  class closed under the Cantor decomposition), `rwB_levO` (**`B_n(Ω₁·(X̂₀ + Ω^f·z)) = Ω₁·(X̂₀_B + Ω^{B_n f}·B_n z)`**);
* `rwEE_B` (**`B_n(EE_j(X₀, β, f)) = EE_j(X₀_B, B_n β, B_n f)`** for an own base `β` in `MvD`);
* `rwF_B` (**every member `RwF β X X̂ f` whose codes below `ψ_{Ω₂}(β + W^X)` move gives the member
  `RwF' (B_n β) X_B X̂_B (B_n f)` at `λ'`, with `B_n(Ω₂·X) = Ω₂·X_B`, `B_n(Ω₁·X̂) = Ω₁·X̂_B`**), `rwShF_B` (the
  hypothesis `hShB` of `Rw.rwDigMove` for the family `rwShF`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

theorem rwC_SC (n : ℕ) : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _

/-- The class of the countable ordinals below `c_{n+1}`. -/
theorem rwSmall_cls {n : ℕ} :
    (∀ x, (x < Om 1 ∧ x < Bc.bcC S (n + 1)) → MvD S x) ∧
    (∀ x, (x < Om 1 ∧ x < Bc.bcC S (n + 1)) → x ≠ 0 →
      (log ω x < Om 1 ∧ log ω x < Bc.bcC S (n + 1)) ∧
      (x - ω ^ log ω x < Om 1 ∧ x - ω ^ log ω x < Bc.bcC S (n + 1))) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  exact ⟨fun x hx => mvD_of_lt (hx.2.trans hLw), fun x hx _ =>
    ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩⟩

/-- `1 + f` is countable and below `c_{n+1}`, and `B_n(1 + f) = 1 + B_n f`. -/
theorem rwOne_add {n : ℕ} {f : Ordinal.{0}} (hf1 : f < Om 1) (hfc : f < Bc.bcC S (n + 1)) :
    1 + f < Om 1 ∧ 1 + f < Bc.bcC S (n + 1) ∧ MvD S f ∧ Bc.bcB S n (1 + f) = 1 + Bc.bcB S n f := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hDf : MvD S f := mvD_of_lt (hfc.trans hLw)
  obtain ⟨-, hB⟩ := mvB_add (k := n) hD1 hDf
  refine ⟨Ph.ph_SC_Om1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)) hf1,
    (rwC_SC n).isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC (rwC_SC n))) hfc, hDf, ?_⟩
  rw [hB, mwB_one]

/-- **`B_n(Ω₂·(X₀ + W^f·y)) = Ω₂·(X₀_B + W^{B_n f}·B_n y)`.** -/
theorem rwB_lev {n : ℕ} {X0 X0B f : Ordinal.{0}} (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B) (hf1 : f < Om 1) (hfc : f < Bc.bcC S (n + 1))
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {y : Ordinal.{0}} (hy : P y) :
    MvD S (Om (1 + 1) * (X0 + leWe f * y)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe f * y)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n f) * Bc.bcB S n y) := by
  obtain ⟨h1f, h1fc, -, hB1f⟩ := rwOne_add (S := S) (n := n) hf1 hfc
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hQD, hQdec⟩ := rwSmall_cls (S := S) (n := n)
  obtain ⟨hDK, hBK⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1)) hQD hQdec
    (fun x hx => hx.1.trans gg_Om1_lt_Om2) (1 + f) ⟨h1f, h1fc⟩
  have hWK : Om (1 + 1 : Ordinal.{0}) ≤ Om (1 + 1) * (1 + f) :=
    le_mul_left _ (zero_lt_one.trans_le le_self_add)
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK P hPD hPdec (fun x hx => (hPW x hx).trans_le hWK) y hy
  have e1 : ∀ Y z w : Ordinal.{0}, Om (1 + 1) * (Y + leWe z * w) = Om (1 + 1) * Y + ω ^ (Om (1 + 1) * (1 + z)) * w :=
    fun Y z w => by rw [mul_add, ← mul_assoc, rvWe_mul]; rfl
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDm
  rw [e1, e1]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBX0, hBm, hBK, hB1f]

/-- **`B_n(Ω₁·(X̂₀ + Ω^f·z)) = Ω₁·(X̂₀_B + Ω^{B_n f}·B_n z)`.** -/
theorem rwB_levO {n : ℕ} {Xh0 Xh0B f z : Ordinal.{0}} (hDX0 : MvD S (Om 1 * Xh0))
    (hBX0 : Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B) (hf1 : f < Om 1) (hfc : f < Bc.bcC S (n + 1))
    (hz1 : z < Om 1) (hzc : z < Bc.bcC S (n + 1)) :
    MvD S (Om 1 * (Xh0 + leOe f * z)) ∧
      Bc.bcB S n (Om 1 * (Xh0 + leOe f * z)) = Om 1 * (Xh0B + leOe (Bc.bcB S n f) * Bc.bcB S n z) := by
  obtain ⟨h1f, h1fc, -, hB1f⟩ := rwOne_add (S := S) (n := n) hf1 hfc
  obtain ⟨hQD, hQdec⟩ := rwSmall_cls (S := S) (n := n)
  obtain ⟨hDK, hBK⟩ := leB_mulOm1 (S := S) (n := n) h1f h1fc
  have hΩK : Om (1 : Ordinal.{0}) ≤ Om 1 * (1 + f) := le_mul_left _ (zero_lt_one.trans_le le_self_add)
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1)) hQD hQdec
    (fun x hx => hx.1.trans_le hΩK) z ⟨hz1, hzc⟩
  have e1 : ∀ Y u w : Ordinal.{0}, Om 1 * (Y + leOe u * w) = Om 1 * Y + ω ^ (Om 1 * (1 + u)) * w :=
    fun Y u w => by rw [mul_add, ← mul_assoc, rvOe_mul]; rfl
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDm
  rw [e1, e1]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBX0, hBm, hBK, hB1f]

/-- **`B_n(EE_j(X₀, β, f)) = EE_j(X₀_B, B_n β, B_n f)`.** -/
theorem rwEE_B {n : ℕ} {X0 X0B β f : Ordinal.{0}} (hDβ : MvD S β) (hβo : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B) (hf1 : f < Om 1) (hfc : f < Bc.bcC S (n + 1)) :
    ∀ j, MvD S (rvEE S X0 β f j) ∧ Bc.bcB S n (rvEE S X0 β f j) = rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n f) j
  | 0 => mvB_Om1
  | j + 1 => by
    obtain ⟨hDy, hBy⟩ := rwEE_B hDβ hβo hX0m hDX0 hBX0 hf1 hfc j
    set y := rvEE S X0 β f j with hy_def
    have hySC : SC y := rvEE_SC j
    have hyE : ω ^ y = y := Low.opow_eq_self_of_SC hySC
    have hlog : log ω y = y := by
      conv_lhs => rw [← hyE]
      exact log_opow one_lt_omega0 y
    have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
    obtain ⟨hDE, hBE⟩ := rwB_lev (S := S) (n := n) hDX0 hBX0 hf1 hfc (fun x => x = 0 ∨ x = y)
      (fun x hx => by rcases hx with rfl | rfl; exacts [hD0, hDy])
      (fun x hx hx0 => by
        rcases hx with rfl | rfl
        · exact absurd rfl hx0
        · refine ⟨Or.inr hlog, Or.inl ?_⟩
          rw [hlog, hyE, Ordinal.sub_self])
      (fun x hx => by rcases hx with rfl | rfl; exacts [ldOm2_SC.1, rvEE_lt_Om2 j]) (Or.inr rfl)
    obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDE
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    have hβown : ∀ d, d ≤ leWe (X0 + leWe (f + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
      fun d _ => CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo
    have hlt := rvEE_lt_succ hβown hX0m hf1 j
    have hown : β + leWe (X0 + leWe f * y) ∈
        S.CSet (β + leWe (X0 + leWe f * y)) (S.psi (β + leWe (X0 + leWe f * y)) (Om (1 + 1))) := by
      refine CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo)
        (leWe_mem (CSet.add_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m)
          (leMulWe_mem (rvE_mem hf1) (CSet.of_lt hlt))))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hown
    refine ⟨hDT, ?_⟩
    show Bc.bcB S n (S.psi (β + ω ^ (Om (1 + 1) * (X0 + leWe f * y))) (Om (1 + 1))) =
      S.psi (Bc.bcB S n β + ω ^ (Om (1 + 1) * (X0B + leWe (Bc.bcB S n f) *
        rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n f) j))) (Om (1 + 1))
    rw [hBT, hBa, hBW, hBE, ← hBy]

section Main

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')
  (h2 : upsilon l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hl hX hl' hX' h2 hB

omit hl' hX' in
/-- **Every member of the family moves** to a member at `λ'` over `B_n β`. -/
theorem rwF_B {β X Xh f : Ordinal.{0}} (h : RwF S l β X Xh f) : MvD S β →
    β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, RwF S l' (Bc.bcB S n β) XB XhB (Bc.bcB S n f) ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hDρ : MvD S (upsilon l) := mvD_of_lt (h2.trans hLw)
  -- the level data
  have hlev : ∀ f, 1 ≤ f → f < upsilon l →
      f < Om 1 ∧ f < Bc.bcC S (n + 1) ∧ MvD S f ∧ 1 ≤ Bc.bcB S n f ∧ Bc.bcB S n f < upsilon l' := by
    intro f h1 hfρ
    have hDf : MvD S f := mvD_of_lt ((hfρ.trans h2).trans hLw)
    refine ⟨hfρ.trans hρ1, hfρ.trans h2, hDf, ?_, ?_⟩
    · have := leB_le (n := n) hD1 hDf h1; rwa [mwB_one] at this
    · have := (mvB_lt_iff (k := n) hDf hDρ).2 hfρ; rwa [hB] at this
  -- the class of codes for `rwB_lev`
  have hcls : ∀ (B : Ordinal.{0}), (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < B → MvD S x) →
      (∀ x, (GxCl (upsilon l) (ldAtR S l) x ∧ x < B ∧ x < Om (1 + 1)) → x ≠ 0 →
        (GxCl (upsilon l) (ldAtR S l) (log ω x) ∧ log ω x < B ∧ log ω x < Om (1 + 1)) ∧
        (GxCl (upsilon l) (ldAtR S l) (x - ω ^ log ω x) ∧ x - ω ^ log ω x < B ∧
          x - ω ^ log ω x < Om (1 + 1))) := fun B _ x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  -- one step: the term `W^f·ζ` over an offset `X₀ ↦ X₀_B`
  have hstep : ∀ {X0 Xh0 X0B Xh0B f ζ : Ordinal.{0}}, 1 ≤ f → f < upsilon l →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β f j) →
      MvD S β → β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))) →
      MvD S (Om (1 + 1) * X0) → Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B →
      MvD S (Om 1 * Xh0) → Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X0 + leWe f * ζ)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      leOe f * gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n ζ) ∧ Bc.bcB S n ζ ≠ 0 ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ζ) < Om 1 ∧
      (∃ j, Bc.bcB S n ζ < rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n f) j) ∧
      MvD S (Om (1 + 1) * (X0 + leWe f * ζ)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe f * ζ)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n f) * Bc.bcB S n ζ) ∧
      MvD S (Om 1 * (Xh0 + leOe f * gxTh (upsilon l) (ldAtR S l) ζ)) ∧
      Bc.bcB S n (Om 1 * (Xh0 + leOe f * gxTh (upsilon l) (ldAtR S l) ζ)) =
        Om 1 * (Xh0B + leOe (Bc.bcB S n f) * gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ζ)) := by
    intro X0 Xh0 X0B Xh0B f ζ h1 hfρ hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0 hDXh0 hBXh0 IH
    obtain ⟨hf1, hfc, hDf, -, -⟩ := hlev f h1 hfρ
    obtain ⟨j, hj⟩ := hj
    have hζown : ζ < S.psi (β + leWe (X0 + leWe f * ζ)) (Om (1 + 1)) := rvEE_gt j ζ hj
    obtain ⟨hDζ, hBζc, hΘζc, hΘζ⟩ := IH ζ hζ hζown
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hζ0)
      rw [gxTh_zero] at this; exact this.ne'
    have hBζ0 : Bc.bcB S n ζ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDζ).2 (pos_iff_ne_zero.2 hζ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    obtain ⟨hDEE, hBEE⟩ := rwEE_B (S := S) (n := n) hDβ hβo hX0m hDX0 hBX0 hf1 hfc j
    have hBlt := (mvB_lt_iff (k := n) hDζ hDEE).2 hj
    rw [hBEE] at hBlt
    -- the codes below `ψ_{Ω₂}(β + W^{X₀ + W^f ζ})` for `rwB_lev`
    obtain ⟨hDW, hBW⟩ := rwB_lev (S := S) (n := n) hDX0 hBX0 hf1 hfc
      (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (β + leWe (X0 + leWe f * ζ)) (Om (1 + 1)) ∧
        x < Om (1 + 1))
      (fun x hx => (IH x hx.1 hx.2.1).1) (hcls _ (fun x hx hxs => (IH x hx hxs).1))
      (fun x hx => hx.2.2) ⟨hζ, hζown, hj.trans (rvEE_lt_Om2 j)⟩
    obtain ⟨hDO, hBO⟩ := rwB_levO (S := S) (n := n) hDXh0 hBXh0 hf1 hfc (hΘζc.trans hc1) hΘζc
    refine ⟨mul_ne_zero (leOe_pos f).ne' hΘ0, hBζc, hBζ0, ?_, ⟨j, hBlt⟩, hDW, hBW, hDO, ?_⟩
    · rw [hΘζ]; exact (Bc.bcB_bound' S n _ hΘζc).trans (psi_lt Low.InR_Om_one _)
    · rw [hBO, hΘζ]
  intro hDβ hβo IH
  induction h with
  | @one f ζ h1 hfρ hζ hζ0 hΘ hj =>
    obtain ⟨-, -, -, hB1, hBρ⟩ := hlev f h1 hfρ
    have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (β + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
    obtain ⟨hne, hBc, hB0, hBΘ, hBj, hDW, hBW, hDO, hBO⟩ := hstep (X0B := 0) (Xh0B := 0) h1 hfρ hζ hζ0
      (by rwa [] at hj) hDβ hβo hX0m (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero])
      (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero]) (by
        intro x hx hxs; rw [zero_add] at hxs; exact IH x hx hxs)
    simp only [zero_add] at hDW hBW hDO hBO
    exact ⟨hne, _, _, RwF.one hB1 hBρ hBc hB0 hBΘ hBj, hDW, hBW, hDO, hBO⟩
  | @add X0 Xh0 f0 f ζ h0 h1 hff hζ hζ0 hΘ hj ih =>
    obtain ⟨-, hf0ρ, -, -, -, -⟩ := rwF_data hl hX h0
    have hfρ := hff.trans hf0ρ
    obtain ⟨-, -, -, hB1, hBρ⟩ := hlev f h1 hfρ
    obtain ⟨hf1, hfc, hDf, -, -⟩ := hlev f h1 hfρ
    obtain ⟨-, hf0c, hDf0, -, -⟩ := hlev f0 (h1.trans hff.le) hf0ρ
    have hBff : Bc.bcB S n f < Bc.bcB S n f0 := (mvB_lt_iff (k := n) hDf hDf0).2 hff
    have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe f * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
    obtain ⟨-, X0B, Xh0B, hF0, hDX0, hBX0, hDXh0, hBXh0⟩ := ih (fun x hx hxs => IH x hx (hxs.trans_le hle0))
    have hX0m := (rwF_sh hl hX h0).1.mem
    obtain ⟨hne, hBc, hB0, hBΘ, hBj, hDW, hBW, hDO, hBO⟩ := hstep h1 hfρ hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0
      hDXh0 hBXh0 IH
    refine ⟨?_, _, _, RwF.add hF0 hB1 hBff hBc hB0 hBΘ hBj, hDW, hBW, hDO, hBO⟩
    intro h'
    exact hne (le_antisymm (h' ▸ le_add_self) zero_le)

omit hl' hX' in
/-- **The hypothesis `hShB` of `Rw.rwDigMove` for the family `rwShF`.** -/
theorem rwShF_B : ∀ b X Xh, rwShF S l b X Xh → MvD S b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (b + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, rwShF S l' (Bc.bcB S n b) XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  rintro b X Xh ⟨f, hf⟩ hDb hbo IH
  obtain ⟨hne, XB, XhB, hF, h3, h4, h5, h6⟩ := rwF_B hl hX h2 hB hf hDb hbo IH
  exact ⟨hne, XB, XhB, ⟨_, hF⟩, h3, h4, h5, h6⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw
