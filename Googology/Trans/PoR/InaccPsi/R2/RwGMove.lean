import Googology.Trans.PoR.InaccPsi.R2.RwGCls

/-!
# The code-level family `RwG` moves under `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ' = gxTh ρ_{λ'} (ldAtR λ')`, `W^E = Ω₂^E`,
`Ω^x = Ω₁^x`, `EE_j(X₀, β, E) = Rv.rvEE S X₀ β E j`, `EX_j(X₀, β) = Rw.rwEX S X₀ β j`.

* `rwB_levC` (**`B_n(Ω₂·(X₀ + W^E·y)) = Ω₂·(X₀_B + W^{B_n E}·B_n y)`** for a code level `E` and `y` in classes closed
  under the Cantor decomposition);
* `rwEEc_B` (**`B_n(EE_j(X₀, β, E)) = EE_j(X₀_B, B_n β, B_n E)`**), `rwEX_B` (**`B_n(EX_j(X₀, β)) =
  EX_j(X₀_B, B_n β)`**);
* `rwG_B` (**every member `RwG β X X̂ E` whose codes below `ψ_{Ω₂}(β + W^X)` move gives the member
  `RwG' (B_n β) X_B X̂_B (B_n E)` at `λ'`, with `B_n(Ω₂·X) = Ω₂·X_B`, `B_n(Ω₁·X̂) = Ω₁·X̂_B`**), `rwShG_B` (the
  hypothesis `hShB` of `Rw.rwDigMove` for `rwShG`).

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

/-- **`B_n(Ω₂·(X₀ + W^E·y)) = Ω₂·(X₀_B + W^{B_n E}·B_n y)`** (`E ∈ P_E`, `y ∈ P_y`, both classes below `Ω₂`). -/
theorem rwB_levC {n : ℕ} {X0 X0B E : Ordinal.{0}} (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B)
    (PE : Ordinal.{0} → Prop) (hPED : ∀ x, PE x → MvD S x)
    (hPEdec : ∀ x, PE x → x ≠ 0 → PE (log ω x) ∧ PE (x - ω ^ log ω x)) (hPEW : ∀ x, PE x → x < Om (1 + 1))
    (hE : PE E)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {y : Ordinal.{0}} (hy : P y) :
    MvD S (Om (1 + 1) * (X0 + leWe E * y)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe E * y)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) * Bc.bcB S n y) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDE, hBE⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 PE hPED hPEdec hPEW E hE
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hD2 hDE
  rw [hB2, hBE] at hBK
  have eK : ∀ z : Ordinal.{0}, Om (1 + 1) * (1 + z) = Om (1 + 1) + Om (1 + 1) * z := fun z => by
    rw [mul_add, mul_one]
  have hWK : Om (1 + 1 : Ordinal.{0}) ≤ Om (1 + 1) + Om (1 + 1) * E := le_self_add
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK P hPD hPdec (fun x hx => (hPW x hx).trans_le hWK) y hy
  have e1 : ∀ Y z w : Ordinal.{0},
      Om (1 + 1) * (Y + leWe z * w) = Om (1 + 1) * Y + ω ^ (Om (1 + 1) + Om (1 + 1) * z) * w :=
    fun Y z w => by rw [mul_add, ← mul_assoc, rvWe_mul, ← eK]; rfl
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDm
  rw [e1, e1]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBX0, hBm, hBK]

/-- The class `{0, y}` of an `ε`-number `y < Ω₂` in `MvD`. -/
theorem rwPair_cls {y : Ordinal.{0}} (hySC : SC y) (hyW : y < Om (1 + 1)) (hDy : MvD S y) :
    (∀ x, (x = 0 ∨ x = y) → MvD S x) ∧
    (∀ x, (x = 0 ∨ x = y) → x ≠ 0 → (log ω x = 0 ∨ log ω x = y) ∧ (x - ω ^ log ω x = 0 ∨ x - ω ^ log ω x = y)) ∧
    (∀ x, (x = 0 ∨ x = y) → x < Om (1 + 1)) := by
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hyE : ω ^ y = y := Low.opow_eq_self_of_SC hySC
  have hlog : log ω y = y := by
    conv_lhs => rw [← hyE]
    exact log_opow one_lt_omega0 y
  refine ⟨fun x hx => by rcases hx with rfl | rfl; exacts [hD0, hDy], fun x hx hx0 => ?_,
    fun x hx => by rcases hx with rfl | rfl; exacts [ldOm2_SC.1, hyW]⟩
  rcases hx with rfl | rfl
  · exact absurd rfl hx0
  · exact ⟨Or.inr hlog, Or.inl (by rw [hlog, hyE, Ordinal.sub_self])⟩

/-- **`B_n(EE_j(X₀, β, E)) = EE_j(X₀_B, B_n β, B_n E)`** for an own code level `E` in a class `P_E`. -/
theorem rwEEc_B {n : ℕ} {X0 X0B β E : Ordinal.{0}} (hDβ : MvD S β) (hβo : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B)
    (heo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)))
    (PE : Ordinal.{0} → Prop) (hPED : ∀ x, PE x → MvD S x)
    (hPEdec : ∀ x, PE x → x ≠ 0 → PE (log ω x) ∧ PE (x - ω ^ log ω x)) (hPEW : ∀ x, PE x → x < Om (1 + 1))
    (hE : PE E) :
    ∀ j, MvD S (rvEE S X0 β E j) ∧ Bc.bcB S n (rvEE S X0 β E j) = rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j
  | 0 => mvB_Om1
  | j + 1 => by
    obtain ⟨hDy, hBy⟩ := rwEEc_B hDβ hβo hX0m hDX0 hBX0 heo PE hPED hPEdec hPEW hE j
    set y := rvEE S X0 β E j with hy_def
    obtain ⟨hQD, hQdec, hQW⟩ := rwPair_cls (S := S) (rvEE_SC j) (rvEE_lt_Om2 j) hDy
    obtain ⟨hDE, hBE⟩ := rwB_levC (S := S) (n := n) hDX0 hBX0 PE hPED hPEdec hPEW hE (fun x => x = 0 ∨ x = y)
      hQD hQdec hQW (Or.inr rfl)
    obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDE
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    have hβown : ∀ d, d ≤ leWe (X0 + leWe (E + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
      fun d _ => CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo
    have hlt := rwEEc_lt_succ hβown hX0m heo j
    have hown : β + leWe (X0 + leWe E * y) ∈
        S.CSet (β + leWe (X0 + leWe E * y)) (S.psi (β + leWe (X0 + leWe E * y)) (Om (1 + 1))) := by
      refine CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo)
        (leWe_mem (CSet.add_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m)
          (leMulWe_mem (CSet.of_lt (rwEEc_e_lt heo (rvEE_one_le j))) (CSet.of_lt hlt))))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hown
    refine ⟨hDT, ?_⟩
    show Bc.bcB S n (S.psi (β + ω ^ (Om (1 + 1) * (X0 + leWe E * y))) (Om (1 + 1))) =
      S.psi (Bc.bcB S n β + ω ^ (Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) *
        rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j))) (Om (1 + 1))
    rw [hBT, hBa, hBW, hBE, ← hBy]

/-- **`B_n(EX_j(X₀, β)) = EX_j(X₀_B, B_n β)`.** -/
theorem rwEX_B {n : ℕ} {X0 X0B β : Ordinal.{0}} (hDβ : MvD S β) (hβo : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1)))) (hDX0 : MvD S (Om (1 + 1) * X0))
    (hBX0 : Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B) :
    ∀ j, MvD S (rwEX S X0 β j) ∧ Bc.bcB S n (rwEX S X0 β j) = rwEX S X0B (Bc.bcB S n β) j
  | 0 => mvB_Om1
  | j + 1 => by
    obtain ⟨hDy, hBy⟩ := rwEX_B hDβ hβo hX0m hDX0 hBX0 j
    set y := rwEX S X0 β j with hy_def
    have hySC : SC y := rwEX_SC j
    obtain ⟨hQD, hQdec, hQW⟩ := rwPair_cls (S := S) hySC (rwEX_lt_Om2 j) hDy
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    obtain ⟨hDK, hBK⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 (fun x => x = 0 ∨ x = y) hQD hQdec hQW y
      (Or.inr rfl)
    obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDK
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDX0 hDo
    -- `Ω₂·(X₀ + W^y) = Ω₂·X₀ + ω^{Ω₂·y}`
    have hyω : ω ≤ y := (Lw.lw_omega_lt_SC hySC).le
    have hBy' : ω ≤ Bc.bcB S n y := by rw [hBy]; exact (Lw.lw_omega_lt_SC (rwEX_SC j)).le
    have eW : ∀ Y z : Ordinal.{0}, ω ≤ z → Om (1 + 1) * (Y + leWe z) = Om (1 + 1) * Y + ω ^ (Om (1 + 1) * z) :=
      fun Y z hz => by
        rw [mul_add, rvWe_mul, Ordinal.one_add_of_omega0_le hz]; rfl
    have hD1 : MvD S (Om (1 + 1) * (X0 + leWe y)) := by rw [eW _ _ hyω]; exact hDs
    have hB1 : Bc.bcB S n (Om (1 + 1) * (X0 + leWe y)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n y)) := by
      rw [eW _ _ hyω, hBs, hBX0, hBo, hBK, eW _ _ hBy']
    obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hD1
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    have hβown : ∀ d, d ≤ leWe (X0 + leWe (Om (1 + 1))) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) :=
      fun d _ => CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo
    have hlt := rwEX_lt_succ hβown hX0m j
    have hown : β + leWe (X0 + leWe y) ∈
        S.CSet (β + leWe (X0 + leWe y)) (S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1))) := by
      refine CSet.add_mem (CSet_mono le_self_add (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hβo)
        (leWe_mem (CSet.add_mem (CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m) (leWe_mem (CSet.of_lt hlt))))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDa hown
    refine ⟨hDT, ?_⟩
    show Bc.bcB S n (S.psi (β + ω ^ (Om (1 + 1) * (X0 + leWe y))) (Om (1 + 1))) =
      S.psi (Bc.bcB S n β + ω ^ (Om (1 + 1) * (X0B + leWe (rwEX S X0B (Bc.bcB S n β) j)))) (Om (1 + 1))
    rw [hBT, hBa, hBW, hB1, hBy]

section Main

variable {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every member of the code-level family moves** to a member at `λ'` over `B_n β`. -/
theorem rwG_B {β X Xh E : Ordinal.{0}} (h : RwG S l β X Xh E) : MvD S β →
    β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ MvD S E ∧ ∃ XB XhB, RwG S l' (Bc.bcB S n β) XB XhB (Bc.bcB S n E) ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  -- the class of codes below a bound
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
  -- one step: the term `W^E·ζ` over an offset `X₀ ↦ X₀_B`
  have hstep : ∀ {X0 Xh0 X0B Xh0B E ζ : Ordinal.{0}}, 1 ≤ E → GxCl (upsilon l) (ldAtR S l) E →
      (∃ j, E < rwEX S X0 β j) →
      GxCl (upsilon l) (ldAtR S l) ζ → ζ ≠ 0 → (∃ j, ζ < rvEE S X0 β E j) →
      MvD S β → β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))) →
      MvD S (Om (1 + 1) * X0) → Bc.bcB S n (Om (1 + 1) * X0) = Om (1 + 1) * X0B →
      MvD S (Om 1 * Xh0) → Bc.bcB S n (Om 1 * Xh0) = Om 1 * Xh0B →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 ∧
      MvD S E ∧ 1 ≤ Bc.bcB S n E ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n E) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n E) < Om 1 ∧
      (∃ j, Bc.bcB S n E < rwEX S X0B (Bc.bcB S n β) j) ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n ζ) ∧ Bc.bcB S n ζ ≠ 0 ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ζ) < Om 1 ∧
      (∃ j, Bc.bcB S n ζ < rvEE S X0B (Bc.bcB S n β) (Bc.bcB S n E) j) ∧
      MvD S (Om (1 + 1) * (X0 + leWe E * ζ)) ∧
      Bc.bcB S n (Om (1 + 1) * (X0 + leWe E * ζ)) = Om (1 + 1) * (X0B + leWe (Bc.bcB S n E) * Bc.bcB S n ζ) ∧
      MvD S (Om 1 * (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ)) ∧
      Bc.bcB S n (Om 1 * (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) * gxTh (upsilon l) (ldAtR S l) ζ)) =
        Om 1 * (Xh0B + leOe (gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n E)) *
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ζ)) := by
    intro X0 Xh0 X0B Xh0B E ζ h1 hE hEX hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0 hDXh0 hBXh0 IH
    obtain ⟨j', hj'⟩ := hEX
    obtain ⟨j, hj⟩ := hj
    have hζ1 : 1 ≤ ζ := Order.one_le_iff_ne_zero.2 hζ0
    have hζown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) := rvEE_gt j ζ hj
    have hEo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) := rwEX_gt j' E hj'
    have hEo' : E < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) := rwEEc_e_lt hEo hζ1
    obtain ⟨hDζ, hBζc, hΘζc, hΘζ⟩ := IH ζ hζ hζown
    obtain ⟨hDE, hBEc, hΘEc, hΘE⟩ := IH E hE hEo'
    have hΘ0 : gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hζ0)
      rw [gxTh_zero] at this; exact this.ne'
    have hBζ0 : Bc.bcB S n ζ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDζ).2 (pos_iff_ne_zero.2 hζ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    have hB1E : 1 ≤ Bc.bcB S n E := by have := leB_le (n := n) hD1 hDE h1; rwa [mwB_one] at this
    -- the classes
    set PB : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
      x < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hPB_def
    have hPBD : ∀ x, PB x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
    have hPBdec := hcls _ (fun x hx hxs => (IH x hx hxs).1)
    have hPBW : ∀ x, PB x → x < Om (1 + 1) := fun x hx => hx.2.2
    have hEW : E < Om (1 + 1) := hj'.trans (rwEX_lt_Om2 j')
    have hPE : PB E := ⟨hE, hEo', hEW⟩
    -- the level bounds move
    obtain ⟨hDEX, hBEX⟩ := rwEX_B (S := S) (n := n) hDβ hβo hX0m hDX0 hBX0 j'
    have hBEj : Bc.bcB S n E < rwEX S X0B (Bc.bcB S n β) j' := by
      have := (mvB_lt_iff (k := n) hDE hDEX).2 hj'; rwa [hBEX] at this
    obtain ⟨hDEE, hBEE⟩ := rwEEc_B (S := S) (n := n) hDβ hβo hX0m hDX0 hBX0 hEo PB hPBD hPBdec hPBW hPE j
    have hBlt := (mvB_lt_iff (k := n) hDζ hDEE).2 hj
    rw [hBEE] at hBlt
    obtain ⟨hDW, hBW⟩ := rwB_levC (S := S) (n := n) hDX0 hBX0 PB hPBD hPBdec hPBW hPE PB hPBD hPBdec hPBW
      ⟨hζ, hζown, hj.trans (rvEE_lt_Om2 j)⟩
    obtain ⟨hDO, hBO⟩ := rwB_levO (S := S) (n := n) hDXh0 hBXh0 (hΘEc.trans hc1) hΘEc (hΘζc.trans hc1) hΘζc
    refine ⟨mul_ne_zero (leOe_pos _).ne' hΘ0, hDE, hB1E, hBEc, ?_, ⟨j', hBEj⟩, hBζc, hBζ0, ?_, ⟨j, hBlt⟩,
      hDW, hBW, hDO, ?_⟩
    · rw [hΘE]; exact (Bc.bcB_bound' S n _ hΘEc).trans (psi_lt Low.InR_Om_one _)
    · rw [hΘζ]; exact (Bc.bcB_bound' S n _ hΘζc).trans (psi_lt Low.InR_Om_one _)
    · rw [hBO, hΘζ, hΘE]
  intro hDβ hβo IH
  induction h with
  | @one E ζ h1 hE hΘE hEX hζ hζ0 hΘ hj =>
    have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (β + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
    obtain ⟨hne, hDE, hB1, hBEc, hBΘE, hBEX, hBc, hB0, hBΘ, hBj, hDW, hBW, hDO, hBO⟩ :=
      hstep (X0B := 0) (Xh0B := 0) h1 hE hEX hζ hζ0 hj hDβ hβo hX0m (by rw [mul_zero]; exact hD0)
        (by rw [mul_zero, Bc.bcB_zero]) (by rw [mul_zero]; exact hD0) (by rw [mul_zero, Bc.bcB_zero]) (by
        intro x hx hxs; rw [zero_add] at hxs; exact IH x hx hxs)
    simp only [zero_add] at hDW hBW hDO hBO
    exact ⟨hne, hDE, _, _, RwG.one hB1 hBEc hBΘE hBEX hBc hB0 hBΘ hBj, hDW, hBW, hDO, hBO⟩
  | @add X0 Xh0 E0 E ζ h0 h1 hEE hE hΘE hEX hζ hζ0 hΘ hj ih =>
    have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
    obtain ⟨-, hDE0, X0B, Xh0B, hF0, hDX0, hBX0, hDXh0, hBXh0⟩ := ih (fun x hx hxs => IH x hx (hxs.trans_le hle0))
    have hX0m := (rwG_sh hl hX h0).1.mem
    obtain ⟨hne, hDE, hB1, hBEc, hBΘE, hBEX, hBc, hB0, hBΘ, hBj, hDW, hBW, hDO, hBO⟩ :=
      hstep h1 hE hEX hζ hζ0 hj hDβ hβo hX0m hDX0 hBX0 hDXh0 hBXh0 IH
    have hBEE : Bc.bcB S n E < Bc.bcB S n E0 := (mvB_lt_iff (k := n) hDE hDE0).2 hEE
    refine ⟨?_, hDE, _, _, RwG.add hF0 hB1 hBEE hBEc hBΘE hBEX hBc hB0 hBΘ hBj, hDW, hBW, hDO, hBO⟩
    intro h'
    exact hne (le_antisymm (h' ▸ le_add_self) zero_le)

/-- **The hypothesis `hShB` of `Rw.rwDigMove` for the family `rwShG`.** -/
theorem rwShG_B : ∀ b X Xh, rwShG S l b X Xh → MvD S b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (b + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, rwShG S l' (Bc.bcB S n b) XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB := by
  rintro b X Xh ⟨E, hE⟩ hDb hbo IH
  obtain ⟨hne, -, XB, XhB, hF, h3, h4, h5, h6⟩ := rwG_B hl hX hE hDb hbo IH
  exact ⟨hne, XB, XhB, ⟨_, hF⟩, h3, h4, h5, h6⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rw
