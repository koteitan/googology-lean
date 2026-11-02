import Googology.Trans.PoR.InaccPsi.R2.YbLev

/-!
# Refute first: the inacc-free level statement `Yb.YbIF`

`I₀ = S.I 0`, `Ω_k = Om k`, `Y = ψ_{Ω₃}(I₀)` (`ygY`), `K_q = Vd.VdK S 0 q` (the closure WITH the inaccessibles),
`YbK S q` (the closure WITHOUT them, `Yb.YbK`).

* `ygK_mem` (**every member of `YbK S q`, `q ≤ Ω₁`, lies in `Cl(I₀, b)` for every `b ≥ Ω₂`, and below `I₀`**: the
  inacc-free closure never needs a collapse argument `≥ I₀`);
* `ygY_notK` (**`Y = ψ_{Ω₃}(I₀) ∉ YbK S q`** for `q ≤ Ω₁`: else `Y ∈ Cl(I₀, Y) ∩ Ω₃ ⊆ Y`), `ygY_VdK` (**`Y ∈ K_q` for
  every `q`**, spelled with `I₀`), `ygVdK_notYb` (**NO-GO for the naive route**: `K_q ⊄ YbK S q`, so `YbIF` cannot be
  proved by copying a `K_q`-derivation and dropping the inaccessibles; a derivation may pass through `Y`);
* `ygTwin` (**the inaccessible washes out below `Ω₂`**: `ψ_{Ω₂}(Y) = ψ_{Ω₂}(Ω₃)`, since `Cl(Ω₃, b) ∩ Ω₃ ⊆ Y` for
  `b < Y`), `ygTwin_lev` (**the level `M₀ = ψ_{Ω₂}(ψ_{Ω₃}(I₀))` lies in `[B₂, θ)`, has the inacc spelling of datum `0`
  and the inacc-free spelling `ψ_{Ω₂}(Ω₃)`**: `YbIF` holds there, no evidence against it);
* `ygIF_low` (**`YbIF` holds at every level whose datum is below `Γ₀`**, by the clause `fix`), `YgIFHi`, `ygIF_of_hi`
  (**`YbIF` reduces to levels with datum `≥ Γ₀`**), `ygIF_B_add` (**`YbIF` holds at `B₂ + c`, `c < q`**).

No new axiom.  New definitions: `ygY` (one ordinal), `YgIFHi` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- `Y = ψ_{Ω₃}(I₀)`. -/
noncomputable def ygY (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (S.I 0) (Om (1 + 1 + 1))

theorem yg_W3_R : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)

theorem yg_W2_R : S.InR (Om (1 + 1)) := InR_Om_succ 1

theorem yg_I0_SC : SC (S.I 0) := InaccSeq.InR.SC S (InR_I 0)

theorem yg_Om_lt_I0 {x : Ordinal.{0}} (h : x < S.I 0) : Om x < S.I 0 :=
  calc Om x < Om (S.I 0) := Om_lt_Om.2 h
    _ = S.I 0 := S.fix 0

theorem yg_fin_lt_I0 : (1 + 1 + 1 : Ordinal.{0}) < S.I 0 :=
  (yg_I0_SC (S := S)).add_one_lt (Yb.yb_two_lt yg_I0_SC)

theorem yg_Om1_lt_Om2 : (Om1 : Ordinal.{0}) < OmTwo := by
  rw [Tw.tw_Om1_eq, Uc.uc_Om2_eq]
  exact Om_lt_Om.2 (lt_add_of_pos_right 1 zero_lt_one)

theorem yg_Om2_lt_I0 : (OmTwo : Ordinal.{0}) < S.I 0 := by
  rw [Uc.uc_Om2_eq]
  exact yg_Om_lt_I0 ((lt_add_of_pos_right (1 + 1) zero_lt_one).trans yg_fin_lt_I0)

theorem yg_Om3_lt_I0 : (Om (1 + 1 + 1) : Ordinal.{0}) < S.I 0 := yg_Om_lt_I0 yg_fin_lt_I0

/-- A fixed atom (`Vd.VdLtIn v Γ₀`) is below `Ω₂`. -/
theorem yg_fix_lt {v : Ordinal.{0}} (h : Vd.VdLtIn v (gamma 0)) : v < OmTwo := by
  rcases h with ⟨hvB, -⟩ | ⟨S', -, hvθ, -⟩
  · exact hvB.trans Uc.ucB_lt_Om2
  · rw [Uc.uc_Om2_eq]
    exact hvθ.trans (psi_lt (S := S') (InR_Om_succ 1) _)

/-- **Every member of the inacc-free closure lies in `Cl(I₀, b)` (`b ≥ Ω₂`) and below `I₀`.** -/
theorem ygK_mem {q b : Ordinal.{0}} (hq : q ≤ Om1) (hb : OmTwo ≤ b) :
    ∀ x, Yb.YbK S q x → x ∈ S.CSet (S.I 0) b ∧ x < S.I 0 := by
  intro x hx
  induction hx with
  | small h =>
    have h2 : _ < OmTwo := (h.trans_le hq).trans yg_Om1_lt_Om2
    exact ⟨CSet.of_lt (h2.trans_le hb), h2.trans yg_Om2_lt_I0⟩
  | fix hv =>
    have h2 := yg_fix_lt hv
    exact ⟨CSet.of_lt (h2.trans_le hb), h2.trans yg_Om2_lt_I0⟩
  | add _ _ ih1 ih2 => exact ⟨CSet.add_mem ih1.1 ih2.1, yg_I0_SC.isPrincipal ih1.2 ih2.2⟩
  | phi _ _ ih1 ih2 => exact ⟨CSet.phi_mem ih1.1 ih2.1, yg_I0_SC.2 _ ih1.2 _ ih2.2⟩
  | om _ ih => exact ⟨CSet.Om_mem ih.1, yg_Om_lt_I0 ih.2⟩
  | coll hπ _ _ _ ihπ ihe => exact ⟨CSet.psi_mem ihe.2 hπ ihπ.1 ihe.1, (psi_lt hπ _).trans ihπ.2⟩

theorem ygY_bounds : (OmTwo : Ordinal.{0}) < ygY S ∧ ygY S < Om (1 + 1 + 1) := by
  rw [Uc.uc_Om2_eq]; exact psiS_bounds (S.I 0) (1 + 1)

/-- **`Y = ψ_{Ω₃}(I₀)` is not in the inacc-free closure** (`q ≤ Ω₁`). -/
theorem ygY_notK {q : Ordinal.{0}} (hq : q ≤ Om1) : ¬ Yb.YbK S q (ygY S) := fun h => by
  obtain ⟨hC, -⟩ := ygK_mem hq ygY_bounds.1.le _ h
  exact lt_irrefl _ (lt_psi_of_mem yg_W3_R hC (psi_lt yg_W3_R _))

theorem yg_VdK_one (q : Ordinal.{0}) : Vd.VdK S 0 q 1 := by
  have h := Vd.VdK.phi (S := S) (s := 0) (q := q) Vd.VdK.zero Vd.VdK.zero
  rwa [veblen_zero_apply, opow_zero] at h

theorem yg_W3_ne : (Om (1 + 1 + 1) : Ordinal.{0}) ≠ Om (0 + 1) := by
  intro h
  have e := Om_strictMono.injective h
  rw [zero_add] at e
  have : (1 : Ordinal.{0}) < 1 + 1 + 1 :=
    (lt_add_of_pos_right 1 zero_lt_one).trans (lt_add_of_pos_right (1 + 1) zero_lt_one)
  exact absurd e this.ne'

/-- **`Y` is in the closure with inaccessibles at every threshold** (spelling `ψ_{Ω₃}(I₀)`). -/
theorem ygY_VdK (q : Ordinal.{0}) : Vd.VdK S 0 q (ygY S) :=
  Vd.VdK.coll yg_W3_R yg_W3_ne
    (Vd.VdK.om (Vd.VdK.add (Vd.VdK.add (yg_VdK_one q) (yg_VdK_one q)) (yg_VdK_one q))) (Vd.VdK.inacc 0)

/-- **NO-GO for the naive route to `YbIF`**: at every threshold `q ≤ Ω₁` the closure with inaccessibles is not
contained in the inacc-free one. -/
theorem ygVdK_notYb {q : Ordinal.{0}} (hq : q ≤ Om1) : ¬ ∀ x, Vd.VdK S 0 q x → Yb.YbK S q x :=
  fun h => ygY_notK hq (h _ (ygY_VdK q))

/-! ## The inaccessible washes out below `Ω₂` -/

/-- `Cl(Ω₃, b) ⊆ Cl(Y, b) ∩ Cl(I₀, Y)` for `b < Y`. -/
theorem ygTwin_sub {b : Ordinal.{0}} (hbY : b < ygY S) :
    ∀ x ∈ S.CSet (Om (1 + 1 + 1)) b, x ∈ S.CSet (ygY S) b ∧ x ∈ S.CSet (S.I 0) (ygY S) := by
  intro x hx
  induction hx with
  | small h => exact ⟨CSet.of_lt h, CSet.of_lt (h.trans hbY)⟩
  | zero => exact ⟨CSet.zero_mem _ _, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨CSet.I_mem _ _ n, CSet.I_mem _ _ n⟩
  | inaccW => exact ⟨CSet.Iw_mem _ _, CSet.Iw_mem _ _⟩
  | add _ _ ih1 ih2 => exact ⟨CSet.add_mem ih1.1 ih2.1, CSet.add_mem ih1.2 ih2.2⟩
  | phi _ _ ih1 ih2 => exact ⟨CSet.phi_mem ih1.1 ih2.1, CSet.phi_mem ih1.2 ih2.2⟩
  | om _ ih => exact ⟨CSet.Om_mem ih.1, CSet.Om_mem ih.2⟩
  | @coll π e hπ _ _ ihπ ihe =>
    have heI : e.1 < S.I 0 := e.2.trans yg_Om3_lt_I0
    have heY : e.1 < ygY S := lt_psi_of_mem yg_W3_R ihe.2 e.2
    exact ⟨CSet.psi_mem heY hπ ihπ.1 ihe.1, CSet.psi_mem heI hπ ihπ.2 ihe.2⟩

/-- **`ψ_{Ω₂}(ψ_{Ω₃}(I₀)) = ψ_{Ω₂}(Ω₃)`.** -/
theorem ygTwin : S.psi (ygY S) (Om (1 + 1)) = S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) := by
  refine le_antisymm (psi_mono yg_W2_R ygY_bounds.2.le).1 ?_
  have hb2 : S.psi (ygY S) (Om (1 + 1)) < Om (1 + 1) := psi_lt yg_W2_R _
  have hbY : S.psi (ygY S) (Om (1 + 1)) < ygY S := by
    have := ygY_bounds (S := S).1; rw [Uc.uc_Om2_eq] at this; exact hb2.trans this
  refine psi_le_of_good ?_ fun x hx hx2 => lt_psi_of_mem yg_W2_R (ygTwin_sub hbY x hx).1 hx2
  exact CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))

theorem yg_fin_lt_omega : (1 + 1 + 1 : Ordinal.{0}) < ω := by
  exact isPrincipal_add_omega0 (isPrincipal_add_omega0 one_lt_omega0 one_lt_omega0) one_lt_omega0

/-- **The level `M₀ = ψ_{Ω₂}(ψ_{Ω₃}(I₀))`**: in `[B₂, θ)`, spelled with `I₀` at every threshold (datum `0`), and
equal to the inacc-free `ψ_{Ω₂}(Ω₃)`, which lies in `YbK S q` for every strongly critical `q`. -/
theorem ygTwin_lev {q : Ordinal.{0}} (hq : SC q) :
    Uc.ucB ≤ S.psi (ygY S) (Om (1 + 1)) ∧ S.psi (ygY S) (Om (1 + 1)) < ConjT.th S ∧
      Vd.VdK S 0 q (S.psi (ygY S) (Om (1 + 1))) ∧ Yb.YbK S q (S.psi (ygY S) (Om (1 + 1))) := by
  have hne : (Om (1 + 1) : Ordinal.{0}) ≠ Om (0 + 1) := by
    intro h; have e := Om_strictMono.injective h; rw [zero_add] at e
    exact absurd e (lt_add_of_pos_right (1 : Ordinal.{0}) zero_lt_one).ne'
  have hW3 : (Om (1 + 1 + 1) : Ordinal.{0}) ∈ S.CSet (Om ω) (ConjT.th S) :=
    CSet.Om_mem (CSet.add_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _)) (CSet.one_mem _ _))
  have hlt : (Om (1 + 1 + 1) : Ordinal.{0}) < Om ω := Om_lt_Om.2 yg_fin_lt_omega
  have h30 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_one (1 + 1))).ne'
  have hS : SC (Om (1 + 1 + 1) : Ordinal.{0}) := SC_Om h30
  have h23 : (Om (1 + 1) : Ordinal.{0}) < Om (1 + 1 + 1) :=
    Om_lt_Om.2 (lt_add_of_pos_right (1 + 1) zero_lt_one)
  have h13 : (1 : Ordinal.{0}) < Om (1 + 1 + 1) :=
    (lt_add_of_pos_right (1 : Ordinal.{0}) zero_lt_one).trans (Yb.yb_two_lt hS)
  have hE : Uc.ucE < Om (1 + 1 + 1) := by
    rw [Uc.uc_E_eq_veblen, Uc.uc_Om2_eq]
    exact hS.2 _ h13 _ (hS.add_one_lt h23)
  have hne1 : (Om (1 + 1) : Ordinal.{0}) ≠ Om 1 := by
    intro h; have e := Om_strictMono.injective h
    exact absurd e (lt_add_of_pos_right (1 : Ordinal.{0}) zero_lt_one).ne'
  have h2q : (1 + 1 : Ordinal.{0}) < q := Yb.yb_two_lt hq
  have h3q : (1 + 1 + 1 : Ordinal.{0}) < q := hq.add_one_lt h2q
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ygTwin, ← Uc.uc_psiE_eq_B (S := S)]; exact (psi_mono yg_W2_R hE.le).1
  · rw [ygTwin]; exact psi_lt_psi_of_mem yg_W2_R hlt hW3
  · exact Vd.VdK.coll yg_W2_R hne
      (Vd.VdK.om (Vd.VdK.add (yg_VdK_one q) (yg_VdK_one q))) (ygY_VdK q)
  · rw [ygTwin]; exact Yb.YbK.coll yg_W2_R hne1 (Yb.YbK.om (Yb.YbK.small h2q)) (Yb.YbK.om (Yb.YbK.small h3q))

/-! ## `YbIF` at low data, and the reduction to data `≥ Γ₀` -/

/-- **`YbIF` holds at every level whose datum is below `Γ₀`** (clause `fix` of `Yb.YbK`). -/
theorem ygIF_low {M : Ordinal.{0}} (q : Ordinal.{0}) (hMθ : M < ConjT.th S)
    (h1 : M < Uc.ucB → Uc.ucDat M < gamma 0) (h2 : Uc.ucB ≤ M → Vd.vdD S 0 M < gamma 0) : Yb.YbK S q M := by
  rcases lt_or_ge M Uc.ucB with hMB | hMB
  · exact Yb.YbK.fix (Or.inl ⟨hMB, h1 hMB⟩)
  · exact Yb.YbK.fix (Or.inr ⟨S, hMB, hMθ, gamma 0, Lq.lq_gamma_SC 0, le_rfl, h2 hMB⟩)

/-- **`YbIF` at the levels with datum `≥ Γ₀`** (the part of `Yb.YbIF` not covered by `fix`). -/
def YgIFHi (S : InaccSeq.{0}) : Prop :=
  ∀ M q : Ordinal.{0}, Om1 ≤ M → M < ConjT.th S → SC q → q ≤ Om1 →
    (M < Uc.ucB → Uc.ucDat M < q) → (Uc.ucB ≤ M → Vd.vdD S 0 M < q) →
    (M < Uc.ucB → gamma 0 ≤ Uc.ucDat M) → (Uc.ucB ≤ M → gamma 0 ≤ Vd.vdD S 0 M) → Yb.YbK S q M

/-- **`YbIF` reduces to `YgIFHi`.** -/
theorem ygIF_of_hi (H : YgIFHi S) : Yb.YbIF S := by
  intro M q hΩM hMθ hq hq1 h1 h2
  rcases lt_or_ge M Uc.ucB with hMB | hMB
  · rcases lt_or_ge (Uc.ucDat M) (gamma 0) with hd | hd
    · exact ygIF_low q hMθ (fun _ => hd) (fun h => absurd h (not_le.2 hMB))
    · exact H M q hΩM hMθ hq hq1 h1 h2 (fun _ => hd) (fun h => absurd h (not_le.2 hMB))
  · rcases lt_or_ge (Vd.vdD S 0 M) (gamma 0) with hd | hd
    · exact ygIF_low q hMθ (fun h => absurd hMB (not_le.2 h)) (fun _ => hd)
    · exact H M q hΩM hMθ hq hq1 h1 h2 (fun h => absurd hMB (not_le.2 h)) (fun _ => hd)

/-- **`YbIF` at the levels `B₂ + c`, `c < q`** (just above `B₂`). -/
theorem ygIF_B_add {q c : Ordinal.{0}} (hq : SC q) (hc : c < q) : Yb.YbK S q (Uc.ucB + c) :=
  Yb.YbK.add (Yb.ybK_B hq) (Yb.YbK.small hc)

end Googology.Trans.PoR.InaccPsi.R2.Yg
